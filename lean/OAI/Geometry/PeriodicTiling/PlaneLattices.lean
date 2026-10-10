import OAI.Geometry.PeriodicTiling.TilingBasic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

namespace OAI

universe uG uι

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

section Periods

variable {G : Type uG} [AddCommGroup G] {A : Set G} {v : G}

theorem Period.zsmul (hv : Period A v) (n : ℤ) : Period A (n • v) :=
  (periodSubgroup A).zsmul_mem hv n

theorem Period.nsmul (hv : Period A v) (n : ℕ) : Period A (n • v) :=
  (periodSubgroup A).nsmul_mem hv n

theorem exists_pos_zsmul_mem (P : AddSubgroup G) (hP : P.FiniteIndex) (v : G) :
    ∃ q : ℕ, 0 < q ∧ (q : ℤ) • v ∈ P := by
  obtain ⟨q, hq, _, hmem⟩ :=
    AddSubgroup.exists_nsmul_mem_of_index_ne_zero (H := P) hP.index_ne_zero v
  exact ⟨q, hq, by simpa only [natCast_zsmul] using hmem⟩

end Periods

def bezoutCoordinates (a b s t : ℤ) (h : s * a + t * b = 1) : Plane ≃+ Plane where
  toFun z := (a * z.1 - t * z.2, b * z.1 + s * z.2)
  invFun z := (s * z.1 + t * z.2, -b * z.1 + a * z.2)
  left_inv := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · change s * (a * x - t * y) + t * (b * x + s * y) = x
      calc
        _ = (s * a + t * b) * x := by ring
        _ = x := by rw [h, one_mul]
    · change -b * (a * x - t * y) + a * (b * x + s * y) = y
      calc
        _ = (s * a + t * b) * y := by ring
        _ = y := by rw [h, one_mul]
  right_inv := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · change a * (s * x + t * y) - t * (-b * x + a * y) = x
      calc
        _ = (s * a + t * b) * x := by ring
        _ = x := by rw [h, one_mul]
    · change b * (s * x + t * y) + s * (-b * x + a * y) = y
      calc
        _ = (s * a + t * b) * y := by ring
        _ = y := by rw [h, one_mul]
  map_add' := by
    rintro ⟨x, y⟩ ⟨z, w⟩
    apply Prod.ext <;> dsimp <;> ring

theorem exists_primitive_coordinates {h : Plane} (hh : h ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ T : Plane ≃+ Plane, T ((m : ℤ), 0) = h := by
  have hcoords : h.1 ≠ 0 ∨ h.2 ≠ 0 := by
    by_cases hx : h.1 = 0
    · right
      intro hy
      exact hh (Prod.ext hx hy)
    · exact Or.inl hx
  have hg : 0 < Int.gcd h.1 h.2 := Int.gcd_pos_iff.mpr hcoords
  obtain ⟨a, b, hab, ha, hb⟩ := Int.exists_gcd_one hg
  have hbez : Int.gcdA a b * a + Int.gcdB a b * b = 1 := by
    have he := Int.gcd_eq_gcd_ab a b
    rw [hab] at he
    simpa only [Int.natCast_one, mul_comm] using he.symm
  refine ⟨Int.gcd h.1 h.2, hg, bezoutCoordinates a b _ _ hbez, ?_⟩
  change (a * (Int.gcd h.1 h.2 : ℤ) - Int.gcdB a b * 0,
    b * (Int.gcd h.1 h.2 : ℤ) + Int.gcdA a b * 0) = h
  apply Prod.ext
  · simpa using ha.symm
  · simpa using hb.symm

def coordinateSubgroup (T : Plane ≃+ Plane) (m L : ℤ) : AddSubgroup Plane :=
  ((AddSubgroup.zmultiples m).prod (AddSubgroup.zmultiples L)).map T.toAddMonoidHom

theorem index_coordinateSubgroup (T : Plane ≃+ Plane) (m L : ℤ) :
    (coordinateSubgroup T m L).index = m.natAbs * L.natAbs := by
  rw [coordinateSubgroup, AddSubgroup.index_map_of_bijective T.bijective,
    AddSubgroup.index_prod, Int.index_zmultiples, Int.index_zmultiples]

theorem coordinateSubgroup_le (P : AddSubgroup Plane) (T : Plane ≃+ Plane) (m L : ℤ)
    (hm : T (m, 0) ∈ P) (hL : T (0, L) ∈ P) : coordinateSubgroup T m L ≤ P := by
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp hx.1
  obtain ⟨b, hb⟩ := AddSubgroup.mem_zmultiples_iff.mp hx.2
  have he : a • (m, (0 : ℤ)) + b • ((0 : ℤ), L) = x := by
    apply Prod.ext
    · simpa using ha
    · simpa using hb
  have hmem := P.add_mem (P.zsmul_mem hm a) (P.zsmul_mem hL b)
  rwa [← map_zsmul, ← map_zsmul, ← map_add, he] at hmem

theorem finiteIndex_of_coordinate_mem (P : AddSubgroup Plane) (T : Plane ≃+ Plane)
    (m L : ℤ) (hm : m ≠ 0) (hL : L ≠ 0)
    (hpm : T (m, 0) ∈ P) (hpL : T (0, L) ∈ P) : P.FiniteIndex := by
  let : (coordinateSubgroup T m L).FiniteIndex := ⟨by
    rw [index_coordinateSubgroup]
    exact mul_ne_zero (fun h => hm (Int.natAbs_eq_zero.mp h))
      (fun h => hL (Int.natAbs_eq_zero.mp h))⟩
  exact AddSubgroup.finiteIndex_of_le (coordinateSubgroup_le P T m L hpm hpL)

theorem FullyPeriodic.exists_coordinate_period {E : Set Plane}
    (hE : FullyPeriodic E) (T : Plane ≃+ Plane) :
    ∃ Q : ℕ, 0 < Q ∧ Period E (T (0, (Q : ℤ))) := by
  obtain ⟨P, hP, hperiod⟩ := hE
  obtain ⟨Q, hQ, hmem⟩ := exists_pos_zsmul_mem P hP (T (0, 1))
  have he : (Q : ℤ) • T (0, 1) = T (0, (Q : ℤ)) := by
    rw [← map_zsmul]
    congr 1
    ext <;> simp
  refine ⟨Q, hQ, ?_⟩
  rw [← he]
  exact hperiod _ hmem

theorem fullyPeriodic_of_coordinate_periods {E : Set Plane}
    (T : Plane ≃+ Plane) (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (hx : Period E (T ((m : ℤ), 0))) (hy : Period E (T (0, (L : ℤ)))) :
    FullyPeriodic E := by
  refine ⟨periodSubgroup E, ?_, fun _ hv => hv⟩
  exact finiteIndex_of_coordinate_mem (periodSubgroup E) T m L
    (by exact_mod_cast (ne_of_gt hm)) (by exact_mod_cast (ne_of_gt hL)) hx hy

theorem Period.mem_coordinate_mod {D : Set Plane} {T : Plane ≃+ Plane} {m : ℕ}
    (hv : Period D (T ((m : ℤ), 0))) (x y : ℤ) :
    T (x, y) ∈ D ↔ T (x % (m : ℤ), y) ∈ D := by
  have he : T (x % (m : ℤ), y) + (x / (m : ℤ)) • T ((m : ℤ), 0) = T (x, y) := by
    rw [← map_zsmul, ← map_add]
    congr 1
    apply Prod.ext
    · change x % (m : ℤ) + (x / (m : ℤ)) * (m : ℤ) = x
      simpa only [add_comm, mul_comm] using Int.emod_add_mul_ediv x (m : ℤ)
    · simp
  have hp := (hv.zsmul (x / (m : ℤ))) (T (x % (m : ℤ), y))
  rwa [he] at hp

def planeDet (u v : Plane) : ℤ := u.1 * v.2 - u.2 * v.1

@[simp] theorem planeDet_self (u : Plane) : planeDet u u = 0 := by
  simp [planeDet, mul_comm]

theorem planeDet_swap (u v : Plane) : planeDet u v = -planeDet v u := by
  dsimp [planeDet]
  ring

theorem planeDet_zsmul_left (n : ℤ) (u v : Plane) :
    planeDet (n • u) v = n * planeDet u v := by
  change (n * u.1) * v.2 - (n * u.2) * v.1 = n * (u.1 * v.2 - u.2 * v.1)
  ring

theorem planeDet_zsmul_right (n : ℤ) (u v : Plane) :
    planeDet u (n • v) = n * planeDet u v := by
  change u.1 * (n * v.2) - u.2 * (n * v.1) = n * (u.1 * v.2 - u.2 * v.1)
  ring

theorem zsmul_plane_ne_zero {n : ℤ} {v : Plane} (hn : n ≠ 0) (hv : v ≠ 0) :
    n • v ≠ 0 := by
  intro he
  apply hv
  apply Prod.ext
  · have h := congrArg Prod.fst he
    change n * v.1 = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hn
  · have h := congrArg Prod.snd he
    change n * v.2 = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hn

def integerCombination (u v : Plane) : Plane →+ Plane where
  toFun z := z.1 • u + z.2 • v
  map_zero' := by simp
  map_add' := by
    intro x y
    change (x.1 + y.1) • u + (x.2 + y.2) • v =
      (x.1 • u + x.2 • v) + (y.1 • u + y.2 • v)
    rw [add_smul, add_smul]
    abel

def integerSpan2 (u v : Plane) : AddSubgroup Plane := (integerCombination u v).range

theorem mem_integerSpan2 (u v z : Plane) :
    z ∈ integerSpan2 u v ↔ ∃ a b : ℤ, a • u + b • v = z := by
  constructor
  · rintro ⟨⟨a, b⟩, he⟩
    exact ⟨a, b, he⟩
  · rintro ⟨a, b, he⟩
    exact ⟨(a, b), he⟩

theorem determinant_smul_eq (u v z : Plane) :
    planeDet u v • z = planeDet z v • u + planeDet u z • v := by
  apply Prod.ext
  · change (u.1 * v.2 - u.2 * v.1) * z.1 =
      (z.1 * v.2 - z.2 * v.1) * u.1 + (u.1 * z.2 - u.2 * z.1) * v.1
    ring
  · change (u.1 * v.2 - u.2 * v.1) * z.2 =
      (z.1 * v.2 - z.2 * v.1) * u.2 + (u.1 * z.2 - u.2 * z.1) * v.2
    ring

theorem integerSpan2_finiteIndex (u v : Plane) (huv : planeDet u v ≠ 0) :
    (integerSpan2 u v).FiniteIndex := by
  have hm (z : Plane) : planeDet u v • z ∈ integerSpan2 u v :=
    (mem_integerSpan2 u v _).mpr ⟨planeDet z v, planeDet u z,
      (determinant_smul_eq u v z).symm⟩
  apply finiteIndex_of_coordinate_mem (integerSpan2 u v) (AddEquiv.refl Plane)
    (planeDet u v) (planeDet u v) huv huv
  · simpa using hm (1, 0)
  · simpa using hm (0, 1)

theorem fullyPeriodic_of_independent_periods {E : Set Plane} {u v : Plane}
    (hu : Period E u) (hv : Period E v) (huv : planeDet u v ≠ 0) : FullyPeriodic E := by
  refine ⟨integerSpan2 u v, integerSpan2_finiteIndex u v huv, ?_⟩
  intro z hz
  obtain ⟨a, b, rfl⟩ := (mem_integerSpan2 u v z).mp hz
  exact (hu.zsmul a).add (hv.zsmul b)

theorem exists_smul_eq_of_collinear {u v : Plane}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : planeDet u v = 0) :
    ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • u = b • v := by
  by_cases hu₁ : u.1 = 0
  · have hu₂ : u.2 ≠ 0 := fun h => hu (Prod.ext hu₁ h)
    have he : u.2 * v.1 = 0 := by
      simpa only [planeDet, hu₁, zero_mul, zero_sub, neg_eq_zero] using huv
    have hv₁ : v.1 = 0 := (mul_eq_zero.mp he).resolve_left hu₂
    have hv₂ : v.2 ≠ 0 := fun h => hv (Prod.ext hv₁ h)
    refine ⟨v.2, u.2, hv₂, hu₂, ?_⟩
    apply Prod.ext
    · change v.2 * u.1 = u.2 * v.1
      simp [hu₁, hv₁]
    · change v.2 * u.2 = u.2 * v.2
      exact mul_comm _ _
  · have he : u.1 * v.2 = u.2 * v.1 := sub_eq_zero.mp huv
    have hv₁ : v.1 ≠ 0 := by
      intro hv₁
      have hv₂ : v.2 = 0 := (mul_eq_zero.mp (by simpa [hv₁] using he)).resolve_left hu₁
      exact hv (Prod.ext hv₁ hv₂)
    refine ⟨v.1, u.1, hv₁, hu₁, ?_⟩
    apply Prod.ext
    · change v.1 * u.1 = u.1 * v.1
      exact mul_comm _ _
    · change v.1 * u.2 = u.1 * v.2
      simpa only [mul_comm] using he.symm

theorem planeDet_zero_trans {u v w : Plane} (hv : v ≠ 0)
    (huv : planeDet u v = 0) (hvw : planeDet v w = 0) : planeDet u w = 0 := by
  by_cases hu : u = 0
  · simp [hu, planeDet]
  obtain ⟨a, b, ha, _, he⟩ := exists_smul_eq_of_collinear hu hv huv
  have hd : planeDet (a • u) w = planeDet (b • v) w :=
    congrArg (fun z => planeDet z w) he
  rw [planeDet_zsmul_left, planeDet_zsmul_left, hvw, mul_zero] at hd
  exact (mul_eq_zero.mp hd).resolve_left ha

theorem exists_common_collinear_multiple (s : Finset Plane) (hne : s.Nonempty)
    (h0 : ∀ v ∈ s, v ≠ 0)
    (hcol : ∀ v ∈ s, ∀ w ∈ s, planeDet v w = 0) :
    ∃ u : Plane, u ≠ 0 ∧ ∀ v ∈ s, ∃ n : ℤ, u = n • v := by
  classical
  obtain ⟨v₀, hv₀⟩ := hne
  have hex : ∀ w : ↥s, ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • v₀ = b • (w : Plane) :=
    fun w => exists_smul_eq_of_collinear (h0 v₀ hv₀) (h0 w w.property)
      (hcol v₀ hv₀ w w.property)
  choose a b ha hb he using hex
  let c : ℤ := ∏ w : ↥s, a w
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun w _ => ha w)
  refine ⟨c • v₀, zsmul_plane_ne_zero hc (h0 v₀ hv₀), ?_⟩
  intro v hv
  let w : ↥s := ⟨v, hv⟩
  let d : ℤ := ∏ w' ∈ (Finset.univ.erase w), a w'
  have hdc : d * a w = c := by
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ w)
  refine ⟨d * b w, ?_⟩
  calc
    c • v₀ = (d * a w) • v₀ := by rw [hdc]
    _ = d • (a w • v₀) := mul_smul _ _ _
    _ = d • (b w • v) := by rw [he w]
    _ = (d * b w) • v := (mul_smul _ _ _).symm

theorem exists_transverse_vector (s : Finset Plane) (h0 : ∀ v ∈ s, v ≠ 0) :
    ∃ e : Plane, e ≠ 0 ∧ ∀ v ∈ s, planeDet e v ≠ 0 := by
  classical
  obtain ⟨N, hN⟩ := (s.image (fun v => v.2 / v.1)).exists_notMem
  refine ⟨(1, N), by simp, ?_⟩
  intro v hv he
  have he' : v.2 = N * v.1 := by
    change 1 * v.2 - N * v.1 = 0 at he
    simpa only [one_mul] using sub_eq_zero.mp he
  have hv₁ : v.1 ≠ 0 := by
    intro hv₁
    have hv₂ : v.2 = 0 := by simpa [hv₁] using he'
    exact h0 v hv (Prod.ext hv₁ hv₂)
  apply hN
  apply Finset.mem_image.mpr
  refine ⟨v, hv, ?_⟩
  rw [he']
  exact Int.mul_ediv_cancel N hv₁

theorem exists_common_transverse {ι : Type uι} [Fintype ι]
    (v : ι → Plane) (h0 : ∀ i, v i ≠ 0)
    (hpair : ∀ i j, i ≠ j → planeDet (v i) (v j) ≠ 0) :
    ∃ e : Plane, e ≠ 0 ∧ (∀ i, planeDet e (v i) ≠ 0) ∧
      ∀ i j, i ≠ j → ∃ a b : ℤ, e = a • v i + b • v j := by
  classical
  obtain ⟨w, hw, htrans⟩ := exists_transverse_vector (Finset.univ.image v) (by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact h0 i)
  let J := {ij : ι × ι // ij.1 ≠ ij.2}
  let P : AddSubgroup Plane := ⨅ ij : J, integerSpan2 (v ij.val.1) (v ij.val.2)
  have hP : P.FiniteIndex := AddSubgroup.finiteIndex_iInf
    (fun ij : J => integerSpan2_finiteIndex _ _ (hpair _ _ ij.property))
  obtain ⟨q, hq, hmem⟩ := exists_pos_zsmul_mem P hP w
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  refine ⟨(q : ℤ) • w, zsmul_plane_ne_zero hq' hw, ?_, ?_⟩
  · intro i
    rw [planeDet_zsmul_left]
    exact mul_ne_zero hq' (htrans (v i) (Finset.mem_image_of_mem v (Finset.mem_univ i)))
  · intro i j hij
    have hm : (q : ℤ) • w ∈ integerSpan2 (v i) (v j) :=
      (AddSubgroup.mem_iInf.mp hmem) (⟨(i, j), hij⟩ : J)
    obtain ⟨a, b, he⟩ := (mem_integerSpan2 _ _ _).mp hm
    exact ⟨a, b, he.symm⟩

theorem exists_common_second_vector {ι : Type uι} [Fintype ι]
    (v : ι → Plane) (i₀ : ι) (e : Plane)
    (htrans : ∀ i, planeDet e (v i) ≠ 0) :
    ∃ K : ℕ, 0 < K ∧ ∀ i, ∃ a b : ℤ, a ≠ 0 ∧
      (K : ℤ) • v i₀ = b • e + a • v i := by
  let P : AddSubgroup Plane := ⨅ i, integerSpan2 e (v i)
  have hP : P.FiniteIndex := AddSubgroup.finiteIndex_iInf
    (fun i => integerSpan2_finiteIndex e (v i) (htrans i))
  obtain ⟨K, hK, hmem⟩ := exists_pos_zsmul_mem P hP (v i₀)
  have hK' : (K : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  refine ⟨K, hK, ?_⟩
  intro i
  obtain ⟨b, a, he⟩ := (mem_integerSpan2 e (v i) _).mp
    ((AddSubgroup.mem_iInf.mp hmem) i)
  refine ⟨a, b, ?_, he.symm⟩
  intro ha
  have hd : planeDet e ((K : ℤ) • v i₀) = 0 := by
    rw [← he, ha, zero_smul, add_zero, planeDet_zsmul_right, planeDet_self, mul_zero]
  rw [planeDet_zsmul_right] at hd
  exact mul_ne_zero hK' (htrans i₀) hd

end PeriodicTilingThree

end

end OAI
