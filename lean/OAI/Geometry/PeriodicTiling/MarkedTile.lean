import OAI.Geometry.PeriodicTiling.TilingBasic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

namespace OAI

namespace PeriodicTilingThree.MarkedTile

abbrev Residue (m : ℕ) := Fin 3 → ZMod m

def scale (m : ℕ) : Lattice 3 →+ Lattice 3 where
  toFun x i := (m : ℤ) * x i
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [mul_add]

@[simp] theorem scale_apply (m : ℕ) (x : Lattice 3) (i : Fin 3) :
    scale m x i = (m : ℤ) * x i := rfl

theorem scale_injective (m : ℕ) [NeZero m] : Function.Injective (scale m) := by
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  intro x y h
  funext i
  exact mul_left_cancel₀ hm (congrFun h i)

def residue (m : ℕ) : Lattice 3 →+ Residue m where
  toFun x i := (x i : ZMod m)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

@[simp] theorem residue_apply (m : ℕ) (x : Lattice 3) (i : Fin 3) :
    residue m x i = (x i : ZMod m) := rfl

@[simp] theorem residue_scale (m : ℕ) (x : Lattice 3) :
    residue m (scale m x) = 0 := by
  ext i
  simp [scale, residue]

theorem exists_scale_of_residue_eq_zero (m : ℕ) {x : Lattice 3}
    (h : residue m x = 0) : ∃ a : Lattice 3, scale m a = x := by
  have hd : ∀ i : Fin 3, ∃ a : ℤ, x i = (m : ℤ) * a := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (x i) m).mp
    exact congrFun h i
  choose a ha using hd
  exact ⟨a, funext fun i => (ha i).symm⟩

structure ResidueSection (m : ℕ) where
  t : Residue m → Lattice 3
  residue_t : ∀ v, residue m (t v) = v

namespace ResidueSection

variable {m : ℕ} (s : ResidueSection m)

@[simp] theorem residue_t_apply (v : Residue m) : residue m (s.t v) = v :=
  s.residue_t v

theorem t_injective : Function.Injective s.t := by
  intro v v' h
  have := congrArg (residue m) h
  simpa using this

def t0 : Lattice 3 := s.t 0

@[simp] theorem residue_t0 : residue m s.t0 = 0 := s.residue_t 0

theorem coordinates_injective [NeZero m] :
    Function.Injective (fun p : Lattice 3 × Residue m => scale m p.1 + s.t p.2) := by
  rintro ⟨a, v⟩ ⟨a', v'⟩ h
  have hv : v = v' := by
    have := congrArg (residue m) h
    simpa using this
  subst v'
  have ha : a = a' := scale_injective m (add_right_cancel h)
  exact Prod.ext ha rfl

theorem coordinates_surjective :
    Function.Surjective (fun p : Lattice 3 × Residue m => scale m p.1 + s.t p.2) := by
  intro x
  have hz : residue m (x - s.t (residue m x)) = 0 := by simp
  obtain ⟨a, ha⟩ := exists_scale_of_residue_eq_zero m hz
  refine ⟨(a, residue m x), ?_⟩
  change scale m a + s.t (residue m x) = x
  rw [ha, sub_add_cancel]

theorem coordinates_bijective [NeZero m] :
    Function.Bijective (fun p : Lattice 3 × Residue m => scale m p.1 + s.t p.2) :=
  ⟨s.coordinates_injective, s.coordinates_surjective⟩

noncomputable section

variable [NeZero m]

def T0 : Finset (Lattice 3) := Finset.univ.image s.t

def Tstar : Finset (Lattice 3) := s.T0.erase s.t0

def t1 (w : Lattice 3) (v : Residue m) : Lattice 3 :=
  if v = 0 then scale m w + s.t0 else s.t v

def T1 (w : Lattice 3) : Finset (Lattice 3) := Finset.univ.image (s.t1 w)

@[simp] theorem mem_T0 {x : Lattice 3} : x ∈ s.T0 ↔ ∃ v, s.t v = x := by
  classical
  simp [T0]

@[simp] theorem t0_mem_T0 : s.t0 ∈ s.T0 := by
  exact s.mem_T0.mpr ⟨0, rfl⟩

theorem mem_Tstar {x : Lattice 3} :
    x ∈ s.Tstar ↔ ∃ v : Residue m, v ≠ 0 ∧ s.t v = x := by
  classical
  constructor
  · intro hx
    obtain ⟨hx0, hxT⟩ := Finset.mem_erase.mp hx
    obtain ⟨v, hv⟩ := s.mem_T0.mp hxT
    refine ⟨v, ?_, hv⟩
    intro h0
    apply hx0
    simpa [h0, t0] using hv.symm
  · rintro ⟨v, hv0, rfl⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_, s.mem_T0.mpr ⟨v, rfl⟩⟩
    intro h
    exact hv0 (s.t_injective h)

@[simp] theorem residue_t1
    {m : ℕ} (s : ResidueSection m) [NeZero m]
    (w : Lattice 3) (v : Residue m) :
    residue m (s.t1 w v) = v := by
  classical
  by_cases hv : v = 0
  · simp [t1, hv]
  · simp [t1, hv]

theorem t1_injective (w : Lattice 3) : Function.Injective (s.t1 w) := by
  intro v v' h
  have := congrArg (residue m) h
  simpa using this

@[simp] theorem mem_T1 {w x : Lattice 3} : x ∈ s.T1 w ↔ ∃ v, s.t1 w v = x := by
  classical
  simp [T1]

theorem T1_eq_insert (w : Lattice 3) :
    s.T1 w = insert (scale m w + s.t0) s.Tstar := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨v, rfl⟩ := s.mem_T1.mp hx
    by_cases hv : v = 0
    · simp [t1, hv]
    · apply Finset.mem_insert_of_mem
      exact s.mem_Tstar.mpr ⟨v, hv, by simp [t1, hv]⟩
  · intro hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact s.mem_T1.mpr ⟨0, by simp [t1, hx]⟩
    · obtain ⟨v, hv, rfl⟩ := s.mem_Tstar.mp hx
      exact s.mem_T1.mpr ⟨v, by simp [t1, hv]⟩

theorem card_T0 : s.T0.card = m ^ 3 := by
  classical
  rw [T0, Finset.card_image_of_injective _ s.t_injective]
  simp [Residue]

theorem card_Tstar : s.Tstar.card = m ^ 3 - 1 := by
  classical
  rw [Tstar, Finset.card_erase_of_mem s.t0_mem_T0, s.card_T0]

theorem card_T1 (w : Lattice 3) : (s.T1 w).card = m ^ 3 := by
  classical
  rw [T1, Finset.card_image_of_injective _ (s.t1_injective w)]
  simp [Residue]

def point (w u : Lattice 3) (v : Residue m) : Lattice 3 :=
  if u = 0 ∧ v = 0 then scale m w + s.t0 else scale m u + s.t v

@[simp] theorem point_zero
    {m : ℕ} (s : ResidueSection m) [NeZero m]
    (w : Lattice 3) (v : Residue m) :
    s.point w 0 v = s.t1 w v := by
  classical
  by_cases hv : v = 0 <;> simp [point, t1, hv]

theorem point_of_ne_zero
    {m : ℕ} (s : ResidueSection m) [NeZero m]
    (w : Lattice 3) {u : Lattice 3} (hu : u ≠ 0)
    (v : Residue m) : s.point w u v = scale m u + s.t v := by
  classical
  simp [point, hu]

@[simp] theorem residue_point
    {m : ℕ} (s : ResidueSection m) [NeZero m]
    (w u : Lattice 3) (v : Residue m) :
    residue m (s.point w u v) = v := by
  classical
  by_cases h : u = 0 ∧ v = 0
  · simp [point, h]
  · simp [point, h]

theorem point_injective {w : Lattice 3} {U : Finset (Lattice 3)}
    (hw : w ∉ U) :
    Function.Injective (fun q : ↥U × Residue m => s.point w q.1 q.2) := by
  classical
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have hv : v = v' := by
    have := congrArg (residue m) h
    simpa using this
  subst v'
  suffices hu : u = u' from congrArg (fun a : ↥U => (a, v)) hu
  apply Subtype.ext
  by_cases h0 : (u : Lattice 3) = 0
  · by_cases h0' : (u' : Lattice 3) = 0
    · exact h0.trans h0'.symm
    · by_cases hv0 : v = 0
      · have he : scale m w = scale m (u' : Lattice 3) := by
          apply add_right_cancel (b := s.t0)
          simpa [point, h0, h0', hv0, t0] using h
        have he' := scale_injective m he
        exact False.elim (hw (he'.symm ▸ u'.property))
      · have he : scale m (u : Lattice 3) = scale m (u' : Lattice 3) := by
          apply add_right_cancel (b := s.t v)
          simpa [point, hv0] using h
        exact scale_injective m he
  · by_cases h0' : (u' : Lattice 3) = 0
    · by_cases hv0 : v = 0
      · have he : scale m (u : Lattice 3) = scale m w := by
          apply add_right_cancel (b := s.t0)
          simpa [point, h0, h0', hv0, t0] using h
        have he' := scale_injective m he
        exact False.elim (hw (he' ▸ u.property))
      · have he : scale m (u : Lattice 3) = scale m (u' : Lattice 3) := by
          apply add_right_cancel (b := s.t v)
          simpa [point, hv0] using h
        exact scale_injective m he
    · have he : scale m (u : Lattice 3) = scale m (u' : Lattice 3) := by
        apply add_right_cancel (b := s.t v)
        simpa [point, h0, h0'] using h
      exact scale_injective m he

def finalTile (w : Lattice 3) (U : Finset (Lattice 3)) : Finset (Lattice 3) :=
  Finset.univ.image (fun q : ↥U × Residue m => s.point w q.1 q.2)

theorem mem_finalTile {w x : Lattice 3} {U : Finset (Lattice 3)} :
    x ∈ s.finalTile w U ↔ ∃ u ∈ U, ∃ v, s.point w u v = x := by
  classical
  simp only [finalTile, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨u, v⟩, h⟩
    exact ⟨u, u.property, v, h⟩
  · rintro ⟨u, hu, v, h⟩
    exact ⟨(⟨u, hu⟩, v), h⟩

theorem card_finalTile {w : Lattice 3} {U : Finset (Lattice 3)} (hw : w ∉ U) :
    (s.finalTile w U).card = U.card * m ^ 3 := by
  classical
  rw [finalTile, Finset.card_image_of_injective _ (s.point_injective hw)]
  simp [Residue]

theorem finalTile_nonempty (w : Lattice 3) {U : Finset (Lattice 3)}
    (h0 : 0 ∈ U) : (s.finalTile w U).Nonempty := by
  exact ⟨s.point w 0 0, s.mem_finalTile.mpr ⟨0, h0, 0, rfl⟩⟩

theorem finalTile_eq_union (w : Lattice 3) {U : Finset (Lattice 3)} (h0 : 0 ∈ U) :
    s.finalTile w U = s.T1 w ∪
      (U.erase 0).biUnion (fun u => s.T0.image (fun x => scale m u + x)) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, v, rfl⟩ := s.mem_finalTile.mp hx
    by_cases hu0 : u = 0
    · apply Finset.mem_union_left
      exact s.mem_T1.mpr ⟨v, by simp [hu0]⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨u, Finset.mem_erase.mpr ⟨hu0, hu⟩, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨s.t v, s.mem_T0.mpr ⟨v, rfl⟩, (s.point_of_ne_zero w hu0 v).symm⟩
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨v, hv⟩ := s.mem_T1.mp hx
      exact s.mem_finalTile.mpr ⟨0, h0, v, by simpa using hv⟩
    · obtain ⟨u, hu, hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hu0, huU⟩ := Finset.mem_erase.mp hu
      obtain ⟨t, ht, htx⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv⟩ := s.mem_T0.mp ht
      refine s.mem_finalTile.mpr ⟨u, huU, v, ?_⟩
      rw [s.point_of_ne_zero w hu0 v, hv, htx]

theorem constituent_disjoint {w : Lattice 3} {U : Finset (Lattice 3)}
    (hw : w ∉ U) {u u' : ↥U} (hne : u ≠ u') :
    Disjoint (Set.range (s.point w (u : Lattice 3)))
      (Set.range (s.point w (u' : Lattice 3))) := by
  rw [Set.disjoint_left]
  rintro x ⟨v, hv⟩ ⟨v', hv'⟩
  apply hne
  have hp : (u, v) = (u', v') := s.point_injective hw (hv.trans hv'.symm)
  exact congrArg Prod.fst hp

end
end ResidueSection
end PeriodicTilingThree.MarkedTile

end OAI
