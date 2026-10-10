import OAI.NumberTheory.PiExponent.Geometry.ProjectiveMonomialFinite

namespace OAI

namespace PiExponent.ProjectiveMonomialCohomology
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech ProjectiveMonomialCechHigher ProjectiveMonomialFinite

variable {ι K : Type*} [Fintype ι] [CommRing K]

def differentialLinear (d : ℤ) (q : ℕ) :
    Cochain ι (Laurent ι K d) q →ₗ[K] Cochain ι (Laurent ι K d) (q + 1) where
  toFun := differential
  map_add' c e := by
    funext t
    simp only [differential, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    funext t
    simp only [differential, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

def regularCochains (d : ℤ) (q : ℕ) : Submodule K (Cochain ι (Laurent ι K d) q) where
  carrier := {c | Regular c}
  zero_mem' := by intro t a h; exact (h rfl).elim
  add_mem' {c e} hc he := by
    intro t a h i hi
    by_cases hca : c t a = 0
    · apply he t a _ i hi
      simpa only [Pi.add_apply, Finsupp.add_apply, hca, zero_add] using h
    · exact hc t a hca i hi
  smul_mem' r c hc := by
    intro t a h i hi
    apply hc t a _ i hi
    intro hz
    apply h
    simp [hz]

def cycles (d : ℤ) (q : ℕ) : Submodule K (Cochain ι (Laurent ι K d) q) :=
  regularCochains d q ⊓ (differentialLinear d q).ker

theorem degreeZero_coeff_eq {d : ℤ} (c : cycles (ι := ι) (K := K) d 0) (i j : ι) :
    c.val (fun _ => i) = c.val (fun _ => j) := by
  have hc := congrFun c.property.2 ![i, j]
  change differential c.val ![i, j] = 0 at hc
  rw [differential, Fin.sum_univ_two] at hc
  have h0 : (![i, j] ∘ (0 : Fin 2).succAbove) = (fun _ : Fin 1 => j) := by
    funext k
    fin_cases k
    rfl
  have h1 : (![i, j] ∘ (1 : Fin 2).succAbove) = (fun _ : Fin 1 => i) := by
    funext k
    fin_cases k
    rfl
  have hh : c.val (fun _ => j) - c.val (fun _ => i) = 0 := by
    simpa only [h0, h1, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
      neg_one_zsmul, sub_eq_add_neg] using hc
  exact (sub_eq_zero.mp hh).symm

theorem degreeZero_nonnegative [Nontrivial ι] {d : ℤ}
    (c : cycles (ι := ι) (K := K) d 0) (t : Fin 1 → ι) (a : Monomial ι d)
    (ha : c.val t a ≠ 0) : ∀ i, 0 ≤ a.val i := by
  intro i
  by_contra hi
  have hin : a.val i < 0 := lt_of_not_ge hi
  obtain ⟨j, hj⟩ := exists_ne i
  have ht : t = (fun _ => t 0) := by
    funext k
    exact congrArg t (Fin.eq_zero k)
  have he : c.val t = c.val (fun _ => j) := by
    rw [ht]
    exact degreeZero_coeff_eq c (t 0) j
  rw [he] at ha
  obtain ⟨k, hk⟩ := c.property.1 (fun _ => j) a ha i hin
  exact hj hk

def degreeZeroCoefficients (d : ℤ) (i : ι) :
    cycles (ι := ι) (K := K) d 0 →ₗ[K]
      ({a : Monomial ι d // ∀ j, 0 ≤ a.val j} → K) where
  toFun c a := c.val (fun _ => i) a.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem degreeZeroCoefficients_injective [Nontrivial ι] (d : ℤ) (i : ι) :
    Function.Injective (degreeZeroCoefficients (ι := ι) (K := K) d i) := by
  intro c e h
  apply Subtype.ext
  funext t
  ext a
  by_cases ha : ∀ j, 0 ≤ a.val j
  · have hc : c.val t = c.val (fun _ => i) := by
      have ht : t = (fun _ => t 0) := by
        funext k
        exact congrArg t (Fin.eq_zero k)
      rw [ht]
      exact degreeZero_coeff_eq c (t 0) i
    have he : e.val t = e.val (fun _ => i) := by
      have ht : t = (fun _ => t 0) := by
        funext k
        exact congrArg t (Fin.eq_zero k)
      rw [ht]
      exact degreeZero_coeff_eq e (t 0) i
    rw [hc, he]
    exact congrFun h ⟨a, ha⟩
  · have hc : c.val t a = 0 := by
      by_contra hh
      exact ha (degreeZero_nonnegative c t a hh)
    have he : e.val t a = 0 := by
      by_contra hh
      exact ha (degreeZero_nonnegative e t a hh)
    rw [hc, he]

instance degreeZero_finite [IsNoetherianRing K] (d : ℤ) :
    Module.Finite K (cycles (ι := ι) (K := K) d 0) := by
  cases subsingleton_or_nontrivial ι with
  | inl h => infer_instance
  | inr h =>
      let i : ι := Classical.choice (inferInstance : Nonempty ι)
      exact Module.Finite.of_injective (degreeZeroCoefficients d i)
        (degreeZeroCoefficients_injective d i)

def boundaryMap (d : ℤ) (q : ℕ) :
    regularCochains (ι := ι) (K := K) d q →ₗ[K] cycles (ι := ι) (K := K) d (q + 1) :=
  ((differentialLinear (ι := ι) (K := K) d q).comp (regularCochains d q).subtype).codRestrict
    (cycles d (q + 1)) (fun c =>
      ⟨differential_regular c.val c.property, differential_squared c.val⟩)

def negativeCycles (d : ℤ) (q : ℕ) : Submodule K (cycles (ι := ι) (K := K) d (q + 1)) where
  carrier := {c | ∀ t a, ¬ AllNegative a → c.val t a = 0}
  zero_mem' := by
    intro t a ha
    rfl
  add_mem' {c e} hc he := by
    intro t a ha
    change c.val t a + e.val t a = 0
    rw [hc t a ha, he t a ha, zero_add]
  smul_mem' r c hc := by
    intro t a ha
    change r • (c.val t a) = 0
    rw [hc t a ha, smul_zero]

def negativeCoefficients (d : ℤ) (q : ℕ) :
    negativeCycles (ι := ι) (K := K) d q →ₗ[K]
      ((Fin (q + 2) → ι) → ({a : Monomial ι d // AllNegative a} → K)) where
  toFun c t a := c.val.val t a.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem negativeCoefficients_injective (d : ℤ) (q : ℕ) :
    Function.Injective (negativeCoefficients (ι := ι) (K := K) d q) := by
  intro c e h
  apply Subtype.ext
  apply Subtype.ext
  funext t
  ext a
  by_cases ha : AllNegative a
  · exact congrFun (congrFun h t) ⟨a, ha⟩
  · rw [c.property t a ha, e.property t a ha]

instance negativeCycles_finite [IsNoetherianRing K] (d : ℤ) (q : ℕ) :
    Module.Finite K (negativeCycles (ι := ι) (K := K) d q) :=
  Module.Finite.of_injective (negativeCoefficients d q) (negativeCoefficients_injective d q)

theorem exists_negative_representative (d : ℤ) (q : ℕ)
    (c : cycles (ι := ι) (K := K) d (q + 1)) :
    ∃ z : negativeCycles (ι := ι) (K := K) d q,
      ∃ b : regularCochains (ι := ι) (K := K) d q,
        c = boundaryMap d q b + z.val := by
  classical
  let z : cycles (ι := ι) (K := K) d (q + 1) :=
    ⟨filterCochain AllNegative c.val,
      filterCochain_regular _ c.val c.property.1,
      filterCochain_closed _ c.val c.property.2⟩
  have hz : z ∈ negativeCycles d q := by
    intro t a ha
    change filterCochain AllNegative c.val t a = 0
    simp [ha]
  obtain ⟨b, hb, heq⟩ := cocycle_eq_boundary_add_negative c.val c.property.1 c.property.2
  exact ⟨⟨z, hz⟩, ⟨b, hb⟩, Subtype.ext heq⟩

theorem finite_of_boundary_annihilating_surjective [IsNoetherianRing K] (d : ℤ) (q : ℕ)
    {V : Type*} [AddCommGroup V] [Module K V]
    (f : cycles (ι := ι) (K := K) d (q + 1) →ₗ[K] V)
    (hboundary : ∀ b, f (boundaryMap d q b) = 0)
    (hsurj : Function.Surjective f) : Module.Finite K V := by
  let g : negativeCycles (ι := ι) (K := K) d q →ₗ[K] V :=
    f.comp (negativeCycles d q).subtype
  apply Module.Finite.of_surjective g
  intro x
  obtain ⟨c, hc⟩ := hsurj x
  obtain ⟨z, b, heq⟩ := exists_negative_representative d q c
  refine ⟨z, ?_⟩
  change f z.val = x
  rw [← hc, heq, map_add, hboundary, zero_add]

end
end PiExponent.ProjectiveMonomialCohomology

end OAI
