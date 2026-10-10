import Mathlib

namespace OAI

noncomputable section

namespace Problem340.PolynomialSpectrum

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def HasPair (A : Module.End ℝ V) (z : ℂ) (u v : V) : Prop :=
  A u = z.re • u - z.im • v ∧ A v = z.im • u + z.re • v

lemma hasPair_add {A B : Module.End ℝ V} {z w : ℂ} {u v : V}
    (hA : HasPair A z u v) (hB : HasPair B w u v) :
    HasPair (A + B) (z + w) u v := by
  constructor
  · simp only [LinearMap.add_apply, hA.1, hB.1, Complex.add_re, Complex.add_im,
      add_smul]
    abel
  · simp only [LinearMap.add_apply, hA.2, hB.2, Complex.add_re, Complex.add_im,
      add_smul]
    abel

lemma hasPair_mul {A B : Module.End ℝ V} {z w : ℂ} {u v : V}
    (hA : HasPair A z u v) (hB : HasPair B w u v) :
    HasPair (A * B) (z * w) u v := by
  constructor
  · simp only [Module.End.mul_apply, hB.1, map_sub, map_smul, hA.1, hA.2,
      Complex.mul_re, Complex.mul_im]
    module
  · simp only [Module.End.mul_apply, hB.2, map_add, map_smul, hA.1, hA.2,
      Complex.mul_re, Complex.mul_im]
    module

lemma hasPair_algebraMap (a : ℝ) (u v : V) :
    HasPair (algebraMap ℝ (Module.End ℝ V) a) (a : ℂ) u v := by
  simp [HasPair, Module.algebraMap_end_apply]

lemma hasPair_pow {A : Module.End ℝ V} {z : ℂ} {u v : V}
    (hA : HasPair A z u v) (n : ℕ) : HasPair (A ^ n) (z ^ n) u v := by
  induction n with
  | zero => simp [HasPair]
  | succ n ih =>
    simpa only [pow_succ] using hasPair_mul ih hA

lemma hasPair_aeval {A : Module.End ℝ V} {z : ℂ} {u v : V}
    (hA : HasPair A z u v) (p : ℝ[X]) :
    HasPair (aeval A p) (aeval z p) u v := by
  refine p.induction_on' ?_ ?_
  · intro p q hp hq
    simpa only [map_add] using hasPair_add hp hq
  · intro n a
    rw [← C_mul_X_pow_eq_monomial]
    simpa only [map_mul, map_pow, aeval_C, aeval_X, Complex.coe_algebraMap] using
      hasPair_mul (hasPair_algebraMap a u v) (hasPair_pow hA n)

lemma hasPair_zero {z : ℂ} {u v : V} (huv : u ≠ 0 ∨ v ≠ 0)
    (h : HasPair (0 : Module.End ℝ V) z u v) : z = 0 := by
  rcases h with ⟨hu, hv⟩
  change 0 = z.re • u - z.im • v at hu
  change 0 = z.im • u + z.re • v at hv
  have hsu : (z.re ^ 2 + z.im ^ 2) • u = 0 := by
    calc
      (z.re ^ 2 + z.im ^ 2) • u =
          z.re • (z.re • u - z.im • v) +
            z.im • (z.im • u + z.re • v) := by module
      _ = 0 := by rw [← hu, ← hv]; simp
  have hsv : (z.re ^ 2 + z.im ^ 2) • v = 0 := by
    calc
      (z.re ^ 2 + z.im ^ 2) • v =
          -z.im • (z.re • u - z.im • v) +
            z.re • (z.im • u + z.re • v) := by module
      _ = 0 := by rw [← hu, ← hv]; simp
  have hs : z.re ^ 2 + z.im ^ 2 = 0 := by
    rcases huv with hu | hv
    · exact (smul_eq_zero.mp hsu).resolve_right hu
    · exact (smul_eq_zero.mp hsv).resolve_right hv
  apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im]
  · nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  · nlinarith [sq_nonneg z.re, sq_nonneg z.im]

lemma aeval_eq_zero_of_hasPair {A : Module.End ℝ V} {z : ℂ} {u v : V}
    (huv : u ≠ 0 ∨ v ≠ 0) (hA : HasPair A z u v)
    {p : ℝ[X]} (hpA : aeval A p = 0) : aeval z p = 0 := by
  apply hasPair_zero huv
  simpa only [hpA] using hasPair_aeval hA p

def pairRadii (A : Module.End ℝ V) : Set ℝ :=
  {r | ∃ a b : ℝ, ∃ u v : V,
    (u ≠ 0 ∨ v ≠ 0) ∧
    A u = a • u - b • v ∧ A v = b • u + a • v ∧
    r = Real.sqrt (a ^ 2 + b ^ 2)}

theorem finite_pairRadii_of_annihilator (A : Module.End ℝ V)
    (p : ℝ[X]) (hp : p ≠ 0) (hpA : aeval A p = 0) :
    (pairRadii A).Finite := by
  have hroots : Set.Finite {z : ℂ | (p.map (algebraMap ℝ ℂ)).IsRoot z} :=
    Polynomial.finite_setOfPred_isRoot (Polynomial.map_ne_zero hp)
  apply (hroots.image (fun z : ℂ => ‖z‖)).subset
  rintro r ⟨a, b, u, v, huv, hu, hv, rfl⟩
  refine ⟨⟨a, b⟩, ?_, ?_⟩
  · change (p.map (algebraMap ℝ ℂ)).eval ⟨a, b⟩ = 0
    rw [Polynomial.eval_map]
    exact aeval_eq_zero_of_hasPair huv (show HasPair A ⟨a, b⟩ u v from ⟨hu, hv⟩) hpA
  · exact Complex.norm_eq_sqrt_sq_add_sq ⟨a, b⟩

theorem bddAbove_pairRadii_of_annihilator (A : Module.End ℝ V)
    (p : ℝ[X]) (hp : p ≠ 0) (hpA : aeval A p = 0) :
    BddAbove (pairRadii A) :=
  (finite_pairRadii_of_annihilator A p hp hpA).bddAbove

theorem finite_pairRadii [FiniteDimensional ℝ V] (A : Module.End ℝ V) :
    (pairRadii A).Finite :=
  finite_pairRadii_of_annihilator A A.charpoly A.charpoly_monic.ne_zero A.aeval_self_charpoly

theorem bddAbove_pairRadii [FiniteDimensional ℝ V] (A : Module.End ℝ V) :
    BddAbove (pairRadii A) := (finite_pairRadii A).bddAbove

theorem finite_iUnion_pairRadii_of_annihilator {ι : Type*}
    {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℝ (W i)]
    (A : ∀ i, Module.End ℝ (W i)) (p : ℝ[X]) (hp : p ≠ 0)
    (hpA : ∀ i, aeval (A i) p = 0) :
    (⋃ i, pairRadii (A i)).Finite := by
  have hroots : Set.Finite {z : ℂ | (p.map (algebraMap ℝ ℂ)).IsRoot z} :=
    Polynomial.finite_setOfPred_isRoot (Polynomial.map_ne_zero hp)
  apply (hroots.image (fun z : ℂ => ‖z‖)).subset
  intro r hr
  rcases Set.mem_iUnion.mp hr with ⟨i, a, b, u, v, huv, hu, hv, rfl⟩
  refine ⟨⟨a, b⟩, ?_, ?_⟩
  · change (p.map (algebraMap ℝ ℂ)).eval ⟨a, b⟩ = 0
    rw [Polynomial.eval_map]
    exact aeval_eq_zero_of_hasPair huv
      (show HasPair (A i) ⟨a, b⟩ u v from ⟨hu, hv⟩) (hpA i)
  · exact Complex.norm_eq_sqrt_sq_add_sq ⟨a, b⟩

theorem bddAbove_iUnion_pairRadii_of_annihilator {ι : Type*}
    {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℝ (W i)]
    (A : ∀ i, Module.End ℝ (W i)) (p : ℝ[X]) (hp : p ≠ 0)
    (hpA : ∀ i, aeval (A i) p = 0) :
    BddAbove (⋃ i, pairRadii (A i)) :=
  (finite_iUnion_pairRadii_of_annihilator A p hp hpA).bddAbove

theorem pairRadii_subset_zero_one_two_of_cubic (A : Module.End ℝ V)
    (hA : A * (A - 1) * (A - 2) = 0) :
    pairRadii A ⊆ {r : ℝ | r = 0 ∨ r = 1 ∨ r = 2} := by
  rintro r ⟨a, b, u, v, huv, hu, hv, rfl⟩
  let z : ℂ := ⟨a, b⟩
  have hz : z * (z - 1) * (z - 2) = 0 := by
    have h := aeval_eq_zero_of_hasPair huv
      (show HasPair A z u v from ⟨hu, hv⟩)
      (p := X * (X - 1) * (X - 2))
      (by simpa only [map_mul, map_sub, aeval_X, map_one, map_ofNat] using hA)
    simpa only [map_mul, map_sub, aeval_X, map_one, map_ofNat] using h
  have hr : Real.sqrt (a ^ 2 + b ^ 2) = ‖z‖ :=
    (Complex.norm_eq_sqrt_sq_add_sq z).symm
  change Real.sqrt (a ^ 2 + b ^ 2) = 0 ∨
    Real.sqrt (a ^ 2 + b ^ 2) = 1 ∨ Real.sqrt (a ^ 2 + b ^ 2) = 2
  rw [hr]
  simp only [mul_eq_zero, sub_eq_zero] at hz
  rcases hz with (hz | hz) | hz <;> simp [hz]

theorem pairRadii_le_two_of_cubic (A : Module.End ℝ V)
    (hA : A * (A - 1) * (A - 2) = 0) {r : ℝ} (hr : r ∈ pairRadii A) :
    r ≤ 2 := by
  rcases pairRadii_subset_zero_one_two_of_cubic A hA hr with rfl | rfl | rfl <;> norm_num

section Factorization

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem pairRadii_comp_subset (I : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W) :
    pairRadii (I.comp P) ⊆ insert 0 (pairRadii (P.comp I)) := by
  rintro r ⟨a, b, u, v, huv, hu, hv, rfl⟩
  by_cases hP : P u ≠ 0 ∨ P v ≠ 0
  · apply Set.mem_insert_of_mem
    refine ⟨a, b, P u, P v, hP, ?_, ?_, rfl⟩
    · simpa only [LinearMap.comp_apply, map_sub, map_smul] using congrArg P hu
    · simpa only [LinearMap.comp_apply, map_add, map_smul] using congrArg P hv
  · push Not at hP
    have hz : (⟨a, b⟩ : ℂ) = 0 := by
      apply hasPair_zero huv
      constructor
      · simpa only [LinearMap.zero_apply, LinearMap.comp_apply, hP.1, map_zero] using hu
      · simpa only [LinearMap.zero_apply, LinearMap.comp_apply, hP.2, map_zero] using hv
    have ha : a = 0 := congrArg Complex.re hz
    have hb : b = 0 := congrArg Complex.im hz
    simp [ha, hb]

theorem finite_pairRadii_of_factor [FiniteDimensional ℝ W]
    (I : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W) :
    (pairRadii (I.comp P)).Finite :=
  ((finite_pairRadii (P.comp I)).insert 0).subset (pairRadii_comp_subset I P)

theorem bddAbove_pairRadii_of_factor [FiniteDimensional ℝ W]
    (I : W →ₗ[ℝ] V) (P : V →ₗ[ℝ] W) :
    BddAbove (pairRadii (I.comp P)) :=
  (finite_pairRadii_of_factor I P).bddAbove

end Factorization

theorem iUnion_pairRadii_comp_subset {ι : Type*} {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℝ (W i)]
    (I : ∀ i, W i →ₗ[ℝ] V i) (P : ∀ i, V i →ₗ[ℝ] W i) :
    (⋃ i, pairRadii ((I i).comp (P i))) ⊆
      insert 0 (⋃ i, pairRadii ((P i).comp (I i))) := by
  intro r hr
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hr
  rcases pairRadii_comp_subset (I i) (P i) hi with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl h)
  · exact Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨i, h⟩)

theorem bddAbove_iUnion_pairRadii_comp {ι : Type*} {V W : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℝ (W i)]
    (I : ∀ i, W i →ₗ[ℝ] V i) (P : ∀ i, V i →ₗ[ℝ] W i)
    (h : BddAbove (⋃ i, pairRadii ((P i).comp (I i)))) :
    BddAbove (⋃ i, pairRadii ((I i).comp (P i))) :=
  (h.insert 0).mono (iUnion_pairRadii_comp_subset I P)

end Problem340.PolynomialSpectrum

end

end OAI
