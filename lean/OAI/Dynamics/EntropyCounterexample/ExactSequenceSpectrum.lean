import OAI.Dynamics.EntropyCounterexample.PolynomialSpectralBound

namespace OAI

noncomputable section

namespace Problem340.PolynomialSpectrum

open Polynomial

section PolynomialIntertwining

variable {R U V W : Type*} [CommRing R]
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [Module R U] [Module R V] [Module R W]

theorem intertwines_pow (i : U →ₗ[R] V) (A : Module.End R U) (B : Module.End R V)
    (hi : B.comp i = i.comp A) (n : ℕ) :
    (B ^ n).comp i = i.comp (A ^ n) := by
  induction n with
  | zero => ext x; rfl
  | succ n ih =>
    ext x
    have hi' (y : U) : B (i y) = i (A y) := congrArg (fun f => f y) hi
    have ih' (y : U) : (B ^ n) (i y) = i ((A ^ n) y) :=
      congrArg (fun f => f y) ih
    simp only [pow_succ, LinearMap.comp_apply, Module.End.mul_apply, hi', ih']

theorem intertwines_aeval (i : U →ₗ[R] V) (A : Module.End R U) (B : Module.End R V)
    (hi : B.comp i = i.comp A) (p : R[X]) :
    (aeval B p).comp i = i.comp (aeval A p) := by
  refine p.induction_on' ?_ ?_
  · intro p q hp hq
    ext x
    have hp' := congrArg (fun f => f x) hp
    have hq' := congrArg (fun f => f x) hq
    simp only [LinearMap.comp_apply] at hp' hq'
    simp only [map_add, LinearMap.comp_apply, LinearMap.add_apply, hp', hq']
  · intro n a
    ext x
    have hn := congrArg (fun f => f x) (intertwines_pow i A B hi n)
    simp only [LinearMap.comp_apply] at hn
    simp only [aeval_monomial, LinearMap.comp_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, map_smul, hn]

theorem aeval_mul_eq_zero_of_exact
    (i : U →ₗ[R] V) (j : V →ₗ[R] W) (hexact : Function.Exact i j)
    (A : Module.End R U) (B : Module.End R V) (C : Module.End R W)
    (hi : B.comp i = i.comp A) (hj : C.comp j = j.comp B)
    (p q : R[X]) (hp : aeval A p = 0) (hq : aeval C q = 0) :
    aeval B (p * q) = 0 := by
  ext x
  have hjq (y : V) : j ((aeval B q) y) = 0 := by
    have h := congrArg (fun f => f y) (intertwines_aeval j B C hj q)
    simpa only [LinearMap.comp_apply, hq, LinearMap.zero_apply] using h.symm
  obtain ⟨u, hu⟩ := (hexact ((aeval B q) x)).mp (hjq x)
  have hip (y : U) : (aeval B p) (i y) = 0 := by
    have h := congrArg (fun f => f y) (intertwines_aeval i A B hi p)
    simpa only [LinearMap.comp_apply, hp, LinearMap.zero_apply, map_zero] using h
  simpa only [map_mul, Module.End.mul_apply, LinearMap.zero_apply, ← hu] using hip u

theorem aeval_pow_eq_zero_of_exact
    (i : U →ₗ[R] V) (j : V →ₗ[R] W) (hexact : Function.Exact i j)
    (A : Module.End R U) (B : Module.End R V) (C : Module.End R W)
    (hi : B.comp i = i.comp A) (hj : C.comp j = j.comp B)
    (p : R[X]) (m n : ℕ)
    (hp : (aeval A p) ^ m = 0) (hq : (aeval C p) ^ n = 0) :
    (aeval B p) ^ (m + n) = 0 := by
  have h := aeval_mul_eq_zero_of_exact i j hexact A B C hi hj (p ^ m) (p ^ n)
    (by simpa only [map_pow] using hp) (by simpa only [map_pow] using hq)
  simpa only [← pow_add, map_pow] using h

end PolynomialIntertwining

section CategoricalExactness

open CategoryTheory

theorem aeval_mul_eq_zero_of_shortComplex_exact
    {R : Type*} [CommRing R] (S : ShortComplex (ModuleCat R)) (hS : S.Exact)
    (φ : S ⟶ S) (p q : R[X])
    (hp : aeval φ.τ₁.hom p = 0) (hq : aeval φ.τ₃.hom q = 0) :
    aeval φ.τ₂.hom (p * q) = 0 := by
  apply aeval_mul_eq_zero_of_exact S.f.hom S.g.hom
    (LinearMap.exact_iff.mpr hS.moduleCat_range_eq_ker.symm)
    φ.τ₁.hom φ.τ₂.hom φ.τ₃.hom _ _ p q hp hq
  · exact (congrArg ModuleCat.Hom.hom φ.comm₁₂).symm
  · exact (congrArg ModuleCat.Hom.hom φ.comm₂₃).symm

end CategoricalExactness

section RealSpectrum

variable {U V W : Type*}
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [Module ℝ U] [Module ℝ V] [Module ℝ W]

theorem finite_pairRadii_of_exact
    (i : U →ₗ[ℝ] V) (j : V →ₗ[ℝ] W) (hexact : Function.Exact i j)
    (A : Module.End ℝ U) (B : Module.End ℝ V) (C : Module.End ℝ W)
    (hi : B.comp i = i.comp A) (hj : C.comp j = j.comp B)
    (p q : ℝ[X]) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hp : aeval A p = 0) (hq : aeval C q = 0) :
    (pairRadii B).Finite :=
  finite_pairRadii_of_annihilator B (p * q) (mul_ne_zero hp0 hq0)
    (aeval_mul_eq_zero_of_exact i j hexact A B C hi hj p q hp hq)

theorem bddAbove_pairRadii_of_exact
    (i : U →ₗ[ℝ] V) (j : V →ₗ[ℝ] W) (hexact : Function.Exact i j)
    (A : Module.End ℝ U) (B : Module.End ℝ V) (C : Module.End ℝ W)
    (hi : B.comp i = i.comp A) (hj : C.comp j = j.comp B)
    (p q : ℝ[X]) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hp : aeval A p = 0) (hq : aeval C q = 0) :
    BddAbove (pairRadii B) :=
  (finite_pairRadii_of_exact i j hexact A B C hi hj p q hp0 hq0 hp hq).bddAbove

end RealSpectrum

section GradedSpectrum

variable {ι : Type*} {U V W : ι → Type*}
  [∀ k, AddCommGroup (U k)] [∀ k, AddCommGroup (V k)] [∀ k, AddCommGroup (W k)]
  [∀ k, Module ℝ (U k)] [∀ k, Module ℝ (V k)] [∀ k, Module ℝ (W k)]

theorem finite_iUnion_pairRadii_of_exact
    (i : ∀ k, U k →ₗ[ℝ] V k) (j : ∀ k, V k →ₗ[ℝ] W k)
    (hexact : ∀ k, Function.Exact (i k) (j k))
    (A : ∀ k, Module.End ℝ (U k)) (B : ∀ k, Module.End ℝ (V k))
    (C : ∀ k, Module.End ℝ (W k))
    (hi : ∀ k, (B k).comp (i k) = (i k).comp (A k))
    (hj : ∀ k, (C k).comp (j k) = (j k).comp (B k))
    (p q : ℝ[X]) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hp : ∀ k, aeval (A k) p = 0) (hq : ∀ k, aeval (C k) q = 0) :
    (⋃ k, pairRadii (B k)).Finite :=
  finite_iUnion_pairRadii_of_annihilator B (p * q) (mul_ne_zero hp0 hq0)
    (fun k => aeval_mul_eq_zero_of_exact (i k) (j k) (hexact k)
      (A k) (B k) (C k) (hi k) (hj k) p q (hp k) (hq k))

end GradedSpectrum

section NilpotentPolynomial

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem aeval_eq_zero_of_hasPair_of_pow
    {A : Module.End ℝ V} {z : ℂ} {u v : V}
    (huv : u ≠ 0 ∨ v ≠ 0) (hA : HasPair A z u v)
    {p : ℝ[X]} {N : ℕ} (hpA : (aeval A p) ^ N = 0) :
    aeval z p = 0 := by
  have h : aeval z (p ^ N) = 0 :=
    aeval_eq_zero_of_hasPair huv hA (by simpa only [map_pow] using hpA)
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

theorem finite_iUnion_pairRadii_of_pointwise_pow
    {ι : Type*} {W : ι → Type*} [∀ k, AddCommGroup (W k)] [∀ k, Module ℝ (W k)]
    (A : ∀ k, Module.End ℝ (W k)) (p : ℝ[X]) (hp : p ≠ 0)
    (hpow : ∀ k, ∃ N : ℕ, (aeval (A k) p) ^ N = 0) :
    (⋃ k, pairRadii (A k)).Finite := by
  have hroots : Set.Finite {z : ℂ | (p.map (algebraMap ℝ ℂ)).IsRoot z} :=
    Polynomial.finite_setOfPred_isRoot (Polynomial.map_ne_zero hp)
  apply (hroots.image (fun z : ℂ => ‖z‖)).subset
  intro r hr
  rcases Set.mem_iUnion.mp hr with ⟨k, a, b, u, v, huv, hu, hv, rfl⟩
  obtain ⟨N, hN⟩ := hpow k
  refine ⟨⟨a, b⟩, ?_, ?_⟩
  · change (p.map (algebraMap ℝ ℂ)).eval ⟨a, b⟩ = 0
    rw [Polynomial.eval_map]
    exact aeval_eq_zero_of_hasPair_of_pow huv
      (show HasPair (A k) ⟨a, b⟩ u v from ⟨hu, hv⟩) hN
  · exact Complex.norm_eq_sqrt_sq_add_sq ⟨a, b⟩

theorem pairRadii_subset_zero_one_two_of_cubic_pow (A : Module.End ℝ V)
    {N : ℕ} (hA : (A * (A - 1) * (A - 2)) ^ N = 0) :
    pairRadii A ⊆ {r : ℝ | r = 0 ∨ r = 1 ∨ r = 2} := by
  rintro r ⟨a, b, u, v, huv, hu, hv, rfl⟩
  let z : ℂ := ⟨a, b⟩
  have hz : z * (z - 1) * (z - 2) = 0 := by
    have h := aeval_eq_zero_of_hasPair_of_pow huv
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

theorem pairRadii_le_two_of_cubic_pow (A : Module.End ℝ V)
    {N : ℕ} (hA : (A * (A - 1) * (A - 2)) ^ N = 0)
    {r : ℝ} (hr : r ∈ pairRadii A) : r ≤ 2 := by
  rcases pairRadii_subset_zero_one_two_of_cubic_pow A hA hr with rfl | rfl | rfl <;>
    norm_num

theorem bddAbove_iUnion_pairRadii_of_cubic_pow
    {ι : Type*} {W : ι → Type*} [∀ k, AddCommGroup (W k)] [∀ k, Module ℝ (W k)]
    (A : ∀ k, Module.End ℝ (W k))
    (hpow : ∀ k, ∃ N : ℕ, (A k * (A k - 1) * (A k - 2)) ^ N = 0) :
    BddAbove (⋃ k, pairRadii (A k)) := by
  refine ⟨2, ?_⟩
  intro r hr
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hr
  obtain ⟨N, hN⟩ := hpow k
  exact pairRadii_le_two_of_cubic_pow (A k) hN hk

end NilpotentPolynomial

end Problem340.PolynomialSpectrum

end

end OAI
