import OAI.Analysis.Mahler.CovectorVolume

namespace OAI

open scoped BigOperators

namespace Mahler
variable {T J ι : Type*} [AddCommGroup T] [Module ℝ T]
  [Fintype J] [Fintype ι] [DecidableEq ι]

noncomputable def complexCoord (b : Module.Basis J ℝ T) (j : J) : T →ₗ[ℝ] ℂ :=
  Complex.ofRealLI.toLinearMap.comp (b.coord j)

omit [Fintype J] in
@[simp] lemma complexCoord_apply [Fintype J] (b : Module.Basis J ℝ T) (j : J) (x : T) :
    complexCoord b j x = (b.repr x j : ℂ) := rfl

lemma multilinear_basis_expansion (b : Module.Basis J ℝ T)
    (a : MultilinearMap ℝ (fun _ : ι => T) ℂ) :
    a = ∑ q : ι → J, a (b ∘ q) •
      ((MultilinearMap.mkPiAlgebra ℝ ι ℂ).compLinearMap (complexCoord b ∘ q)) := by
  classical
  ext v
  calc
    a v = a (fun i => ∑ j, b.repr (v i) j • b j) := by
      congr 1
      funext i
      exact (b.sum_repr (v i)).symm
    _ = ∑ q : ι → J, (∏ i, b.repr (v i) (q i)) • a (b ∘ q) := by
      rw [a.map_sum]
      simp only [MultilinearMap.map_smul_univ, Function.comp_def]
    _ = _ := by
      simp only [sum_apply, smul_apply, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, Function.comp_apply, complexCoord_apply]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [Complex.real_smul, Complex.ofReal_prod]
      ring
/-- Every finite-dimensional form is an explicit finite sum of simple forms.
The factorial is retained, matching the unnormalized alternatization. -/
theorem alternating_basis_expansion (b : Module.Basis J ℝ T)
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) :
    (Fintype.card ι).factorial • a =
      ∑ q : ι → J, a (b ∘ q) • covectorVolume (complexCoord b ∘ q) := by
  have hs (c : ℂ) (f : MultilinearMap ℝ (fun _ : ι => T) ℂ) :
      MultilinearMap.alternatization (c • f) = c • MultilinearMap.alternatization f := by
    ext v
    simp only [MultilinearMap.alternatization_apply, smul_apply,
      MultilinearMap.domDomCongr_apply, AlternatingMap.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    exact smul_comm _ _ _
  have h := congrArg MultilinearMap.alternatization
    (multilinear_basis_expansion b a.toMultilinearMap)
  simpa only [AlternatingMap.coe_alternatization, map_sum,
    hs, covectorVolume, AlternatingMap.coe_multilinearMap] using h

theorem alternating_basis_expansion_normalized (b : Module.Basis J ℝ T)
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) :
    a = ∑ q : ι → J, (a (b ∘ q) / (Fintype.card ι).factorial) •
      covectorVolume (complexCoord b ∘ q) := by
  have hf : ((Fintype.card ι).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card ι)
  have h := congrArg (fun A : T [⋀^ι]→ₗ[ℝ] ℂ =>
    (((Fintype.card ι).factorial : ℂ)⁻¹) • A) (alternating_basis_expansion b a)
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hf, one_smul] at h
  simpa only [Finset.smul_sum, smul_smul, div_eq_mul_inv, mul_comm] using h

/-- Induction on simple forms, justified by a finite basis expansion. -/
theorem alternating_induction (b : Module.Basis J ℝ T)
    (P : (T [⋀^ι]→ₗ[ℝ] ℂ) → Prop)
    (hz : P 0) (ha : ∀ A B, P A → P B → P (A+B))
    (hs : ∀ (c : ℂ) A, P A → P (c • A))
    (hv : ∀ l : ι → T →ₗ[ℝ] ℂ, P (covectorVolume l))
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) : P a := by
  classical
  rw [alternating_basis_expansion_normalized b a]
  apply Finset.sum_induction
  · exact ha
  · exact hz
  · intro q hq
    exact hs _ _ (hv _)

end Mahler

end OAI
