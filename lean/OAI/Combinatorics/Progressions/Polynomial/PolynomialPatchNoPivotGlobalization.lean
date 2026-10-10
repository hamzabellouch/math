import OAI.Combinatorics.Progressions.Linear.KernelProjectionNoPivotGlobalization
import OAI.Combinatorics.Progressions.Nilpotent.PolynomialPatchWeightedChartNiltest

namespace OAI

section

namespace Erdos3.PolynomialPatch

variable {σ τ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)

noncomputable def ofTranslatedShearOrbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    (orbit : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : PolynomialPatch τ s d :=
  A.ofShearOrbit ((polynomialShearFiltration A.weight s A.weight_le).realification.constantGroupOrbit
    (fun _ : τ => 1) g * orbit)

@[simp] theorem ofTranslatedShearOrbit_weight
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    (orbit : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : (A.ofTranslatedShearOrbit g orbit).weight = A.weight := rfl

@[simp] theorem ofTranslatedShearOrbit_kernel
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    (orbit : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) : (A.ofTranslatedShearOrbit g orbit).kernel = A.kernel := rfl

theorem ofTranslatedShearOrbit_value_integer
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    (orbit : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) (t : τ → ℤ) :
    (A.ofTranslatedShearOrbit g orbit).value (fun i => (t i : ℝ)) =
      A.shearObservable (g • QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fun _ : τ => 1) t orbit)) := by
  rw [ofTranslatedShearOrbit, ofShearOrbit_value_integer, map_mul,
    NilpotentLieFiltration.polynomialOrbitEval_constantGroupOrbit]
  rfl

end Erdos3.PolynomialPatch

end

section

namespace Erdos3.PolynomialPatch

open scoped NNReal TensorProduct

variable {σ τ Ω G : Type*} {s d : ℕ} [Fintype Ω] [Fintype G]
    (A : PolynomialPatch σ s d)
    [Fintype (PolynomialShearIndex A.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

theorem exists_patch_of_kernelProjection_scores
    (M : ℝ≥0) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M)
    {p : ℝ} (hcomplex : (A.shearNiltest M hA).ComplexityLE p)
    (K : Submodule ℚ (PolynomialShearLieAlgebra A.weight ℚ))
    (hK : K ≤ (polynomialShearFiltration A.weight s A.weight_le).layer s)
    (orbit : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1))
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights G)
    (point : Ω → G → τ → ℤ) (weight : Ω → G → ℝ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ x, |weight a x| ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun x => (weight a x : ℂ) *
        (((A.shearNiltest M hA).kernelProjection K hK).withOrbit orbit).eval (point a x))).re) :
    ∃ (P : PolynomialPatch τ s d)
      (T : (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : τ => 1))
      (H' : Finset Ω),
      P.weight = A.weight ∧ P.kernel = A.kernel ∧
      T.observable = (A.shearNiltest M hA).observable ∧
      T.normBound = (A.shearNiltest M hA).normBound ∧
      T.lipBound = (A.shearNiltest M hA).lipBound ∧
      T.UnitIntervalValued ∧ T.ComplexityLE p ∧
      (∀ t, T.eval t = (P.value (fun i => (t i : ℝ)) : ℂ)) ∧
      H' ⊆ H ∧ 0 < outer.mass H' ∧
      δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
      ∀ a ∈ H', δ / 2 ≤ (localLaw a).mean
        (fun x => weight a x * P.value (fun i => (point a x i : ℝ))) := by
  obtain ⟨z, _, H', hsub, hpos, hmass, hobs, hnorm, hlip, hunit, hc, hs⟩ :=
    (A.shearNiltest M hA).exists_kernelProjection_restored_orbit
      (A.shearNiltest_unitInterval M hA) hcomplex K hK orbit outer H hH localLaw
      point (fun a x => (weight a x : ℂ)) hB hδ
      (fun a ha x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hweight a ha x)
      hscore
  let P := A.ofTranslatedShearOrbit z orbit
  let T := (A.shearNiltest M hA).withLeftTranslatedOrbit z orbit
  have heval (t : τ → ℤ) : T.eval t = (P.value (fun i => (t i : ℝ)) : ℂ) := by
    exact ((A.shearNiltest M hA).withLeftTranslatedOrbit_eval z orbit t).trans
      (congrArg (fun r : ℝ => (r : ℂ))
        (A.ofTranslatedShearOrbit_value_integer z orbit t).symm)
  refine ⟨P, T, H', rfl, rfl, hobs, hnorm, hlip, hunit, hc, heval,
    hsub, hpos, hmass, ?_⟩
  intro a ha
  have h := hs a ha
  change δ / 2 ≤ ((localLaw a).complexMean
    (fun x => (weight a x : ℂ) * T.eval (point a x))).re at h
  simpa only [heval, FiniteProbabilityWeights.complexMean, FiniteProbabilityWeights.mean,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero] using h

end Erdos3.PolynomialPatch

end

section

namespace Erdos3.PolynomialPatch

open scoped NNReal TensorProduct

variable {σ τ Ω G J : Type*} {d r : ℕ} [Fintype Ω] [Fintype G]
    (A : PolynomialPatch σ 1 d)
    [Fintype (PolynomialShearIndex A.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

theorem exists_noPivot_ambient_patch
    (M : ℝ≥0) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M)
    {p : ℝ} (hcomplex : (A.shearNiltest M hA).ComplexityLE p)
    (eta : J → PolynomialShearLieAlgebra A.weight ℚ →ₗ[ℚ] ℚ)
    (code : Fin r → Option J) (hnone : ∀ i, code i = none)
    (localOrbit : Ω → (polynomialShearFiltration A.weight 1 A.weight_le).realification.PolynomialOrbit
      (fun _ : σ => 1))
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights G)
    (localPoint : Ω → G → σ → ℤ) (physical : Ω → G → τ → ℤ)
    (weight : Ω → G → ℝ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ x, |weight a x| ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun x => (weight a x : ℂ) *
        (((A.shearNiltest M hA).kernelProjection
          (frequencyCodeKernel ((polynomialShearFiltration A.weight 1 A.weight_le).layer 1)
            eta code) (finiteFrequencyKernel_le _ _ _)).withOrbit (localOrbit a)).eval
              (localPoint a x))).re) :
    ∃ (P : PolynomialPatch τ 1 d)
      (T : (polynomialShearNilmanifold A.weight 1 A.weight_le).Niltest (fun _ : τ => 1))
      (H' : Finset Ω),
      P.weight = A.weight ∧ P.kernel = A.kernel ∧
      T.observable = (A.shearNiltest M hA).observable ∧
      T.normBound = (A.shearNiltest M hA).normBound ∧
      T.lipBound = (A.shearNiltest M hA).lipBound ∧
      T.UnitIntervalValued ∧ T.ComplexityLE p ∧
      (∀ t, T.eval t = (P.value (fun i => (t i : ℝ)) : ℂ)) ∧
      H' ⊆ H ∧ 0 < outer.mass H' ∧
      δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
      ∀ a ∈ H', δ / 2 ≤ (localLaw a).mean
        (fun x => weight a x * P.value (fun i => (physical a x i : ℝ))) := by
  let D := polynomialShearNilmanifold A.weight 1 A.weight_le
  let K := frequencyCodeKernel (D.filtration.layer 1) eta code
  have hK : K ≤ D.filtration.layer 1 := finiteFrequencyKernel_le _ _ _
  let S := (A.shearNiltest M hA).kernelProjection K hK
  let tests := fun a => S.withOrbit (localOrbit a)
  obtain ⟨ambient, hobs, _, _, heval⟩ :=
    S.exists_noPivot_ambient_realization (X := τ) tests (fun _ => rfl) eta code hnone
      ((A.shearNiltest M hA).kernelProjection_invariant K hK)
      ((A.shearNiltest M hA).kernelProjection_complexity K hK hcomplex)
      ((A.shearNiltest M hA).kernelProjection_unitInterval K hK
        (A.shearNiltest_unitInterval M hA))
  have hambient (t : τ → ℤ) : (S.withOrbit ambient.orbit).eval t = ambient.eval t := by
    exact (congrFun hobs _).symm
  apply A.exists_patch_of_kernelProjection_scores M hA hcomplex K hK ambient.orbit
    outer H hH localLaw physical weight hB hδ hweight
  intro a ha
  have hvalues (x : G) :
      (S.withOrbit ambient.orbit).eval (physical a x) = (tests a).eval (localPoint a x) :=
    (hambient _).trans (heval a _ _)
  change δ ≤ ((localLaw a).complexMean (fun x => (weight a x : ℂ) *
    (S.withOrbit ambient.orbit).eval (physical a x))).re
  rw [show (fun x => (weight a x : ℂ) *
      (S.withOrbit ambient.orbit).eval (physical a x)) =
      (fun x => (weight a x : ℂ) * (tests a).eval (localPoint a x)) from
        funext (fun x => congrArg ((weight a x : ℂ) * ·) (hvalues x))]
  exact hscore a ha

end Erdos3.PolynomialPatch

end

end OAI
