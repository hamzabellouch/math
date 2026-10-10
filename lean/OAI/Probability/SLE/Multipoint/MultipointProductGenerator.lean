import OAI.Probability.SLE.Multipoint.MultipointProductDrift
import OAI.Probability.SLE.Multipoint.MultipointProductCalculus

namespace OAI

/-! The generator of the actual regularized product in simultaneous
Loewner logarithmic coordinates. -/

noncomputable section
open scoped BigOperators

namespace SLEExactGauge.Multipoint

def regularizedProduct {ι : Type*} (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ)
    (z : ι → ℂ × ℝ) (x : ℝ) : ℝ :=
  ∏ i ∈ s, regularizedLogFactor κ (D i) (σ i) (z i) x

def productDriftCost {ι : Type*} [DecidableEq ι] (s : Finset ι) (κ : ℝ)
    (D σ : ι → ℝ) (z : ι → ℂ × ℝ) (x : ℝ) : ℝ :=
  let p := greenExponent κ
  let ε := (negativeDrift p/2)/(4*((s.card : ℝ)+1))
  let C := driftAllowance p*driftThreshold p^(-p)
  let L := youngConstant p (angularCoefficientConstant p^2) ε
  κ*(C*(∑ i ∈ s, branchRegulator κ (D i) (σ i) (z i)*logVelocity κ (z i) x^2) +
    L*(∑ ij ∈ s.offDiag,
      (branchRegulator κ (D ij.1) (σ ij.1) (z ij.1)*
        branchRegulator κ (D ij.2) (σ ij.2) (z ij.2))^(-exponent p)*
      (logVelocity κ (z ij.1) x*logVelocity κ (z ij.2) x)))

lemma regularizedProduct_contDiff {ι : Type*} [Fintype ι]
    (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ι → ℂ × ℝ) × ℝ => regularizedProduct s κ D σ p.1 p.2) := by
  unfold regularizedProduct
  apply contDiff_prod
  intro i _
  exact (regularizedLogFactor_contDiff κ (D i) (σ i)).comp
    (((contDiff_apply ℝ (ℂ × ℝ) i).comp contDiff_fst).prodMk contDiff_snd)

lemma regularizedFactor_state_directional {ι : Type*} [Fintype ι]
    (i : ι) (κ D σ : ℝ) (z v : ι → ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun z => regularizedLogFactor κ D σ (z i) x) z) v =
      (fderiv ℝ (fun q => regularizedLogFactor κ D σ q x) (z i)) (v i) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun q => regularizedLogFactor κ D σ q x) :=
    (regularizedLogFactor_contDiff κ D σ).comp (contDiff_id.prodMk contDiff_const)
  have hd := ((hcd.differentiable (by simp)) (z i)).hasFDerivAt
  have hproj : HasFDerivAt (fun q : ι → ℂ × ℝ => q i)
      (ContinuousLinearMap.proj i) z := hasFDerivAt_apply (𝕜 := ℝ) i z
  have he := hd.comp z hproj
  have heq := congrArg (fun A : (ι → ℂ × ℝ) →L[ℝ] ℝ => A v) he.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using heq

/-- Completed and not-yet-active points impose no velocity condition. -/
lemma regularizedProduct_directional_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i)
    (z v w : ι → ℂ × ℝ) (x : ℝ) (hvw : ∀ i ∈ s, v i = w i) :
    (fderiv ℝ (fun q => regularizedProduct s κ D σ q x) z) v =
      (fderiv ℝ (fun q => regularizedProduct s κ D σ q x) z) w := by
  have hf (i : ι) : DifferentiableAt ℝ
      (fun q : ι → ℂ × ℝ => regularizedLogFactor κ (D i) (σ i) (q i) x) z :=
    (((regularizedLogFactor_contDiff κ (D i) (σ i)).comp
      ((contDiff_apply ℝ (ℂ × ℝ) i).prodMk contDiff_const)).differentiable (by simp)) z
  have hne (i : ι) (hi : i ∈ s) : regularizedLogFactor κ (D i) (σ i) (z i) x ≠ 0 :=
    (regularizedLogFactor_pos κ (D i) (σ i) (hD i hi) _ _).ne'
  unfold regularizedProduct
  rw [finite_product_directional_relative s _ z v (fun i _ => hf i) hne,
    finite_product_directional_relative s _ z w (fun i _ => hf i) hne]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [regularizedFactor_state_directional, regularizedFactor_state_directional, hvw i hi]

theorem regularizedProduct_generator_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i)
    (z : ι → ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun z => regularizedProduct s κ D σ z x) z)
        (fun i => physicalLogLoewnerField (Real.sqrt κ*x) (z i)) +
      (1/2 : ℝ)*iteratedDeriv 2 (regularizedProduct s κ D σ z) x =
    regularizedProduct s κ D σ z x *
      ((∑ i ∈ s, logGenerator κ (regularizedLogFactor κ (D i) (σ i)) (z i) x /
        regularizedLogFactor κ (D i) (σ i) (z i) x) +
      (1/2 : ℝ)*(∑ ij ∈ s.offDiag,
        (deriv (regularizedLogFactor κ (D ij.1) (σ ij.1) (z ij.1)) x /
          regularizedLogFactor κ (D ij.1) (σ ij.1) (z ij.1) x)*
        (deriv (regularizedLogFactor κ (D ij.2) (σ ij.2) (z ij.2)) x /
          regularizedLogFactor κ (D ij.2) (σ ij.2) (z ij.2) x))) := by
  have hcd (i : ι) : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ι → ℂ × ℝ) × ℝ => regularizedLogFactor κ (D i) (σ i) (p.1 i) p.2) :=
    (regularizedLogFactor_contDiff κ (D i) (σ i)).comp
      (((contDiff_apply ℝ (ℂ × ℝ) i).comp contDiff_fst).prodMk contDiff_snd)
  have h := finite_product_generator s
    (fun i z x => regularizedLogFactor κ (D i) (σ i) (z i) x) (fun i _ => hcd i)
    (fun i hi z x => (regularizedLogFactor_pos κ (D i) (σ i) (hD i hi) (z i) x).ne')
    z (fun i => physicalLogLoewnerField (Real.sqrt κ*x) (z i)) x
  simp only [regularizedFactor_state_directional] at h
  exact h

theorem regularizedProduct_generator_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (D σ : ι → ℝ) (z : ι → ℂ × ℝ) (x : ℝ)
    (hD : ∀ i ∈ s, 0 < D i) (hσ : ∀ i ∈ s, σ i ≤ 1)
    (hδ : ∀ i ∈ s, branchRegulator κ (D i) (σ i) (z i) ≤ 1) :
    (fderiv ℝ (fun z => regularizedProduct s κ D σ z x) z)
        (fun i => physicalLogLoewnerField (Real.sqrt κ*x) (z i)) +
      (1/2 : ℝ)*iteratedDeriv 2 (regularizedProduct s κ D σ z) x ≤
    regularizedProduct s κ D σ z x * productDriftCost s κ D σ z x := by
  rw [regularizedProduct_generator_identity s κ D σ hD]
  apply mul_le_mul_of_nonneg_left (regularized_product_relative_drift s κ hκ hκ8 D σ z x hD hσ hδ)
  exact (Finset.prod_pos (fun i hi => regularizedLogFactor_pos κ (D i) (σ i) (hD i hi) (z i) x)).le

end SLEExactGauge.Multipoint

end

end OAI
