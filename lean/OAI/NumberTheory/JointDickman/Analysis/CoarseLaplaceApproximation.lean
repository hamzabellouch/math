import OAI.NumberTheory.JointDickman.Amplification.CoarseFeaturePolynomial

namespace OAI

/-! # Coarse prime features admit fixed finite multiplicative approximations -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem primeCoarseFeature_laplace_approximation
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {m : ℕ} (hm : 0 < m) (d : Fin m) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℝ, ∀ᶠ B : ℕ in atTop,
      (∑ x, fullPrimeMass (auxiliaryPrimes B) x*
        (primeCoarseFeature m B d x-
          ∑ v ∈ range (P.natDegree+1), P.coeff v*primeLaplaceFeature (auxiliaryPrimes B) B v x)^2) < ε := by
  obtain ⟨M,C,hM0,hC,hb⟩ := primeHalfLogInterval_upper hSD hSW hM hMP
  let D := channelMesh m
  have hD : 0 < D := channelMesh_pos hm
  let δ := min (1/8 : ℝ) (ε*D^2/(16*(M+1)))
  let η := min (1 : ℝ) (ε/8)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδsmall : δ ≤ 1/8 := min_le_left _ _
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηsmall : 2*η^2 ≤ ε/4 := by
    have h₁ : η ≤ 1 := min_le_left _ _
    have h₂ : η ≤ ε/8 := min_le_right _ _
    nlinarith
  have hδsmall' : 4*M*δ/D^2 ≤ ε/4 := by
    have h₁ : δ ≤ ε*D^2/(16*(M+1)) := min_le_right _ _
    have h₂ := (le_div_iff₀ (by positivity : 0 < 16*(M+1))).mp h₁
    apply (div_le_iff₀ (by positivity : 0 < D^2)).mpr
    nlinarith
  obtain ⟨P,hP⟩ := interval_polynomial_approximation
    (fun t => logIntervalRamp (channelLower m d) (channelUpper m d) δ t/D)
    (((logIntervalRamp_continuous _ _ hδ).div_const D).continuousOn) hη
  have ht : Tendsto (fun B : ℕ => 4*C/D^2*(B : ℝ)^(-(80 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using
      (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 80)).comp
        tendsto_natCast_atTop_atTop).const_mul (4*C/D^2))
  refine ⟨P,?_⟩
  filter_upwards [hb,ht.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < ε/4)),
    eventually_gt_atTop 0] with B hb htail hB
  have he := coarseFeature_polynomial_error hm hB d hδ hδsmall P
    (fun t ht => (hP t ht).le) hb
  change _ ≤ 4*M*δ/D^2+4*C/D^2*(B : ℝ)^(-(80 : ℝ))+2*η^2 at he
  linarith

end JointDickman

end OAI
