import OAI.Analysis.LipschitzHilbert.Trees.SourceEnvelopeWeightComparison

namespace OAI

/-! Cauchy--Schwarz pairs the packed short envelopes with the actual
weighted long-tree maximum. All weights are explicit functions. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem reciprocal_weighted_pairing_sq {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (S U D V : X → ℝ) (K : ℝ)
    (hSm : AEStronglyMeasurable S mu) (hUm : AEStronglyMeasurable U mu)
    (hS : ∀ z, 0≤S z) (hU : ∀ z, 0≤U z)
    (hD : ∀ z, 0≤D z) (hV : ∀ z, 0≤V z)
    (hweight : ∀ z, 1≤K*(D z*V z))
    (hDS : MemLp (fun z => D z*S z) 2 mu)
    (hVU : MemLp (fun z => V z*U z) 2 mu) :
    Integrable (fun z => S z*U z) mu ∧
      (∫ z, S z*U z ∂mu)^2≤K^2*
        (∫ z, (D z*S z)^2 ∂mu)*(∫ z, (V z*U z)^2 ∂mu) := by
  let F := fun z => D z*S z
  let G := fun z => V z*U z
  have hF (z) : 0≤F z := mul_nonneg (hD z) (hS z)
  have hG (z) : 0≤G z := mul_nonneg (hV z) (hU z)
  have hprod : Integrable (fun z => F z*G z) mu := hDS.integrable_mul hVU
  have hp (z) : S z*U z≤K*(F z*G z) := by
    have hh := mul_le_mul_of_nonneg_right (hweight z) (mul_nonneg (hS z) (hU z))
    dsimp [F,G]
    nlinarith only [hh]
  have hi : Integrable (fun z => S z*U z) mu :=
    (hprod.const_mul K).mono' (hSm.mul hUm) (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hS z) (hU z))]
      exact hp z))
  have hI : (∫ z, S z*U z ∂mu)≤K*(∫ z, F z*G z ∂mu) := by
    rw [←integral_const_mul]
    exact integral_mono hi (hprod.const_mul K) hp
  have hcs : (∫ z, F z*G z ∂mu)≤
      Real.sqrt (∫ z, (F z)^2 ∂mu)*Real.sqrt (∫ z, (G z)^2 ∂mu) := by
    simpa only [Real.rpow_two,←Real.sqrt_eq_rpow] using
      integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall hF) (Filter.Eventually.of_forall hG)
        (by simpa using hDS) (by simpa using hVU)
  have hsq := pow_le_pow_left₀ (integral_nonneg fun z => mul_nonneg (hF z) (hG z)) hcs 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg fun z => sq_nonneg (F z)),
    Real.sq_sqrt (integral_nonneg fun z => sq_nonneg (G z))] at hsq
  refine ⟨hi,?_⟩
  have hs := pow_le_pow_left₀ (integral_nonneg fun z => mul_nonneg (hS z) (hU z)) hI 2
  rw [mul_pow] at hs
  exact hs.trans (by simpa only [mul_assoc,F,G] using
    mul_le_mul_of_nonneg_left hsq (sq_nonneg K))

theorem short_long_weighted_pairing_sq (S U : (ℝ×ℝ) → ℝ)
    (a b L W t : ℝ) (hL : 0<L) (hW : 0<W)
    (hSm : AEStronglyMeasurable S (volume.prod volume))
    (hUm : AEStronglyMeasurable U (volume.prod volume))
    (hS : ∀ z, 0≤S z) (hU : ∀ z, 0≤U z)
    (hDS : MemLp (fun z => shearedTopReciprocal a b L W t z*S z) 2 (volume.prod volume))
    (hVU : MemLp (fun z => treeProductPolynomial a (b-t*a) L W t z*U z) 2
      (volume.prod volume)) :
    Integrable (fun z => S z*U z) (volume.prod volume) ∧
      (∫ z, S z*U z ∂volume.prod volume)^2≤256*
        (∫ z, (shearedTopReciprocal a b L W t z*S z)^2 ∂volume.prod volume)*
        (∫ z, (treeProductPolynomial a (b-t*a) L W t z*U z)^2 ∂volume.prod volume) := by
  simpa only [show (16:ℝ)^2=256 by norm_num] using
    reciprocal_weighted_pairing_sq (volume.prod volume) S U
      (shearedTopReciprocal a b L W t) (treeProductPolynomial a (b-t*a) L W t)
      16 hSm hUm hS hU
      (fun z => topReciprocalWeight_nonneg a (b-t*a) L W _)
      (fun z => (treeProductPolynomial_pos a (b-t*a) L W t z).le)
      (envelope_tree_weight_lower a b L W t hL hW) hDS hVU

end LipschitzHilbert

end

end OAI
