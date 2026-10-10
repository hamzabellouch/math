import OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy
import OAI.NumberTheory.DirichletL.Moments.PositiveSummability

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSourceAbsoluteEnvelope
open HeckeFamily CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentSourceRectangleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeHeight CenteredMomentPositiveSummability
open CenteredMomentAbsoluteEnergy QuadraticInitialBound ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

 theorem actual_source_absolute (Q:Finset (Ideal O)) (c:Ideal O→ℂ) (η:Character) (t:ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    sourceRestrictedEnergy keep Q c (heightCoeff η t) Φ K≤
      diagonalControl Φ*max 1 K*(∑I∈Q,‖c I‖)^2 := by
  let F:O→ℂ:=fun z=>rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I:supportedColumns Q=>c I*heightCoeff η t I) z
  let B:ℝ:=∑I∈Q,‖c I‖
  have hB:0≤B:=Finset.sum_nonneg (fun I _=>norm_nonneg _)
  have hF (z:O):‖F z‖≤B:=by
    change ‖rowPolynomial Finset.univ (sourceGenerator Q) (fun I:supportedColumns Q=>c I*heightCoeff η t I) z‖≤∑I∈Q,‖c I‖
    rw [height_source_row η t Q c z]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg (c I)) (rowWeight_norm_le_one_all η CenteredMomentSecondHeightFamily.fixedBadMask 1 z t I)
  have hs:=bounded_radial_summable F B hF keep Φ K hK
  have hh:=hs.tsum_le_tsum (g:=fun z:O=>B^2*‖Φ (‖eisEmbedding z‖^2/K)‖) (fun z=>by
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hF z) 2) (norm_nonneg _))
    · positivity) ((radial_norm_summable Φ K hK).mul_left (B^2))
  rw [tsum_mul_left] at hh
  apply hh.trans
  exact (mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) (sq_nonneg B)).trans_eq (by ring)

end SevenEighths.CenteredMomentSourceAbsoluteEnvelope

end

end OAI
