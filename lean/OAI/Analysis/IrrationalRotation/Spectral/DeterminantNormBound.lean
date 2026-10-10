import OAI.Analysis.IrrationalRotation.Spectral.SpectralNaturality
import OAI.Analysis.IrrationalRotation.Spectral.VectorSpectral

namespace OAI

noncomputable section
open Filter
open scoped ENNReal Topology CStarAlgebra

namespace Invariant233

variable {A : Type*} [CStarAlgebra A]

section Ordered
variable [PartialOrder A] [StarOrderedRing A]

theorem TracialState.real_nonneg_of_nonneg (τ : TracialState A)
    {a : A} (ha : 0 ≤ a) : 0 ≤ (τ a).re := by
  have hs : star (CFC.sqrt a) = CFC.sqrt a :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  have h := τ.positive (CFC.sqrt a)
  rwa [hs, CFC.sqrt_mul_sqrt_self a ha] at h

theorem TracialState.real_mono (τ : TracialState A) {a b : A} (hab : a ≤ b) :
    (τ a).re ≤ (τ b).re := by
  have h := τ.real_nonneg_of_nonneg (sub_nonneg.mpr hab)
  change 0 ≤ (τ.toContinuousLinearMap (b - a)).re at h
  simpa only [map_sub, Complex.sub_re, sub_nonneg] using h

theorem regularizedLog_le_norm (a : A) (ε : ℝ) (hε : 0 < ε) :
    CFC.log (star a * a + ε • (1 : A)) ≤
      algebraMap ℝ A (Real.log (‖a‖ ^ 2 + ε)) := by
  have hp := regularizedNormSquare_spectrum_pos a ε hε
  have hc : ContinuousOn Real.log (spectrum ℝ (star a * a + ε • (1 : A))) := by
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (hp x hx)
  have hs : IsSelfAdjoint (star a * a + ε • (1 : A)) := by
    simp [IsSelfAdjoint]
  have hbound : star a * a + ε • (1 : A) ≤ algebraMap ℝ A (‖a‖ ^ 2 + ε) := by
    rw [map_add, Algebra.algebraMap_eq_smul_one ε]
    exact add_le_add (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := a)) le_rfl
  apply cfc_le_algebraMap Real.log _ _ _ hc hs
  intro x hx
  exact Real.log_le_log (hp x hx) ((le_algebraMap_iff_spectrum_le hs).mp hbound x hx)

theorem TracialState.regularizedLog_le (τ : TracialState A)
    (a : A) (ε : ℝ) (hε : 0 < ε) :
    (τ (CFC.log (star a * a + ε • (1 : A)))).re ≤ Real.log (‖a‖ ^ 2 + ε) := by
  simpa only [TracialState.map_real, Complex.ofReal_re] using
    τ.real_mono (regularizedLog_le_norm a ε hε)

end Ordered

theorem fugledeKadisonDeterminant_le_norm (τ : TracialState A) (a : A) :
    fugledeKadisonDeterminant τ a ≤ ENNReal.ofReal ‖a‖ := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  rw [← iInf_sqrt_sq_add_pos ‖a‖ (norm_nonneg a)]
  apply le_iInf
  intro ε
  refine (iInf_le _ ε).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [← exp_half_log_eq_sqrt (by nlinarith [ε.property, sq_nonneg ‖a‖])]
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
    (τ.regularizedLog_le a ε.val ε.property) (by norm_num))

theorem fugledeKadisonDeterminant_lt_top (τ : TracialState A) (a : A) :
    fugledeKadisonDeterminant τ a < ⊤ :=
  (fugledeKadisonDeterminant_le_norm τ a).trans_lt ENNReal.ofReal_lt_top

theorem IsFaithfulTracialVector.determinant_le_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} {ξ : H} (h : IsFaithfulTracialVector M ξ) (a : M) :
    vectorFugledeKadisonDeterminant ξ (a : H →L[ℂ] H) ≤
      ENNReal.ofReal ‖(a : H →L[ℂ] H)‖ := by
  rw [← h.determinant_eq_vector a]
  exact fugledeKadisonDeterminant_le_norm h.toTracialState a

end Invariant233

end

end OAI
