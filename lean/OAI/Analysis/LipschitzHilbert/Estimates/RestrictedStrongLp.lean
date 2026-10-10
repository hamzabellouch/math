import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeLp
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteRestrictedStrongNull
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace OAI

/-! A continuous bilinear form with the paper's restricted logarithmic
estimate has the uniform L2 bound. Continuity is used only in the final
passage from actual finite amplitude approximations. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem restricted_strong_Lp (μ : Measure X)
    (B : Lp (EuclideanSpace ℂ κ) 2 μ →L[ℝ] Lp (EuclideanSpace ℂ κ) 2 μ →L[ℝ] ℂ)
    (C : ℝ) (hC : 0≤C)
    (hB : ∀ F G : Set X, MeasurableSet F → MeasurableSet G → μ F≠∞ → μ G≠∞ →
      0<μ.real F → 0<μ.real G →
      ∀ (u v : X → EuclideanSpace ℂ κ), Measurable u → Measurable v →
        (∀ x, ‖u x‖≤1) → (∀ x, ‖v x‖≤1) →
        (∀ x, x∉F → u x=0) → (∀ x, x∉G → v x=0) →
      ∀ (hu : MemLp u 2 μ) (hv : MemLp v 2 μ),
        ‖B (hu.toLp u) (hv.toLp v)‖≤C*((1+|Real.log (μ.real F/μ.real G)|)^3)⁻¹*
          Real.sqrt (μ.real F)*Real.sqrt (μ.real G))
    (f g : X → EuclideanSpace ℂ κ) (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) :
    ‖B (hf2.toLp f) (hg2.toLp g)‖≤
      4*C*restrictedStrongConstant*Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
  let beta := fun i j : ℤ => B (amplitudeLpPiece μ hf hf2 i) (amplitudeLpPiece μ hg hg2 j)
  have hbeta (i j : ℤ) : ‖beta i j‖≤
      C*((1+|Real.log (μ.real (amplitudeLevel f i)/μ.real (amplitudeLevel g j))|)^3)⁻¹*
        Real.sqrt (μ.real (amplitudeLevel f i))*Real.sqrt (μ.real (amplitudeLevel g j)) := by
    by_cases hi : μ.real (amplitudeLevel f i)=0
    · simp only [beta,amplitudeLpPiece_zero μ hf hf2 i hi,map_zero,zero_apply,
        norm_zero,hi,Real.sqrt_zero,mul_zero,zero_mul,le_refl]
    · by_cases hj : μ.real (amplitudeLevel g j)=0
      · simp only [beta,amplitudeLpPiece_zero μ hg hg2 j hj,map_zero,norm_zero,
          hj,Real.sqrt_zero,mul_zero,le_refl]
      · exact hB _ _ (amplitudeLevel_measurable hf.norm i) (amplitudeLevel_measurable hg.norm j)
          (amplitudeLevel_finite μ hf2 i) (amplitudeLevel_finite μ hg2 j)
          (lt_of_le_of_ne measureReal_nonneg (Ne.symm hi)) (lt_of_le_of_ne measureReal_nonneg (Ne.symm hj))
          _ _ (amplitudePiece_measurable hf i) (amplitudePiece_measurable hg j)
          (amplitudePiece_bounded f i) (amplitudePiece_bounded g j)
          (amplitudePiece_supported f i) (amplitudePiece_supported g j)
          (amplitudePiece_memLp μ hf hf2 i) (amplitudePiece_memLp μ hg hg2 j)
  have hfinite (I J : Finset ℤ) :
      ‖B ((amplitudeApprox_memLp μ hf hf2 I).toLp (amplitudeApprox f I))
        ((amplitudeApprox_memLp μ hg hg2 J).toLp (amplitudeApprox g J))‖≤
      4*C*restrictedStrongConstant*Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
    have heq : B ((amplitudeApprox_memLp μ hf hf2 I).toLp (amplitudeApprox f I))
        ((amplitudeApprox_memLp μ hg hg2 J).toLp (amplitudeApprox g J))=
        ∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • beta i j := by
      rw [amplitudeApprox_toLp,amplitudeApprox_toLp]
      simp only [map_sum,map_smul,sum_apply,smul_apply,
        Finset.smul_sum,smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm]
    rw [heq]
    have hn := finite_restricted_strong_nonneg I J
      (fun i => μ.real (amplitudeLevel f i)) (fun j => μ.real (amplitudeLevel g j)) beta C hC
      (fun _ _ => measureReal_nonneg) (fun _ _ => measureReal_nonneg) (fun i _ j _ => hbeta i j)
    have hEf := amplitude_energy_budget μ hf2 hf.norm I
    have hEg := amplitude_energy_budget μ hg2 hg.norm J
    have hrootf : Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (μ.real (amplitudeLevel f i)))^2)≤
        2*Real.sqrt (∫ x, ‖f x‖^2 ∂μ) := by
      calc
        _ ≤ Real.sqrt (4*(∫ x, ‖f x‖^2 ∂μ)) := Real.sqrt_le_sqrt hEf
        _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
    have hrootg : Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (μ.real (amplitudeLevel g j)))^2)≤
        2*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
      calc
        _ ≤ Real.sqrt (4*(∫ x, ‖g x‖^2 ∂μ)) := Real.sqrt_le_sqrt hEg
        _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
    apply hn.trans
    calc
      _ ≤ C*restrictedStrongConstant*(2*Real.sqrt (∫ x, ‖f x‖^2 ∂μ))*(2*Real.sqrt (∫ x, ‖g x‖^2 ∂μ)) := by
        have hconstant := restrictedStrongConstant_pos.le
        gcongr
      _ = _ := by ring
  have hfn := amplitudeApprox_Lp_tendsto μ hf hf2
  have hgn := amplitudeApprox_Lp_tendsto μ hg hg2
  have hlim := (B.isBoundedBilinearMap.continuous.tendsto _).comp (hfn.prodMk_nhds hgn)
  exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall (fun n =>
    hfinite (Finset.Icc (-(n:ℤ)) n) (Finset.Icc (-(n:ℤ)) n)))

end LipschitzHilbert

end

end OAI
