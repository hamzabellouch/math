import Mathlib
import OAI.Analysis.SymmetricDomains.HorizontalGraphComplexification
import OAI.Analysis.SymmetricDomains.AffineBand

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Flatten
open Set Filter Metric
open scoped Topology

lemma realEmbedding_norm {k : ℕ} (x : Fin k → ℝ) : ‖realEmbedding k x‖ = ‖x‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i => by
      simpa [realEmbedding] using norm_le_pi_norm x i
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => by
      simpa [realEmbedding] using norm_le_pi_norm (realEmbedding k x) i

lemma realPart_norm_le {k : ℕ} (z : Fin k → ℂ) : ‖realPart k z‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (Complex.abs_re_le_norm (z i)).trans (norm_le_pi_norm z i)

lemma imaginaryPart_norm_le {k : ℕ} (z : Fin k → ℂ) : ‖imaginaryPart k z‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (Complex.abs_im_le_norm (z i)).trans (norm_le_pi_norm z i)

lemma complexification_derivative_norm_le {k m : ℕ}
    {f : (Fin k → ℝ) → Fin m → ℝ} (hf : DifferentiableAt ℝ f 0)
    {g : (Fin k → ℂ) → Fin m → ℂ} (hg : DifferentiableAt ℂ g 0)
    (he : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), g (realEmbedding k x) = realEmbedding m (f x)) :
    ‖fderiv ℂ g 0‖ ≤ 2*‖fderiv ℝ f 0‖ := by
  have h1 := ((hg.hasFDerivAt.restrictScalars ℝ).comp 0 (realEmbedding k).hasFDerivAt)
  have h2 := ((realEmbedding m).hasFDerivAt.comp 0 hf.hasFDerivAt)
  have hreal : ∀ x, fderiv ℂ g 0 (realEmbedding k x) = realEmbedding m (fderiv ℝ f 0 x) := by
    have h1' : HasFDerivAt (fun x => realEmbedding m (f x))
        ((fderiv ℂ g 0).restrictScalars ℝ ∘L realEmbedding k) 0 :=
      h1.congr_of_eventuallyEq (he.mono fun x hx => hx.symm)
    have h := h1'.unique h2
    intro x
    exact congrArg (fun L : (Fin k → ℝ) →L[ℝ] (Fin m → ℂ) => L x) h
  apply (fderiv ℂ g 0).opNorm_le_bound (by positivity)
  intro z
  have hz : z = realEmbedding k (realPart k z)+Complex.I • realEmbedding k (imaginaryPart k z) := by
    ext i
    simpa [realEmbedding,realPart,imaginaryPart,mul_comm] using (Complex.re_add_im (z i)).symm
  calc
    ‖fderiv ℂ g 0 z‖ = ‖realEmbedding m (fderiv ℝ f 0 (realPart k z)) +
        Complex.I • realEmbedding m (fderiv ℝ f 0 (imaginaryPart k z))‖ := by
          conv_lhs => rw [hz]
          rw [map_add,map_smul,hreal,hreal]
    _ ≤ ‖fderiv ℝ f 0 (realPart k z)‖ + ‖fderiv ℝ f 0 (imaginaryPart k z)‖ := by
      simpa only [norm_smul,Complex.norm_I,one_mul,realEmbedding_norm] using norm_add_le
        (realEmbedding m (fderiv ℝ f 0 (realPart k z)))
        (Complex.I • realEmbedding m (fderiv ℝ f 0 (imaginaryPart k z)))
    _ ≤ ‖fderiv ℝ f 0‖ * ‖z‖ + ‖fderiv ℝ f 0‖ * ‖z‖ :=
      add_le_add ((fderiv ℝ f 0).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_left (realPart_norm_le z) (norm_nonneg _)))
        ((fderiv ℝ f 0).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_left (imaginaryPart_norm_le z) (norm_nonneg _)))
    _ = _ := by ring

theorem small_slope_graph_complexification {k : ℕ} {φ : (Fin k → ℝ) → Fin k → ℝ}
    (hφ : AnalyticAt ℝ φ 0) (hφ0 : φ 0 = 0) (hdφ : ‖fderiv ℝ φ 0‖ < 1/2) :
    ∃ e : OpenPartialHomeomorph (Fin k → ℂ) (Fin k → ℂ),
      (0 : Fin k → ℂ) ∈ e.source ∧ e 0 = 0 ∧
      AnalyticAt ℂ e 0 ∧ AnalyticAt ℂ e.symm 0 ∧
      ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
        e (realEmbedding k x) = fun i => (x i : ℂ)+Complex.I*(φ x i : ℂ) := by
  obtain ⟨Φ,hΦ,hΦeq⟩ := Release061.Complexify.vector hφ
  have hEq : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), Φ (realEmbedding k x) = realEmbedding k (φ x) := hΦeq
  have hΦ0 : Φ 0 = 0 := by
    simpa only [map_zero,hφ0] using hEq.self_of_nhds
  let L := fderiv ℂ Φ 0
  have hLn : ‖L‖ < 1 := (complexification_derivative_norm_le hφ.differentiableAt
    hΦ.differentiableAt hEq).trans_lt (by linarith)
  have hu : IsUnit (1+Complex.I • L) := by
    have hn : ‖-(Complex.I • L)‖ < 1 := by simpa only [norm_neg,norm_smul,Complex.norm_I,one_mul] using hLn
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hn
  obtain ⟨u,hu⟩ := hu
  let i := ContinuousLinearEquiv.ofUnit u
  have hi : (i : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) = 1+Complex.I • L := hu
  let Q : (Fin k → ℂ) → Fin k → ℂ := fun z => z+Complex.I • Φ z
  have hQa : AnalyticAt ℂ Q 0 := analyticAt_id.add (hΦ.const_smul (c := Complex.I))
  have hQ0 : Q 0 = 0 := by simp only [Q,hΦ0,smul_zero,add_zero]
  have hQd : HasFDerivAt Q (i : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) 0 := by
    rw [hi]
    exact (hasFDerivAt_id (𝕜 := ℂ) (0 : Fin k → ℂ)).add (hΦ.differentiableAt.hasFDerivAt.const_smul Complex.I)
  have hs : HasStrictFDerivAt Q (i : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) 0 := by
    simpa only [hQd.fderiv] using hQa.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph Q
  have he : (e : (Fin k → ℂ) → Fin k → ℂ) = Q := hs.toOpenPartialHomeomorph_coe
  have hem : (0 : Fin k → ℂ) ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  obtain ⟨p,hp⟩ := hQa
  have hc : p 1 = (continuousMultilinearCurryFin1 ℂ (Fin k → ℂ) (Fin k → ℂ)).symm
      (i : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) := by
    apply (continuousMultilinearCurryFin1 ℂ (Fin k → ℂ) (Fin k → ℂ)).injective
    simpa using hp.hasFDerivAt.unique hQd
  have hia := (e.hasFPowerSeriesAt_symm hem (he ▸ hp) hc).analyticAt
  refine ⟨e,hem,by rw [he,hQ0],he ▸ hp.analyticAt,?_,?_⟩
  · simpa only [he,hQ0] using hia
  · filter_upwards [hEq] with x hx
    rw [he]
    dsimp [Q]
    rw [hx]
    rfl
end Release061.Flatten

end

end OAI
