import OAI.Analysis.LipschitzHilbert.Fourier.VerticalL2Projection
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinEnergy
import Mathlib.Topology.DenseEmbedding

namespace OAI

/-! A pointwise square bound for finitely many vertical multipliers gives
the same L2 square bound, with no dependence on the number of scales. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {ι : Type*}

theorem verticalFrame_schwartz (I : Finset ι) (p : ι → SchwartzMap ℝ ℂ) (w : ι → ℝ)
    (M : ℝ) (hM : ∀ eta, (∑ i∈I, ‖p i (w i*eta)‖^2)≤M)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    (∑ i∈I, ∫ z, ‖schwartzVerticalProjection (p i) (w i) 0 f z‖^2 ∂planeMeasure)≤
      M*∫ z, ‖f z‖^2 ∂planeMeasure := by
  have heq (i : ι) := planar_integral_norm_sq_fourier (schwartzVerticalProjection (p i) (w i) 0 f)
  have hi (i : ι) : Integrable (fun omega =>
      ‖planarFourier (schwartzVerticalProjection (p i) (w i) 0 f) omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz (schwartzVerticalProjection (p i) (w i) 0 f)).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  have hfi : Integrable (fun omega => ‖planarFourier f omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz f).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  calc
    _ = ∑ i∈I, ∫ omega, ‖planarFourier (schwartzVerticalProjection (p i) (w i) 0 f) omega‖^2 ∂planeMeasure :=
      Finset.sum_congr rfl (fun i _ => (heq i).symm)
    _ = ∫ omega, ∑ i∈I, ‖planarFourier (schwartzVerticalProjection (p i) (w i) 0 f) omega‖^2 ∂planeMeasure :=
      (integral_finsetSum I (fun i _ => hi i)).symm
    _ ≤ ∫ omega, M*‖planarFourier f omega‖^2 ∂planeMeasure := by
      apply integral_mono (integrable_finsetSum I (fun i _ => hi i)) (hfi.const_mul M)
      intro omega
      simp only [schwartzVerticalProjection_fourier,sub_zero,norm_mul,mul_pow]
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hM omega.2) (sq_nonneg _)
    _ = _ := by rw [integral_const_mul,planar_integral_norm_sq_fourier]

theorem verticalFrame_L2 (I : Finset ι) (p : ι → SchwartzMap ℝ ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0<w i) (M : ℝ) (hM : ∀ eta, (∑ i∈I, ‖p i (w i*eta)‖^2)≤M)
    (f : Lp ℂ 2 planeMeasure) :
    (∑ i∈I, ‖verticalL2Projection (p i) (w i) f‖^2)≤M*‖f‖^2 := by
  have hd : DenseRange (fun g : SchwartzMap (ℝ×ℝ) ℂ => g.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro g
    have h := verticalFrame_schwartz I p w M hM g
    have hp (i : ι) : ‖verticalL2Projection (p i) (w i) (g.toLp 2 planeMeasure)‖^2=
        ∫ z, ‖schwartzVerticalProjection (p i) (w i) 0 g z‖^2 ∂planeMeasure := by
      rw [verticalL2Projection_onSchwartz _ _ (hw i)]
      exact memLp_toL2_norm_sq planeMeasure _ ((schwartzVerticalProjection (p i) (w i) 0 g).memLp 2 planeMeasure)
    have hg : ‖g.toLp 2 planeMeasure‖^2=∫ z, ‖g z‖^2 ∂planeMeasure :=
      memLp_toL2_norm_sq planeMeasure g (g.memLp 2 planeMeasure)
    simpa only [hp,hg] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
