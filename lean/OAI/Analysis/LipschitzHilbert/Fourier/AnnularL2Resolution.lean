import OAI.Analysis.LipschitzHilbert.Fourier.AnnularSchwartzResolution
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalProjectionAlgebra

namespace OAI

/-! Uniformly bounded concrete annular partial sums resolve every L2
input, rather than only a dense class of Schwartz functions. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketRepresentation

def annularL2Sum (N : ℕ) : Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  ∑ n∈Finset.range (2*N+1), verticalL2Projection reassemblyDifferenceSchwartz (reassemblyScale N n)

theorem annularL2Sum_onSchwartz (N : ℕ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    annularL2Sum N (f.toLp 2 planeMeasure)=(schwartzAnnularSum N f).toLp 2 planeMeasure := by
  simp only [annularL2Sum,sum_apply,
    verticalL2Projection_onSchwartz _ _ (reassemblyScale_pos _ _)]
  exact (map_sum (SchwartzMap.toLpCLM ℂ ℂ 2 planeMeasure) _ _).symm

theorem schwartzAnnularSum_norm (N : ℕ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖(schwartzAnnularSum N f).toLp 2 planeMeasure‖≤2*‖f.toLp 2 planeMeasure‖ := by
  have hfi : Integrable (fun omega => ‖planarFourier f omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz f).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  have hgi : Integrable (fun omega => ‖planarFourier (schwartzAnnularSum N f) omega‖^2) planeMeasure := by
    simpa only [planarFourierSchwartz_apply] using
      ((planarFourierSchwartz (schwartzAnnularSum N f)).memLp 2 planeMeasure).integrable_norm_pow (by decide : 2≠0)
  have h := integral_mono hgi (hfi.const_mul 4) (fun omega => by
    rw [schwartzAnnularSum_fourier,norm_mul,mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hn := reassemblySymbol_norm N omega.2
    nlinarith only [hn,norm_nonneg (reassemblySymbol N omega.2)])
  rw [integral_const_mul,planar_integral_norm_sq_fourier,planar_integral_norm_sq_fourier] at h
  rw [←memLp_toL2_norm_sq planeMeasure _ ((schwartzAnnularSum N f).memLp 2 planeMeasure),
    ←memLp_toL2_norm_sq planeMeasure _ (f.memLp 2 planeMeasure)] at h
  change ‖(schwartzAnnularSum N f).toLp 2 planeMeasure‖^2≤4*‖f.toLp 2 planeMeasure‖^2 at h
  nlinarith only [h,norm_nonneg ((schwartzAnnularSum N f).toLp 2 planeMeasure),norm_nonneg (f.toLp 2 planeMeasure)]

theorem annularL2Sum_bound (N : ℕ) (f : Lp ℂ 2 planeMeasure) : ‖annularL2Sum N f‖≤2*‖f‖ := by
  have hd : DenseRange (fun g : SchwartzMap (ℝ×ℝ) ℂ => g.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro g
  rw [annularL2Sum_onSchwartz]
  exact schwartzAnnularSum_norm N g

theorem annularL2Sum_tendsto (f : Lp ℂ 2 planeMeasure) :
    Tendsto (fun N : ℕ => annularL2Sum N f) atTop (𝓝 f) := by
  have hd : DenseRange (fun g : SchwartzMap (ℝ×ℝ) ℂ => g.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨g,hg⟩ := hd.exists_dist_lt f (show 0<eps/8 by positivity)
  have hlim : Tendsto (fun N : ℕ => annularL2Sum N (g.toLp 2 planeMeasure)) atTop
      (𝓝 (g.toLp 2 planeMeasure)) := by
    simpa only [annularL2Sum_onSchwartz] using schwartzAnnularSum_Lp_tendsto g
  filter_upwards [(Metric.tendsto_nhds.mp hlim) (eps/2) (by positivity)] with N hN
  have hT := annularL2Sum_bound N (f-g.toLp 2 planeMeasure)
  rw [map_sub] at hT
  have hfinal := norm_add_le (annularL2Sum N f-annularL2Sum N (g.toLp 2 planeMeasure))
    (annularL2Sum N (g.toLp 2 planeMeasure)-f)
  have hmid := norm_add_le (annularL2Sum N (g.toLp 2 planeMeasure)-g.toLp 2 planeMeasure)
    (g.toLp 2 planeMeasure-f)
  rw [sub_add_sub_cancel] at hfinal hmid
  simp only [dist_eq_norm] at hg hN ⊢
  rw [norm_sub_rev f (g.toLp 2 planeMeasure)] at hg hT
  linarith only [hfinal,hmid,hT,hN,hg,heps]

end LipschitzHilbert.PacketRepresentation

end

end OAI
