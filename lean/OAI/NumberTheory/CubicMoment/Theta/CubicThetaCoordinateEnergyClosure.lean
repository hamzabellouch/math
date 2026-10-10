import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateData
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateEnergyBound

namespace OAI

/-! A compact C1 coordinate function supported in one injective chart
belongs to the actual closed global energy graph, by explicit smoothing. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff
namespace CubicFirstMoment

theorem cubicThetaCoordinateData_mem_energy {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (hp : tsupport g⊆{y : ℂ × ℝ | 0<y.2})
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hs : cubicThetaPointInclusion.symm '' tsupport g⊆e.source) :
    cubicThetaCoordinateData hg hc hp∈cubicThetaGlobalEnergySpace := by
  let U := (e.symm.trans cubicThetaPointInclusion).target
  have hU : IsOpen U := (e.symm.trans cubicThetaPointInclusion).open_target
  have hgsU : tsupport g⊆U := by
    intro y hy
    change y∈cubicThetaPointInclusion.target ∧ cubicThetaPointInclusion.symm y∈e.source
    exact ⟨by rw [cubicThetaPointInclusion_target]; exact hp hy,hs ⟨y,hy,rfl⟩⟩
  obtain ⟨K,hK,hgK,hKU,happrox⟩ := cubicThetaSmoothing_compact_chart hg hc hU hgsU
  have hpos : K⊆{y : ℂ × ℝ | 0<y.2} := by
    intro y hy
    have h := (hKU hy).1
    rwa [cubicThetaPointInclusion_target] at h
  have hKe : cubicThetaPointInclusion.symm '' K⊆e.source := by
    rintro p ⟨y,hy,rfl⟩
    exact (hKU hy).2
  obtain ⟨C,hC,hbound⟩ := cubicThetaCoordinateEnergy_integral_bound hK hpos
  change cubicThetaCoordinateData hg hc hp∈closure (Set.range cubicThetaGlobalEnergyGraph)
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ := ε/(C+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  obtain ⟨f,hf,hfc,hfK,hv,hd⟩ := happrox δ hδ
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hfp := hfK.trans hpos
  have hdK : tsupport (f-g)⊆K := (tsupport_sub f g).trans (union_subset hfK hgK)
  have hdp := hdK.trans hpos
  let F : cubicThetaSmoothTests :=
    ⟨cubicThetaPoincareSection (cubicThetaCoordinateSeed f hf.continuous hfc hfp),
      cubicThetaCoordinateSection_regular hf hfc hfp,cubicThetaPoincareSection_compact _⟩
  refine ⟨cubicThetaCoordinateData hf1 hfc hfp,⟨F,rfl⟩,?_⟩
  have hdb : ∀ y, ‖fderiv ℝ (f-g) y‖≤δ := by
    intro y
    rw [fderiv_sub (hf1.differentiable one_ne_zero y) (hg.differentiable one_ne_zero y)]
    exact hd y
  have hn : ‖cubicThetaCoordinateData hf1 hfc hfp-cubicThetaCoordinateData hg hc hp‖^2≤C*δ^2 := by
    rw [← cubicThetaCoordinateData_sub hf1 hg hfc hc hfp hp hdp,
      cubicThetaCoordinateData_norm_sq (hf1.sub hg) (hfc.sub hc) hK hpos hdK e he hKe]
    exact hbound (f-g) (hf1.sub hg) δ hδ.le hv hdb
  have heps : δ^2*(C+1)^2=ε^2 := by
    have h := div_mul_cancel₀ ε (show C+1≠0 by linarith)
    change δ*(C+1)=ε at h
    calc
      _ = (δ*(C+1))^2 := (mul_pow δ (C+1) 2).symm
      _ = _ := congrArg (fun x : ℝ => x^2) h
  have hstrict : C*δ^2<ε^2 := by
    rw [← heps,mul_comm (δ^2)]
    exact mul_lt_mul_of_pos_right (by nlinarith [sq_nonneg C]) (sq_pos_of_pos hδ)
  have hnorm : ‖cubicThetaCoordinateData hf1 hfc hfp-cubicThetaCoordinateData hg hc hp‖<ε := by
    nlinarith [_root_.norm_nonneg (cubicThetaCoordinateData hf1 hfc hfp-cubicThetaCoordinateData hg hc hp)]
  simpa only [dist_eq_norm,norm_sub_rev] using hnorm

end CubicFirstMoment

end

end OAI
