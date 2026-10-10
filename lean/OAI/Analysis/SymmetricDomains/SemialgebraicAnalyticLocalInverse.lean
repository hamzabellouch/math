import Mathlib
import OAI.Analysis.SymmetricDomains.AffineInverseGermSemialgebraic

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
namespace Release061

section
open Set Filter Topology
open scoped Classical

theorem semialgebraic_projection_chart_germ {m N : ℕ} (V : Set (Affine N))
    (hV : IsSemialgebraic V)
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (F 0))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (F 0), F (G y) = y)
    (hFV : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V) :
    ∃ (π : Affine N →L[ℂ] Affine m) (H : Affine m → Affine N),
      H 0 = F 0 ∧ AnalyticAt ℂ H 0 ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), π (H z - F 0) = z) ∧
      (∀ᶠ y in 𝓝[V] (F 0), H (π (y-F 0)) = y) ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), H z ∈ V) ∧
      ∃ r : ℝ, 0 < r ∧ SemialgebraicOn {x : Fin (m+m) → ℝ | ‖x‖ < r}
        (fun x => complexRealEquiv N (H ((complexRealEquiv m).symm x))) := by
  obtain ⟨π,H,h0,hH,hπH,hHπ,hHV⟩ := linear_projection_chart_germ V F G hF hG hGF hFG hFV
  refine ⟨π,H,h0,hH,hπH,hHπ,hHV,?_⟩
  let e := complexRealEquiv m
  let d := complexRealEquiv N
  let f := fun x => d (H (e.symm x))
  let L := e.toLinearMap.comp ((π.restrictScalars ℝ).toLinearMap.comp d.symm.toLinearMap)
  let b := -L (d (F 0))
  have hg (y : Fin (N+N) → ℝ) : L y+b = e (π (d.symm y-F 0)) := by
    simp [L,b,sub_eq_add_neg]
  have hef : Tendsto e.symm (𝓝 (0 : Fin (m+m) → ℝ)) (𝓝 (0 : Affine m)) := by
    simpa only [map_zero] using e.symm.continuous.tendsto 0
  have hfH : ContinuousAt (fun x => H (e.symm x)) (0 : Fin (m+m) → ℝ) := by
    apply ContinuousAt.comp_of_eq hH.continuousAt e.symm.continuous.continuousAt
    exact map_zero e.symm
  have hf : ContinuousAt f 0 := d.continuous.continuousAt.comp hfH
  apply affine_inverse_germ_semialgebraic (isSemialgebraic_real_image hV) f L b hf
  · filter_upwards [hef hπH] with x hx
    change π (H (e.symm x)-F 0) = e.symm x at hx
    rw [hg]
    simp only [f,d.symm_apply_apply,hx,e.apply_symm_apply]
  · have hd : Tendsto d.symm (𝓝[d '' V] (f 0)) (𝓝[V] (F 0)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hh := (d.symm.continuous.tendsto (f 0)).mono_left
          (nhdsWithin_le_nhds (s := d '' V))
        simpa only [f,map_zero,h0,d.symm_apply_apply] using hh
      · filter_upwards [self_mem_nhdsWithin] with y hy
        obtain ⟨z,hz,rfl⟩ := hy
        simpa only [d.symm_apply_apply] using hz
    filter_upwards [hd hHπ] with y hy
    rw [hg]
    change d (H (e.symm (e (π (d.symm y-F 0))))) = y
    rw [e.symm_apply_apply,hy,d.apply_symm_apply]
  · filter_upwards [hef hHV] with x hx
    exact ⟨_,hx,rfl⟩
end

open Set Filter Topology Metric
open scoped Classical

theorem semialgebraic_analytic_local_inverse {d n : ℕ}
    {B : Set (Fin d → ℝ)} (hB : IsOpen B)
    {f : (Fin d → ℝ) → (Fin n → ℝ)} (hfs : SemialgebraicOn B f)
    {x : Fin d → ℝ} (hx : x ∈ B) (hfa : AnalyticAt ℝ f x)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hd : HasFDerivAt f (L : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ)) x) :
    ∃ e : OpenPartialHomeomorph (Fin d → ℝ) (Fin n → ℝ),
      (e : (Fin d → ℝ) → (Fin n → ℝ)) = f ∧ x ∈ e.source ∧
      ∃ r : ℝ, 0 < r ∧ ball (f x) r ⊆ e.target ∧
        MapsTo e.symm (ball (f x) r) B ∧
        AnalyticOnNhd ℝ e.symm (ball (f x) r) ∧
        SemialgebraicOn (ball (f x) r) e.symm := by
  obtain ⟨e,he,hes,hea⟩ := real_analytic_local_inverse hfa L hd
  have het : f x ∈ e.target := by simpa only [he] using e.map_source hes
  have heinv : e.symm (f x) = x := by simpa only [he] using e.left_inv hes
  obtain ⟨ρ,hρ,hρsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hB.mem_nhds hx) (e.open_source.mem_nhds hes))
  have hTs : PolynomialSignSet id (ball x ρ) := by
    simpa only [ball,dist_eq_norm] using polynomialSignSet_real_ball x ρ
  have hfgs : SemialgebraicOn (ball x ρ) f := hfs.mono hTs (fun y hy => (hρsub hy).1)
  have hl : ∀ᶠ y in 𝓝 (f x), e.symm y ∈ ball x ρ := by
    apply (by simpa only [heinv] using hea.continuousAt.tendsto : Tendsto e.symm (𝓝 (f x)) (𝓝 x))
    exact Metric.ball_mem_nhds _ hρ
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (hl.and (Filter.Eventually.and (e.open_target.mem_nhds het) hea.eventually_analyticAt))
  refine ⟨e,he,hes,r,hr,fun y hy => (hrsub hy).2.1,
    fun y hy => (hρsub (hrsub hy).1).1,fun y hy => (hrsub hy).2.2,?_⟩
  apply semialgebraicOn_inverse_restrict
    (by simpa only [ball,dist_eq_norm] using polynomialSignSet_real_ball (f x) r)
    f hfgs e.symm
  · exact fun y hy => (hrsub hy).1
  · intro y hy
    have hh := e.right_inv (hrsub hy).2.1
    simpa only [he] using hh
  · intro y hy _
    have hh := e.left_inv (hρsub hy).2
    simpa only [he] using hh
end Release061

end

end OAI
