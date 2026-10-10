import Mathlib
import OAI.Analysis.SymmetricDomains.EventualEquicontinuityOpenSubset

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
namespace Release061
open Set Filter Metric
open scoped Topology

theorem chart_limit_mapsTo_of_anchor {n m : ℕ}
    {S W : Set (Affine n)} {D O : Set (Affine m)}
    (hWS : W ⊆ S) (hD : IsOpen D) (hconn : IsPreconnected D)
    (e : Biholomorph W D)
    {f : ℕ → Affine n → Affine m} {F : Affine n → Affine m}
    {T : ℕ → Set (Affine m)}
    (hf : TendstoLocallyUniformlyOn f F atTop S)
    (hchart : ∀ᶠ j in atTop,
      HolomorphicOnSubset W (fun x => f j x) ∧
      ∀ z ∈ D, (fderiv ℂ
        (f j ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) z).det ≠ 0)
    (hfmap : ∀ K : Set (Affine n), IsCompact K → K ⊆ S →
      ∀ᶠ j in atTop, MapsTo (f j) K (T j))
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Affine m,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ T j)
    (hanchor : ∃ z ∈ D,
      (fderiv ℂ (F ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) z).det ≠ 0) :
    MapsTo F W O := by
  let E := ambientExtend (fun x : D => (e.toHomeomorph.symm x).val)
  have hEc : ContinuousOn E D := continuousOn_ambientExtend
    (continuous_subtype_val.comp e.toHomeomorph.symm.continuous)
  have hEm : MapsTo E D W := by
    intro x hx
    rw [show E x = (e.toHomeomorph.symm ⟨x,hx⟩).val from ambientExtend_apply _ ⟨x,hx⟩]
    exact (e.toHomeomorph.symm ⟨x,hx⟩).property
  have hconv := (hf.mono hWS).comp E hEm hEc
  have hhol : ∀ x ∈ D, ∃ A ∈ 𝓝 x, ∀ᶠ j in atTop,
      AnalyticOnNhd ℂ (f j ∘ E) A ∧ ∀ z ∈ A, (fderiv ℂ (f j ∘ E) z).det ≠ 0 := by
    intro x hx
    exact ⟨D,hD.mem_nhds hx,hchart.mono fun j hj =>
      ⟨analytic_comp_chart_inverse hD e hj.1,hj.2⟩⟩
  have hfull := jacobian_nonzero_of_anchor hD hconn hconv hhol hanchor
  have hhol' : ∀ x ∈ D, ∃ A ∈ 𝓝 x, ∀ᶠ j in atTop,
      AnalyticOnNhd ℂ (f j ∘ E) A := by
    intro x hx
    obtain ⟨A,hA,he⟩ := hhol x hx
    exact ⟨A,hA,he.mono fun j hj => hj.1⟩
  have hstable : ∀ x ∈ D, ∃ r > 0, ∀ᶠ j in atTop,
      ball ((F ∘ E) x) r ⊆ T j := by
    intro x hx
    obtain ⟨r,hr,R,_,hRD,he⟩ :=
      eventually_image_ball_of_nonzero_jacobian hD hconv hhol' hx (hfull x hx)
    have hK : IsCompact (E '' closedBall x R) :=
      (isCompact_closedBall x R).image_of_continuousOn (hEc.mono hRD)
    have hKS : E '' closedBall x R ⊆ S := by
      rintro y ⟨z,hz,rfl⟩
      exact hWS (hEm (hRD hz))
    refine ⟨r,hr,?_⟩
    filter_upwards [he,hfmap _ hK hKS] with j hj hm y hy
    obtain ⟨z,hz,hz'⟩ := hj hy
    exact hz' ▸ hm ⟨z,hz,rfl⟩
  have hmap := mapsTo_of_stable_balls_and_excluded_points hstable hexcluded
  intro q hq
  have hqE : E (e.toHomeomorph ⟨q,hq⟩).val = q := by
    dsimp only [E]
    rw [ambientExtend_apply _ (e.toHomeomorph ⟨q,hq⟩),e.toHomeomorph.symm_apply_apply]
  simpa only [Function.comp_def,hqE] using hmap (e.toHomeomorph ⟨q,hq⟩).property

end Release061

end

end OAI
