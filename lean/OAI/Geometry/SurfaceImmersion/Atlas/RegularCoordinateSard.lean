import OAI.Geometry.SurfaceImmersion.Geometry.CriticalSetClosed
import OAI.Geometry.SurfaceImmersion.Atlas.ScalarSubmersionChart

namespace OAI

/-! A nonzero first coordinate of the derivative reduces the critical
value problem by one source and one target dimension. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasureSpace G] [BorelSpace G] [SFinite (volume : Measure G)]

theorem regular_coordinate_critical_local_null
    (hdim : Module.finrank ℝ E = Module.finrank ℝ H + 1)
    (hsard : ∀ (g : H → G) (V : Set H), IsOpen V → ContDiffOn ℝ ∞ g V →
      volume (g '' {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0)
    {f : E → ℝ × G} (hf : ContDiff ℝ ∞ f) (p : E)
    (hn : fderiv ℝ (fun x => (f x).1) p ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      volume (f '' ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ U)) = 0 := by
  have hs : Function.Surjective (fderiv ℝ (fun x => (f x).1) p) :=
    surjective_of_nonzero_of_finrank_eq_one (by simp : Module.finrank ℝ ℝ = 1)
      (show (fderiv ℝ (fun x => (f x).1) p).toLinearMap ≠ 0 from
        fun h => hn (by ext v; exact congrArg (fun L => L v) h))
  obtain ⟨e,hpe,he,hec,hei⟩ := scalar_submersion_chart hdim hf.fst p hs
  obtain ⟨r,hr,hrsub⟩ := nhds_basis_closedBall.mem_iff.mp (e.open_source.mem_nhds hpe)
  let C := {x | ¬ Function.Surjective (fderiv ℝ f x)}
  let K := C ∩ closedBall p r
  have hK : IsCompact K := (isCompact_closedBall p r).inter_left (smooth_critical_set_closed hf)
  let ψ : (ℝ × H) → ℝ × G := f ∘ e.symm
  have hψ : ContDiffOn ℝ ∞ ψ e.target := hf.comp_contDiffOn hei
  have hψfirst (z : ℝ × H) (hz : z ∈ e.target) : (ψ z).1 = z.1 := by
    change (f (e.symm z)).1 = z.1
    rw [← he,e.right_inv hz]
  have hKe : IsCompact (e '' K) := hK.image hec.continuous
  have hKeT : e '' K ⊆ e.target := by
    rintro z ⟨x,hx,rfl⟩
    exact e.map_source (hrsub hx.2)
  have hcrit (z : ℝ × H) (hz : z ∈ e '' K) :
      ¬ Function.Surjective (fderiv ℝ ψ z) := by
    rcases hz with ⟨x,hx,rfl⟩
    have hxS := hrsub hx.2
    have heinv := (hei.contDiffAt (e.open_target.mem_nhds (e.map_source hxS))).differentiableAt (by simp)
    have hd := ((hf.differentiable (by simp) (e.symm (e x))).hasFDerivAt.comp (e x) heinv.hasFDerivAt).fderiv
    rw [e.left_inv hxS] at hd
    intro hsurj
    apply hx.1
    intro y
    obtain ⟨v,hv⟩ := hsurj y
    rw [hd] at hv
    exact ⟨fderiv ℝ e.symm (e x) v,hv⟩
  have hnul : volume (ψ '' (e '' K)) = 0 :=
    split_sard_compact hsard e.open_target hψ hψfirst hKe hKeT hcrit
  have heq : ψ '' (e '' K) = f '' K := by
    rw [← image_comp]
    apply image_congr
    intro x hx
    exact congrArg f (e.left_inv (hrsub hx.2))
  rw [heq] at hnul
  refine ⟨ball p r,isOpen_ball,mem_ball_self hr,measure_mono_null (image_mono ?_) hnul⟩
  intro x hx
  exact ⟨hx.1,ball_subset_closedBall hx.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
