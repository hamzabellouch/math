import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc

namespace OAI

/-! Reversing a compact smooth regular arc preserves its image and
exchanges the endpoint germs, with no loss of regularity. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
namespace SmoothCompactArc

theorem reverse_arc (P : SmoothCompactArc I N) :
    ∃ R : SmoothCompactArc I N,
      R.start = -P.finish ∧ R.finish = -P.start ∧
      R.domain = (fun t : ℝ => -t) ⁻¹' P.domain ∧
      R.curve = (fun t => P.curve (-t)) ∧
      R.curve '' Icc R.start R.finish = P.curve '' Icc P.start P.finish := by
  let e : ℝ ≃ₜ ℝ := Homeomorph.neg ℝ
  have hes : ContDiff ℝ ∞ e := contDiff_neg
  have hei : ContDiff ℝ ∞ e.symm := contDiff_neg
  have heD : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
    ⟨hes.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn,
      hei.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn⟩
  let U := e ⁻¹' P.domain
  have hsub : Icc (-P.finish) (-P.start) ⊆ U := by
    intro t ht
    apply P.interval_subset
    change P.start ≤ -t ∧ -t ≤ P.finish
    constructor <;> linarith [ht.1,ht.2]
  have hs : ContMDiffOn 𝓘(ℝ) I ∞ (P.curve ∘ e) U :=
    P.smooth.comp hes.contMDiff.contMDiffOn (fun _ ht => ht)
  have hr : ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) I (P.curve ∘ e) t) := by
    intro t ht
    rw [mfderiv_comp t
      ((P.smooth.contMDiffAt (P.domain_open.mem_nhds ht)).mdifferentiableAt (by simp))
      (hes.contMDiff.mdifferentiable (by simp) t)]
    exact (P.regular _ ht).comp (heD.mfderiv_injective (mem_univ t))
  have hi : InjOn (P.curve ∘ e) (Icc (-P.finish) (-P.start)) := by
    intro t ht u hu heq
    have ht' : -t ∈ Icc P.start P.finish := by constructor <;> linarith [ht.1,ht.2]
    have hu' : -u ∈ Icc P.start P.finish := by constructor <;> linarith [hu.1,hu.2]
    exact neg_injective (P.injective ht' hu' heq)
  let R : SmoothCompactArc I N := ⟨P.curve ∘ e,-P.finish,-P.start,
    neg_lt_neg P.start_lt_finish,U,P.domain_open.preimage e.continuous,hsub,hs,hr,hi⟩
  refine ⟨R,rfl,rfl,rfl,rfl,?_⟩
  apply Set.Subset.antisymm
  · rintro y ⟨t,ht,rfl⟩
    refine ⟨-t,?_,rfl⟩
    constructor <;> linarith [ht.1,ht.2]
  · rintro y ⟨t,ht,rfl⟩
    refine ⟨-t,?_,?_⟩
    · constructor <;> linarith [ht.1,ht.2]
    · change P.curve (- -t) = P.curve t
      rw [neg_neg]

end SmoothCompactArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
