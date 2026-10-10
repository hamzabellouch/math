import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
namespace YauCounterexamples
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def preconditionedInverse (R : X →L[ℝ] Y) (L : Y →L[ℝ] X) : X →L[ℝ] Y :=
  R ∘L Ring.inverse (L ∘L R)

omit [CompleteSpace X] in
lemma preconditionedInverse_right (R : X →L[ℝ] Y) (L : Y →L[ℝ] X)
    (h : IsUnit (L ∘L R)) : L ∘L preconditionedInverse R L = 1 := by
  change (L ∘L R) * Ring.inverse (L ∘L R) = 1
  exact Ring.mul_inverse_cancel _ h

omit [CompleteSpace X] in
lemma preconditionedInverse_base (R : X →L[ℝ] Y) (L : Y →L[ℝ] X)
    (h : L ∘L R = 1) : preconditionedInverse R L = R := by
  simp only [preconditionedInverse, h, Ring.inverse_one]
  rfl

lemma continuousAt_preconditionedInverse (R : X →L[ℝ] Y) (L : Y →L[ℝ] X)
    (h : IsUnit (L ∘L R)) : ContinuousAt (preconditionedInverse R) L := by
  have hm : Continuous (fun T : Y →L[ℝ] X => T ∘L R) := by fun_prop
  have hi : ContinuousAt Ring.inverse (L ∘L R) := by
    obtain ⟨u, hu⟩ := h
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hI : Tendsto (fun T : Y →L[ℝ] X => Ring.inverse (T ∘L R)) (𝓝 L)
      (𝓝 (Ring.inverse (L ∘L R))) := hi.tendsto.comp hm.continuousAt.tendsto
  have hout : Continuous (fun D : X →L[ℝ] X => R ∘L D) := by fun_prop
  exact hout.continuousAt.tendsto.comp hI

lemma eventuallyIsUnit_preconditioned (R : X →L[ℝ] Y) (L : Y →L[ℝ] X)
    (h : IsUnit (L ∘L R)) : ∀ᶠ T in 𝓝 L, IsUnit (T ∘L R) := by
  have hm : Continuous (fun T : Y →L[ℝ] X => T ∘L R) := by fun_prop
  exact hm.continuousAt.eventually (Units.isOpen.mem_nhds h)

lemma preconditionedInverse_tendsto {P : Type*} {l : Filter P}
    (R : X →L[ℝ] Y) (L : Y →L[ℝ] X) (h : L ∘L R = 1)
    (T : P → Y →L[ℝ] X) (hT : Tendsto T l (𝓝 L)) :
    Tendsto (fun p => preconditionedInverse R (T p)) l (𝓝 R) := by
  have hi : IsUnit (L ∘L R) := h ▸ isUnit_one
  simpa only [preconditionedInverse_base R L h, Function.comp_def] using
    (continuousAt_preconditionedInverse R L hi).tendsto.comp hT
end YauCounterexamples

end

end OAI
