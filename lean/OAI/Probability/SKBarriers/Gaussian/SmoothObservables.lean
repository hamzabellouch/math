import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianResponse
import OAI.Probability.SKBarriers.Calculus.CoordinateStein
import OAI.Probability.SKBarriers.Hierarchy.HierarchyDensity

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section SmoothObservables
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem HasExpGrowth.const (c : F) : HasExpGrowth (fun _ : E => c) :=
  HasExpGrowth.of_bounded (norm_nonneg c) (fun _ => le_rfl)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem HasExpGrowth.finsetSum {I : Type} (s : Finset I) (f : I → E → F)
    (hf : ∀ i ∈ s, HasExpGrowth (f i)) : HasExpGrowth (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.sum_empty] using HasExpGrowth.const (E := E) (0 : F)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem HasExpGrowth.fderiv_mul {f g : E → ℝ} (hc : Differentiable ℝ f) (hcg : Differentiable ℝ g)
    (hf : HasExpGrowth f) (hg : HasExpGrowth g) (hdf : HasExpGrowth (fderiv ℝ f))
    (hdg : HasExpGrowth (fderiv ℝ g)) : HasExpGrowth (fderiv ℝ (fun z => f z*g z)) := by
  have he : fderiv ℝ (fun z => f z*g z) = fun z => g z • fderiv ℝ f z+f z • fderiv ℝ g z := by
    funext z
    rw [fderiv_fun_mul (hc z) (hcg z)]
    exact add_comm _ _
  rw [he]
  exact (hg.smul hdf).add (hf.smul hdg)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem HasExpGrowth.fderiv_sum {I : Type} (s : Finset I) (f : I → E → ℝ)
    (hc : ∀ i ∈ s, Differentiable ℝ (f i))
    (hd : ∀ i ∈ s, HasExpGrowth (fderiv ℝ (f i))) :
    HasExpGrowth (fderiv ℝ (fun z => ∑ i ∈ s, f i z)) := by
  have he : fderiv ℝ (fun z => ∑ i ∈ s, f i z) = fun z => ∑ i ∈ s, fderiv ℝ (f i) z := by
    funext z
    exact (HasFDerivAt.fun_sum (fun i hi => (hc i hi z).hasFDerivAt)).fderiv
  rw [he]
  exact HasExpGrowth.finsetSum s _ hd

def gradientSquareSum {I : Type} [Fintype I] (F : E → ℝ) (u : I → E) (z : E) : ℝ :=
  ∑ i, directionalGradient F (u i) z*directionalGradient F (u i) z

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem gradientSquareSum_regular {I : Type} [Fintype I] (F : E → ℝ)
    (hF : BoundedDerivs F) (u : I → E) :
    ContDiff ℝ 1 (gradientSquareSum F u) ∧ HasExpGrowth (gradientSquareSum F u) ∧
      HasExpGrowth (fderiv ℝ (gradientSquareSum F u)) := by
  have hc (i) := directionalGradient_contDiff F hF.1 (u i)
  have hg (i) := hF.directionalGradient_bounds (u i)
  refine ⟨ContDiff.sum (fun i _ => (hc i).mul (hc i)),?_,?_⟩
  · exact HasExpGrowth.finsetSum _ _ (fun i _ => (hg i).1.mul (hg i).1)
  · apply HasExpGrowth.fderiv_sum
    · intro i _; exact ((hc i).mul (hc i)).differentiable (by norm_num)
    · intro i _
      exact HasExpGrowth.fderiv_mul ((hc i).differentiable (by norm_num))
        ((hc i).differentiable (by norm_num)) (hg i).1 (hg i).1 (hg i).2 (hg i).2

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem TranslationInvariant.gradientSquareSum {I : Type} [Fintype I] {F : E → ℝ} {v : E}
    (hF : TranslationInvariant F v) (u : I → E) : TranslationInvariant (gradientSquareSum F u) v := by
  intro z t
  have shifted : (fun point => F (point + t • v)) = F := funext (fun point => hF point t)
  have derivative : fderiv ℝ F (z + t • v) = fderiv ℝ F z := by
    rw [← fderiv_comp_add_right (t • v), shifted]
  unfold SK.Analytic.gradientSquareSum SK.Analytic.directionalGradient
  rw [derivative]

end SmoothObservables

section SharedPrefix
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

theorem hierarchyGaussian_shared_stein (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ParameterSpace n → ℝ)
    (hc : ∀ s, ContDiff ℝ 1 (g s)) (hg : ∀ s, HasExpGrowth (g s))
    (hdg : ∀ s, HasExpGrowth (fderiv ℝ (g s))) (a : Fin n → ℝ) (j : Fin (n+1))
    (hU : ∀ s, U s (coordinateVector n a) = 0)
    (hi : ∀ k, k ≠ j → hierarchyAtom n m 1 k = 0 ∨
      TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) k) (coordinateVector n a))
    (hig : ∀ s, TranslationInvariant (g s) (coordinateVector n a)) :
    (∫ sz, coordinateLinear n a sz.2*g sz.1 sz.2 ∂hierarchyGaussianLaw n m U) =
      -hierarchyAtom n m 1 j * ∫ sz,
        g sz.1 sz.2*fderiv ℝ (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j)
          sz.2 (coordinateVector n a) ∂hierarchyGaussianLaw n m U := by
  rw [hierarchyGaussianLaw_eq_spinGaussian]
  have H := spinGaussian_directional_stein n (hierarchyPotential n m U) g
    (hierarchyPotential_boundedDerivs n m U) hc hg hdg a
  have hz (sz : S × ParameterSpace n) :
      fderiv ℝ (g sz.1) sz.2 (coordinateVector n a) = 0 :=
    (hig sz.1).fderiv_zero ((hc sz.1).differentiable (by norm_num)) sz.2
  simp_rw [hz,integral_zero,zero_add] at H
  rw [H]
  simp_rw [hierarchyPotential_directional_cancellation n m U j _ _ hU hi]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with sz
  ring

theorem hierarchyGaussian_gradientSquare_stein {I : Type} [Fintype I]
    (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (u : I → ParameterSpace n) (c : S → ℝ) (a : Fin n → ℝ) (j l : Fin (n+1))
    (hU : ∀ s, U s (coordinateVector n a) = 0)
    (hi : ∀ k, k ≠ j → hierarchyAtom n m 1 k = 0 ∨
      TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) k) (coordinateVector n a))
    (hl : TranslationInvariant (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) l) (coordinateVector n a)) :
    let M := gradientSquareSum (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) l) u
    (∫ sz, coordinateLinear n a sz.2*(c sz.1*M sz.2) ∂hierarchyGaussianLaw n m U) =
      -hierarchyAtom n m 1 j * ∫ sz,
        (c sz.1*M sz.2)*fderiv ℝ (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j)
          sz.2 (coordinateVector n a) ∂hierarchyGaussianLaw n m U := by
  dsimp only
  let F := hierarchyLevel n m (affineLogPartition (fun _ => 0) U) l
  have hF := hierarchyLevel_boundedDerivs n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) l
  have H := gradientSquareSum_regular F hF u
  apply hierarchyGaussian_shared_stein n m U (fun s z => c s*gradientSquareSum F u z)
  · intro s; exact contDiff_const.mul H.1
  · intro s; exact (HasExpGrowth.const (c s)).mul H.2.1
  · intro s
    have he : fderiv ℝ (fun z => c s*gradientSquareSum F u z) =
        fun z => c s • fderiv ℝ (gradientSquareSum F u) z := by
      funext z
      exact ((H.1.differentiable (by norm_num) z).hasFDerivAt.const_mul (c s)).fderiv
    rw [he]
    exact (HasExpGrowth.const (c s)).smul H.2.2
  · exact hU
  · exact hi
  · intro s z t
    exact congrArg (fun r => c s*r) ((hl.gradientSquareSum u) z t)

end SharedPrefix
end SK.Analytic

end
end
end
end
end
end

end

end OAI
