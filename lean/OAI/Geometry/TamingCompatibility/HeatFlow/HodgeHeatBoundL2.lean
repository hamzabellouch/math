import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeKernelAction

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open MeasureTheory Set
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedRing B] (μ : Measure X)
lemma HeatBound.add {N : ℕ} {T A C : ℝ} {K L : Kernel (X := X) (B := B)}
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L) :
    HeatBound μ N T (A+C) (fun t x y => K t x y+L t x y) := by
  have hh := HeatBound.finset_sum μ (Finset.univ : Finset Bool) N T
    (fun b => if b then A else C) (fun b => if b then K else L)
    (by intro b _; cases b <;> simp only [Bool.false_eq_true,↓reduceIte]; exact hL; exact hK)
  simpa [Fintype.univ_bool,Finset.sum_insert,Finset.sum_singleton,add_comm] using hh
end TamingCompatibility.GeometricHilbert.VolterraKernel

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def heatBoundL2 (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (T H : ℝ)
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V) (t : ℝ) : L2 A J α hs ht true := by
  classical
  let := geometricMetricSpace J α hs ht
  exact if htp : t ∈ Ioc 0 T then
    kernelSectionL2 A J α hs ht E hE (K t)
      (VolterraKernel.kernel_section K hK.measurable t) H hK.nonneg
      (by simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK.row_int t htp)
      (by simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK.row t htp)
      v hvm V hV hv
    else 0

lemma heatBoundL2_norm (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (T H : ℝ)
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V) (t : ℝ) :
    ‖heatBoundL2 A J α hs ht E hE K T H hK v hvm V hV hv t‖ ≤
      frameNormConstant A J α hs ht E hE * (H*V) := by
  classical
  let := geometricMetricSpace J α hs ht
  unfold heatBoundL2
  split_ifs
  · exact kernelSectionL2_norm A J α hs ht E hE _ _ _ _ _ _ _ _ _ _ _
  · exact (norm_zero.trans_le (mul_nonneg (frameNormConstant_nonneg A J α hs ht E hE)
      (mul_nonneg hK.nonneg hV)))

lemma heatBoundL2_pairing (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (T H : ℝ)
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : t ∈ Ioc 0 T) :
    ⟪heatBoundL2 A J α hs ht E hE K T H hK v hvm V hV hv t,
      smoothL2 A J α hs ht true a⟫ = kernelWeakAction A J α ht E K v a.val t := by
  classical
  let := geometricMetricSpace J α hs ht
  unfold heatBoundL2
  rw [dite_eq_left htp]
  apply kernelSectionL2_pairing A J α hs ht E hE _ _ _ _ _ _ _ _ _ _ _ (H/t^2)
    (div_nonneg hK.nonneg (sq_nonneg t))
  simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK.sup t htp

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
