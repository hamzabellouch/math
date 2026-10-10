import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalParametrix

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def leadingFiberForm (p : A.centers) (y : X) (t : ℝ) (v : FrameSpace A) : TwoForm X :=
  if y ∈ (extChartAt Model p.val).source then
    leadingSliceForm J α ht A E p (extChartAt Model p.val y) t
      (coordinateDecode J α ht A E p (extChartAt Model p.val y) v) else 0

def residualFiberForm (p : A.centers) (y : X) (t : ℝ) (v : FrameSpace A) : TwoForm X :=
  if y ∈ (extChartAt Model p.val).source then
    residualSliceForm J α ht A E p (extChartAt Model p.val y) t
      (coordinateDecode J α ht A E p (extChartAt Model p.val y) v) else 0

include hE in
lemma leadingFiberForm_smooth (hs : IsSmooth α) (p : A.centers) (y : X)
    {t : ℝ} (htp : 0 < t) (v : FrameSpace A) : IsSmooth (leadingFiberForm J α ht A E p y t v) := by
  unfold leadingFiberForm
  split_ifs
  · exact leadingSliceForm_smooth_all J α ht A E hE hs p _ htp _
  · exact TamingCompatibility.IsSmooth.zero

include hE in
lemma residualFiberForm_smooth (hs : IsSmooth α) (p : A.centers) (y : X)
    {t : ℝ} (htp : 0 < t) (v : FrameSpace A) : IsSmooth (residualFiberForm J α ht A E p y t v) := by
  unfold residualFiberForm
  split_ifs
  · exact residualSliceForm_smooth_all J α ht A E hE hs p _ htp _
  · exact TamingCompatibility.IsSmooth.zero

include hE in
omit [T2Space X] in
lemma leadingFiberForm_encode (p : A.centers) (y x : X) (t : ℝ) (v : FrameSpace A) :
    frameEncode J α ht A E x (leadingFiberForm J α ht A E p y t v x) =
      ManifoldKernelExtension.push p.val (leadingMatrix J α ht A E p t) (y,x) v := by
  unfold leadingFiberForm
  by_cases hy : y ∈ (extChartAt Model p.val).source
  · rw [ite_eq_left hy]
    unfold leadingSliceForm
    rw [frameEncode_manifoldTest J α ht A E p _
      (leadingSlice_domain_all J α ht A E hE p _ t _)]
    by_cases hx : x ∈ (extChartAt Model p.val).source
    · rw [ite_eq_left hx,ManifoldKernelExtension.push,ite_eq_left ⟨hy,hx⟩]
      rfl
    · rw [ite_eq_right hx,ManifoldKernelExtension.push,ite_eq_right (by simpa only [Set.mem_prod,hy,true_and] using hx)]
      rfl
  · simp only [ite_eq_right hy,Pi.zero_apply]
    erw [map_zero]
    rw [ManifoldKernelExtension.push,ite_eq_right (fun h => hy h.1)]
    rfl

include hE in
omit [T2Space X] in
lemma residualFiberForm_encode (p : A.centers) (y x : X) (t : ℝ) (v : FrameSpace A) :
    frameEncode J α ht A E x (residualFiberForm J α ht A E p y t v x) =
      ManifoldKernelExtension.push p.val (residualMatrix J α ht A E p t) (y,x) v := by
  unfold residualFiberForm
  by_cases hy : y ∈ (extChartAt Model p.val).source
  · rw [ite_eq_left hy]
    unfold residualSliceForm
    rw [frameEncode_manifoldTest J α ht A E p _
      (residualSlice_domain_all J α ht A E hE p _ t _)]
    by_cases hx : x ∈ (extChartAt Model p.val).source
    · rw [ite_eq_left hx,ManifoldKernelExtension.push,ite_eq_left ⟨hy,hx⟩]
      rfl
    · rw [ite_eq_right hx,ManifoldKernelExtension.push,ite_eq_right (by simpa only [Set.mem_prod,hy,true_and] using hx)]
      rfl
  · simp only [ite_eq_right hy,Pi.zero_apply]
    erw [map_zero]
    rw [ManifoldKernelExtension.push,ite_eq_right (fun h => hy h.1)]
    rfl

def leadingKernelForm (t : ℝ) (y : X) (v : FrameSpace A) : TwoForm X :=
  if 0 < t then ∑ p : A.centers, leadingFiberForm J α ht A E p y t v else 0

def residualKernelForm (t : ℝ) (y : X) (v : FrameSpace A) : TwoForm X :=
  if 0 < t then ∑ p : A.centers, residualFiberForm J α ht A E p y t v else 0

include hE in
lemma leadingKernelForm_smooth (hs : IsSmooth α) (t : ℝ) (y : X) (v : FrameSpace A) :
    IsSmooth (leadingKernelForm J α ht A E t y v) := by
  unfold leadingKernelForm
  split_ifs with htpos
  · apply Finset.sum_induction _ (fun a : TwoForm X => IsSmooth a)
    · exact fun _ _ ha hb => ha.add hb
    · exact TamingCompatibility.IsSmooth.zero
    · intro p _
      exact leadingFiberForm_smooth J α ht A E hE hs p y htpos v
  · exact TamingCompatibility.IsSmooth.zero

include hE in
lemma residualKernelForm_smooth (hs : IsSmooth α) (t : ℝ) (y : X) (v : FrameSpace A) :
    IsSmooth (residualKernelForm J α ht A E t y v) := by
  unfold residualKernelForm
  split_ifs with htpos
  · apply Finset.sum_induction _ (fun a : TwoForm X => IsSmooth a)
    · exact fun _ _ ha hb => ha.add hb
    · exact TamingCompatibility.IsSmooth.zero
    · intro p _
      exact residualFiberForm_smooth J α ht A E hE hs p y htpos v
  · exact TamingCompatibility.IsSmooth.zero

include hE in
omit [T2Space X] in
lemma leadingKernelForm_encode (t : ℝ) (y x : X) (v : FrameSpace A) :
    frameEncode J α ht A E x (leadingKernelForm J α ht A E t y v x) =
      globalLeading J α ht A E t x y v := by
  unfold leadingKernelForm globalLeading assemble
  split_ifs
  · erw [Finset.sum_apply,map_sum,_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro p _
    exact leadingFiberForm_encode J α ht A E hE p y x t v
  · exact map_zero _

include hE in
omit [T2Space X] in
lemma residualKernelForm_encode (t : ℝ) (y x : X) (v : FrameSpace A) :
    frameEncode J α ht A E x (residualKernelForm J α ht A E t y v x) =
      globalResidual J α ht A E t x y v := by
  unfold residualKernelForm globalResidual assemble
  split_ifs
  · erw [Finset.sum_apply,map_sum,_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro p _
    exact residualFiberForm_encode J α ht A E hE p y x t v
  · exact map_zero _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def framePairing (a : TwoForm X) (x : X) : FrameSpace A →L[ℝ] ℝ :=
  (squareMass A x)⁻¹ • ∑ p : A.centers, ∑ j : Fin 6,
    GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) x •
      (ContinuousLinearMap.proj (p,j) : FrameSpace A →L[ℝ] ℝ)

omit [CompactSpace X] [T2Space X] in
lemma framePairing_apply (a : TwoForm X) (x : X) (v : FrameSpace A) :
    framePairing A J α ht E a x v = GeometricAdjoint.pairing J α ht a
      (fun z => frameDecode J α ht A E z v) x := by
  change X → MetricForms.Form Space 2 at a
  let L : MetricForms.Form Space 2 →L[ℝ] ℝ :=
    MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2 (a x)
  change _ = L (frameDecode J α ht A E x v)
  rw [frameDecode_apply]
  have he (g : A.centers → Fin 6 → MetricForms.Form Space 2) (c : A.centers → Fin 6 → ℝ) :
      L (∑ p : A.centers, ∑ j : Fin 6, c p j • g p j) =
        ∑ p : A.centers, ∑ j : Fin 6, c p j * L (g p j) := by
    simp only [map_sum,map_smul,smul_eq_mul]
  calc
    _ = ∑ p : A.centers, ∑ j : Fin 6,
        ((squareMass A x)⁻¹ * v (p,j)) * L (globalFrame J α ht A E p j x) := by
      simp only [framePairing,_root_.sum_apply,_root_.smul_apply,
        ContinuousLinearMap.proj_apply,smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (squareMass A x)⁻¹ * (GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) x * v (p,j)) =
        ((squareMass A x)⁻¹ * v (p,j)) * GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) x
      ring
    _ = _ := (he (fun p j => globalFrame J α ht A E p j x)
      (fun p j => (squareMass A x)⁻¹*v (p,j))).symm

include hs hE in
lemma framePairing_continuous (a : TwoForm X) (ha : IsSmooth a) :
    Continuous (framePairing A J α ht E a) := by
  unfold framePairing
  apply (squareMass_inv_smooth A).continuous.smul
  apply continuous_finsetSum
  intro p _
  apply continuous_finsetSum
  intro j _
  exact (GeometricAdjoint.pairing_two_smooth J α hs ht ha
    (globalFrame_smooth J α ht A E hE hs p j)).continuous.smul continuous_const

include hs hE in
lemma framePairing_bound (a : TwoForm X) (ha : IsSmooth a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖framePairing A J α ht E a x‖ ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (framePairing_continuous A J α hs ht E hE a ha).continuousOn
  exact ⟨max C 0,le_max_right _ _,fun x => (hC x (mem_univ x)).trans (le_max_left _ _)⟩

include hE in
omit [T2Space X] in
lemma leadingKernelForm_pairing (a : TwoForm X) (y : X) (v : FrameSpace A) (t : ℝ) (x : X) :
    GeometricAdjoint.pairing J α ht a (leadingKernelForm J α ht A E t y v) x =
      framePairing A J α ht E a x (globalLeading J α ht A E t x y v) := by
  rw [← leadingKernelForm_encode J α ht A E hE]
  rw [framePairing_apply]
  unfold GeometricAdjoint.pairing
  dsimp only
  erw [frameDecode_encode J α ht A E hE]

include hE in
omit [T2Space X] in
lemma residualKernelForm_pairing (a : TwoForm X) (y : X) (v : FrameSpace A) (t : ℝ) (x : X) :
    GeometricAdjoint.pairing J α ht a (residualKernelForm J α ht A E t y v) x =
      framePairing A J α ht E a x (globalResidual J α ht A E t x y v) := by
  rw [← residualKernelForm_encode J α ht A E hE]
  rw [framePairing_apply]
  unfold GeometricAdjoint.pairing
  dsimp only
  erw [frameDecode_encode J α ht A E hE]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
