import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalGamma

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma framePairing_encode (a b : TwoForm X) (x : X) :
    framePairing A J α ht E a x (frameEncode J α ht A E x (b x)) =
      GeometricAdjoint.pairing J α ht a b x := by
  rw [framePairing_apply]
  change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x) (a x)
    (frameDecode J α ht A E x (frameEncode J α ht A E x (b x))) = _
  erw [frameDecode_encode J α ht A E hE]
  rfl

include hE in
omit [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] in
lemma smoothL2_eq_of_framePairings (f : L2 A J α hs ht true)
    (b : PreL2 A J α hs ht true)
    (hf : ∀ a : PreL2 A J α hs ht true,
      ⟪f,smoothL2 A J α hs ht true a⟫ = ∫ y, framePairing A J α ht E a.val y
        (frameEncode J α ht A E y (b.val y)) ∂geometricVolume A J α) :
    f = smoothL2 A J α hs ht true b := by
  apply ext_inner_right ℝ
  intro v
  refine (smoothL2_dense A J α hs ht true).induction_on v
    (_root_.isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
  intro a
  rw [hf a,(smoothL2 A J α hs ht true).inner_map_map,preL2_inner]
  unfold l2Pairing
  apply integral_congr_ae
  filter_upwards [] with y
  rw [framePairing_encode A J α ht E hE]
  exact MetricForms.pairing_symm _ _ _

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma framePairing_fun_smul (a : TwoForm X) (φ : X → ℝ) (x : X) (v : FrameSpace A) :
    framePairing A J α ht E (fun y => φ y • a y) x v =
      φ x * framePairing A J α ht E a x v := by
  erw [framePairing_apply,framePairing_apply]
  change X → MetricForms.Form Space 2 at a
  change (MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2
    (φ x • a x)) (frameDecode J α ht A E x v) =
    φ x * (MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2
      (a x)) (frameDecode J α ht A E x v)
  rw [map_smul,_root_.smul_apply,smul_eq_mul]

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma frame_kernel_pairing_continuous (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (a b : TwoForm X) (ha : IsSmooth a) (hb : IsSmooth b) :
    Continuous (fun p : X × X => framePairing A J α ht E a p.1
      (K p.1 p.2 (frameEncode J α ht A E p.2 (b p.2)))) :=
  ((framePairing_continuous A J α hs ht E hE a ha).comp continuous_fst).clm_apply
    (hK.clm_apply ((frameEncode_section_smooth J α ht A E hE hs b hb).continuous.comp continuous_snd))

include hs hE in
omit [ConnectedSpace X] in
lemma frame_kernel_scalar_eq_of_smooth_tests
    (K L : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (hL : Continuous (fun p : X × X => L p.1 p.2))
    (htest : ∀ a b : TwoForm X, IsSmooth a → IsSmooth b →
      (∫ x, ∫ y, framePairing A J α ht E a x (K x y (frameEncode J α ht A E y (b y)))
        ∂geometricVolume A J α ∂geometricVolume A J α) =
      ∫ x, ∫ y, framePairing A J α ht E a x (L x y (frameEncode J α ht A E y (b y)))
        ∂geometricVolume A J α ∂geometricVolume A J α)
    (a b : TwoForm X) (ha : IsSmooth a) (hb : IsSmooth b) (x y : X) :
    framePairing A J α ht E a x (K x y (frameEncode J α ht A E y (b y))) =
      framePairing A J α ht E a x (L x y (frameEncode J α ht A E y (b y))) := by
  let := geometricVolume_finite A J α hs ht
  let := geometricVolume_openPos A J α hs ht
  have hlocal (φ ψ : X → ℝ) (hφ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ φ)
      (hψ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ψ) :
      (∫ x, ∫ y, φ x*ψ y*(framePairing A J α ht E a x
        (K x y (frameEncode J α ht A E y (b y)))) ∂geometricVolume A J α ∂geometricVolume A J α) =
      ∫ x, ∫ y, φ x*ψ y*(framePairing A J α ht E a x
        (L x y (frameEncode J α ht A E y (b y)))) ∂geometricVolume A J α ∂geometricVolume A J α := by
    have h := htest (fun x => φ x • a x) (fun y => ψ y • b y)
      (Smooth.fun_smul hφ ha) (Smooth.fun_smul hψ hb)
    have he (Z : X → X → FrameSpace A →L[ℝ] FrameSpace A) (x y : X) :
        framePairing A J α ht E (fun x => φ x • a x) x
          (Z x y (frameEncode J α ht A E y (ψ y • b y))) =
        φ x*ψ y*(framePairing A J α ht E a x
          (Z x y (frameEncode J α ht A E y (b y)))) := by
      erw [framePairing_fun_smul, map_smul, map_smul, map_smul]
      simp only [smul_eq_mul]
      ring
    simpa only [he] using h
  have hcK := frame_kernel_pairing_continuous A J α hs ht E hE K hK a b ha hb
  have hcL := frame_kernel_pairing_continuous A J α hs ht E hE L hL a b ha hb
  apply le_antisymm
  · exact continuous_kernel_le_of_smooth_tests (geometricVolume A J α) _ _ hcK hcL
      (fun φ ψ hφ hψ _ _ => (hlocal φ ψ hφ hψ).le) x y
  · exact continuous_kernel_le_of_smooth_tests (geometricVolume A J α) _ _ hcL hcK
      (fun φ ψ hφ hψ _ _ => (hlocal φ ψ hφ hψ).ge) x y

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

def pairingEvaluationTerm (b : PreL2 A J α hs ht true) (i : C.centers) (j : Fin 6) (x : X) :
    L2 A J α hs ht true →L[ℝ] ℝ :=
  GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val x •
    (EuclideanSpace.proj j).comp ((C.patch i).smoothing.realEvaluation
      (extChartAt Model (C.patch i).chart.val x))

lemma pairingEvaluationTerm_continuous (b : PreL2 A J α hs ht true) (i : C.centers) (j : Fin 6) :
    Continuous (C.pairingEvaluationTerm b i j) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport (C.partition i)
  · have hc := (continuousOn_extChartAt _ _ (C.subordinate i hx).1).continuousAt
      ((isOpen_extChartAt_source _).mem_nhds (C.subordinate i hx).1)
    exact (GeometricAdjoint.pairing_two_smooth J α hs ht b.property
      (C.basisForm i j).property).continuous.continuousAt.smul
      (continuousAt_const.clm_comp ((C.patch i).smoothing.realEvaluation_continuous.continuousAt.comp hc))
  · apply (continuousAt_const (y := (0 : L2 A J α hs ht true →L[ℝ] ℝ))).congr_of_eventuallyEq
    have hn : ∀ᶠ y in 𝓝 x, y ∉ tsupport (C.partition i) :=
      (isClosed_tsupport (C.partition i)).isOpen_compl.mem_nhds hx
    filter_upwards [hn] with y hy
    unfold pairingEvaluationTerm
    have hz : GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val y = 0 := by
      change (MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht y) 2 (b.val y))
        ((C.basisForm i j).val y) = 0
      erw [C.basisForm_zero i j hy,map_zero]
    rw [hz,zero_smul]

def pairingEvaluation (b : PreL2 A J α hs ht true) (x : X) :
    L2 A J α hs ht true →L[ℝ] ℝ :=
  ∑ i : C.centers, ∑ j : Fin 6, C.pairingEvaluationTerm b i j x

lemma pairingEvaluation_continuous (b : PreL2 A J α hs ht true) :
    Continuous (C.pairingEvaluation b) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact C.pairingEvaluationTerm_continuous b i j

lemma pairingEvaluationTerm_smooth_sum (b : PreL2 A J α hs ht true) (i : C.centers) (x : X)
    (f : L2 A J α hs ht true) (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a) :
    ∑ j : Fin 6, C.pairingEvaluationTerm b i j x f =
      C.partition i x * GeometricAdjoint.pairing J α ht b.val a.val x := by
  classical
  by_cases hx : x ∈ tsupport (C.partition i)
  · let aa : MetricForms.Form Space 2 := a.val x
    let bb : MetricForms.Form Space 2 := b.val x
    let v : Fin 6 → MetricForms.Form Space 2 := fun j => (C.basisForm i j).val x
    let c : Fin 6 → ℝ := fun j => (rawVector J α ht (C.patch i).chart.val
      (D (C.patch i).chart).toData a.val (extChartAt Model (C.patch i).chart.val x)) j
    let L : MetricForms.Form Space 2 →L[ℝ] ℝ :=
      MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2 bb
    have he : (∑ j : Fin 6, c j • v j) = C.partition i x • aa :=
      C.basisForm_expansion i a.val hx
    have hl := congrArg L he
    change L (∑ j : Fin 6, c j • v j) = L (C.partition i x • aa) at hl
    simp only [map_sum,map_smul,smul_eq_mul] at hl
    change ∑ j : Fin 6, GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val x *
      (((C.patch i).smoothing.realEvaluation (extChartAt Model (C.patch i).chart.val x) f) j) = _
    rw [(C.patch i).smoothing.realEvaluation_smooth f a ha (C.subordinate i hx).2]
    change ∑ j : Fin 6, L (v j) * c j = (C.partition i x) * L aa
    simpa only [mul_comm] using hl
  · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
    apply Finset.sum_eq_zero
    intro j _
    change GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val x * _ = 0
    have hz : GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val x = 0 := by
      change (MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2 (b.val x))
        ((C.basisForm i j).val x) = 0
      erw [C.basisForm_zero i j hx,map_zero]
    rw [hz,zero_mul]

lemma pairingEvaluation_smooth (b : PreL2 A J α hs ht true) (x : X)
    (f : L2 A J α hs ht true) (a : PreL2 A J α hs ht true)
    (ha : hodgeRegularization A J α hs ht r f = smoothL2 A J α hs ht true a) :
    C.pairingEvaluation b x f = GeometricAdjoint.pairing J α ht b.val a.val x := by
  simp only [pairingEvaluation,sum_apply]
  simp_rw [C.pairingEvaluationTerm_smooth_sum b _ x f a ha]
  rw [← Finset.sum_mul]
  have hp : ∑ i : C.centers, C.partition i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using C.partition.sum_eq_one (mem_univ x)
  rw [hp,one_mul]

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
