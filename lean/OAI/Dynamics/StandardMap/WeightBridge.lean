import OAI.Dynamics.StandardMap.WeightUnit

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def farTestIndex : ArrayTestIndex := ⟨(dyadicInt 4097,dyadicInt 4098),by norm_num⟩
noncomputable def middleCapOpen (η:ℝ) : Set DistanceArray :=
  {d | (999/1000:ℝ)*4096 < d.val (dyadicInt 1) (dyadicInt 4097) ∧
    η < clippedShortfall (dyadicInt 4097) (dyadicInt 4098) d ∧
    0 < arrayShortfall 0 (dyadicInt 1) d ∧ 0 < arrayShortfall (dyadicInt 1) (dyadicInt 2) d}
lemma isOpen_middleCapOpen (η:ℝ) : IsOpen (middleCapOpen η) :=
  (isOpen_lt continuous_const (continuous_arrayEval (dyadicInt 1) (dyadicInt 4097))).inter
    ((isOpen_lt continuous_const (continuous_clippedShortfall _ _)).inter
      ((isOpen_lt continuous_const (continuous_arrayShortfall _ _)).inter (isOpen_lt continuous_const (continuous_arrayShortfall _ _))))
lemma clippedTest_core_positive {d:DistanceArray} (h1:0≤arrayShortfall 0 (dyadicInt 1) d)
    (h2:0≤arrayShortfall (dyadicInt 1) (dyadicInt 2) d) : clippedTest coreTestIndex d=arrayTest coreTestIndex d := by
  apply testObservation_eq_arrayTest
  · change arrayShortfall 0 (dyadicMid 0 (dyadicInt 2)) d∈Icc (0:ℝ) 1
    rw [dyadicMid_zero_two]
    exact ⟨h1,(shortfall_ambient_mem d 0 (dyadicInt 1) (by norm_num)).2⟩
  · change arrayShortfall (dyadicMid 0 (dyadicInt 2)) (dyadicInt 2) d∈Icc (0:ℝ) 1
    rw [dyadicMid_zero_two]
    exact ⟨h2,(shortfall_ambient_mem d (dyadicInt 1) (dyadicInt 2) (by norm_num)).2⟩
lemma affine_mem_middleOpen (w:Icc (0:ℝ) 1) {η:ℝ} (hw:999/1000<w.val) (he:η<1-w.val) (hw1:w.val<1) :
    affineArray w∈middleCapOpen η := by
  have h0 : 0≤1-w.val := by linarith [w.property.2]
  have h1 : 1-w.val≤1 := by linarith [w.property.1]
  change _ ∧ η < unitClip (arrayShortfall _ _ _) ∧ _
  rw [affine_shortfall _ _ _ (by norm_num),unitClip_eq ⟨h0,h1⟩,
    affine_shortfall _ _ _ (by norm_num),affine_shortfall _ _ _ (by norm_num)]
  refine ⟨?_,he,by linarith,by linarith⟩
  change (999/1000:ℝ)*4096 < w.val*|(dyadicInt 4097:ℝ)-(dyadicInt 1:ℝ)|
  norm_num; nlinarith
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence)
lemma middle_weight_tendsto {α η:ℝ} (hη:0<η) (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (g:C_c(DistanceArray,ℝ))
    (hg:∀d,0≤g d) (hz:∀d∉middleCapOpen η,g d=0) :
    Tendsto (fun i => ∫d,g d*f d ∂S.multiLaw i) atTop (𝓝 0) := by
  let W:=testEndpoint coreTestIndex
  let H:=shortfallEndpoint farTestIndex
  have hW:W.inWindow (dyadicInt 1) 0 := by
    apply testEndpoint_inWindow
    constructor <;> norm_num [intervalInWindow,coreTestIndex]
  have hH:H.inWindow (dyadicInt 4097) 0 := by
    apply shortfallEndpoint_inWindow
    constructor <;> norm_num [intervalInWindow,farTestIndex]
  obtain ⟨B,hu,hv,hsw,htw,hsh,hth⟩:=exists_bridgeGrid (dyadicInt 1) (dyadicInt 4097) (by norm_num)
    W.left W.right H.left H.right W.ordered H.ordered 0 (by norm_num) hW.1 hW.2 hH.1 hH.2
  have heW:∀d,arrayObservation B.sw B.tw W.function d=clippedTest coreTestIndex d := by intro d; rw [hsw,htw]; rfl
  have heH:∀d,arrayObservation B.sh B.th H.function d=clippedShortfall (dyadicInt 4097) (dyadicInt 4098) d := by intro d; rw [hsh,hth]; rfl
  obtain ⟨C,hC,hcap⟩:=capG_bound α
  obtain ⟨D,hD⟩:=isCompact_univ.exists_bound_of_continuousOn g.continuous.continuousOn
  have hgd:∀d,g d ≤ max D 0 := fun d => (le_abs_self _).trans ((hD d (mem_univ d)).trans (le_max_left _ _))
  have hbound:∀d,g d*f d≤(max D 0*C)*arrayObservation B.sw B.tw W.function d := by
    intro d
    rw [heW]
    by_cases hd:d∈middleCapOpen η
    · rw [clippedTest_core_positive hd.2.2.1.le hd.2.2.2.le]
      calc
        _ ≤ max D 0*f d := mul_le_mul_of_nonneg_right (hgd d) (h0 d)
        _ ≤ max D 0*(C*arrayTest coreTestIndex d) := mul_le_mul_of_nonneg_left ((hb d).trans (hcap d)) (le_max_right _ _)
        _ = _ := by ring
    · rw [hz d hd,zero_mul]
      exact mul_nonneg (mul_nonneg (le_max_right _ _) hC) (clippedTest_nonneg _ _)
  obtain ⟨T,hT⟩:=S.multiLaw_test_bound coreTestIndex
  have htest:∀ᶠi in atTop,(∫d,arrayObservation B.sw B.tw W.function d ∂S.multiLaw i)≤T := by
    filter_upwards [hT] with i hi
    simp_rw [heW]
    exact (integral_mono (integrable_clippedTest _ _) ((continuous_arrayTest _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (clippedTest_le _)).trans hi
  apply S.bridge_integral_tendsto B (criticalLowerExponent S.offset) (fun i => S.exponent i-criticalLowerExponent S.offset i)
    S.lowerExponent_tendsto (fun i j hj => by have := S.lower_lt i; omega)
    W.function H.function 6 W.lipschitz H.lipschitz W.at_zero H.at_zero
    (fun d => by rw [heW]; exact clippedTest_nonneg _ _) (fun d => by rw [heH]; exact clippedShortfall_nonneg _ _ _)
    T (by filter_upwards [htest] with i hi; exact Or.inl hi) η hη (fun d => g d*f d) (g.continuous.mul hf)
    (fun d => mul_nonneg (hg d) (h0 d)) (max D 0*C) (mul_nonneg (le_max_right _ _) hC) hbound
  intro d hn
  have hnot:d∉middleCapOpen η := by
    intro hd
    apply hn
    rw [hu,hv,heH]
    norm_num only [dyadicInt_val,Int.cast_ofNat,Int.cast_one]
    exact ⟨by nlinarith [hd.1],hd.2.1⟩
  rw [hz d hnot,zero_mul]
lemma weight_middle_null (L:S.LimitLaws) {α:ℝ} (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f)
    {η:ℝ} (hη:0<η) : Q.law (middleCapOpen η)=0 := by
  apply Q.open_null (isOpen_middleCapOpen η)
  intro g hg hz
  exact (S.middle_weight_tendsto hη f hf h0 hb g hg hz).mono_left L.refines
end CriticalScaleSequence
end StandardMapEntropy

end OAI
