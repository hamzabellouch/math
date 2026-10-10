import Mathlib
import OAI.Probability.Ballisticity.Estimates.CappedMomentTransfer
import OAI.Probability.Ballisticity.Estimates.CurveWordDisjoint

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma medianDeviation_le_iff {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) (X : Path d) (B : ℝ) :
    medianDeviation ℓ f b H X ≤ B ↔
      ∀ j ≤ H, |signedCoordinate f (recordIndexPosition ℓ j X)-b j| ≤ B := by
  rw [← not_lt]
  change X ∉ {X | B < medianDeviation ℓ f b H X} ↔ _
  rw [medianDeviation_tail]
  simp [MedianTubeFailure]

lemma curvePrefix_ae_eq {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    CurvePrefix (realPosition (step e)) f x b B H =ᵐ[quenchedKernel (ω,x)]
      (Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∩
      {X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B} : Set (Path d)) := by
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  apply propext
  rw [curvePrefix_iff e f x b B hH X h0 hnn,Set.mem_inter_iff,Set.mem_ofPred_eq,
    medianDeviation_le_iff]

lemma curveEndpoint_eq_map {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    curveEndpoint (realPosition (step e)) f x b B H ω =
      ((quenchedKernel (ω,x)).restrict (CurvePrefix (realPosition (step e)) f x b B H)).map
        (fun X => x+recordIndexPosition (realPosition (step e)) H (fun j => X j-x)) := by
  let ℓ := realPosition (step e)
  let Y := fun X : Path d => x+recordIndexPosition ℓ H (fun j => X j-x)
  have hY : Measurable Y := (measurable_const.add
    ((measurable_recordIndexPosition ℓ H).comp (by fun_prop)))
  ext U hU
  rw [curveEndpoint_apply,Measure.map_apply hY hU,Measure.restrict_apply (hY hU)]
  change (∑' n, quenchedKernel (ω,x) ((fun X => X n) ⁻¹' U ∩ CurvePrefixAt ℓ f x b B H n)) =
    quenchedKernel (ω,x) (Y ⁻¹' U ∩ ⋃ n, CurvePrefixAt ℓ f x b B H n)
  rw [Set.inter_iUnion,measure_iUnion]
  · apply tsum_congr; intro n
    apply measure_congr
    filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
    apply propext
    have he (hX : X ∈ CurvePrefixAt ℓ f x b B H n) : Y X = X n := by
      dsimp [Y]
      rw [coordinate_hitAt_record e x X h0 hnn hH hX.1]
      abel
    constructor
    · rintro ⟨hu,hn⟩
      exact ⟨by simpa only [Set.mem_preimage,he hn] using hu,hn⟩
    · rintro ⟨hu,hn⟩
      exact ⟨by simpa only [Set.mem_preimage,he hn] using hu,hn⟩
  · intro n m hnm
    exact (curvePrefixAt_disjoint ℓ f x b B H hnm).mono Set.inter_subset_right Set.inter_subset_right
  · intro n
    exact (hY hU).inter (measurableSet_curvePrefixAt ℓ f x b B H n)

lemma curveEndpoint_lateral_map {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    (curveEndpoint (realPosition (step e)) f x b B H ω).map (fun y => signedCoordinate f (y-x)) =
      ((quenchedKernel (ω,x)).restrict (CurvePrefix (realPosition (step e)) f x b B H)).map
        (fun X => signedCoordinate f (recordIndexPosition (realPosition (step e)) H (fun j => X j-x))) := by
  rw [curveEndpoint_eq_map e f x b B hH ω,Measure.map_map]
  · congr 1
    ext X
    simp
  · exact measurable_of_countable _
  · exact measurable_const.add ((measurable_recordIndexPosition _ _).comp (by fun_prop))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma hitAt_translate_zero {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) (n : ℕ) :
    (fun X : Path d => fun j => X j-x) ⁻¹' HitAt (Strip ℓ 0 H) (Upper ℓ 0 H) n =
      HitAt (Strip ℓ x H) (Upper ℓ x H) n := by
  ext X
  simp only [Set.mem_preimage,HitAt,Strip,Upper,Set.mem_ofPred_eq,dot_realPosition_sub]
  have hz : dot (realPosition (0:Lattice d)) ℓ = 0 := by simp [dot,realPosition]
  simp only [hz,zero_add]
  constructor
  · rintro ⟨h,h'⟩
    refine ⟨by linarith,fun j hj => ?_⟩
    have hh := h' j hj
    constructor <;> linarith [hh.1,hh.2]
  · rintro ⟨h,h'⟩
    refine ⟨by linarith,fun j hj => ?_⟩
    have hh := h' j hj
    constructor <;> linarith [hh.1,hh.2]

lemma curvePrefixAt_translate_zero {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H n : ℕ) :
    (fun X : Path d => fun j => X j-x) ⁻¹' CurvePrefixAt ℓ f 0 b B H n =
      CurvePrefixAt ℓ f x b B H n := by
  unfold CurvePrefixAt
  rw [Set.preimage_inter,hitAt_translate_zero]
  simp only [sub_zero,Set.preimage_ofPred_eq]

lemma curveEndpoint_increment_translation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    (curveEndpoint ℓ f x b B H ω).map (fun y => y-x) =
      curveEndpoint ℓ f 0 b B H (fun y => ω (x+y)) := by
  have hm : Measurable (fun X : Path d => fun j => X j-x) := by fun_prop
  have hmap : (quenchedKernel (ω,x)).map (fun X : Path d => fun j => X j-x) =
      quenchedKernel ((fun y => ω (x+y)),0) := by
    simpa only [add_zero] using quenched_translation ω x 0
  ext U hU
  rw [Measure.map_apply (measurable_of_countable _) hU,curveEndpoint_apply,curveEndpoint_apply]
  apply tsum_congr; intro n
  rw [← hmap,Measure.map_apply hm
    (((measurable_pi_apply n) hU).inter (measurableSet_curvePrefixAt ℓ f 0 b B H n)),
    Set.preimage_inter,curvePrefixAt_translate_zero]
  rfl

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma conditional_selection_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Set Ω) (hN : MeasurableSet N)
    (hμN : μ N ≠ 0) (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G)
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hF0 : ∀ x, 0 ≤ F x) (hFB : ∀ x ∈ N, F x ≤ B)
    (hG0 : ∀ x, 0 ≤ G x) (hGB : ∀ x, G x ≤ B)
    (hGN : ∀ x ∉ N, G x = B) (hFG : ∀ x ∈ N, F x ≤ a+G x) :
    (∫ x, F x ∂μ[|N]) ≤ a+2*∫ x, G x ∂μ := by
  have := cond_isProbabilityMeasure hμN
  have hFi : Integrable F μ[|N] := Integrable.of_bound hF.aestronglyMeasurable B (by
    filter_upwards [ae_cond_mem hN] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hF0 x)] using hFB x hx)
  have hGi : Integrable G μ := Integrable.of_bound hG.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hG0 x)] using hGB x)
  have hGci : Integrable G μ[|N] := Integrable.of_bound hG.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hG0 x)] using hGB x)
  have hI0 : 0 ≤ ∫ x, G x ∂μ := integral_nonneg hG0
  by_cases hq : 1/2 ≤ μ.real N
  · have hq0 : 0 < μ.real N := by linarith
    have hinv : (μ.real N)⁻¹ ≤ (2:ℝ) := by
      rw [inv_eq_one_div,div_le_iff₀ hq0]
      linarith
    have hcondG : (∫ x, G x ∂μ[|N]) ≤ 2*∫ x, G x ∂μ := by
      rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
      calc
        _ ≤ (μ N).toReal⁻¹*(∫ x, G x ∂μ) := mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hGi (Eventually.of_forall hG0)) (by positivity)
        _ ≤ 2*(∫ x, G x ∂μ) := mul_le_mul_of_nonneg_right hinv hI0
    have hh := integral_mono_ae hFi ((integrable_const a).add hGci)
      (by filter_upwards [ae_cond_mem hN] with x hx; exact hFG x hx)
    change (∫ x, F x ∂μ[|N]) ≤ (∫ x, a+G x ∂μ[|N]) at hh
    rw [integral_add (integrable_const a) hGci] at hh
    simp only [integral_const,probReal_univ,one_smul] at hh
    linarith
  · have hIF : (∫ x, F x ∂μ[|N]) ≤ B := by
      simpa only [integral_const,probReal_univ,one_smul] using
        integral_mono_ae hFi (integrable_const B)
          (by filter_upwards [ae_cond_mem hN] with x hx; exact hFB x hx)
    have hIG : B*μ.real Nᶜ ≤ ∫ x, G x ∂μ := by
      calc
        _ = ∫ x in Nᶜ, G x ∂μ := by
          rw [setIntegral_congr_fun hN.compl (fun x hx => hGN x hx)]
          simp [mul_comm]
        _ ≤ _ := setIntegral_le_integral hGi (Eventually.of_forall hG0)
    rw [measureReal_compl hN,probReal_univ] at hIG
    have hq' : μ.real N < 1/2 := lt_of_not_ge hq
    nlinarith

end DirectionalTransience

end

end

end OAI
