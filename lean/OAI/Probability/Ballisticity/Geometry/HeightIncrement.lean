import Mathlib
import OAI.Probability.Ballisticity.Estimates.AlignedRecordPrefix

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma block_transfer_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F B : ℕ → Ω → ℝ) {q : ℝ} (hq : 0 ≤ q) {H b M : ℕ} (hM : H/b ≤ M)
    {a : ℝ}
    (htransfer : q*μ.real (HeightOscillation F (HeightBlockRelation H b) (2*a)) ≤
      μ.real {ω | ∃ s h, (s,h) ∈ HeightBlockRelation H b ∧
        2*a < |B h ω-B s ω|+|F s ω-B s ω|}) :
    q*μ.real (HeightGapEvent F B H (6*a)) ≤
      (q+1)*(μ.real (HeightOscillation B (HeightBlockRelation H b) a)+
        μ.real (BlockDecoration F B M b a)) := by
  have hs : {ω | ∃ s h, (s,h) ∈ HeightBlockRelation H b ∧
      2*a < |B h ω-B s ω|+|F s ω-B s ω|} ⊆
      HeightOscillation B (HeightBlockRelation H b) a ∪ BlockDecoration F B M b a := by
    rintro ω ⟨s,h,hsj,hbig⟩
    by_cases hb : a < |B h ω-B s ω|
    · exact Or.inl ⟨s,h,hsj,hb⟩
    · apply Or.inr
      refine ⟨h/b,(Nat.div_le_div_right hsj.1).trans hM,?_⟩
      rw [← hsj.2]
      have := le_of_not_gt hb
      linarith
  have ht := htransfer.trans ((measureReal_mono hs (measure_ne_top _ _)).trans
    (measureReal_union_le (μ := μ) _ _))
  have hg := (measureReal_mono (heightGap_subset F B hM (a := a)) (measure_ne_top _ _)).trans
    ((measureReal_union_le (μ := μ) _ _).trans
      (add_le_add (measureReal_union_le (μ := μ) _ _) le_rfl))
  have hmul := mul_le_mul_of_nonneg_left hg hq
  nlinarith

lemma blockDecoration_finite_union {Ω : Type*} (F B : ℕ → Ω → ℝ) (M b : ℕ) (z : ℝ) :
    BlockDecoration F B M b z = ⋃ j ∈ Finset.range (M+1), {ω | z < |F (j*b) ω-B (j*b) ω|} := by
  ext ω
  simp only [BlockDecoration,Set.mem_ofPred_eq,Set.mem_iUnion,Finset.mem_range,Nat.lt_succ_iff,exists_prop]

lemma blockDecoration_small {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F B : ℕ → Ω → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (hdec : ∀ h : ℕ → ℕ, TendstoInMeasure μ (fun i ω => (F (h i) ω-B (h i) ω)/r i) atTop 0)
    (M : ℕ) (b : ℕ → ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i => μ.real (BlockDecoration F B M (b i) (a*r i))) atTop (𝓝 0) := by
  have hj (j : ℕ) : Tendsto (fun i => μ.real {ω | a*r i < |F (j*b i) ω-B (j*b i) ω|}) atTop (𝓝 0) := by
    have ht := tendstoInMeasure_iff_measureReal_norm.mp (hdec (fun i => j*b i)) a ha
    simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at ht
    apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ ht
    filter_upwards [hr.eventually (eventually_gt_atTop (0:ℝ))] with i hri
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    simp only [Set.mem_ofPred_eq,abs_div,abs_of_pos hri]
    exact ((lt_div_iff₀ hri).2 hω).le
  have ht := tendsto_finsetSum (Finset.range (M+1)) (fun j _ => hj j)
  simp only [Finset.sum_const_zero] at ht
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro i
  rw [blockDecoration_finite_union]
  exact measureReal_biUnion_finset_le _ _

lemma renewal_height_block_subset {Ω : Type*} (X : ℕ → Ω → ℝ) (L : ℕ → Ω → ℕ)
    {n T c δ z : ℝ} (hn : 1 ≤ n) (hT : 0 ≤ T) (hc : 1 ≤ c) (hδ : 0 ≤ δ) (hδn : 4 ≤ δ*n) :
    HeightOscillation (fun h ω => realPartialSum (fun k => X k ω)
      (renewalCount (fun k => L k ω) h)) (HeightBlockRelation (⌊T*n⌋₊+1) ⌊(δ/4)*n⌋₊) z ⊆
    {ω | ∃ h : ℕ, (h:ℝ) ≤ (T+1)*n ∧
      δ/8 < |(renewalCount (fun j => L j ω) h : ℝ)/n-(h:ℝ)/(c*n)|} ∪
      GridOscillation X ⌊(T+1)*n⌋₊ ⌊δ*n⌋₊ z := by
  rintro ω ⟨s,h,hsj,hbad⟩
  by_cases hclock : ω ∈ {ω | ∃ h : ℕ, (h:ℝ) ≤ (T+1)*n ∧
      δ/8 < |(renewalCount (fun j => L j ω) h : ℝ)/n-(h:ℝ)/(c*n)|}
  · exact Or.inl hclock
  apply Or.inr
  let C := renewalCount (fun k => L k ω)
  have hn0 : 0 < n := by linarith
  have hc0 : 0 < c := by linarith
  have hs : s ≤ h := heightBlockRelation_order _ _ _ hsj
  have hH : (h:ℝ) ≤ (T+1)*n := by
    have := (show (h:ℝ) ≤ (⌊T*n⌋₊:ℝ)+1 by exact_mod_cast hsj.1)
    have hf := Nat.floor_le (mul_nonneg hT hn0.le)
    nlinarith
  have hsH := (Nat.cast_le.mpr hs).trans hH
  have hb : (h:ℝ)-(s:ℝ) ≤ (δ/4)*n := by
    have hrem : h-s = h % ⌊(δ/4)*n⌋₊ := by
      have he : s = h / ⌊(δ/4)*n⌋₊ * ⌊(δ/4)*n⌋₊ := hsj.2
      have heq : h % ⌊(δ/4)*n⌋₊ + h / ⌊(δ/4)*n⌋₊ * ⌊(δ/4)*n⌋₊ = h := by
        simpa only [Nat.mul_comm] using Nat.mod_add_div h ⌊(δ/4)*n⌋₊
      omega
    have hb0 : 0 < ⌊(δ/4)*n⌋₊ := by
      apply Nat.succ_le_iff.mp
      apply Nat.le_floor
      norm_num
      linarith
    have hh : h-s ≤ ⌊(δ/4)*n⌋₊ := by rw [hrem]; exact (Nat.mod_lt _ hb0).le
    have hh' : (h:ℝ)-(s:ℝ) ≤ (⌊(δ/4)*n⌋₊:ℝ) := by
      rw [← Nat.cast_sub hs]
      exact_mod_cast hh
    exact hh'.trans (Nat.floor_le (mul_nonneg (by positivity) hn0.le))
  have hclock' (j : ℕ) (hj : (j:ℝ) ≤ (T+1)*n) : |(C j:ℝ)-(j:ℝ)/c| ≤ δ*n/8 := by
    have he : |(C j:ℝ)/n-(j:ℝ)/(c*n)| ≤ δ/8 :=
      le_of_not_gt (fun hh => hclock ⟨j,hj,hh⟩)
    have heq : ((C j:ℝ)/n-(j:ℝ)/(c*n))*n = (C j:ℝ)-(j:ℝ)/c := by field_simp
    have he' := mul_le_mul_of_nonneg_right he hn0.le
    have he'' : |((C j:ℝ)/n-(j:ℝ)/(c*n))*n| ≤ δ/8*n := by
      simpa only [abs_mul,abs_of_pos hn0] using he'
    rw [heq] at he''
    convert he'' using 1; ring
  have hch := (abs_le.mp (hclock' h hH)).2
  have hcs := (abs_le.mp (hclock' s hsH)).1
  have hdiv : ((h:ℝ)-(s:ℝ))/c ≤ (h:ℝ)-(s:ℝ) := div_le_self (sub_nonneg.mpr (Nat.cast_le.mpr hs)) hc
  have hd : (C h:ℝ)-(C s:ℝ) ≤ δ*n := by
    have he : (h:ℝ)/c-(s:ℝ)/c = ((h:ℝ)-(s:ℝ))/c := (sub_div _ _ _).symm
    have hδn := mul_nonneg hδ hn0.le
    linarith
  have hC := renewalCount_monotone (fun k => L k ω) hs
  have hdiff : C h-C s ≤ ⌊δ*n⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_sub hC]
    exact hd
  refine ⟨C s,?_,C h,?_,hC,by omega,hbad⟩
  · exact (renewalCount_le _ _).trans (Nat.le_floor hsH)
  · exact (renewalCount_le _ _).trans (Nat.le_floor hH)

lemma gaussian_renewal_block_modulus {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k))
    (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω) {c : ℝ} (hc : 1 ≤ c)
    (hmean : ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => (renewalSum (fun j => L j ω) k : ℝ)/k)
      atTop (𝓝 c)) (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T a β : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop,
      μ.real (HeightOscillation (fun h ω => realPartialSum (fun k => X k ω)
        (renewalCount (fun k => L k ω) h))
        (HeightBlockRelation (⌊T*fluctuationScale μ (X 0) (r i)⌋₊+1)
          ⌊δ*fluctuationScale μ (X 0) (r i)⌋₊) (a*r i)) ≤ β := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  obtain ⟨δ,hδ,hgrid⟩ := gaussian_grid_modulus μ X hX hind hident hsym hI hne r hr
    (by linarith : 0 ≤ T+1) ha (by linarith : 0 < β/2)
  let A := fun i => {ω | ∃ h : ℕ, (h:ℝ) ≤ (T+1)*n i ∧
    δ/8 < |(renewalCount (fun j => L j ω) h : ℝ)/n i-(h:ℝ)/(c*n i)|}
  have hclock : Tendsto (fun i => μ (A i)) atTop (𝓝 0) :=
    renewalCount_uniform_in_probability μ L hL hpos (by linarith) hmean n hn
      (by linarith) (by positivity)
  have hclockR : Tendsto (fun i => μ.real (A i)) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero,Function.comp_def,Measure.real] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hclock
  have hevent := (tendsto_order.mp hclockR).2 (β/2) (by linarith)
  refine ⟨δ/4,by positivity,?_⟩
  filter_upwards [hgrid,hevent,hn.eventually (eventually_ge_atTop (1:ℝ)),
    (hn.const_mul_atTop hδ).eventually (eventually_ge_atTop (4:ℝ))] with i hg ha hni hdni
  have hs := renewal_height_block_subset X L hni hT hc hδ.le hdni (z := a*r i)
  have hh := (measureReal_mono hs (measure_ne_top _ _)).trans (measureReal_union_le (μ := μ) _ _)
  change μ.real (A i) < β/2 at ha
  change μ.real (GridOscillation X ⌊(T+1)*n i⌋₊ ⌊δ*n i⌋₊ (a*r i)) ≤ β/2 at hg
  exact hh.trans (by linarith)

theorem heightGap_small_of_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F B : ℕ → Ω → ℝ)
    (r n : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hn : Tendsto n atTop atTop)
    {q T : ℝ} (hq : 0 < q) (hT : 0 ≤ T)
    (htransfer : ∀ J : Set (ℕ × ℕ), (∀ sr ∈ J, sr.1 ≤ sr.2) → ∀ z, 0 ≤ z →
      q*μ.real (HeightOscillation F J z) ≤
        μ.real {ω | ∃ s h, (s,h) ∈ J ∧ z < |B h ω-B s ω|+|F s ω-B s ω|})
    (hdec : ∀ h : ℕ → ℕ, TendstoInMeasure μ (fun i ω => (F (h i) ω-B (h i) ω)/r i) atTop 0)
    (hmod : ∀ a β : ℝ, 0 < a → 0 < β → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop,
      μ.real (HeightOscillation B (HeightBlockRelation (⌊T*n i⌋₊+1) ⌊δ*n i⌋₊) (a*r i)) ≤ β)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun i => μ.real (HeightGapEvent F B (⌊T*n i⌋₊+1) (ε*r i))) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  · intro β hβ
    let a := ε/6
    let b := β*q/(4*(q+1))
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    obtain ⟨δ,hδ,hm⟩ := hmod a b ha hb
    obtain ⟨M,hM⟩ := exists_nat_gt ((T+1)/δ)
    have hM' : T+1 < (M:ℝ)*δ := (div_lt_iff₀ hδ).mp hM
    have hcovered := eventually_floor_horizon_covered n hn (by linarith : 0 ≤ T+1) hδ M hM'
    have hd := blockDecoration_small μ F B r hr hdec M (fun i => ⌊δ*n i⌋₊) ha
    have hdevent := (tendsto_order.mp hd).2 b hb
    filter_upwards [hm,hcovered,hdevent,hr.eventually (eventually_gt_atTop (0:ℝ)),
      hn.eventually (eventually_ge_atTop (1:ℝ))] with i hmi hci hdi hri hni
    have hH : ⌊T*n i⌋₊+1 ≤ ⌊(T+1)*n i⌋₊ := by
      apply Nat.le_floor
      push_cast
      have hf := Nat.floor_le (mul_nonneg hT (by linarith : 0 ≤ n i))
      nlinarith
    have hdiv : (⌊T*n i⌋₊+1)/⌊δ*n i⌋₊ ≤ M := by
      exact ((Nat.div_lt_iff_lt_mul hci.1).mpr (hH.trans_lt hci.2)).le
    have hz : 0 ≤ 2*(a*r i) := by positivity
    have ht := block_transfer_bound μ F B hq.le hdiv
      (htransfer _ (heightBlockRelation_order _ _) (2*(a*r i)) hz)
    have he : 6*(a*r i) = ε*r i := by dsimp [a]; ring
    rw [he] at ht
    have hfin : q*μ.real (HeightGapEvent F B (⌊T*n i⌋₊+1) (ε*r i)) < q*β := by
      have hbq : (q+1)*(2*b) = q*β/2 := by dsimp [b]; field_simp; ring
      have := mul_lt_mul_of_pos_left (add_lt_add_of_le_of_lt hmi hdi) (by linarith : 0 < q+1)
      rw [← two_mul,hbq] at this
      nlinarith
    exact (mul_lt_mul_iff_of_pos_left hq).mp hfin

theorem transverse_firstHit_uniform_error {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    Tendsto (fun i => (independentConditionedPairLaw ν (realPosition (step e))).real
      (HeightGapEvent (firstHitPairGap (realPosition (step e)) f)
        (commonBoundaryGap (realPosition (step e)) f)
        (⌊T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)⌋₊+1) (ε*r i))) atTop (𝓝 0) := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ (ne_of_gt hp)
  have hi := independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e)
    htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hn := (fluctuationScale_tendsto μ (commonIncrementProcess ℓ f 0)
    (measurable_commonIncrementProcess ℓ f 0) hi hne).comp hr.1
  apply heightGap_small_of_transfer μ (firstHitPairGap ℓ f) (commonBoundaryGap ℓ f)
    r _ hr.1 hn (q := (annealedLaw ν (NoDrop ℓ 0)).toReal^2)
    (sq_pos_of_pos (ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _))) hT _ _ _ hε
  · intro J hJ z hz
    have hh := independent_firstHit_gap_transfer ν ℓ f htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) J hJ hz
    have hh' := ENNReal.toReal_mono (measure_ne_top _ _) hh
    simpa only [HeightOscillation,Measure.real,ENNReal.toReal_mul,ENNReal.toReal_pow,μ] using hh'
  · intro h
    exact independent_firstHit_decoration_small ν ℓ f htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) r hr.1 h
  · intro a β ha hβ
    apply gaussian_renewal_block_modulus μ (commonIncrementProcess ℓ f)
      (measurable_commonIncrementProcess ℓ f)
      (commonIncrements_independent ν ℓ htrans (signedHeight e)
        (signedHeight_projection e) (signedHeight_step_le e) f)
      (commonIncrements_identDistrib ν ℓ htrans (signedHeight e)
        (signedHeight_projection e) (signedHeight_step_le e) f)
      (independent_commonWordIncrement_symmetric ν ℓ htrans f) hi hne
      (commonWidthProcess ℓ) (measurable_commonWidthProcess ℓ) _
      (commonMeanWidth_ge_one ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e))
      (commonWidth_strongLaw ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e))
      r hr hT ha hβ
    filter_upwards [independent_conditioned_all_firstPairWords ν ℓ htrans
      (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)] with P hP k
    exact commonWordWidth_positive ℓ _ _ (hP k)

def heightIncrement (F : ℕ → ℝ) (k : ℕ) : ℝ := F (k+1)-F k

lemma realPartialSum_heightIncrement (F : ℕ → ℝ) (h : ℕ) :
    realPartialSum (heightIncrement F) h = F h-F 0 := by
  induction h with
  | zero => simp [realPartialSum]
  | succ h ih => rw [realPartialSum_succ,ih,heightIncrement]; ring

lemma measurable_heightIncrement {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hF : ∀ k, Measurable (F k)) (j : ℕ) :
    Measurable (fun ω => heightIncrement (fun k => F k ω) j) := (hF (j+1)).sub (hF j)

lemma height_polygon_difference_le (F B : ℕ → ℝ) (h0 : F 0 = B 0)
    {r n T a : ℝ} (hr : 0 < r) (hn : 0 ≤ n) (hT : 0 ≤ T)
    (hgap : ∀ h ≤ ⌊T*n⌋₊+1, |F h-B h| ≤ a*r) :
    ‖scaledPolygon (heightIncrement F) r n T-scaledPolygon (heightIncrement B) r n T‖ ≤ a := by
  apply (ContinuousMap.norm_le_of_nonempty _).mpr
  intro t
  let u := T*n*(t:ℝ)
  let j := ⌊u⌋₊
  have hu : 0 ≤ u := mul_nonneg (mul_nonneg hT hn) t.2.1
  have huT : u ≤ T*n := mul_le_of_le_one_right (mul_nonneg hT hn) t.2.2
  have hj : j < ⌊T*n⌋₊+1 := Nat.lt_succ_of_le (Nat.floor_mono huT)
  have hj0 : (j:ℝ) ≤ u := Nat.floor_le hu
  have hj1 : u < (j:ℝ)+1 := Nat.lt_floor_add_one u
  have hdet := abs_convex_sub_le (q := u-j) (by linarith) (by linarith)
    (z := (0:ℝ)) (by simpa only [sub_zero] using hgap j hj.le)
    (by simpa only [sub_zero] using hgap (j+1) hj)
  have he : linearPolygon (heightIncrement F) (⌊T*n⌋₊+1) u-
      linearPolygon (heightIncrement B) (⌊T*n⌋₊+1) u =
      (1-(u-j))*(F j-B j)+(u-j)*(F (j+1)-B (j+1)) := by
    rw [linearPolygon_formula _ _ hu hj,linearPolygon_formula _ _ hu hj,
      realPartialSum_heightIncrement,realPartialSum_heightIncrement]
    simp only [heightIncrement,h0]
    dsimp only [j]
    ring
  rw [sub_zero,← he] at hdet
  simp only [ContinuousMap.sub_apply,Real.norm_eq_abs,scaledPolygon_apply]
  rw [← sub_div,abs_div,abs_of_pos hr]
  exact (div_le_iff₀ hr).2 hdet

lemma height_polygon_difference_small {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F B : ℕ → Ω → ℝ)
    (h0 : ∀ᵐ ω ∂μ, F 0 ω = B 0 ω) (r n : ℕ → ℝ)
    (hr : Tendsto r atTop atTop) (hn : Tendsto n atTop atTop) {T : ℝ} (hT : 0 ≤ T)
    (hgap : ∀ ε, 0 < ε → Tendsto (fun i => μ.real
      (HeightGapEvent F B (⌊T*n i⌋₊+1) (ε*r i))) atTop (𝓝 0)) :
    TendstoInMeasure μ (fun i ω => scaledPolygon (heightIncrement (fun h => F h ω)) (r i) (n i) T-
      scaledPolygon (heightIncrement (fun h => B h ω)) (r i) (n i) T) atTop 0 := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  simp only [Pi.zero_apply,sub_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ (hgap (ε/2) (by linarith))
  filter_upwards [hr.eventually (eventually_gt_atTop (0:ℝ)),
    hn.eventually (eventually_ge_atTop (0:ℝ))] with i hri hni
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae _)
  filter_upwards [h0] with ω h0 hbig
  by_contra hnot
  have hb (h : ℕ) (hh : h ≤ ⌊T*n i⌋₊+1) : |F h ω-B h ω| ≤ ε/2*r i :=
    le_of_not_gt (fun hbad => hnot ⟨h,hh,hbad⟩)
  have hh := height_polygon_difference_le (fun h => F h ω) (fun h => B h ω) h0 hri hni hT hb
  change ε ≤ ‖scaledPolygon (heightIncrement (fun h => F h ω)) (r i) (n i) T-
    scaledPolygon (heightIncrement (fun h => B h ω)) (r i) (n i) T‖ at hbig
  linarith

lemma commonBoundary_heightIncrement {d : ℕ} (ℓ : Vector d) (e : Direction d) (P : Path d × Path d) :
    heightIncrement (fun h => commonBoundaryGap ℓ e h P) =
      renewalRewardIncrement (fun k => commonIncrementProcess ℓ e k P)
        (fun k => commonWidthProcess ℓ k P) := rfl

theorem transverse_firstHit_path_error {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    TendstoInMeasure (independentConditionedPairLaw ν (realPosition (step e))) (fun i P =>
      scaledPolygon (heightIncrement (fun h => firstHitPairGap (realPosition (step e)) f h P))
        (r i) (fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)) T-
      scaledPolygon (renewalRewardIncrement (fun k => commonIncrementProcess (realPosition (step e)) f k P)
        (fun k => commonWidthProcess (realPosition (step e)) k P))
        (r i) (fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)) T) atTop 0 := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ (ne_of_gt hp)
  have hi := independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e)
    htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hn := (fluctuationScale_tendsto μ (commonIncrementProcess ℓ f 0)
    (measurable_commonIncrementProcess ℓ f 0) hi hne).comp hr.1
  apply height_polygon_difference_small μ (firstHitPairGap ℓ f) (commonBoundaryGap ℓ f) _ r _ hr.1 hn hT
  · exact fun ε hε => transverse_firstHit_uniform_error ν hue e f hef htrans r hr hT hε

  · let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ (ne_of_gt hp)
    have hac := conditionedLaw_absolutelyContinuous ν ℓ
    have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
      (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
    filter_upwards [h0] with P hP
    simp only [firstHitPairGap,recordIndexPosition,recordIndexTime_zero,hP.1,hP.2,sub_self,
      commonBoundaryGap,renewalCount_zero,realPartialSum_zero]

theorem transverse_firstHit_path_limit {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    letI : IsProbabilityMeasure (independentConditionedPairLaw ν (realPosition (step e))) :=
      independentConditionedPairLaw_probability ν _
        (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i P => scaledPolygon
        (heightIncrement (fun h => firstHitPairGap (realPosition (step e)) f h P)) (r i)
        (fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)) T)
        atTop id (fun _ => independentConditionedPairLaw ν (realPosition (step e))) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun f : C(unitInterval,ℝ) => I.restrict f) =
          gaussianPathFiniteLaw (T/commonMeanWidth ν (realPosition (step e))) I := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  obtain ⟨W,hW,hf⟩ := transverse_common_boundary_path_limit ν hue e f hef htrans r hr hT
  refine ⟨W,?_,hf⟩
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ id hW
  · exact transverse_firstHit_path_error ν hue e f hef htrans r hr hT
  · intro i
    exact (measurable_scaledPolygon _
      (measurable_heightIncrement (firstHitPairGap ℓ f) (measurable_firstHitPairGap ℓ f)) _ _ _).aemeasurable

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
