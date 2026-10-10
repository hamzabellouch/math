import Mathlib
import OAI.Probability.Ballisticity.Estimates.OrderedTimes

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma renewalCount_uniform (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) {c : ℝ} (hc : 0 < c)
    (hmean : Tendsto (fun k : ℕ => (renewalSum L k : ℝ)/k) atTop (𝓝 c))
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, 0 < a ∧ ∀ h : ℕ, (h : ℝ) ≤ T*a →
      |(renewalCount L h : ℝ)/a-(h : ℝ)/(c*a)| ≤ ε := by
  have hlinear := linear_error_uniform (fun k => (renewalSum L k : ℝ)) c hmean
    (T := T+1) (ε := ε*c/2) (by linarith) (by positivity)
  filter_upwards [hlinear,eventually_ge_atTop (max 1 (2/ε))] with a ha ha'
  have ha1 : 1 ≤ a := (le_max_left _ _).trans ha'
  have ha0 : 0 < a := by linarith
  refine ⟨ha0,fun h hh => ?_⟩
  let k := renewalCount L h
  have hk : (k : ℝ) ≤ T*a := (Nat.cast_le.2 (renewalCount_le L h)).trans hh
  have hk' : (k+1 : ℝ) ≤ (T+1)*a := by linarith
  have haK := ha k (by nlinarith : (k : ℝ) ≤ (T+1)*a)
  have haK' := ha (k+1) (by simpa using hk')
  have hlo : (renewalSum L k : ℝ) ≤ (h : ℝ) := by exact_mod_cast renewalCount_lower L h
  have hup : (h : ℝ) < (renewalSum L (k+1) : ℝ) := by exact_mod_cast renewalCount_upper L hL h
  have hbig : 2 ≤ ε*a := by simpa [mul_comm] using (div_le_iff₀ hε).1 ((le_max_right _ _).trans ha')
  have he : (k : ℝ)/a-(h : ℝ)/(c*a) = (c*k-h)/(c*a) := by field_simp
  rw [he,abs_div,abs_of_pos (mul_pos hc ha0),div_le_iff₀ (mul_pos hc ha0)]
  rcases abs_le.mp haK with ⟨haK1,haK2⟩
  rcases abs_le.mp haK' with ⟨haK1',haK2'⟩
  push_cast at haK1' haK2'
  apply abs_le.2
  constructor <;> nlinarith

lemma measurable_renewalCount {Ω : Type*} [MeasurableSpace Ω]
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k)) (h : ℕ) :
    Measurable (fun ω => renewalCount (fun k => L k ω) h) := by
  classical
  apply measurable_findGreatest
  intro k _
  exact measurableSet_le (Finset.measurable_sum _ (fun j _ => hL j)) measurable_const

lemma measure_tendsto_zero_of_ae_eventually_notMem {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : ℕ → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (he : ∀ᵐ ω ∂μ, ∀ᶠ i in atTop, ω ∉ A i) :
    Tendsto (fun i => μ (A i)) atTop (𝓝 0) := by
  let F := fun i => (A i).indicator (fun _ => (1 : ℝ))
  have hF : ∀ i, Measurable (F i) := fun i => measurable_const.indicator (hA i)
  have hc : TendstoInMeasure μ F atTop 0 := by
    apply tendstoInMeasure_of_tendsto_ae (fun i => (hF i).aestronglyMeasurable)
    filter_upwards [he] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with i hi
    simp [F,hi]
  have h := (tendstoInMeasure_iff_norm.1 hc) 1 zero_lt_one
  have hi : ∀ i, {ω | (1:ℝ) ≤ ‖F i ω-(0 : Ω → ℝ) ω‖} = A i := by
    intro i
    ext ω
    by_cases hω : ω ∈ A i <;> simp [F,hω]
  simpa only [hi] using h

lemma renewalCount_uniform_in_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (L : ℕ → Ω → ℕ)
    (hL : ∀ k, Measurable (L k)) (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω)
    {c : ℝ} (hc : 0 < c)
    (hmean : ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => (renewalSum (fun j => L j ω) k : ℝ)/k)
      atTop (𝓝 c)) (n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    Tendsto (fun i => μ {ω | ∃ h : ℕ, (h : ℝ) ≤ T*n i ∧
      ε < |(renewalCount (fun j => L j ω) h : ℝ)/n i-(h : ℝ)/(c*n i)|}) atTop (𝓝 0) := by
  apply measure_tendsto_zero_of_ae_eventually_notMem
  · intro i
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro h
    exact (MeasurableSet.const _).inter
      (measurableSet_lt measurable_const ((((measurable_of_countable (fun j : ℕ => (j : ℝ))).comp (measurable_renewalCount L hL h)).div_const _).sub
        measurable_const).abs)
  · filter_upwards [hpos,hmean] with ω hpos hmean
    have h := hn.eventually (renewalCount_uniform (fun j => L j ω) hpos hc hmean hT hε)
    filter_upwards [h] with i hi
    rintro ⟨h,hh,hbad⟩
    exact (not_lt_of_ge (hi.2 h hh)) hbad

noncomputable def commonWidthProcess {d : ℕ} (ℓ : Vector d)
    (n : ℕ) (P : Path d × Path d) : ℕ := commonWordWidth ℓ (commonWords ℓ P n)

lemma measurable_commonWidthProcess {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    Measurable (commonWidthProcess ℓ (d := d) n) :=
  (measurable_of_countable (commonWordWidth ℓ)).comp
    ((measurable_firstPairWord ℓ).comp ((measurable_renewPairSuffix ℓ).iterate n))

noncomputable def commonMeanWidth {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) : ℝ :=
  ∫ P, (commonWidthProcess ℓ 0 P : ℝ) ∂independentConditionedPairLaw ν ℓ

lemma commonMeanWidth_ge_one {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) : 1 ≤ commonMeanWidth ν ℓ := by
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hi := (independent_commonWordWidth_integrable ν ℓ htrans height hproj hstep).1
  have he := integral_mono_ae (integrable_const (1:ℝ)) hi (by
    filter_upwards [independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep] with P hP
    exact_mod_cast commonWordWidth_positive ℓ _ _ (hP 0))
  simpa [commonMeanWidth,commonWidthProcess,commonWords] using he

lemma commonWidth_strongLaw {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentConditionedPairLaw ν ℓ,
      Tendsto (fun n : ℕ => (renewalSum (fun k => commonWidthProcess ℓ k P) n : ℝ)/n)
        atTop (𝓝 (commonMeanWidth ν ℓ)) := by
  have hi := (independent_commonWordWidth_integrable ν ℓ htrans height hproj hstep).1
  have hind := (common_words_independent ν ℓ htrans height hproj hstep).comp
    (fun _ wv => (commonWordWidth ℓ wv : ℝ)) (fun _ => measurable_of_countable _)
  have hid (n : ℕ) := (common_words_identDistrib ν ℓ htrans height hproj hstep n).comp
    (measurable_of_countable (fun wv => (commonWordWidth ℓ wv : ℝ)))
  have h := strong_law_ae_real _ hi (fun i j hij => hind.indepFun hij) hid
  simpa only [renewalSum,Nat.cast_sum,commonWidthProcess,commonMeanWidth,commonWords,Function.comp_apply] using h

theorem common_boundary_count_uniform {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    Tendsto (fun i => independentConditionedPairLaw ν ℓ {P | ∃ h : ℕ, (h : ℝ) ≤ T*n i ∧
      ε < |(renewalCount (fun j => commonWidthProcess ℓ j P) h : ℝ)/n i-
        (h : ℝ)/(commonMeanWidth ν ℓ*n i)|}) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  apply renewalCount_uniform_in_probability _ _ (measurable_commonWidthProcess ℓ) _
    (zero_lt_one.trans_le (commonMeanWidth_ge_one ν ℓ htrans height hproj hstep))
    (commonWidth_strongLaw ν ℓ htrans height hproj hstep) n hn hT hε
  filter_upwards [independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep] with P hP n
  exact commonWordWidth_positive ℓ _ _ (hP n)

noncomputable def renewalRewardIncrement (x : ℕ → ℝ) (L : ℕ → ℕ) (h : ℕ) : ℝ :=
  realPartialSum x (renewalCount L (h+1))-realPartialSum x (renewalCount L h)

lemma renewalReward_sum (x : ℕ → ℝ) (L : ℕ → ℕ) (h : ℕ) :
    realPartialSum (renewalRewardIncrement x L) h = realPartialSum x (renewalCount L h) := by
  induction h with
  | zero => simp [realPartialSum,renewalCount_zero]
  | succ h ih => rw [realPartialSum_succ,ih,renewalRewardIncrement]; ring

lemma measurable_nat_select {Ω : Type*} [MeasurableSpace Ω] (F : ℕ → Ω → ℝ)
    (hF : ∀ k, Measurable (F k)) (k : Ω → ℕ) (hk : Measurable k) :
    Measurable (fun ω => F (k ω) ω) :=
  (measurable_from_prod_countable_left (f := fun p : Ω × ℕ => F p.2 p.1) (fun j => hF j)).comp (measurable_id.prodMk hk)

lemma measurable_renewalRewardIncrement {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (L : ℕ → Ω → ℕ) (hX : ∀ k, Measurable (X k))
    (hL : ∀ k, Measurable (L k)) (h : ℕ) :
    Measurable (fun ω => renewalRewardIncrement (fun k => X k ω) (fun k => L k ω) h) := by
  exact (measurable_nat_select _ (measurable_realPartialSum X hX) _
    (measurable_renewalCount L hL (h+1))).sub
      (measurable_nat_select _ (measurable_realPartialSum X hX) _ (measurable_renewalCount L hL h))

lemma abs_convex_sub_le {a b z q A : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : |a-z| ≤ A) (hb : |b-z| ≤ A) : |(1-q)*a+q*b-z| ≤ A := by
  have he : (1-q)*a+q*b-z = (1-q)*(a-z)+q*(b-z) := by ring
  rw [he]
  calc
    _ ≤ |(1-q)*(a-z)|+|q*(b-z)| := abs_add_le _ _
    _ = (1-q)*|a-z|+q*|b-z| := by rw [abs_mul,abs_mul,abs_of_nonneg hq,abs_of_nonneg (by linarith : 0 ≤ 1-q)]
    _ ≤ (1-q)*A+q*A := add_le_add (mul_le_mul_of_nonneg_left ha (by linarith))
      (mul_le_mul_of_nonneg_left hb hq)
    _ = A := by ring

lemma renewalRewardPolygon_close {Ω : Type*} (X : ℕ → Ω → ℝ) (L : ℕ → Ω → ℕ) (ω : Ω)
    {r n T c δ ε : ℝ} (hr : 0 < r) (hn : 1 ≤ n) (hT : 0 ≤ T)
    (hc : 1 ≤ c) (_hδ : 0 < δ) (hδn : 8 ≤ δ*n)
    (hclock : ∀ h : ℕ, (h : ℝ) ≤ (T+1)*n →
      |(renewalCount (fun k => L k ω) h : ℝ)/n-(h : ℝ)/(c*n)| ≤ δ/4)
    (hgrid : ω ∉ GridOscillation X ⌊(T+2)*n⌋₊ ⌊δ*n⌋₊ (ε*r)) :
    ‖scaledPolygon (renewalRewardIncrement (fun k => X k ω) (fun k => L k ω)) r n T-
      scaledPolygon (fun k => X k ω) r n (T/c)‖ ≤ 2*ε := by
  have hn0 : 0 < n := by linarith
  have hc0 : 0 < c := by linarith
  have hTn : 0 ≤ T*n := mul_nonneg hT hn0.le
  have hTc : 0 ≤ T/c := div_nonneg hT hc0.le
  apply (ContinuousMap.norm_le_of_nonempty _).mpr
  intro t
  let u := T*n*(t : ℝ)
  let v := (T/c)*n*(t : ℝ)
  let j := ⌊u⌋₊
  let k := ⌊v⌋₊
  let S := realPartialSum (fun l => X l ω)
  let C := renewalCount (fun l => L l ω)
  have hu : 0 ≤ u := mul_nonneg hTn t.2.1
  have huT : u ≤ T*n := mul_le_of_le_one_right hTn t.2.2
  have hv : 0 ≤ v := mul_nonneg (mul_nonneg hTc hn0.le) t.2.1
  have huv : v = u/c := by dsimp [u,v]; ring
  have hvu : v ≤ u := by rw [huv]; exact div_le_self hu hc
  have hj : (j : ℝ) ≤ u := Nat.floor_le hu
  have hj' : u < (j : ℝ)+1 := Nat.lt_floor_add_one u
  have hk : (k : ℝ) ≤ v := Nat.floor_le hv
  have hk' : v < (k : ℝ)+1 := Nat.lt_floor_add_one v
  have hjH : ∀ h : ℕ, (h : ℝ) ≤ (j : ℝ)+1 → (h : ℝ) ≤ (T+1)*n := by
    intro h hh
    nlinarith
  have hH : 1 ≤ ⌊δ*n⌋₊ := by apply Nat.le_floor; norm_num; linarith
  have hkN : k+1 ≤ ⌊(T+2)*n⌋₊ := by apply Nat.le_floor; push_cast; nlinarith
  have hb : ∀ h : ℕ, |(h : ℝ)-u| ≤ 1 → (h : ℝ) ≤ (j : ℝ)+1 →
      |S (C h)-S k| ≤ ε*r := by
    intro h hhu hhj
    have hhN : C h ≤ ⌊(T+2)*n⌋₊ := by
      apply (renewalCount_le _ _).trans
      apply Nat.le_floor
      have := hjH h hhj
      nlinarith
    have he := hclock h (hjH h hhj)
    have hcV : |(C h : ℝ)-v| ≤ δ*n/2 := by
      have hrw : ((C h : ℝ)/n-(h : ℝ)/(c*n))*n = (C h : ℝ)-(h : ℝ)/c := by
        dsimp [C]; field_simp
      have hb := mul_le_mul_of_nonneg_right he hn0.le
      change |(C h : ℝ)/n-(h : ℝ)/(c*n)| *n ≤ δ/4*n at hb
      have heq : |((C h : ℝ)/n-(h : ℝ)/(c*n))*n| =
          |(C h : ℝ)/n-(h : ℝ)/(c*n)| *n := by rw [abs_mul,abs_of_pos hn0]
      rw [← heq,hrw] at hb
      have he2 : |(h : ℝ)/c-v| ≤ 1 := by
        rw [huv,← sub_div,abs_div,abs_of_pos hc0]
        apply (div_le_iff₀ hc0).2
        simpa using hhu.trans hc
      have ht := abs_add_le ((C h : ℝ)-(h : ℝ)/c) ((h : ℝ)/c-v)
      have he3 : (C h : ℝ)-v = ((C h : ℝ)-(h : ℝ)/c)+((h : ℝ)/c-v) := by ring
      rw [← he3] at ht
      dsimp [C] at hb ⊢
      nlinarith
    have hnear := floor_scaled_close (Nat.cast_nonneg (C h)) hv (by linarith : 4 ≤ δ*n) hcV
    have hnear' := floor_scaled_close hv (Nat.cast_nonneg (C h)) (by linarith : 4 ≤ δ*n)
      (by simpa [abs_sub_comm] using hcV)
    simp only [Nat.floor_natCast] at hnear hnear'
    exact not_gridOscillation_bound X hgrid (by omega) hhN hnear' hnear
  have hb0 := hb j (by apply abs_le.2; constructor <;> linarith) (by linarith)
  have hb1 := hb (j+1) (by push_cast; apply abs_le.2; constructor <;> linarith) (by push_cast; rfl)
  have hpoly := abs_convex_sub_le (q := u-j) (by linarith) (by linarith) hb0 hb1
  have hpN : j < ⌊T*n⌋₊+1 := Nat.lt_succ_of_le (Nat.floor_mono huT)
  have hqN : k < ⌊(T/c)*n⌋₊+1 := Nat.lt_succ_of_le
    (Nat.floor_mono (mul_le_of_le_one_right (mul_nonneg hTc hn0.le) t.2.2))
  have hpolyEq : linearPolygon (renewalRewardIncrement (fun l => X l ω) (fun l => L l ω))
      (⌊T*n⌋₊+1) u = (1-(u-j))*S (C j)+(u-j)*S (C (j+1)) := by
    rw [linearPolygon_formula _ _ hu hpN,renewalReward_sum,renewalRewardIncrement]
    dsimp [j,S,C]
    ring
  rw [← hpolyEq] at hpoly
  have hx : |X k ω| ≤ ε*r := by
    rw [← realPartialSum_step (fun l => X l ω)]
    exact not_gridOscillation_bound X hgrid (by omega) hkN (by omega) (by omega)
  have hdet := linearPolygon_near_partialSum (x := fun l => X l ω) hv hqN hx
  change |linearPolygon (fun l => X l ω) (⌊(T/c)*n⌋₊+1) v-S k| ≤ ε*r at hdet
  have hfin := (abs_sub_le _ (S k) _).trans (add_le_add hpoly (by simpa [abs_sub_comm] using hdet))
  simp only [ContinuousMap.sub_apply,Real.norm_eq_abs,scaledPolygon_apply]
  rw [← sub_div,abs_div,abs_of_pos hr]
  apply (div_le_iff₀ hr).2
  convert hfin using 1; ring

lemma gaussian_renewal_path_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k))
    (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω) {c : ℝ} (hc : 1 ≤ c)
    (hmean : ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => (renewalSum (fun j => L j ω) k : ℝ)/k)
      atTop (𝓝 c)) (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) :
    TendstoInMeasure μ (fun i ω =>
      scaledPolygon (renewalRewardIncrement (fun k => X k ω) (fun k => L k ω))
        (r i) (fluctuationScale μ (X 0) (r i)) T-
      scaledPolygon (fun k => X k ω) (r i) (fluctuationScale μ (X 0) (r i)) (T/c)) atTop 0 := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  simp only [Pi.zero_apply,sub_zero]
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro β hβ
    obtain ⟨δ,hδ,hgrid⟩ := gaussian_grid_modulus μ X hX hind hident hsym hI hne r hr
      (by linarith : 0 ≤ T+2) (by linarith : 0 < ε/4) (by linarith : 0 < β/3)
    let A := fun i => {ω | ∃ h : ℕ, (h : ℝ) ≤ (T+1)*n i ∧
      δ/4 < |(renewalCount (fun j => L j ω) h : ℝ)/n i-(h : ℝ)/(c*n i)|}
    have hclock := renewalCount_uniform_in_probability μ L hL hpos
      (by linarith : 0 < c) hmean n hn (by linarith : 0 ≤ T+1) (by linarith : 0 < δ/4)
    have hclock' : Tendsto (fun i => μ.real (A i)) atTop (𝓝 0) := by
      convert (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).comp hclock using 1 <;>
        simp [Function.comp_def,Measure.real,A]
    have hb := (tendsto_order.mp hclock').2 (β/3) (by linarith)
    filter_upwards [hgrid,hb,hr.1.eventually (eventually_gt_atTop (0:ℝ)),
      hn.eventually (eventually_ge_atTop (1:ℝ)),
      (hn.const_mul_atTop hδ).eventually (eventually_ge_atTop (8:ℝ))]
      with i hg ha hri hni hdni
    let B := GridOscillation X ⌊(T+2)*n i⌋₊ ⌊δ*n i⌋₊ ((ε/4)*r i)
    have hs : {ω | ε ≤ ‖scaledPolygon (renewalRewardIncrement (fun k => X k ω)
        (fun k => L k ω)) (r i) (n i) T-
        scaledPolygon (fun k => X k ω) (r i) (n i) (T/c)‖} ⊆ A i ∪ B := by
      intro ω hω
      by_contra hnot
      have hnot : ω ∉ A i ∧ ω ∉ B := by simpa only [Set.mem_union,not_or] using hnot
      have hclockdet : ∀ h : ℕ, (h : ℝ) ≤ (T+1)*n i →
          |(renewalCount (fun k => L k ω) h : ℝ)/n i-(h : ℝ)/(c*n i)| ≤ δ/4 := by
        intro h hh
        exact le_of_not_gt (fun hh' => hnot.1 ⟨h,hh,hh'⟩)
      have hd := renewalRewardPolygon_close X L ω hri hni hT hc hδ hdni hclockdet hnot.2
      simp only [Set.mem_ofPred_eq] at hω
      linarith
    have hm := (measureReal_mono (μ := μ) hs (measure_ne_top _ _)).trans
      (measureReal_union_le (μ := μ) (A i) B)
    change μ.real B ≤ β/3 at hg
    exact hm.trans_lt (by linarith)

theorem gaussian_renewal_path_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k))
    (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω) {c : ℝ} (hc : 1 ≤ c)
    (hmean : ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => (renewalSum (fun j => L j ω) k : ℝ)/k)
      atTop (𝓝 c)) (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i ω => scaledPolygon
        (renewalRewardIncrement (fun k => X k ω) (fun k => L k ω))
        (r i) (fluctuationScale μ (X 0) (r i)) T) atTop id (fun _ => μ) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun f : C(unitInterval,ℝ) => I.restrict f) =
          gaussianPathFiniteLaw (T/c) I := by
  obtain ⟨W,hW,hf⟩ := gaussian_iid_path_limit μ X hX hind hident hsym hI hne r hr
    (div_nonneg hT (by linarith : 0 ≤ c))
  refine ⟨W,?_,hf⟩
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ id hW
  · exact gaussian_renewal_path_error μ X hX hind hident hsym hI hne L hL hpos hc hmean r hr hT
  · intro i
    exact (measurable_scaledPolygon _ (measurable_renewalRewardIncrement X L hX hL) _ _ _).aemeasurable

theorem transverse_common_boundary_path_limit {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    letI : IsProbabilityMeasure (independentConditionedPairLaw ν (realPosition (step e))) :=
      independentConditionedPairLaw_probability ν _
        (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i P => scaledPolygon
        (renewalRewardIncrement (fun k => commonIncrementProcess (realPosition (step e)) f k P)
          (fun k => commonWidthProcess (realPosition (step e)) k P)) (r i)
        (fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)) T)
        atTop id (fun _ => independentConditionedPairLaw ν (realPosition (step e))) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) =
          gaussianPathFiniteLaw (T/commonMeanWidth ν (realPosition (step e))) I := by
  let ℓ := realPosition (step e)
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  apply gaussian_renewal_path_limit _ _ (measurable_commonIncrementProcess ℓ f)
    (commonIncrements_independent ν ℓ htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) f)
    (commonIncrements_identDistrib ν ℓ htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) f)
    (independent_commonWordIncrement_symmetric ν ℓ htrans f)
    (independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e)
      htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
    (independent_commonWordIncrement_nonzero ν hue e f hef htrans)
    _ (measurable_commonWidthProcess ℓ) _
    (commonMeanWidth_ge_one ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e))
    (commonWidth_strongLaw ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e))
    r hr hT
  filter_upwards [independent_conditioned_all_firstPairWords ν ℓ htrans
    (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)] with P hP k
  exact commonWordWidth_positive ℓ _ _ (hP k)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
