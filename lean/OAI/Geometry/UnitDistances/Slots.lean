import OAI.Geometry.UnitDistances.Scale

namespace OAI

namespace PlanarUnitDistances.LevelGeometry
open MeasureTheory Set Real FiniteStates PlaceLevels LevelStates BudgetPlaces
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [NumberField K]

def allowance {S : Finset K} : Place K S → ℝ
  | .inl _ => log 2
  | .inr _ => 0
lemma allowance_nonneg {S : Finset K} (v : Place K S) : 0 ≤ allowance v := by
  cases v <;> simp [allowance,Real.log_nonneg]

lemma first_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (h : (state S z w u (v,s) x).1=(state S z w u (v,s) y).1) :
    av K v (z x-z y) ≤ exp (allowance v-s) := by
  cases v with
  | inl σ =>
    have hg : GridShift.gridLabel (exp (-s)) (σ (z x)) (u σ).1=
        GridShift.gridLabel (exp (-s)) (σ (z y)) (u σ).1 :=
      (label_eq_iff _ _ _).mp h
    have hb := GridShift.norm_le_of_same_grid (exp_pos (-s)) hg
    simpa only [av,WeightedAbsoluteValues.infiniteEntry_apply,map_sub,allowance,
      sub_eq_add_neg,map_add,map_neg,exp_add,exp_log (by norm_num : (0:ℝ)<2)] using hb
  | inr v =>
    have hb : WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2 (z x-z y) ≤ exp (-s) :=
      (label_eq_iff _ _ _).mp h
    simpa only [av,allowance,zero_sub] using hb

lemma second_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (h : (state S z w u (v,s) x).2=(state S z w u (v,s) y).2) :
    av K v (w x-w y) ≤ exp (allowance v+s) := by
  cases v with
  | inl σ =>
    have hg : GridShift.gridLabel (exp s) (σ (w x)) (u σ).2=
        GridShift.gridLabel (exp s) (σ (w y)) (u σ).2 :=
      (label_eq_iff _ _ _).mp h
    have hb := GridShift.norm_le_of_same_grid (exp_pos s) hg
    simpa only [av,WeightedAbsoluteValues.infiniteEntry_apply,map_sub,allowance,
      exp_add,exp_log (by norm_num : (0:ℝ)<2)] using hb
  | inr v =>
    have hb : WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2 (w x-w y) ≤ exp s :=
      (label_eq_iff _ _ _).mp h
    simpa only [av,allowance,zero_add] using hb

lemma first_log_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (hxy : z x≠z y) (h : (state S z w u (v,s) x).1=(state S z w u (v,s) y).1) :
    log (av K v (z x-z y)) ≤ allowance v-s := by
  have hb := log_le_log ((av K v).pos (sub_ne_zero.mpr hxy)) (first_bound S z w u v s x y h)
  simpa only [log_exp] using hb
lemma second_log_bound (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y : V)
    (hxy : w x≠w y) (h : (state S z w u (v,s) x).2=(state S z w u (v,s) y).2) :
    log (av K v (w x-w y)) ≤ allowance v+s := by
  have hb := log_le_log ((av K v).pos (sub_ne_zero.mpr hxy)) (second_bound S z w u v s x y h)
  simpa only [log_exp] using hb

lemma thickness_nonneg {S : Finset K} (v : Place K S) {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') : 0 ≤ alpha (av K v) d d'+allowance v := by
  cases v with
  | inl σ => exact alpha_add_log_two_nonneg _ hd hd' hdd
  | inr v =>
    simpa only [av,allowance,add_zero] using
      alpha_nonneg_nonarch (WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2)
        (WeightedAbsoluteValues.finiteEntry_nonarch K v.val.1 v.val.2) hd hd' hdd

omit [NumberField K] in
lemma opposite_log {d d' : K} (v : AbsoluteValue K ℝ)
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') :
    log (v (d⁻¹-d'⁻¹)) = max (threshold v d) (threshold v d')-alpha v d d' := by
  rw [inv_difference_abs v hd hd']
  rw [log_div ((v.pos (sub_ne_zero.mpr hdd)).ne') (mul_ne_zero ((v.pos hd).ne') ((v.pos hd').ne')),
    log_mul ((v.pos hd).ne') ((v.pos hd').ne')]
  unfold alpha threshold
  have hm := min_add_max (-log (v d)) (-log (v d'))
  linarith

theorem positive_flanks (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s : ℝ) (x y y' : V)
    (hu : (z x-z y)*(w x-w y)=1) (hu' : (z x-z y')*(w x-w y')=1)
    (hyy : z y≠z y') :
    let d := z x-z y
    let d' := z x-z y'
    let b := min (threshold (av K v) d) (threshold (av K v) d')
    let b' := max (threshold (av K v) d) (threshold (av K v) d')
    let T := alpha (av K v) d d'+allowance v
    ((s<threshold (av K v) d ∧ s<threshold (av K v) d' ∧
        (state S z w u (v,s) y).2=(state S z w u (v,s) y').2) → s∈Icc (b-T) b) ∧
    ((threshold (av K v) d ≤ s ∧ threshold (av K v) d' ≤ s ∧
        (state S z w u (v,s) y).1=(state S z w u (v,s) y').1) → s∈Icc b' (b'+T)) := by
  dsimp only
  have hd : z x-z y≠0 := left_ne_zero_of_mul_eq_one hu
  have hd' : z x-z y'≠0 := left_ne_zero_of_mul_eq_one hu'
  have hdd : z x-z y≠z x-z y' := by exact sub_right_injective.ne hyy
  have hw : w x-w y=(z x-z y)⁻¹ := eq_inv_of_mul_eq_one_right hu
  have hw' : w x-w y'=(z x-z y')⁻¹ := eq_inv_of_mul_eq_one_right hu'
  have he : w y-w y'=-((z x-z y)⁻¹-(z x-z y')⁻¹) := by rw [←hw,←hw']; ring
  have hz : z y-z y'=-((z x-z y)-(z x-z y')) := by ring
  have hwyy : w y≠w y' := by
    intro hh
    have hi : (z x-z y)⁻¹=(z x-z y')⁻¹ := by rw [←hw,←hw',hh]
    exact hdd (inv_injective hi)
  have hm : min (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')) ≤
      max (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')) := min_le_max
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    have hb := second_log_bound S z w u v s y y' hwyy h₃
    rw [he,AbsoluteValue.map_neg,opposite_log (av K v) hd hd' hdd] at hb
    refine ⟨by linarith,(le_min h₁.le h₂.le)⟩
  · rintro ⟨h₁,h₂,h₃⟩
    have hb := first_log_bound S z w u v s y y' hyy h₃
    rw [hz,AbsoluteValue.map_neg] at hb
    refine ⟨max_le h₁ h₂,?_⟩
    unfold alpha threshold at *
    linarith

end
end PlanarUnitDistances.LevelGeometry

namespace PlanarUnitDistances.BudgetIntervals
open Finset Set
open scoped BigOperators
noncomputable section

def overlap (a b l r : ℝ) : ℝ := max 0 (min b r-max a l)

lemma overlap_nonneg (a b l r : ℝ) : 0 ≤ overlap a b l r := le_max_left _ _

lemma overlap_le_length {a b l r : ℝ} (hab : a ≤ b) :
    overlap a b l r ≤ b-a := by
  apply max_le
  · linarith
  · linarith [min_le_left b r,le_max_left a l]

lemma overlap_pos_iff {a b l r : ℝ} :
    0 < overlap a b l r ↔ max a l < min b r := by
  simp only [overlap,lt_max_iff,lt_self_iff_false,false_or,sub_pos]

lemma disjoint_overlap_sum {a b c d l r : ℝ} (hbc : b ≤ c) :
    overlap a b l r+overlap c d l r ≤ max 0 (r-l) := by
  by_cases h₁ : 0 < min b r-max a l
  · rw [overlap,max_eq_right h₁.le]
    by_cases h₂ : 0 < min d r-max c l
    · rw [overlap,max_eq_right h₂.le]
      have hbr := min_le_right b r
      have hdl := min_le_right d r
      have hal := le_max_right a l
      have hcl := le_max_left c l
      have hbb := min_le_left b r
      have hr := le_max_right 0 (r-l)
      linarith
    · rw [overlap,max_eq_left (le_of_not_gt h₂),add_zero]
      linarith [min_le_right b r,le_max_right a l,le_max_right 0 (r-l)]
  · rw [overlap,max_eq_left (le_of_not_gt h₁),zero_add]
    apply max_le (le_max_left _ _)
    linarith [min_le_right d r,le_max_right c l,le_max_right 0 (r-l)]

theorem central_envelope {b b' T l r lam : ℝ} (hbb : b ≤ b')
    (hT : 0 ≤ T) (hlam : 0 < lam) (_hlam₁ : lam < 1) :
    max 0 ((1-lam)*2*T+2*lam*(overlap (b-T) b l r+overlap b' (b'+T) l r)-2*T) ≤
      lam*max 0 (r-l)*(if l < b ∧ b < r ∧ l < b' ∧ b' < r then 1 else 0) := by
  let a := overlap (b-T) b l r+overlap b' (b'+T) l r
  have h₁ : overlap (b-T) b l r ≤ T := by
    simpa using overlap_le_length (l := l) (r := r) (show b-T ≤ b by linarith)
  have h₂ : overlap b' (b'+T) l r ≤ T := by
    simpa using overlap_le_length (l := l) (r := r) (show b' ≤ b'+T by linarith)
  have hA : overlap (b-T) b l r+overlap b' (b'+T) l r ≤ 2*T := by linarith
  have hW := disjoint_overlap_sum (a := b-T) (d := b'+T) (l := l) (r := r) hbb
  have hn : 0 ≤ lam*max 0 (r-l) := mul_nonneg hlam.le (le_max_left _ _)
  split_ifs with hi
  · simp only [mul_one]
    apply max_le hn
    nlinarith
  · simp only [mul_zero]
    apply max_le le_rfl
    have ha : overlap (b-T) b l r+overlap b' (b'+T) l r ≤ T := by
      by_contra! he
      have hp₁ : 0 < overlap (b-T) b l r := by linarith
      have hp₂ : 0 < overlap b' (b'+T) l r := by linarith
      have hx := overlap_pos_iff.mp hp₁
      have hy := overlap_pos_iff.mp hp₂
      have hlb : l < b := lt_of_le_of_lt (le_max_right (b-T) l) (hx.trans_le (min_le_left b r))
      have hbr : b' < r := lt_of_le_of_lt (le_max_left b' l) (hy.trans_le (min_le_right (b'+T) r))
      exact hi ⟨hlb,hbb.trans_lt hbr,hlb.trans_le hbb,hbr⟩
    nlinarith

variable {E : Type*} [Fintype E]

def tail (μ : E → ℝ) (x : E → ℝ) (s : ℝ) : ℝ :=
  ∑ e, μ e * if s < x e then 1 else 0

def interiorMass (μ : E → ℝ) (x : E → ℝ) (l r : ℝ) : ℝ :=
  ∑ e, μ e * if l < x e ∧ x e < r then 1 else 0

lemma interiorMass_nonneg (μ : E → ℝ) (hμ : ∀ e, 0 ≤ μ e) (x : E → ℝ) (l r : ℝ) :
    0 ≤ interiorMass μ x l r := by
  apply sum_nonneg; intro e _; apply mul_nonneg (hμ e); split <;> norm_num

theorem interior_mass_le {μ : E → ℝ} (_hμ : ∀ e, 0 ≤ μ e) (x : E → ℝ)
    {l r δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ s ∈ Ioo l r, |tail μ x s-1/2| ≤ δ) :
    interiorMass μ x l r ≤ 2*δ := by
  classical
  let A := univ.filter (fun e => l < x e ∧ x e < r)
  by_cases ha : A.Nonempty
  · let a := (A.image x).min' (ha.image x)
    let b := (A.image x).max' (ha.image x)
    have haM : a ∈ A.image x := min'_mem _ _
    have hbM : b ∈ A.image x := max'_mem _ _
    obtain ⟨ea,hea,hea'⟩ := mem_image.mp haM
    obtain ⟨eb,heb,heb'⟩ := mem_image.mp hbM
    have hap : l < a ∧ a < r := by
      rw [← hea']; exact (mem_filter.mp hea).2
    have hbp : l < b ∧ b < r := by
      rw [← heb']; exact (mem_filter.mp heb).2
    have hab : a ≤ b := min'_le _ _ hbM
    let u := (l+a)/2
    have hu : u ∈ Ioo l r := by constructor <;> dsimp [u] <;> linarith
    have hum : u < a := by dsimp [u]; linarith
    have hm : interiorMass μ x l r = tail μ x u-tail μ x b := by
      rw [interiorMass,tail,tail,← sum_sub_distrib]
      apply sum_congr rfl
      intro e _
      by_cases he : l < x e ∧ x e < r
      · have heA : e ∈ A := mem_filter.mpr ⟨mem_univ _,he⟩
        have hae : a ≤ x e := min'_le _ _ (mem_image.mpr ⟨e,heA,rfl⟩)
        have heb : x e ≤ b := le_max' _ _ (mem_image.mpr ⟨e,heA,rfl⟩)
        simp [he,hum.trans_le hae,not_lt.mpr heb]
      · by_cases hux : u < x e
        · have hbx : b < x e := by
            by_contra! hle
            exact he ⟨hu.1.trans hux,hle.trans_lt hbp.2⟩
          simp [he,hux,hbx]
        · have hbx : ¬b < x e := by
            intro hh; exact hux (hum.trans_le hab |>.trans hh)
          simp [he,hux,hbx]
    rw [hm]
    have hc₁ := (abs_le.mp (hc u hu)).2
    have hc₂ := (abs_le.mp (hc b hbp)).1
    linarith
  · have hm : interiorMass μ x l r = 0 := by
      apply sum_eq_zero
      intro e _
      have he : ¬(l < x e ∧ x e < r) := by
        intro he
        exact ha ⟨e,mem_filter.mpr ⟨mem_univ _,he⟩⟩
      simp [he]
    rw [hm]; linarith

lemma overlap_eq_volume (a b l r : ℝ) :
    overlap a b l r = MeasureTheory.volume.real (Icc a b ∩ Icc l r) := by
  rw [Icc_inter_Icc,Real.volume_real_Icc]
  exact max_comm _ _

lemma sorted_interior {x y l r : ℝ} :
    (l < min x y ∧ min x y < r ∧ l < max x y ∧ max x y < r) ↔
    (l < x ∧ x < r) ∧ (l < y ∧ y < r) := by
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨⟨h₁.trans_le (min_le_left _ _),(le_max_left _ _).trans_lt h₄⟩,
      ⟨h₁.trans_le (min_le_right _ _),(le_max_right _ _).trans_lt h₄⟩⟩
  · rintro ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩
    exact ⟨lt_min h₁ h₃,(min_le_left _ _).trans_lt h₂,
      h₁.trans_le (le_max_left _ _),max_lt h₂ h₄⟩

lemma pair_interior_mass (μ : E → ℝ) (x : E → ℝ) (l r : ℝ) :
    (∑ e, ∑ e', μ e*μ e'*
      (if l < min (x e) (x e') ∧ min (x e) (x e') < r ∧
          l < max (x e) (x e') ∧ max (x e) (x e') < r then 1 else 0)) =
      (interiorMass μ x l r)^2 := by
  classical
  rw [pow_two,interiorMass,sum_mul_sum]
  apply sum_congr rfl; intro e _
  apply sum_congr rfl; intro e' _
  simp only [sorted_interior]
  by_cases h₁ : l < x e ∧ x e < r <;>
    by_cases h₂ : l < x e' ∧ x e' < r <;> simp [h₁,h₂]

theorem expected_central_envelope {μ : E → ℝ} (hμ : ∀ e, 0 ≤ μ e)
    (x : E → ℝ) (T : E → E → ℝ) (hT : ∀ e e', 0 ≤ T e e')
    {l r δ lam : ℝ} (hδ : 0 ≤ δ) (hlam : 0 < lam) (hlam₁ : lam < 1)
    (hc : ∀ s ∈ Ioo l r, |tail μ x s-1/2| ≤ δ) :
    (∑ e, ∑ e', μ e*μ e' *
      max 0 ((1-lam)*2*T e e'+2*lam*
        (overlap (min (x e) (x e')-T e e') (min (x e) (x e')) l r+
         overlap (max (x e) (x e')) (max (x e) (x e')+T e e') l r)-2*T e e')) ≤
      4*δ^2*lam*max 0 (r-l) := by
  classical
  have hw : 0 ≤ lam*max 0 (r-l) := mul_nonneg hlam.le (le_max_left _ _)
  calc
    _ ≤ ∑ e, ∑ e', μ e*μ e' * (lam*max 0 (r-l) *
        (if l < min (x e) (x e') ∧ min (x e) (x e') < r ∧
            l < max (x e) (x e') ∧ max (x e) (x e') < r then 1 else 0)) := by
      apply sum_le_sum; intro e _
      apply sum_le_sum; intro e' _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hμ e) (hμ e'))
      exact central_envelope min_le_max (hT e e') hlam hlam₁
    _ = (lam*max 0 (r-l))*(interiorMass μ x l r)^2 := by
      rw [← pair_interior_mass]
      simp only [mul_sum]
      apply sum_congr rfl; intro e _
      apply sum_congr rfl; intro e' _
      ring
    _ ≤ (lam*max 0 (r-l))*(2*δ)^2 := by
      apply mul_le_mul_of_nonneg_left _ hw
      exact (sq_le_sq₀ (interiorMass_nonneg μ hμ x l r) (by positivity)).mpr
        (interior_mass_le hμ x hδ hc)
    _ = _ := by ring

end
end PlanarUnitDistances.BudgetIntervals

namespace PlanarUnitDistances.PlaceScore
open MeasureTheory Set Real BudgetIntervals StrictCross
open scoped Classical
noncomputable section

def common (ε p : ℝ) : Prop := ε ≤ p ∧ p ≤ 1-ε

def reward (ε p ρ : ℝ) (one : Bool) : ℝ :=
  if common ε p then coefficient ρ
  else if (if one then p<ε else 1-ε<p) then 2 else 0

lemma coefficient_bounds (ρ : ℝ) : 0 ≤ coefficient ρ ∧ coefficient ρ ≤ 2 := by
  unfold coefficient
  split_ifs <;> norm_num
lemma reward_bounds (ε p ρ : ℝ) (one : Bool) : 0≤reward ε p ρ one ∧ reward ε p ρ one ≤ 2 := by
  unfold reward
  split_ifs <;> try norm_num
  exact coefficient_bounds ρ
lemma reward_true_zero {ε p ρ : ℝ} (hε : ε<1/2) (hp : 1-ε<p) : reward ε p ρ true=0 := by
  have hc : ¬common ε p := fun h => not_lt_of_ge h.2 hp
  have hn : ¬p<ε := by linarith
  simp [reward,hc,hn]
lemma reward_false_zero {ε p ρ : ℝ} (hε : ε<1/2) (hp : p<ε) : reward ε p ρ false=0 := by
  have hc : ¬common ε p := fun h => not_lt_of_ge h.1 hp
  have hn : ¬1-ε<p := by linarith
  simp [reward,hc,hn]

def ind (A : Set ℝ) (s : ℝ) : ℝ := A.indicator (fun _ => 1) s
lemma ind_nonneg (A : Set ℝ) (s : ℝ) : 0 ≤ ind A s := by
  unfold ind Set.indicator; split_ifs <;> norm_num
lemma ind_le_one (A : Set ℝ) (s : ℝ) : ind A s ≤ 1 := by
  unfold ind Set.indicator; split_ifs <;> norm_num
lemma ind_Icc_integrable (a b : ℝ) : Integrable (ind (Icc a b)) := by
  exact (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Icc a b)).integrable_indicator measurableSet_Icc
lemma ind_Icc_integral (a b : ℝ) : ∫s,ind (Icc a b) s = max 0 (b-a) := by
  change (∫s,(Icc a b).indicator (fun _ => (1:ℝ)) s)=_
  rw [integral_indicator_const (1:ℝ) measurableSet_Icc]
  simp only [smul_eq_mul,mul_one,Real.volume_real_Icc,max_comm]
lemma ind_inter_integrable (a b l r : ℝ) : Integrable (ind (Icc a b ∩ Icc l r)) := by
  rw [Icc_inter_Icc]
  exact ind_Icc_integrable _ _
lemma ind_inter_integral (a b l r : ℝ) :
    ∫s,ind (Icc a b ∩ Icc l r) s=overlap a b l r := by
  rw [Icc_inter_Icc,ind_Icc_integral]
  rfl

def cap (ε : ℝ) (g ρ : ℝ → ℝ) (b b' T s : ℝ) : ℝ :=
  reward ε (g s) (ρ s) true*ind (Icc (b-T) b ∩ Iio b) s+
  reward ε (g s) (ρ s) false*ind (Icc b' (b'+T)) s

lemma low_cap {ε b b' T : ℝ} {g ρ : ℝ → ℝ}
    (hε : ε<1/2) (hg : Antitone g) (hbb : b ≤ b') (h : g b<ε) (s : ℝ) :
    cap ε g ρ b b' T s ≤ 2*ind (Icc (b-T) b) s := by
  have h₁ : reward ε (g s) (ρ s) true*ind (Icc (b-T) b ∩ Iio b) s ≤
      2*ind (Icc (b-T) b) s := by
    unfold ind Set.indicator
    split_ifs with hi hi'
    · simpa using (reward_bounds ε (g s) (ρ s) true).2
    · exact False.elim (hi' hi.1)
    · norm_num
    · norm_num
  have h₂ : reward ε (g s) (ρ s) false*ind (Icc b' (b'+T)) s=0 := by
    by_cases hs : s∈Icc b' (b'+T)
    · rw [reward_false_zero hε ((hg (hbb.trans hs.1)).trans_lt h),zero_mul]
    · simp [ind,hs]
  unfold cap
  rw [h₂,add_zero]
  exact h₁

lemma high_cap {ε b b' T : ℝ} {g ρ : ℝ → ℝ}
    (hε : ε<1/2) (hg : Antitone g) (hbb : b ≤ b') (h : 1-ε<g b') (s : ℝ) :
    cap ε g ρ b b' T s ≤ 2*ind (Icc b' (b'+T)) s := by
  have h₁ : reward ε (g s) (ρ s) true*ind (Icc (b-T) b ∩ Iio b) s=0 := by
    by_cases hs : s∈Icc (b-T) b ∩ Iio b
    · rw [reward_true_zero hε (h.trans_le (hg (hs.1.2.trans hbb))),zero_mul]
    · simp [ind,hs]
  have h₂ := mul_le_mul_of_nonneg_right (reward_bounds ε (g s) (ρ s) false).2
    (ind_nonneg (Icc b' (b'+T)) s)
  unfold cap
  rw [h₁,zero_add]
  exact h₂

lemma middle_reward {ε p ρ : ℝ} (one : Bool)
    (hn : ¬(if one then p<ε else 1-ε<p)) :
    reward ε p ρ one ≤ 1-1/20000+2*(1/20000:ℝ)*(if common ε p ∧ |ρ-1/2| ≤ 1/100 then 1 else 0) := by
  by_cases hc : common ε p <;> by_cases hz : |ρ-1/2| ≤ (1/100:ℝ) <;>
    simp only [reward,coefficient,hc,hz,hn,and_self,ite_true,ite_false,and_true] <;> norm_num

lemma middle_cap {ε b b' T l r : ℝ} {g ρ : ℝ → ℝ}
    (hg : Antitone g) (hlow : ε ≤ g b) (hhigh : g b' ≤ 1-ε)
    (hJ : ∀s,common ε (g s) ∧ |ρ s-1/2| ≤ 1/100 ↔ s∈Ico l r) (s : ℝ) :
    cap ε g ρ b b' T s ≤
      (1-1/20000:ℝ)*(ind (Icc (b-T) b) s+ind (Icc b' (b'+T)) s)+
      2*(1/20000:ℝ)*(ind (Icc (b-T) b ∩ Icc l r) s+ind (Icc b' (b'+T) ∩ Icc l r) s) := by
  have hlo : reward ε (g s) (ρ s) true*ind (Icc (b-T) b ∩ Iio b) s ≤
      (1-1/20000:ℝ)*ind (Icc (b-T) b) s+2*(1/20000:ℝ)*ind (Icc (b-T) b ∩ Icc l r) s := by
    by_cases hs : s∈Icc (b-T) b ∩ Iio b
    · have hn : ¬g s<ε := not_lt.mpr (hlow.trans (hg hs.1.2))
      have hr := middle_reward true (by simpa using hn : ¬(if true then g s<ε else 1-ε<g s)) (ρ:=ρ s)
      have hI : (if common ε (g s) ∧ |ρ s-1/2| ≤ 1/100 then (1:ℝ) else 0) ≤ ind (Icc l r) s := by
        split_ifs with hc
        · have hjs : s∈Icc l r := ⟨((hJ s).mp hc).1,((hJ s).mp hc).2.le⟩
          simp [ind,hjs]
        · exact ind_nonneg _ _
      simp only [ind,Set.indicator_of_mem hs,Set.indicator_of_mem hs.1,mul_one]
      have he : (Icc (b-T) b ∩ Icc l r).indicator (fun _ => (1:ℝ)) s=ind (Icc l r) s := by
        simp [ind,Set.indicator,hs.1]
      rw [he]
      linarith
    · have hn : ind (Icc (b-T) b ∩ Iio b) s=0 := by simp [ind,hs]
      rw [hn,mul_zero]
      exact add_nonneg (mul_nonneg (by norm_num) (ind_nonneg _ _)) (mul_nonneg (by norm_num) (ind_nonneg _ _))
  have hhi : reward ε (g s) (ρ s) false*ind (Icc b' (b'+T)) s ≤
      (1-1/20000:ℝ)*ind (Icc b' (b'+T)) s+2*(1/20000:ℝ)*ind (Icc b' (b'+T) ∩ Icc l r) s := by
    by_cases hs : s∈Icc b' (b'+T)
    · have hn : ¬1-ε<g s := not_lt.mpr ((hg hs.1).trans hhigh)
      have hr := middle_reward false (by simpa using hn : ¬(if false then g s<ε else 1-ε<g s)) (ρ:=ρ s)
      have hI : (if common ε (g s) ∧ |ρ s-1/2| ≤ 1/100 then (1:ℝ) else 0) ≤ ind (Icc l r) s := by
        split_ifs with hc
        · have hjs : s∈Icc l r := ⟨((hJ s).mp hc).1,((hJ s).mp hc).2.le⟩
          simp [ind,hjs]
        · exact ind_nonneg _ _
      simp only [ind,Set.indicator_of_mem hs,mul_one]
      have he : (Icc b' (b'+T) ∩ Icc l r).indicator (fun _ => (1:ℝ)) s=ind (Icc l r) s := by
        simp [ind,Set.indicator,hs]
      rw [he]
      linarith
    · have hn : ind (Icc b' (b'+T)) s=0 := by simp [ind,hs]
      rw [hn,mul_zero,mul_zero,zero_add]
      exact mul_nonneg (by norm_num) (ind_nonneg _ _)
  unfold cap
  linarith

theorem positive_budget {ε b b' T l r : ℝ} {g ρ f : ℝ → ℝ}
    (hε : ε<1/2) (hg : Antitone g) (hbb : b ≤ b') (hT : 0 ≤ T)
    (hJ : ∀s,common ε (g s) ∧ |ρ s-1/2| ≤ 1/100 ↔ s∈Ico l r)
    (hf : Integrable f) (hcap : ∀s,f s ≤ cap ε g ρ b b' T s) :
    (∫s,f s) ≤ 2*T+(1/20000:ℝ)*max 0 (r-l)*
      (if l<b ∧ b<r ∧ l<b' ∧ b'<r then 1 else 0) := by
  have hex : 0 ≤ (1/20000:ℝ)*max 0 (r-l)*(if l<b ∧ b<r ∧ l<b' ∧ b'<r then 1 else 0) := by
    split_ifs <;> positivity
  by_cases hlo : g b<ε
  · have hi := integral_mono hf ((ind_Icc_integrable (b-T) b).const_mul 2)
      (fun s => (hcap s).trans (low_cap hε hg hbb hlo s))
    rw [integral_const_mul,ind_Icc_integral] at hi
    have he : max 0 (b-(b-T))=T := by rw [show b-(b-T)=T by ring,max_eq_right hT]
    rw [he] at hi
    linarith
  by_cases hhi : 1-ε<g b'
  · have hi := integral_mono hf ((ind_Icc_integrable b' (b'+T)).const_mul 2)
      (fun s => (hcap s).trans (high_cap hε hg hbb hhi s))
    rw [integral_const_mul,ind_Icc_integral] at hi
    have he : max 0 (b'+T-b')=T := by rw [show b'+T-b'=T by ring,max_eq_right hT]
    rw [he] at hi
    linarith
  have h₁ := ((ind_Icc_integrable (b-T) b).add (ind_Icc_integrable b' (b'+T))).const_mul (1-1/20000:ℝ)
  have h₂ := ((ind_inter_integrable (b-T) b l r).add (ind_inter_integrable b' (b'+T) l r)).const_mul (2*(1/20000:ℝ))
  change Integrable (fun s => (1-1/20000:ℝ)*(ind (Icc (b-T) b) s+ind (Icc b' (b'+T)) s)) at h₁
  change Integrable (fun s => 2*(1/20000:ℝ)*(ind (Icc (b-T) b ∩ Icc l r) s+ind (Icc b' (b'+T) ∩ Icc l r) s)) at h₂
  have hi := integral_mono hf (h₁.add h₂)
    (fun s => (hcap s).trans (middle_cap hg (le_of_not_gt hlo) (le_of_not_gt hhi) hJ s))
  change (∫s,f s) ≤ ∫s,((1-1/20000:ℝ)*(ind (Icc (b-T) b) s+ind (Icc b' (b'+T)) s)+
      2*(1/20000:ℝ)*(ind (Icc (b-T) b ∩ Icc l r) s+ind (Icc b' (b'+T) ∩ Icc l r) s)) at hi
  rw [integral_add h₁ h₂,integral_const_mul,integral_const_mul,
    integral_add (ind_Icc_integrable (b-T) b) (ind_Icc_integrable b' (b'+T)),
    integral_add (ind_inter_integrable (b-T) b l r) (ind_inter_integrable b' (b'+T) l r),
    ind_Icc_integral,ind_Icc_integral,ind_inter_integral,ind_inter_integral] at hi
  have he : max 0 (b-(b-T))=T := by rw [show b-(b-T)=T by ring,max_eq_right hT]
  have he' : max 0 (b'+T-b')=T := by rw [show b'+T-b'=T by ring,max_eq_right hT]
  rw [he,he'] at hi
  have hc := central_envelope (l:=l) (r:=r) (lam:=(1/20000:ℝ)) hbb hT (by norm_num) (by norm_num)
  have hm := le_max_right 0 ((1-(1/20000:ℝ))*2*T+2*(1/20000:ℝ)*
    (overlap (b-T) b l r+overlap b' (b'+T) l r)-2*T)
  linarith
end
end PlanarUnitDistances.PlaceScore

namespace PlanarUnitDistances.LevelScores
open FiniteLaw StrictCross CrossStructure RareScore PlaceScore
open scoped Classical
noncomputable section
variable {A B : Type*}

def minority (p : ℝ) : Bool := decide (p<1/2)

def positive (ε p ρ : ℝ) (good : Prop) (l base y z : A×B) (b c : Bool) : ℝ :=
  if common ε p then coefficient ρ*RareScore.ind (b=c ∧ nonshared b y z)
  else if good then 2*RareScore.ind (exceptional (minority p) l base ∧
    b=minority p ∧ c=minority p ∧ nonshared (minority p) y z) else 0

def score (ε p ρ : ℝ) (good : Prop) (l base y z : A×B) (b c : Bool) : ℝ :=
  positive ε p ρ good l base y z b c-RareScore.ind (b≠c)

lemma positive_bounds (ε p ρ : ℝ) (good : Prop) (l base y z : A×B) (b c : Bool) :
    0 ≤ positive ε p ρ good l base y z b c ∧ positive ε p ρ good l base y z b c ≤ 2 := by
  unfold positive
  split_ifs
  · exact ⟨mul_nonneg (coefficient_bounds ρ).1 (RareScore.ind_nonneg _),
      (mul_le_mul_of_nonneg_left (RareScore.ind_le_one _) (coefficient_bounds ρ).1).trans
        (by simpa using (coefficient_bounds ρ).2)⟩
  · constructor
    · exact mul_nonneg (by norm_num) (RareScore.ind_nonneg _)
    · nlinarith [RareScore.ind_le_one (exceptional (minority p) l base ∧
        b=minority p ∧ c=minority p ∧ nonshared (minority p) y z)]
  · norm_num
lemma score_bounds (ε p ρ : ℝ) (good : Prop) (l base y z : A×B) (b c : Bool) :
    -1 ≤ score ε p ρ good l base y z b c ∧ score ε p ρ good l base y z b c ≤ 2 := by
  have h := positive_bounds ε p ρ good l base y z b c
  have hn := RareScore.ind_nonneg (b≠c)
  have hm := RareScore.ind_le_one (b≠c)
  unfold score
  constructor <;> linarith

lemma minority_reward {ε p ρ : ℝ} (hε : ε<1/2) (h : ¬common ε p) :
    reward ε p ρ (minority p)=2 := by
  unfold reward
  rw [ite_eq_right h]
  unfold minority
  by_cases hp : p<1/2
  · have hl : p<ε := by unfold common at h; push Not at h; by_contra! hh; have := h hh; linarith
    rw [show decide (p<1/2)=true from decide_eq_true hp]
    simp [hl]
  · have hr : 1-ε<p := by unfold common at h; push Not at h; apply h; linarith
    rw [show decide (p<1/2)=false from decide_eq_false hp]
    simp [hr]

lemma positive_le_rewards {ε p ρ : ℝ} (hε : ε<1/2) (good : Prop)
    (l base y z : A×B) (b c : Bool) :
    positive ε p ρ good l base y z b c ≤
      reward ε p ρ true*RareScore.ind (b=true ∧ c=true ∧ nonshared true y z)+
      reward ε p ρ false*RareScore.ind (b=false ∧ c=false ∧ nonshared false y z) := by
  have hn₀ := (reward_bounds ε p ρ false).1
  have hn₁ := (reward_bounds ε p ρ true).1
  by_cases hc : common ε p
  · unfold positive reward
    rw [ite_eq_left hc,ite_eq_left hc,ite_eq_left hc]
    cases b <;> cases c <;> simp only [RareScore.ind,nonshared,Bool.false_eq_true,
      Bool.true_eq_false,↓reduceIte,true_and,false_and,and_false]
    all_goals try split_ifs
    all_goals nlinarith [(coefficient_bounds ρ).1]
  · have hm := minority_reward (ρ:=ρ) hε hc
    unfold positive
    rw [ite_eq_right hc]
    by_cases hg : good
    · rw [ite_eq_left hg]
      unfold RareScore.ind
      by_cases hp : exceptional (minority p) l base ∧
          b=minority p ∧ c=minority p ∧ nonshared (minority p) y z
      · rw [ite_eq_left hp]
        obtain ⟨_,hb,hc',hns⟩ := hp
        rw [hb,hc']
        cases hr : minority p
        · rw [hr] at hm hns
          simp [hm,hns]
        · rw [hr] at hm hns
          simp [hm,hns]
      · rw [ite_eq_right hp]
        split_ifs <;> nlinarith
    · rw [ite_eq_right hg]
      exact add_nonneg (mul_nonneg hn₁ (RareScore.ind_nonneg _))
        (mul_nonneg hn₀ (RareScore.ind_nonneg _))

lemma rare_score {ε p ρ : ℝ} (good : Prop) (l base y z : A×B) (b c : Bool)
    (hc : ¬common ε p) (hg : good) :
    score ε p ρ good l base y z b c=RareScore.slot (minority p) l base y z b c := by
  simp [score,positive,RareScore.slot,hc,hg]
lemma damaged_score {ε p ρ : ℝ} (good : Prop) (l base y z : A×B) (b c : Bool)
    (hc : ¬common ε p) (hg : ¬good) :
    score ε p ρ good l base y z b c= -RareScore.ind (b≠c) := by
  simp [score,positive,hc,hg]

end
end PlanarUnitDistances.LevelScores

namespace PlanarUnitDistances.LevelSlotGeometry
open MeasureTheory Set Real FiniteStates PlaceLevels LevelStates LevelGeometry BudgetPlaces LevelScores
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [NumberField K]

theorem positive_le_cap (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (s ε : ℝ)
    (g ρ : ℝ → ℝ) (hε : ε<1/2) (good : Prop) (l : (V → Bool)×(V → Bool)) (x y y' : V)
    (hu : (z x-z y)*(w x-w y)=1) (hu' : (z x-z y')*(w x-w y')=1)
    (hyy : z y≠z y') :
    positive ε (g s) (ρ s) good l (state S z w u (v,s) x)
      (state S z w u (v,s) y) (state S z w u (v,s) y')
      (decide (s<threshold (av K v) (z x-z y))) (decide (s<threshold (av K v) (z x-z y'))) ≤
    PlaceScore.cap ε g ρ
      (min (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')))
      (max (threshold (av K v) (z x-z y)) (threshold (av K v) (z x-z y')))
      (alpha (av K v) (z x-z y) (z x-z y')+allowance v) s := by
  have hp := positive_le_rewards hε good l (state S z w u (v,s) x)
    (state S z w u (v,s) y) (state S z w u (v,s) y')
    (decide (s<threshold (av K v) (z x-z y))) (decide (s<threshold (av K v) (z x-z y')))
    (p:=g s) (ρ:=ρ s)
  have hf := positive_flanks S z w u v s x y y' hu hu' hyy
  dsimp only at hf
  refine hp.trans (add_le_add (mul_le_mul_of_nonneg_left ?_ (PlaceScore.reward_bounds ε (g s) (ρ s) true).1)
    (mul_le_mul_of_nonneg_left ?_ (PlaceScore.reward_bounds ε (g s) (ρ s) false).1))
  · unfold RareScore.ind
    split_ifs with h
    · have he₁ : s<threshold (av K v) (z x-z y) := of_decide_eq_true h.1
      have he₂ : s<threshold (av K v) (z x-z y') := of_decide_eq_true h.2.1
      have hi := hf.1 ⟨he₁,he₂,h.2.2⟩
      have hi' := lt_min he₁ he₂
      change 1 ≤ PlaceScore.ind _ s
      rw [PlaceScore.ind,Set.indicator_of_mem (show s∈Icc _ _ ∩ Iio _ from ⟨hi,hi'⟩)]
    · exact PlaceScore.ind_nonneg _ _
  · unfold RareScore.ind
    split_ifs with h
    · have he₁ : threshold (av K v) (z x-z y) ≤ s := le_of_not_gt (of_decide_eq_false h.1)
      have he₂ : threshold (av K v) (z x-z y') ≤ s := le_of_not_gt (of_decide_eq_false h.2.1)
      have hi := hf.2 ⟨he₁,he₂,h.2.2⟩
      simp only [PlaceScore.ind,Set.indicator_of_mem hi,le_refl]
    · exact PlaceScore.ind_nonneg _ _
end
end PlanarUnitDistances.LevelSlotGeometry

namespace PlanarUnitDistances.RareRows
open FiniteLaw FiniteStarCoupling RareScore LevelScores
open scoped Classical
noncomputable section
variable {P Q A B : Type*} [Fintype P] [Fintype Q]

def frequency (π : Law (P×Q)) (bit : P → Q → Bool) : ℝ := event π (fun pq => bit pq.1 pq.2=true)
def scoreP (ε f : ℝ) (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) : ℝ :=
  avg (left π) (fun p => avg (pair (row π p) (row π p)) (fun qq =>
    LevelScores.score ε f (event (row π p) (fun q => bit p q=true)) good l (x p)
      (y qq.1) (y qq.2) (bit p qq.1) (bit p qq.2)))
def scoreQ (ε f : ℝ) (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) : ℝ :=
  avg (right π) (fun q => avg (pair (col π q) (col π q)) (fun pp =>
    LevelScores.score ε f (event (col π q) (fun p => bit p q=true)) good l (y q)
      (x pp.1) (x pp.2) (bit pp.1 q) (bit pp.2 q)))

lemma common_slot {X : Type*} {ε p ρ : ℝ} (hc : PlaceScore.common ε p)
    (good : Prop) (l base : A×B) (s : X → A×B) (b : X → Bool) (i j : X) :
    LevelScores.score ε p ρ good l base (s i) (s j) (b i) (b j)=StarScore.slot ρ b s i j := by
  simp only [LevelScores.score,LevelScores.positive,hc,↓reduceIte,StarScore.slot]
  cases b i <;> cases b j <;> simp [nonshared,ind,mul_ite]

lemma common_P {ε f : ℝ} (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) (hc : PlaceScore.common ε f) :
    scoreP ε f π bit x y good l=DP π bit y := by
  unfold scoreP DP StarScore.score StarScore.frequency
  apply avg_congr
  intro p
  apply avg_congr
  intro qq
  exact common_slot hc good l (x p) y (bit p) qq.1 qq.2
lemma common_Q {ε f : ℝ} (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) (hc : PlaceScore.common ε f) :
    scoreQ ε f π bit x y good l=DQ π bit x := by
  unfold scoreQ DQ StarScore.score StarScore.frequency
  apply avg_congr
  intro q
  apply avg_congr
  intro pp
  exact common_slot hc good l (y q) x (fun p => bit p q) pp.1 pp.2

lemma consistency_symm (b : Bool) (x y : A×B) : CrossStructure.Consistent b x y ↔ CrossStructure.Consistent b y x := by
  cases b <;> simp [CrossStructure.Consistent,eq_comm]

theorem rare_P {ε f : ℝ} (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) (hc : ¬PlaceScore.common ε f) (hg : good) :
    let r := minority f
    2*event (left π) (fun p => exceptional r l (x p))-
      2*event (right π) (fun q => exceptional r l (y q))-
      4*event π (fun pq => exceptional r l (x pq.1) ∧ exceptional r l (y pq.2))-
      6*event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))≤
      scoreP ε f π bit x y good l := by
  dsimp only
  let r := minority f
  have h := avg_mono (left π) (fun p => star_lower (row π p) r l (x p) y (bit p))
  simp only [avg_sub,avg_smul,row_event] at h
  have hleft : avg (left π) (fun p => ind (exceptional r l (x p)))=event (left π) (fun p => exceptional r l (x p)) := rfl
  rw [hleft] at h
  have hright : event π (fun pq => exceptional r l (y pq.2))=event (right π) (fun q => exceptional r l (y q)) := by
    simp only [right,event,push_avg]
  rw [hright] at h
  have hs : scoreP ε f π bit x y good l=avg (left π) (fun p => avg (pair (row π p) (row π p))
      (fun qq => slot r l (x p) (y qq.1) (y qq.2) (bit p qq.1) (bit p qq.2))) := by
    unfold scoreP
    apply avg_congr
    intro p
    apply avg_congr
    intro qq
    exact rare_score good l (x p) (y qq.1) (y qq.2) (bit p qq.1) (bit p qq.2) hc hg
  rw [hs]
  linarith

theorem rare_Q {ε f : ℝ} (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) (hc : ¬PlaceScore.common ε f) (hg : good) :
    let r := minority f
    2*event (right π) (fun q => exceptional r l (y q))-
      2*event (left π) (fun p => exceptional r l (x p))-
      4*event π (fun pq => exceptional r l (x pq.1) ∧ exceptional r l (y pq.2))-
      6*event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))≤
      scoreQ ε f π bit x y good l := by
  dsimp only
  let r := minority f
  have h := avg_mono (right π) (fun q => star_lower (col π q) r l (y q) x (fun p => bit p q))
  simp only [avg_sub,avg_smul,col_event] at h
  have hright : avg (right π) (fun q => ind (exceptional r l (y q)))=event (right π) (fun q => exceptional r l (y q)) := rfl
  rw [hright] at h
  have hleft : event π (fun pq => exceptional r l (x pq.1))=event (left π) (fun p => exceptional r l (x p)) := by
    simp only [left,event,push_avg]
  rw [hleft] at h
  have hj : event π (fun pq => exceptional r l (y pq.2) ∧ exceptional r l (x pq.1))=
      event π (fun pq => exceptional r l (x pq.1) ∧ exceptional r l (y pq.2)) := by simp only [and_comm]
  rw [hj] at h
  have hi : event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (y pq.2) (x pq.1))=
      event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2)) := by
    congr 1
    funext pq
    exact propext (not_congr (consistency_symm (bit pq.1 pq.2) (y pq.2) (x pq.1)))
  rw [hi] at h
  have hs : scoreQ ε f π bit x y good l=avg (right π) (fun q => avg (pair (col π q) (col π q))
      (fun pp => slot r l (y q) (x pp.1) (x pp.2) (bit pp.1 q) (bit pp.2 q))) := by
    unfold scoreQ
    apply avg_congr
    intro q
    apply avg_congr
    intro pp
    exact rare_score good l (y q) (x pp.1) (x pp.2) (bit pp.1 q) (bit pp.2 q) hc hg
  rw [hs]
  linarith

lemma scoreP_lower (ε f : ℝ) (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) : -1≤ scoreP ε f π bit x y good l := by
  apply const_le_avg
  intro p
  apply const_le_avg
  intro qq
  exact (LevelScores.score_bounds _ _ _ _ _ _ _ _ _ _).1
lemma scoreQ_lower (ε f : ℝ) (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) : -1≤ scoreQ ε f π bit x y good l := by
  apply const_le_avg
  intro q
  apply const_le_avg
  intro pp
  exact (LevelScores.score_bounds _ _ _ _ _ _ _ _ _ _).1
end
end PlanarUnitDistances.RareRows

namespace PlanarUnitDistances.TemplateCoupling
open FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]
lemma slice_avg_original (π : Law (P×Q)) (a : Q → Law Θ) (f : P×Q → ℝ) :
    avg (templates π a) (fun θ => avg (slice π a θ) f)=avg π f := by
  rw [slice_avg]
  simp only [avg_const]
lemma slice_event_original (π : Law (P×Q)) (a : Q → Law Θ) (f : P×Q → Prop) :
    avg (templates π a) (fun θ => event (slice π a θ) f)=event π f :=
  slice_avg_original π a _
lemma slice_left_event (π : Law (P×Q)) (a : Q → Law Θ) (f : P → Prop) :
    avg (templates π a) (fun θ => event (left (slice π a θ)) f)=event (left π) f := by
  simp only [left,event,push_avg]
  exact slice_avg_original π a _
lemma slice_right_event (π : Law (P×Q)) (a : Q → Law Θ) (f : Q → Prop) :
    avg (templates π a) (fun θ => event (right (slice π a θ)) f)=event (right π) f := by
  simp only [right,event,push_avg]
  exact slice_avg_original π a _
end
end PlanarUnitDistances.TemplateCoupling

namespace PlanarUnitDistances.RareRows
open FiniteLaw FiniteStarCoupling TemplateCoupling LevelScores RareScore
open scoped Classical
noncomputable section
variable {P Q Θ A B : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

def scoreT (ε f : ℝ) (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) (good : Prop) (l : A×B) : ℝ :=
  avg (templates π a) (fun θ => scoreP ε f (slice π a θ) bit x y good l)

theorem rare_T {ε f : ℝ} (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) (good : Prop) (l : A×B)
    (hc : ¬PlaceScore.common ε f) (hg : good) :
    let r := minority f
    2*event (left π) (fun p => exceptional r l (x p))-
      2*event (right π) (fun q => exceptional r l (y q))-
      4*event π (fun pq => exceptional r l (x pq.1) ∧ exceptional r l (y pq.2))-
      6*event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))≤
      scoreT ε f π a bit x y good l := by
  have h := avg_mono (templates π a) (fun θ => rare_P (slice π a θ) bit x y good l hc hg)
  simpa only [avg_sub,avg_smul,slice_left_event,slice_right_event,slice_event_original,scoreT] using h

lemma common_T {ε f : ℝ} (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) (good : Prop) (l : A×B) (hc : PlaceScore.common ε f) :
    scoreT ε f π a bit x y good l=avg (templates π a) (fun θ => DP (slice π a θ) bit y) := by
  unfold scoreT
  apply avg_congr
  intro θ
  exact common_P (slice π a θ) bit x y good l hc

lemma scoreT_lower (ε f : ℝ) (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) (good : Prop) (l : A×B) :
    -1≤ scoreT ε f π a bit x y good l :=
  const_le_avg _ (fun θ => scoreP_lower ε f (slice π a θ) bit x y good l)
end
end PlanarUnitDistances.RareRows

end OAI
