import Mathlib
import OAI.Analysis.HardSphere.Paths.TimeGaps

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.DyadicSkeleton

lemma orderedEncounterConstant_one_le : 1 ≤ orderedEncounterConstant := by
  simpa only [orderedEncounterConstant,ENNReal.toReal_one] using
    ENNReal.toReal_mono gapKernel_sum_ne_top gapKernel_sum_one_le

def nearPotential (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) (ω : Noise) : ℝ :=
  (nearTest n y R ω).toReal
lemma nearPotential_nonneg (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) (ω : Noise) :
    0 ≤ nearPotential n y R ω := ENNReal.toReal_nonneg
lemma nearPotential_le_one (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) (ω : Noise) :
    nearPotential n y R ω ≤ 1 := by
  simpa only [nearPotential,ENNReal.toReal_one] using
    ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞) ≠ ∞) (nearTest_le_one n y R ω)
lemma nearPotential_cast (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) (ω : Noise) :
    ENNReal.ofReal (nearPotential n y R ω) = nearTest n y R ω :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by norm_num) (nearTest_le_one n y R ω))
@[fun_prop] lemma measurable_nearPotential (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) :
    Measurable (nearPotential n y R) := (measurable_nearTest n y R).ennreal_toReal

def singleRadiusWeights (R : ℕ) (a : ℝ≥0∞) (l : ℕ) : ℝ≥0∞ := if l=R then a else 0
lemma singleRadiusWeights_envelope (R : ℕ) (a : ℝ≥0∞) (n : ℕ)
    (y : Fin 2 → ℝ) (ω : Noise) :
    radiusEnvelope (singleRadiusWeights R a) n y ω = a * nearTest n y (R:ℝ) ω := by
  simp [radiusEnvelope,singleRadiusWeights,ite_mul]
lemma singleRadiusWeights_activity (R : ℕ) (a : ℝ≥0∞) :
    radiusActivity (singleRadiusWeights R a) =
      ENNReal.ofReal orderedEncounterConstant * (a * radiusFactor (R:ℝ)) := by
  simp [radiusActivity,singleRadiusWeights,ite_mul]

def hitConstant : ℝ := (4 * Real.exp 2 * orderedEncounterConstant)⁻¹
lemma hitConstant_pos : 0 < hitConstant := by
  unfold hitConstant
  positivity [orderedEncounterConstant_pos]
lemma hitConstant_le_one : hitConstant ≤ 1 := by
  have he : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hc := orderedEncounterConstant_one_le
  have hd : 1 ≤ 4 * Real.exp 2 * orderedEncounterConstant := by nlinarith
  exact (inv_le_one₀ (by positivity)).mpr hd

lemma same_time_hit_moment (T R : ℕ) (y : ℕ → Fin 2 → ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((hitConstant/(1+(R:ℝ))^2) *
      ∑ u ∈ Finset.range (T+1), nearPotential u (y u) (R:ℝ) ω)) ∂law) ≤ 2 := by
  let a := hitConstant/(2*(1+(R:ℝ))^2)
  have hp : 0 < (1+(R:ℝ))^2 := by positivity
  have ha : 0 ≤ a := by dsimp [a]; exact div_nonneg hitConstant_pos.le (by positivity)
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_one (by positivity)).mpr
    have hr := Nat.cast_nonneg (α:=ℝ) R
    nlinarith [hitConstant_le_one]
  have hsmall : ENNReal.ofReal (2*Real.exp 2) *
      radiusActivity (singleRadiusWeights R (ENNReal.ofReal a)) ≤ (1/2:ℝ≥0∞) := by
    rw [singleRadiusWeights_activity,radiusFactor,
      ← ENNReal.ofReal_mul ha,← ENNReal.ofReal_mul orderedEncounterConstant_pos.le,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*Real.exp 2)]
    have heq : 2*Real.exp 2*(orderedEncounterConstant*(a*(1+(R:ℝ))^2)) = 1/4 := by
      dsimp [a,hitConstant]
      field_simp [ne_of_gt orderedEncounterConstant_pos,ne_of_gt (Real.exp_pos 2)]
    rw [heq]
    norm_num [ENNReal.ofReal_div_of_pos]
  have h := radius_exponential_bound T (singleRadiusWeights R (ENNReal.ofReal a)) y
    (fun n ω ↦ a*nearPotential n (y n) (R:ℝ) ω)
    (fun n ω ↦ mul_nonneg ha (nearPotential_nonneg n (y n) (R:ℝ) ω))
    (fun n ω ↦ (mul_le_mul_of_nonneg_left (nearPotential_le_one n (y n) (R:ℝ) ω) ha).trans
      (by simpa using ha1))
    (by intro n ω; rw [ENNReal.ofReal_mul ha,nearPotential_cast,singleRadiusWeights_envelope]) hsmall
  convert h using 1
  apply lintegral_congr
  intro ω
  congr 2
  rw [← Finset.mul_sum]
  dsimp [a]
  field_simp

def transverseDistance (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) : ℝ :=
  max |position ω 0 n-y 0| |position ω 1 n-y 1|
lemma transverseDistance_nonneg (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) :
    0 ≤ transverseDistance n y ω := (abs_nonneg _).trans (le_max_left _ _)
@[fun_prop] lemma measurable_transverseDistance (n : ℕ) (y : Fin 2 → ℝ) :
    Measurable (transverseDistance n y) := by unfold transverseDistance; fun_prop
lemma nearTest_eq_one (n : ℕ) (y : Fin 2 → ℝ) (R : ℝ) (ω : Noise)
    (h : transverseDistance n y ω ≤ R) : nearTest n y R ω = 1 := by
  have h' := max_le_iff.mp h
  simp [nearTest,coordinateTest,h'.1,h'.2]

def softPotential (B : ℝ) (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) : ℝ :=
  Real.exp (-transverseDistance n y ω/B)
lemma softPotential_nonneg (B : ℝ) (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) :
    0 ≤ softPotential B n y ω := (Real.exp_pos _).le
lemma softPotential_le_one (B : ℝ) (hB : 0 < B) (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) :
    softPotential B n y ω ≤ 1 :=
  Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by
    linarith [transverseDistance_nonneg n y ω]) hB.le)
@[fun_prop] lemma measurable_softPotential (B : ℝ) (n : ℕ) (y : Fin 2 → ℝ) :
    Measurable (softPotential B n y) := by unfold softPotential; fun_prop

def softWeights (B : ℝ) (l : ℕ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((1-(l:ℝ))/B))
lemma softPotential_envelope (B : ℝ) (hB : 0 < B) (n : ℕ) (y : Fin 2 → ℝ) (ω : Noise) :
    ENNReal.ofReal (softPotential B n y ω) ≤ radiusEnvelope (softWeights B) n y ω := by
  let l := ⌈transverseDistance n y ω⌉₊
  have hl : transverseDistance n y ω ≤ (l:ℝ) := Nat.le_ceil _
  have hl' : (l:ℝ) < transverseDistance n y ω+1 :=
    Nat.ceil_lt_add_one (transverseDistance_nonneg n y ω)
  refine le_trans ?_ (ENNReal.le_tsum (f := fun k : ℕ ↦
    softWeights B k * nearTest n y (k:ℝ) ω) l)
  rw [nearTest_eq_one n y (l:ℝ) ω hl,mul_one]
  change ENNReal.ofReal (Real.exp (-transverseDistance n y ω/B)) ≤
    ENNReal.ofReal (Real.exp ((1-(l:ℝ))/B))
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (by linarith) hB.le

lemma soft_activity_ne_top (B : ℝ) (hB : 0 < B) : radiusActivity (softWeights B) ≠ ∞ := by
  let q := Real.exp (-1/B)
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by norm_num) hB
  have hs0 : Summable (fun l : ℕ ↦ q^l) := summable_geometric_of_norm_lt_one hq
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have hs2 := summable_pow_mul_geometric_of_norm_lt_one 2 hq
  have hs : Summable (fun l : ℕ ↦ Real.exp ((1-(l:ℝ))/B)*(1+(l:ℝ))^2) := by
    have h := ((hs2.add (hs1.mul_left 2)).add hs0).mul_left (Real.exp (1/B))
    apply h.congr
    intro l
    have he : Real.exp ((1-(l:ℝ))/B) = Real.exp (1/B) * q^l := by
      rw [show (1-(l:ℝ))/B = 1/B + (l:ℝ)*(-1/B) by ring,Real.exp_add,Real.exp_nat_mul]
    rw [he]
    simp only [pow_one]
    ring
  have he : (∑' l : ℕ, softWeights B l * radiusFactor (l:ℝ)) =
      ENNReal.ofReal (∑' l : ℕ, Real.exp ((1-(l:ℝ))/B)*(1+(l:ℝ))^2) := by
    simp only [softWeights,radiusFactor,← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun l ↦ by positivity) hs).symm
  unfold radiusActivity
  rw [he]
  finiteness

lemma same_time_soft_moment (B : ℝ) (hB : 0 < B) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ (T : ℕ) (y : ℕ → Fin 2 → ℝ),
    (∫⁻ ω, ENNReal.ofReal (Real.exp (ξ *
      ∑ u ∈ Finset.range (T+1), softPotential B u (y u) ω)) ∂law) ≤ 2 := by
  let A := (radiusActivity (softWeights B)).toReal
  let δ := (4*Real.exp 2*(1+A))⁻¹
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hAc : ENNReal.ofReal A = radiusActivity (softWeights B) :=
    ENNReal.ofReal_toReal (soft_activity_ne_top B hB)
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ ≤ 1 := by
    apply (inv_le_one₀ (by positivity)).mpr
    have he : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    nlinarith
  refine ⟨2*δ,by positivity,?_⟩
  intro T y
  let a := fun l ↦ ENNReal.ofReal δ * softWeights B l
  have hsmall : ENNReal.ofReal (2*Real.exp 2) * radiusActivity a ≤ (1/2:ℝ≥0∞) := by
    rw [show radiusActivity a = ENNReal.ofReal δ * radiusActivity (softWeights B) from
      radiusActivity_smul _ _,← hAc,← ENNReal.ofReal_mul hd.le,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*Real.exp 2)]
    calc
      _ ≤ ENNReal.ofReal (1/2:ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        dsimp [δ]
        have he := Real.exp_pos 2
        field_simp
        nlinarith
      _ = _ := by norm_num [ENNReal.ofReal_div_of_pos]
  have h := radius_exponential_bound T a y
    (fun n ω ↦ δ * softPotential B n (y n) ω)
    (fun n ω ↦ mul_nonneg hd.le (softPotential_nonneg B n (y n) ω))
    (fun n ω ↦ (mul_le_mul_of_nonneg_left (softPotential_le_one B hB n (y n) ω) hd.le).trans
      (by simpa using hd1))
    (by
      intro n ω
      rw [ENNReal.ofReal_mul hd.le]
      exact (mul_le_mul_right (softPotential_envelope B hB n (y n) ω) (ENNReal.ofReal δ)).trans_eq
        (radiusEnvelope_smul _ _ n (y n) ω).symm) hsmall
  convert h using 1
  apply lintegral_congr
  intro ω
  congr 2
  rw [← Finset.mul_sum]
  ring

def twoCopyDistance (n : ℕ) (z : Noise × Noise) : ℝ :=
  transverseDistance n (fun j ↦ position z.2 j n) z.1

@[fun_prop] lemma measurable_twoCopyDistance (n : ℕ) :
    Measurable (twoCopyDistance n) := by
  unfold twoCopyDistance transverseDistance
  exact (((measurable_position 0 n).comp measurable_fst).sub
    ((measurable_position 0 n).comp measurable_snd)).abs.max
    (((measurable_position 1 n).comp measurable_fst).sub
    ((measurable_position 1 n).comp measurable_snd)).abs

@[fun_prop] lemma measurable_twoCopyNear (n : ℕ) (R : ℝ) :
    Measurable (fun z : Noise × Noise ↦
      nearPotential n (fun j ↦ position z.2 j n) R z.1) := by
  unfold nearPotential nearTest
  apply Measurable.ennreal_toReal
  apply Measurable.mul
  all_goals
    apply measurable_const.indicator
    apply measurableSet_le _ measurable_const
    apply Measurable.abs
    exact ((measurable_position _ n).comp measurable_fst).sub
      ((measurable_position _ n).comp measurable_snd)

lemma two_copy_hit_moment (T R : ℕ) :
    (∫⁻ z, ENNReal.ofReal (Real.exp ((hitConstant/(1+(R:ℝ))^2) *
      ∑ u ∈ Finset.range (T+1), nearPotential u
        (fun j ↦ position z.2 j u) (R:ℝ) z.1)) ∂law.prod law) ≤ 2 := by
  rw [lintegral_prod_symm _ (by
    apply Measurable.aemeasurable
    apply Measurable.ennreal_ofReal
    apply Measurable.exp
    apply Measurable.const_mul
    exact Finset.measurable_sum _ (fun u _ ↦ measurable_twoCopyNear u (R:ℝ)))]
  calc
    _ ≤ ∫⁻ _ : Noise, (2:ℝ≥0∞) ∂law := lintegral_mono (fun ω ↦
      same_time_hit_moment T R (fun u j ↦ position ω j u))
    _ = 2 := by simp

lemma two_copy_soft_moment (B : ℝ) (hB : 0 < B) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ T : ℕ,
    (∫⁻ z, ENNReal.ofReal (Real.exp (ξ *
      ∑ u ∈ Finset.range (T+1), Real.exp (-twoCopyDistance u z / B)))
      ∂law.prod law) ≤ 2 := by
  obtain ⟨ξ,hξ,h⟩ := same_time_soft_moment B hB
  refine ⟨ξ,hξ,fun T ↦ ?_⟩
  rw [lintegral_prod_symm _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ _ : Noise, (2:ℝ≥0∞) ∂law := lintegral_mono (fun ω ↦
      h T (fun u j ↦ position ω j u))
    _ = 2 := by simp

lemma position_lipschitz (ω : Noise) (j : Fin 2) (s t : ℕ) :
    |position ω j s-position ω j t| ≤ |(s:ℝ)-t|/2 := by
  have hinc (a k : ℕ) : |position ω j (a+k)-position ω j a| ≤ (k:ℝ)/2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ, position_succ]
      calc
        _ = |(position ω j (a+k)-position ω j a)+velocity ω j (a+k)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ (k:ℝ)/2+1/2 := add_le_add ih (velocity_abs_le ω j (a+k))
        _ = _ := by push_cast; ring
  rcases le_total t s with h | h
  · have hs : 0 ≤ (s:ℝ)-t := sub_nonneg.mpr (by exact_mod_cast h)
    rw [abs_of_nonneg hs]
    simpa only [Nat.add_sub_of_le h,Nat.cast_sub h] using hinc t (s-t)
  · have hs : 0 ≤ (t:ℝ)-s := sub_nonneg.mpr (by exact_mod_cast h)
    rw [abs_sub_comm (s:ℝ),abs_of_nonneg hs,abs_sub_comm (position ω j s)]
    simpa only [Nat.add_sub_of_le h,Nat.cast_sub h] using hinc s (t-s)

lemma position_abs_le (ω : Noise) (j : Fin 2) (t : ℕ) :
    |position ω j t| ≤ (t:ℝ)/2 := by
  simpa [position,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) t)] using position_lipschitz ω j t 0

lemma fold_time_lipschitz (n s t : ℕ) (hs : s ≤ n) (ht : t ≤ n) :
    |((min s (n-s):ℕ):ℝ)-((min t (n-t):ℕ):ℝ)| ≤ |(s:ℝ)-t| := by
  have h := abs_min_sub_min_le_max (s:ℝ) ((n:ℝ)-s) (t:ℝ) ((n:ℝ)-t)
  have he : |((n:ℝ)-s)-((n:ℝ)-t)| = |(s:ℝ)-t| := by
    rw [sub_sub_sub_cancel_left,abs_sub_comm]
  simpa only [Nat.cast_min,Nat.cast_sub hs,Nat.cast_sub ht,he,max_self] using h

abbrev Vertex := Fin 3 → ℤ

def baseTrans (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) (t : ℕ) (j : Fin 2) : ℝ :=
  (t:ℝ)*(d j:ℝ)/(n:ℝ)+position ω j (min t (n-t))

def baseVertex (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) (t : ℕ) : Vertex :=
  ![(t:ℤ),⌊baseTrans n d ω t 0⌋,⌊baseTrans n d ω t 1⌋]

@[fun_prop] lemma measurable_baseTrans (n : ℕ) (d : Fin 2 → ℤ) (t : ℕ) (j : Fin 2) :
    Measurable (fun ω ↦ baseTrans n d ω t j) := by unfold baseTrans; fun_prop

@[fun_prop] lemma measurable_baseVertex (n : ℕ) (d : Fin 2 → ℤ) (t : ℕ) :
    Measurable (fun ω ↦ baseVertex n d ω t) := by
  apply Measurable.of_eval
  intro j
  fin_cases j
  · exact measurable_const
  · exact Int.measurable_floor.comp (measurable_baseTrans n d t 0)
  · exact Int.measurable_floor.comp (measurable_baseTrans n d t 1)

lemma drift_rate_le (n : ℕ) (hn : 0 < n) (d : ℤ) (hd : |d| ≤ n) :
    |(d:ℝ)/(n:ℝ)| ≤ 1 := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [abs_div,abs_of_pos hn',div_le_one hn']
  exact_mod_cast hd

lemma baseTrans_lipschitz (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j| ≤ n) (ω : Noise) (s t : ℕ) (hs : s ≤ n) (ht : t ≤ n) (j : Fin 2) :
    |baseTrans n d ω s j-baseTrans n d ω t j| ≤ (3/2)*|(s:ℝ)-t| := by
  have hp := (position_lipschitz ω j (min s (n-s)) (min t (n-t))).trans
    (div_le_div_of_nonneg_right (fold_time_lipschitz n s t hs ht) (by norm_num : (0:ℝ) ≤ 2))
  calc
    _ = |((s:ℝ)-t)*((d j:ℝ)/(n:ℝ))+
        (position ω j (min s (n-s))-position ω j (min t (n-t)))| := by
      unfold baseTrans; congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ |(s:ℝ)-t| + |(s:ℝ)-t|/2 := add_le_add (by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (drift_rate_le n hn (d j) (hd j))
        (abs_nonneg _)).trans_eq (mul_one _)) hp
    _ = _ := by ring

lemma floor_abs_sub_le_two (x y : ℝ) (h : |x-y| ≤ 3/2) :
    |⌊x⌋-⌊y⌋| ≤ (2:ℤ) := by
  have hf := Int.floor_le x
  have hg := Int.lt_floor_add_one y
  have hf' := Int.floor_le y
  have hg' := Int.lt_floor_add_one x
  obtain ⟨hl,hu⟩ := abs_le.mp h
  apply abs_le.mpr
  constructor
  · by_contra hn
    have h' : ⌊y⌋-⌊x⌋ ≥ (3:ℤ) := by omega
    have hh : (3:ℝ) ≤ (⌊y⌋:ℝ)-(⌊x⌋:ℝ) := by exact_mod_cast h'
    linarith
  · by_contra hn
    have h' : ⌊x⌋-⌊y⌋ ≥ (3:ℤ) := by omega
    have hh : (3:ℝ) ≤ (⌊x⌋:ℝ)-(⌊y⌋:ℝ) := by exact_mod_cast h'
    linarith

lemma baseVertex_step (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ)
    (hd : ∀j, |d j| ≤ n) (ω : Noise) (t : ℕ) (ht : t < n) (j : Fin 3) :
    |baseVertex n d ω (t+1) j-baseVertex n d ω t j| ≤ 2 := by
  have hh (i : Fin 2) : |⌊baseTrans n d ω (t+1) i⌋-⌊baseTrans n d ω t i⌋| ≤ (2:ℤ) := by
    apply floor_abs_sub_le_two
    have h := baseTrans_lipschitz n hn d hd ω (t+1) t (by omega) (by omega) i
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left,abs_one,mul_one] using h
  fin_cases j
  · norm_num [baseVertex]
  · exact hh 0
  · exact hh 1

lemma baseVertex_initial (n : ℕ) (d : Fin 2 → ℤ) (ω : Noise) :
    baseVertex n d ω 0 = 0 := by
  ext j
  fin_cases j <;> simp [baseVertex,baseTrans,position]

lemma baseVertex_final (n : ℕ) (hn : 0 < n) (d : Fin 2 → ℤ) (ω : Noise) :
    baseVertex n d ω n = ![(n:ℤ),d 0,d 1] := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  ext j
  fin_cases j <;> simp [baseVertex,baseTrans,position,mul_div_cancel_left₀ _ hn0]

def axisSteps (a b : ℤ) : List ℤ :=
  if a ≤ b then (List.range (b-a).toNat).map (fun k : ℕ ↦ a+(k:ℤ)+1)
  else (List.range (a-b).toNat).map (fun k : ℕ ↦ a-(k:ℤ)-1)

lemma axisSteps_length (a b : ℤ) : (axisSteps a b).length = (b-a).natAbs := by
  unfold axisSteps
  split_ifs with h <;> simp only [List.length_map,List.length_range]
  · have hh := Int.natAbs_of_nonneg (by omega : 0 ≤ b-a)
    have hh' := Int.toNat_of_nonneg (by omega : 0 ≤ b-a)
    omega
  · rw [← Int.natAbs_neg,Int.neg_sub]
    have hh := Int.natAbs_of_nonneg (by omega : 0 ≤ a-b)
    have hh' := Int.toNat_of_nonneg (by omega : 0 ≤ a-b)
    omega

lemma axisSteps_between (a b c : ℤ) (hc : c ∈ axisSteps a b) :
    min a b ≤ c ∧ c ≤ max a b := by
  unfold axisSteps at hc
  split_ifs at hc with h
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hc
    have hk' := List.mem_range.mp hk
    simp only [min_eq_left h,max_eq_right h]
    omega
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hc
    have hk' := List.mem_range.mp hk
    simp only [min_eq_right (by omega : b ≤ a),max_eq_left (by omega : b ≤ a)]
    omega

lemma axisSteps_near_final (a b c : ℤ) (hc : c ∈ axisSteps a b) :
    |c-b| ≤ |a-b| := by
  obtain ⟨hl,hu⟩ := axisSteps_between a b c hc
  rcases le_total a b with h|h
  · rw [min_eq_left h] at hl
    rw [max_eq_right h] at hu
    rw [abs_of_nonpos (by omega : a-b ≤ 0),abs_of_nonpos (by omega : c-b ≤ 0)]
    omega
  · rw [min_eq_right h] at hl
    rw [max_eq_left h] at hu
    rw [abs_of_nonneg (by omega : 0 ≤ a-b),abs_of_nonneg (by omega : 0 ≤ c-b)]
    omega

def refineStep (a b : Vertex) : List Vertex :=
  [![b 0,a 1,a 2]] ++
  (axisSteps (a 1) (b 1)).map (fun c ↦ ![b 0,c,a 2]) ++
  (axisSteps (a 2) (b 2)).map (fun c ↦ ![b 0,b 1,c])

lemma refineStep_length (a b : Vertex) (h : ∀j, |b j-a j| ≤ 2) :
    (refineStep a b).length ≤ 5 := by
  simp only [refineStep,List.length_append,List.length_singleton,List.length_map,axisSteps_length]
  have h1 := h 1
  have h2 := h 2
  have ha1 : (b 1-a 1).natAbs ≤ 2 := by
    have hh : ((b 1-a 1).natAbs:ℤ) ≤ 2 := by simpa only [Int.natCast_natAbs] using h1
    exact_mod_cast hh
  have ha2 : (b 2-a 2).natAbs ≤ 2 := by
    have hh : ((b 2-a 2).natAbs:ℤ) ≤ 2 := by simpa only [Int.natCast_natAbs] using h2
    exact_mod_cast hh
  omega

end HardSphere.DyadicSkeleton
end
end

end OAI
