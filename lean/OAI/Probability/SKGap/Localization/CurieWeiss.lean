import Mathlib
import OAI.Probability.SKGap.Terminal.GibbsExpectationMono
import OAI.Probability.SKGap.Matrix.NormalizedInfluence

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
namespace SKGapCutoff

noncomputable def curieWeiss (a : ℝ) (n : ℕ) : Interaction n :=
  fun i j => if i=j then 0 else a/(n:ℝ)

lemma curieWeiss_symm (a : ℝ) (n : ℕ) :
    ∀ i j, curieWeiss a n i j = curieWeiss a n j i := by
  intro i j
  simp only [curieWeiss, eq_comm]

lemma curieWeiss_diag (a : ℝ) (n : ℕ) : ∀ i, curieWeiss a n i i = 0 := by
  intro i
  simp [curieWeiss]

lemma curieWeiss_energy (a : ℝ) {n : ℕ} (x : Spin n) :
    energy (curieWeiss a n) x = a/(2*(n:ℝ))*(magnetization x^2-(n:ℝ)) := by
  have hentry (i j : Fin n) : spin x i * curieWeiss a n i j * spin x j =
      a/(n:ℝ)*(spin x i*spin x j) - if i=j then a/(n:ℝ) else 0 := by
    by_cases h : i=j
    · subst j
      simp [curieWeiss]
    · simp [curieWeiss, h]
      ring
  have hs : (∑ i, ∑ j, a/(n:ℝ)*(spin x i*spin x j)) =
      a/(n:ℝ)*magnetization x^2 := by
    simp only [magnetization, pow_two, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  simp only [energy, hentry, Finset.sum_sub_distrib,
    Fintype.sum_ite_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hs]
  ring

noncomputable def majority {n : ℕ} (x : Spin n) : ℝ :=
  if 0 < magnetization x then 1 else if magnetization x < 0 then -1 else 0

@[simp] lemma magnetization_invert {n : ℕ} (x : Spin n) :
    magnetization (invert x) = -magnetization x := by
  simp [magnetization]

@[simp] lemma majority_invert {n : ℕ} (x : Spin n) : majority (invert x) = -majority x := by
  simp only [majority, magnetization_invert]
  split_ifs <;> linarith

lemma majority_abs_le_one {n : ℕ} (x : Spin n) : |majority x| ≤ 1 := by
  unfold majority
  split_ifs <;> norm_num

lemma majority_centered {n : ℕ} (J : Interaction n) : gibbsExpectation J majority = 0 := by
  have h := sum_invert (fun x => gibbs J x*majority x)
  simp only [gibbs_invert, majority_invert, mul_neg, Finset.sum_neg_distrib] at h
  unfold gibbsExpectation
  linarith

lemma majority_sq {n : ℕ} (x : Spin n) :
    majority x^2 = if magnetization x=0 then 0 else 1 := by
  rcases lt_trichotomy (magnetization x) 0 with hm | hm | hm
  · simp [majority, hm, not_lt_of_ge (le_of_lt hm), ne_of_lt hm]
  · simp [majority, hm]
  · simp [majority, hm, ne_of_gt hm]

lemma magnetization_replace {n : ℕ} (x : Spin n) (i : Fin n) (b : Bool) :
    magnetization (replace x i b) = magnetization x - spin x i + if b then 1 else -1 := by
  have h : spin (replace x i b) = Function.update (spin x) i (if b then 1 else -1) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp [spin, replace]
    · simp [spin, replace, hj]
  simp only [magnetization, h]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hs := Finset.sum_sdiff (f := spin x) (by simp :
    ({i} : Finset (Fin n)) ⊆ Finset.univ)
  simp only [Finset.sum_singleton] at hs
  linarith

lemma halfDiff_majority_zero {n : ℕ} (x : Spin n) (i : Fin n)
    (hx : 2 < |magnetization x|) : halfDiff i majority x = 0 := by
  have hi := spin_sq x i
  have hi1 : -1 ≤ spin x i ∧ spin x i ≤ 1 := by
    constructor <;> nlinarith
  rcases lt_or_ge (magnetization x) 0 with hm | hm
  · rw [abs_of_neg hm] at hx
    have ht : magnetization (replace x i true) < 0 := by
      simp only [magnetization_replace, ↓reduceIte]
      linarith [hi1.1]
    have hf : magnetization (replace x i false) < 0 := by
      simp only [magnetization_replace, Bool.false_eq_true, ↓reduceIte]
      linarith [hi1.1]
    simp [halfDiff, majority, ht, hf, not_lt_of_ge (le_of_lt ht), not_lt_of_ge (le_of_lt hf)]
  · rw [abs_of_nonneg hm] at hx
    have ht : 0 < magnetization (replace x i true) := by
      simp only [magnetization_replace, ↓reduceIte]
      linarith [hi1.2]
    have hf : 0 < magnetization (replace x i false) := by
      simp only [magnetization_replace, Bool.false_eq_true, ↓reduceIte]
      linarith [hi1.2]
    simp [halfDiff, majority, ht, hf]

lemma halfDiff_majority_abs_le_one {n : ℕ} (x : Spin n) (i : Fin n) :
    |halfDiff i majority x| ≤ 1 := by
  have h := (abs_sub (majority (replace x i true)) (majority (replace x i false))).trans
    (add_le_add (majority_abs_le_one _) (majority_abs_le_one _))
  simp only [halfDiff, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by linarith)

noncomputable def centralMass {n : ℕ} (J : Interaction n) : ℝ :=
  gibbsExpectation J (fun x => if |magnetization x| ≤ 2 then 1 else 0)

lemma majority_variance_lower {n : ℕ} (J : Interaction n) :
    1 - centralMass J ≤ gibbsVariance J majority := by
  rw [gibbsVariance, majority_centered]
  simp only [sub_zero]
  calc
    _ = gibbsExpectation J (fun x => 1-(if |magnetization x| ≤ 2 then 1 else 0)) := by
      rw [gibbsExpectation_sub, gibbsExpectation_const]
      rfl
    _ ≤ _ := gibbsExpectation_mono J _ _ (fun x => by
      rw [majority_sq]
      split_ifs <;> simp_all)

lemma majority_dirichlet_upper {n : ℕ} (J : Interaction n) :
    dirichlet J majority majority ≤ (n:ℝ)*centralMass J := by
  change gibbsExpectation J _ ≤ (n:ℝ)*gibbsExpectation J _
  rw [← gibbsExpectation_mul_const]
  apply gibbsExpectation_mono
  intro x
  by_cases hx : |magnetization x| ≤ 2
  · simp only [hx, ↓reduceIte, mul_one]
    calc
      _ ≤ ∑ _i : Fin n, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have ha := halfDiff_majority_abs_le_one x i
        have hh : (halfDiff i majority x)^2 ≤ 1 :=
          (sq_le_one_iff_abs_le_one _).mpr ha
        nlinarith [(le_of_lt (siteVariance_pos J x i)), siteVariance_le_one J x i,
          mul_le_mul_of_nonneg_left hh ((le_of_lt (siteVariance_pos J x i)))]
      _ = _ := by simp
  · simp [hx, halfDiff_majority_zero x _ (lt_of_not_ge hx)]

lemma gibbs_le_exp_energy_diff {n : ℕ} (J : Interaction n) (x y : Spin n) :
    gibbs J x ≤ Real.exp (energy J x-energy J y) := by
  rw [gibbs, Real.exp_sub]
  apply div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) (Real.exp_pos _)
  exact Finset.single_le_sum (fun z _ => le_of_lt (Real.exp_pos (energy J z))) (Finset.mem_univ y)

lemma curieWeiss_central_point_bound (a : ℝ) (ha : 0 ≤ a) {n : ℕ}
    (hn : 0 < n) (x : Spin n) (hx : |magnetization x| ≤ 2) :
    gibbs (curieWeiss a n) x ≤ Real.exp (-a*(n:ℝ)/2+2*a/(n:ℝ)) := by
  apply (gibbs_le_exp_energy_diff _ x (plusSpin n)).trans
  apply Real.exp_le_exp.mpr
  rw [curieWeiss_energy, curieWeiss_energy, magnetization_plus]
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hsq : magnetization x^2 ≤ 4 := by
    have h := (sq_le_sq₀ (abs_nonneg (magnetization x)) (by norm_num : (0:ℝ)≤2)).mpr hx
    norm_num at h ⊢
    exact h
  calc
    _ = a/(2*(n:ℝ))*magnetization x^2-a*(n:ℝ)/2 := by field_simp; ring
    _ ≤ a/(2*(n:ℝ))*4-a*(n:ℝ)/2 := by gcongr
    _ = _ := by ring

lemma curieWeiss_central_bound (a : ℝ) (ha : 0 ≤ a) {n : ℕ} (hn : 0 < n) :
    centralMass (curieWeiss a n) ≤ (2:ℝ)^n*Real.exp (-a*(n:ℝ)/2+2*a/(n:ℝ)) := by
  unfold centralMass gibbsExpectation
  calc
    _ ≤ ∑ _x : Spin n, Real.exp (-a*(n:ℝ)/2+2*a/(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro x _
      dsimp only
      split_ifs with hx
      · simpa using curieWeiss_central_point_bound a ha hn x hx
      · simp [le_of_lt (Real.exp_pos _)]
    _ = _ := by simp [Spin]

theorem curieWeiss_gap_bottleneck (a : ℝ) (ha : 0 ≤ a) {n : ℕ} (hn : 0 < n)
    {γ : ℝ} (hγ : 0 ≤ γ) (hg : HasGap (curieWeiss a n) γ) :
    γ*(1-(2:ℝ)^n*Real.exp (-a*(n:ℝ)/2+2*a/(n:ℝ))) ≤
      (n:ℝ)*((2:ℝ)^n*Real.exp (-a*(n:ℝ)/2+2*a/(n:ℝ))) := by
  have hb := curieWeiss_central_bound a ha hn
  calc
    _ ≤ γ*(1-centralMass (curieWeiss a n)) := by gcongr
    _ ≤ γ*gibbsVariance (curieWeiss a n) majority :=
      mul_le_mul_of_nonneg_left (majority_variance_lower _) hγ
    _ ≤ dirichlet (curieWeiss a n) majority majority := hg majority
    _ ≤ (n:ℝ)*centralMass (curieWeiss a n) := majority_dirichlet_upper _
    _ ≤ _ := by gcongr

lemma curieWeiss_entry_bound (a : ℝ) (ha : 0 ≤ a) {n : ℕ} (i j : Fin n) :
    |curieWeiss a n i j| ≤ a/(n:ℝ) := by
  unfold curieWeiss
  split_ifs
  · simp only [abs_zero]
    positivity
  · exact (abs_of_nonneg (by positivity)).le

lemma curieWeiss_norm_bound (a : ℝ) (ha : 0 ≤ a) {n : ℕ} (hn : 0 < n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (curieWeiss a n)‖ ≤ a := by
  apply matrix_opNorm_le_schur _ a ha
  · intro i
    calc
      _ ≤ ∑ _j : Fin n, a/(n:ℝ) := Finset.sum_le_sum (fun j _ => curieWeiss_entry_bound a ha i j)
      _ = a := by simp; field_simp
  · intro j
    calc
      _ ≤ ∑ _i : Fin n, a/(n:ℝ) := Finset.sum_le_sum (fun i _ => curieWeiss_entry_bound a ha i j)
      _ = a := by simp; field_simp

lemma curieWeiss_bound_exp (a : ℝ) (n : ℕ) :
    (2:ℝ)^n*Real.exp (-a*(n:ℝ)/2+2*a/(n:ℝ)) =
      Real.exp (-(a/2-Real.log 2)*(n:ℝ))*Real.exp (2*a/(n:ℝ)) := by
  have hp : (2:ℝ)^n = Real.exp ((n:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [hp, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma curieWeiss_bound_tendsto_zero (a : ℝ) (ha : 2*Real.log 2 < a) :
    Tendsto (fun n : ℕ => (2:ℝ)^n*Real.exp (-a*(n:ℝ)/2+2*a/(n:ℝ))) atTop (nhds 0) := by
  have hk : 0 < a/2-Real.log 2 := by linarith
  have h1 : Tendsto (fun n : ℕ => Real.exp (-(a/2-Real.log 2)*(n:ℝ))) atTop (nhds 0) := by
    simpa using (Real.summable_pow_mul_exp_neg_nat_mul 0 hk).tendsto_atTop_zero
  have h2 : Tendsto (fun n : ℕ => Real.exp (2*a/(n:ℝ))) atTop (nhds 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp
      (show Tendsto (fun n : ℕ => 2*a/(n:ℝ)) atTop (nhds 0) from
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  simp_rw [curieWeiss_bound_exp]
  simpa using h1.mul h2

lemma curieWeiss_n_bound_tendsto_zero (a : ℝ) (ha : 2*Real.log 2 < a) :
    Tendsto (fun n : ℕ => (n:ℝ)*((2:ℝ)^n*Real.exp (-a*(n:ℝ)/2+2*a/(n:ℝ))))
      atTop (nhds 0) := by
  have hk : 0 < a/2-Real.log 2 := by linarith
  have h1 : Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-(a/2-Real.log 2)*(n:ℝ)))
      atTop (nhds 0) := by
    simpa using (Real.summable_pow_mul_exp_neg_nat_mul 1 hk).tendsto_atTop_zero
  have h2 : Tendsto (fun n : ℕ => Real.exp (2*a/(n:ℝ))) atTop (nhds 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp
      (show Tendsto (fun n : ℕ => 2*a/(n:ℝ)) atTop (nhds 0) from
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  simp_rw [curieWeiss_bound_exp, ← mul_assoc]
  simpa using h1.mul h2

theorem curieWeiss_no_uniform_gap (a : ℝ) (ha : 2*Real.log 2 < a) :
    ¬ ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n : ℕ in atTop, HasGap (curieWeiss a n) γ := by
  rintro ⟨γ, hγ, hg⟩
  have ha0 : 0 ≤ a := by linarith [Real.log_pos (by norm_num : (1:ℝ)<2)]
  have hbound : ∀ᶠ n : ℕ in atTop,
      γ*(1-(2:ℝ)^n*Real.exp (-a*(n:ℝ)/2+2*a/(n:ℝ))) ≤
        (n:ℝ)*((2:ℝ)^n*Real.exp (-a*(n:ℝ)/2+2*a/(n:ℝ))) := by
    filter_upwards [hg, eventually_gt_atTop 0] with n hn hn0
    exact curieWeiss_gap_bottleneck a ha0 hn0 hγ.le hn
  have hleft : Tendsto (fun n : ℕ => γ*(1-(2:ℝ)^n*Real.exp (-a*(n:ℝ)/2+2*a/(n:ℝ))))
      atTop (nhds γ) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds 1)).sub
      (curieWeiss_bound_tendsto_zero a ha)).const_mul γ
  have hle := le_of_tendsto_of_tendsto hleft (curieWeiss_n_bound_tendsto_zero a ha) hbound
  linarith

lemma curieWeiss_entries_vanish (a : ℝ) (ha : 0 ≤ a) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ i j : Fin n, |curieWeiss a n i j| < ε := by
  have h : Tendsto (fun n : ℕ => a/(n:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually (gt_mem_nhds hε)] with n hn i j
  exact (curieWeiss_entry_bound a ha i j).trans_lt hn

end SKGapCutoff

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology

end

end OAI
