import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

def SymmetricPowerSmoothWith (q D : ℝ) (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ x y : X, ‖x + y‖ ^ q + ‖x - y‖ ^ q ≤
    2 * ‖x‖ ^ q + 2 * D * ‖y‖ ^ q

variable {X : Type*} [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]
variable {q D : ℝ}

theorem norm_rpow_sum_smul_le {ι : Type*} (s : Finset ι)
    (p : ι → ℝ) (z : ι → X) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (hq : 1 ≤ q) :
    ‖∑ i ∈ s, p i • z i‖ ^ q ≤ ∑ i ∈ s, p i * ‖z i‖ ^ q := by
  have hn : ‖∑ i ∈ s, p i • z i‖ ≤ ∑ i ∈ s, p i * ‖z i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖p i • z i‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul, Real.norm_of_nonneg (hp i hi)]
  exact (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith)).trans
    (Real.rpow_arith_mean_le_arith_mean_rpow s p (fun i => ‖z i‖)
      hp hsum (fun i _ => norm_nonneg _) hq)

theorem finite_norm_rpow_jensen {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (z : ι → X) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hq : 1 ≤ q) :
    ‖∑ i, p i • z i‖ ^ q ≤ ∑ i, p i * ‖z i‖ ^ q :=
  norm_rpow_sum_smul_le Finset.univ p z (fun i _ => hp i) hsum hq

omit sectionNormedSpaceℝX in
theorem norm_add_rpow_le_two [NormedSpace ℝ X] (hq : 1 ≤ q) (hq2 : q ≤ 2) (x y : X) :
    ‖x + y‖ ^ q ≤ 2 * (‖x‖ ^ q + ‖y‖ ^ q) := by
  have hm : ((1 / 2 : ℝ) * ‖x‖ + (1 / 2 : ℝ) * ‖y‖) ^ q ≤
      (1 / 2 : ℝ) * ‖x‖ ^ q + (1 / 2 : ℝ) * ‖y‖ ^ q := by
    exact (convexOn_rpow hq).2 (norm_nonneg x) (norm_nonneg y)
      (by norm_num) (by norm_num) (by norm_num)
  have hmid : 0 ≤ (1 / 2 : ℝ) * ‖x‖ + (1 / 2 : ℝ) * ‖y‖ := by positivity
  have htwo : (2 : ℝ) ^ q ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2
      _ = 4 := by norm_num [Real.rpow_two]
  calc
    _ ≤ (‖x‖ + ‖y‖) ^ q :=
      Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) (by linarith)
    _ = (2 : ℝ) ^ q * ((1 / 2 : ℝ) * ‖x‖ + (1 / 2 : ℝ) * ‖y‖) ^ q := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmid]
      congr 1
      ring
    _ ≤ 4 * ((1 / 2 : ℝ) * ‖x‖ + (1 / 2 : ℝ) * ‖y‖) ^ q :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hmid _)
    _ ≤ 4 * ((1 / 2 : ℝ) * ‖x‖ ^ q + (1 / 2 : ℝ) * ‖y‖ ^ q) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

theorem norm_sub_rpow_le_two (hq : 1 ≤ q) (hq2 : q ≤ 2) (x y : X) :
    ‖x - y‖ ^ q ≤ 2 * (‖x‖ ^ q + ‖y‖ ^ q) := by
  simpa only [sub_eq_add_neg, norm_neg] using norm_add_rpow_le_two hq hq2 x (-y)

private theorem double_weighted_left {ι : Type*} (s : Finset ι)
    (p f : ι → ℝ) (hsum : ∑ i ∈ s, p i = 1) :
    (∑ i ∈ s, ∑ j ∈ s, (p i * p j) * f i) = ∑ i ∈ s, p i * f i := by
  calc
    _ = ∑ i ∈ s, (p i * f i) * (∑ j ∈ s, p j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp only [hsum, mul_one]

private theorem double_weighted_right {ι : Type*} (s : Finset ι)
    (p f : ι → ℝ) (hsum : ∑ i ∈ s, p i = 1) :
    (∑ i ∈ s, ∑ j ∈ s, (p i * p j) * f j) = ∑ i ∈ s, p i * f i := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * f i := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := double_weighted_left s p f hsum

theorem centered_q_moment_four {ι : Type*} (s : Finset ι)
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    (p : ι → ℝ) (y : ι → X) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (hzero : ∑ i ∈ s, p i • y i = 0) (x : X) :
    (∑ i ∈ s, p i * ‖x + y i‖ ^ q) ≤
      ‖x‖ ^ q + (4 * D) * ∑ i ∈ s, p i * ‖y i‖ ^ q := by
  let A := ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * ‖x + (y i - y j)‖ ^ q
  let B := ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * ‖x - (y i - y j)‖ ^ q
  let R := ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * ‖y i - y j‖ ^ q
  have hmean (i : ι) : (∑ j ∈ s, p j • (x + (y i - y j))) = x + y i := by
    simp_rw [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, ← Finset.sum_smul, hsum, hzero]
    simp
  have hHA : (∑ i ∈ s, p i * ‖x + y i‖ ^ q) ≤ A := by
    calc
      _ ≤ ∑ i ∈ s, p i * (∑ j ∈ s, p j * ‖x + (y i - y j)‖ ^ q) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := norm_rpow_sum_smul_le s p (fun j => x + (y i - y j)) hp hsum hq
        rw [hmean i] at h
        exact mul_le_mul_of_nonneg_left h (hp i hi)
      _ = A := by simp only [A, Finset.mul_sum, mul_assoc]
  have hAB : A = B := by
    dsimp [A, B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have he : x + (y j - y i) = x - (y i - y j) := by abel
    rw [he, mul_comm (p j) (p i)]
  have htotal : (∑ i ∈ s, ∑ j ∈ s, p i * p j) = 1 := by
    calc
      _ = ∑ i ∈ s, p i := by
        simpa only [mul_one] using double_weighted_left s p (fun _ => 1) hsum
      _ = 1 := hsum
  have hsm : A + B ≤ 2 * ‖x‖ ^ q + (2 * D) * R := by
    calc
      A + B = ∑ i ∈ s, ∑ j ∈ s, (p i * p j) *
          (‖x + (y i - y j)‖ ^ q + ‖x - (y i - y j)‖ ^ q) := by
        simp only [A, B, mul_add, Finset.sum_add_distrib]
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, (p i * p j) *
          (2 * ‖x‖ ^ q + 2 * D * ‖y i - y j‖ ^ q) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hsmooth x (y i - y j))
          (mul_nonneg (hp i hi) (hp j hj))
      _ = (∑ i ∈ s, ∑ j ∈ s, p i * p j) * (2 * ‖x‖ ^ q) + (2 * D) * R := by
        simp only [R, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [htotal, one_mul]
  have hR : R ≤ 4 * ∑ i ∈ s, p i * ‖y i‖ ^ q := by
    calc
      R ≤ ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * (2 * (‖y i‖ ^ q + ‖y j‖ ^ q)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (norm_sub_rpow_le_two hq hq2 (y i) (y j))
          (mul_nonneg (hp i hi) (hp j hj))
      _ = 2 * ((∑ i ∈ s, ∑ j ∈ s, (p i * p j) * ‖y i‖ ^ q) +
          ∑ i ∈ s, ∑ j ∈ s, (p i * p j) * ‖y j‖ ^ q) := by
        rw [← Finset.sum_add_distrib]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_add_distrib]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [double_weighted_left s p _ hsum, double_weighted_right s p _ hsum]
        ring
  have hDR := mul_le_mul_of_nonneg_left hR hD
  rw [← hAB] at hsm
  nlinarith

theorem finite_centered_q_moment_four
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (y : ι → X)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hzero : ∑ i, p i • y i = 0) (x : X) :
    (∑ i, p i * ‖x + y i‖ ^ q) ≤ ‖x‖ ^ q + (4 * D) * ∑ i, p i * ‖y i‖ ^ q :=
  centered_q_moment_four Finset.univ hq hq2 hD hsmooth p y
    (fun i _ => hp i) hsum hzero x

theorem finite_fiber_q_moment_step_four
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    {Ω κ : Type*} [Fintype Ω] [Fintype κ] [DecidableEq κ]
    (w : Ω → ℝ) (key : Ω → κ) (a b : Ω → X)
    (hw : ∀ i, 0 ≤ w i)
    (hadapt : ∀ i j, key i = key j → a i = a j)
    (hzero : ∀ c, ∑ i ∈ Finset.univ.filter (fun i => key i = c), w i • (b i - a i) = 0) :
    (∑ i, w i * ‖b i‖ ^ q) ≤ (∑ i, w i * ‖a i‖ ^ q) +
      (4 * D) * ∑ i, w i * ‖b i - a i‖ ^ q := by
  classical
  have hcell (c : κ) :
      (∑ i ∈ Finset.univ.filter (fun i => key i = c), w i * ‖b i‖ ^ q) ≤
      (∑ i ∈ Finset.univ.filter (fun i => key i = c), w i * ‖a i‖ ^ q) +
      (4 * D) * ∑ i ∈ Finset.univ.filter (fun i => key i = c), w i * ‖b i - a i‖ ^ q := by
    let s := Finset.univ.filter (fun i => key i = c)
    let μ := ∑ i ∈ s, w i
    have hμ0 : 0 ≤ μ := Finset.sum_nonneg (fun i _ => hw i)
    by_cases hμ : μ = 0
    · have hwzero : ∀ i ∈ s, w i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).1 hμ
      change (∑ i ∈ s, w i * ‖b i‖ ^ q) ≤
        (∑ i ∈ s, w i * ‖a i‖ ^ q) + (4 * D) * ∑ i ∈ s, w i * ‖b i - a i‖ ^ q
      have hz (f : Ω → ℝ) : (∑ i ∈ s, w i * f i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hwzero i hi, zero_mul]
      rw [hz, hz, hz]
      simp
    · have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμ)
      have hs : s.Nonempty := by
        by_contra hempty
        have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
        exact hμ (by simp [μ, hse])
      obtain ⟨i₀, hi₀⟩ := hs
      have ha (i : Ω) (hi : i ∈ s) : a i = a i₀ :=
        hadapt i i₀ ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hi₀).2.symm)
      let p : Ω → ℝ := fun i => w i / μ
      have hp : ∀ i ∈ s, 0 ≤ p i := fun i _ => div_nonneg (hw i) hμ0
      have hp1 : (∑ i ∈ s, p i) = 1 := by
        dsimp [p]
        calc
          (∑ i ∈ s, w i / μ) = (∑ i ∈ s, w i) / μ := by
            simp only [div_eq_mul_inv, Finset.sum_mul]
          _ = 1 := div_self hμ
      have hz : (∑ i ∈ s, w i • (b i - a i₀)) = 0 := by
        calc
          _ = ∑ i ∈ s, w i • (b i - a i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [ha i hi]
          _ = 0 := hzero c
      have hpz : (∑ i ∈ s, p i • (b i - a i₀)) = 0 := by
        calc
          _ = μ⁻¹ • ∑ i ∈ s, w i • (b i - a i₀) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [smul_smul]
            congr 1
            dsimp [p]
            ring
          _ = 0 := by rw [hz, smul_zero]
      have hc := centered_q_moment_four s hq hq2 hD hsmooth p
        (fun i => b i - a i₀) hp hp1 hpz (a i₀)
      have he (i : Ω) : a i₀ + (b i - a i₀) = b i := by abel
      simp_rw [he] at hc
      have hscale (f : Ω → ℝ) : μ * (∑ i ∈ s, p i * f i) = ∑ i ∈ s, w i * f i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [p]
        calc
          μ * ((w i / μ) * f i) = ((w i / μ) * μ) * f i := by ring
          _ = w i * f i := by rw [div_mul_cancel₀ _ hμ]
      have hconst : (∑ i ∈ s, w i * ‖a i‖ ^ q) = μ * ‖a i₀‖ ^ q := by
        calc
          _ = ∑ i ∈ s, w i * ‖a i₀‖ ^ q := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [ha i hi]
          _ = _ := (Finset.sum_mul ..).symm
      have hdiff : (∑ i ∈ s, w i * ‖b i - a i₀‖ ^ q) =
          ∑ i ∈ s, w i * ‖b i - a i‖ ^ q := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ha i hi]
      change (∑ i ∈ s, w i * ‖b i‖ ^ q) ≤
        (∑ i ∈ s, w i * ‖a i‖ ^ q) + (4 * D) * ∑ i ∈ s, w i * ‖b i - a i‖ ^ q
      calc
        _ = μ * ∑ i ∈ s, p i * ‖b i‖ ^ q := (hscale _).symm
        _ ≤ μ * (‖a i₀‖ ^ q + (4 * D) * ∑ i ∈ s, p i * ‖b i - a i₀‖ ^ q) :=
          mul_le_mul_of_nonneg_left hc hμ0
        _ = μ * ‖a i₀‖ ^ q + (4 * D) *
            (μ * ∑ i ∈ s, p i * ‖b i - a i₀‖ ^ q) := by ring
        _ = _ := by rw [hscale, ← hconst, hdiff]
  have h := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset κ)) => hcell c)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_fiberwise] using h

theorem finite_martingale_q_moment_four
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    {Ω : Type*} [Fintype Ω] (n : ℕ)
    (K : Fin n → Type*) [∀ k, Fintype (K k)] [∀ k, DecidableEq (K k)]
    (w : Ω → ℝ) (key : ∀ k, Ω → K k) (M : ℕ → Ω → X)
    (hw : ∀ i, 0 ≤ w i) (hstart : ∀ i, M 0 i = 0)
    (hadapt : ∀ k i j, key k i = key k j → M k.val i = M k.val j)
    (hzero : ∀ k c, ∑ i ∈ Finset.univ.filter (fun i => key k i = c),
      w i • (M (k.val + 1) i - M k.val i) = 0) :
    (∑ i, w i * ‖M n i‖ ^ q) ≤ (4 * D) * ∑ k : Fin n, ∑ i,
      w i * ‖M (k.val + 1) i - M k.val i‖ ^ q := by
  let Q (k : ℕ) := ∑ i, w i * ‖M k i‖ ^ q
  let E (k : ℕ) := ∑ i, w i * ‖M (k + 1) i - M k i‖ ^ q
  have hq0 : q ≠ 0 := by linarith
  have hQ0 : Q 0 = 0 := by simp [Q, hstart, Real.zero_rpow hq0]
  have hstep (k : ℕ) (hk : k < n) : Q (k + 1) ≤ Q k + (4 * D) * E k :=
    finite_fiber_q_moment_step_four hq hq2 hD hsmooth w (key ⟨k, hk⟩)
      (M k) (M (k + 1)) hw (hadapt ⟨k, hk⟩) (hzero ⟨k, hk⟩)
  have ht : ∀ j, j ≤ n → Q j ≤ (4 * D) * ∑ k ∈ Finset.range j, E k := by
    intro j
    induction j with
    | zero => intro hj; simp [hQ0]
    | succ j ih =>
      intro hj
      calc
        Q (j + 1) ≤ Q j + (4 * D) * E j := hstep j (by omega)
        _ ≤ (4 * D) * (∑ k ∈ Finset.range j, E k) + (4 * D) * E j :=
          add_le_add_left (ih (by omega)) _
        _ = (4 * D) * ∑ k ∈ Finset.range (j + 1), E k := by
          rw [Finset.sum_range_succ, mul_add]
  change Q n ≤ (4 * D) * ∑ k : Fin n, E k.val
  rw [Fin.sum_univ_eq_sum_range]
  exact ht n le_rfl

end MarkovSuperreflexivity

end

end OAI
