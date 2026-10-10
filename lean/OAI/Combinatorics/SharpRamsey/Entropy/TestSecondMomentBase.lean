import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.StrongDegreeBudget

namespace OAI

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpLogRamsey.SecondMoment

open SharpRamseyFive.PoissonScore SharpRamseyFive.DyadicMoments

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Fintype H]

lemma abs_pairMean_self_le (rate : ι → ℝ≥0) (s : Finset ι)
    {L lam base c : ℝ} (hL : 0 ≤ L) (hbase0 : 0 ≤ base)
    (hmass : mass rate s = L * lam) (hlam : c ≤ lam) (hbase : c ≤ base) :
    |pairMean rate s s (Real.exp (-L * base))| ≤ 2 * Real.exp (-L * c) := by
  rw [pairMean, ← integral_centeredFactor_mul]
  have hb : Real.exp (-L * base) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  have hn : 0 ≤ ∫ ω, centeredFactor s (Real.exp (-L * base)) ω *
      centeredFactor s (Real.exp (-L * base)) ω ∂batchMeasure rate :=
    integral_nonneg (fun ω => mul_self_nonneg _)
  rw [abs_of_nonneg hn]
  refine (integral_mono (integrable_centeredFactor_mul rate s s _)
    (integrable_centeredFactor rate s _).abs ?_).trans
    (integral_abs_centeredFactor_exp_le rate s hL hmass hlam hbase)
  intro ω
  have ha := abs_centeredFactor_le_one s _ hb ω
  have he := sq_abs (centeredFactor s (Real.exp (-L * base)) ω)
  nlinarith [abs_nonneg (centeredFactor s (Real.exp (-L * base)) ω)]

theorem second_moment_finite (rate : ι → ℝ≥0) (directions : H → Finset ι)
    (R : ℕ) (own : H → Fin R → Bool) (L base : ℝ)
    (lam : H → ℝ) (θ : H → H → ℝ)
    (hL : 1 ≤ L) (hbase : 3/4 ≤ base)
    (hmass : ∀ h, mass rate (directions h) = L * lam h)
    (hlam : ∀ h, 3/4 ≤ lam h)
    (hθ : ∀ h k, 0 ≤ θ h k)
    (hinter : ∀ h k, h ≠ k → mass rate (directions h ∩ directions k) = L * θ h k) :
    (∫ ω, (typicalScore Finset.univ directions (Real.exp (-L * base)) own ω)^2
      ∂scheduleMeasure rate R) ≤
    (Fintype.card H : ℝ) * (2 * Real.exp (-L * (3/4)))^R +
    (L^2 * Real.exp (-L * (3/4)))^R * 2^(R-1) *
      ((∑ h, |lam h - base|^R)^2 + ∑ h, ∑ k, (θ h k)^R) := by
  classical
  let A := L^2 * Real.exp (-L * (3/4))
  let d := (2 * Real.exp (-L * (3/4)))^R
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hp (h k : H) : |pairMean rate (directions h) (directions k)
      (Real.exp (-L * base))|^R ≤
    (if h = k then d else 0) + A^R * 2^(R-1) *
      (|lam h - base|^R * |lam k - base|^R + (θ h k)^R) := by
    by_cases hk : h = k
    · subst k
      have hg := pow_le_pow_left₀ (abs_nonneg _) (abs_pairMean_self_le rate
        (directions h) (by linarith : 0 ≤ L) (by linarith : 0 ≤ base)
        (hmass h) (hlam h) hbase) R
      rw [ite_eq_left rfl]
      exact hg.trans (le_add_of_nonneg_right (by positivity [hθ h h]))
    · have hi := abs_integral_centeredFactor_mul_exp_le rate (directions h)
        (directions k) hL (by norm_num : (0 : ℝ) ≤ 3/4) (hmass h) (hmass k)
        (hinter h k hk) (hlam h) (hlam k) hbase
      rw [integral_centeredFactor_mul] at hi
      change |pairMean rate (directions h) (directions k) (Real.exp (-L * base))| ≤
        A * (|lam h - base| * |lam k - base| + θ h k) at hi
      simp only [ite_eq_right hk, zero_add]
      calc
        _ ≤ (A * (|lam h - base| * |lam k - base| + θ h k))^R :=
          pow_le_pow_left₀ (abs_nonneg _) hi R
        _ = A^R * (|lam h - base| * |lam k - base| + θ h k)^R := mul_pow _ _ _
        _ ≤ A^R * (2^(R-1) * ((|lam h - base| * |lam k - base|)^R + (θ h k)^R)) :=
          mul_le_mul_of_nonneg_left (add_pow_le (by positivity) (hθ h k) R)
            (pow_nonneg hA R)
        _ = _ := by rw [mul_pow]; ring
  have hs := (integral_typicalScore_sq_le rate Finset.univ directions
    (Real.exp (-L * base)) own).trans (Finset.sum_le_sum (fun h _ =>
      Finset.sum_le_sum (fun k _ => hp h k)))
  apply hs.trans_eq
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  simp only [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← pow_two]
  rfl

theorem second_moment_dyadic {J : Type*} (rate : ι → ℝ≥0)
    (directions : H → Finset ι) (R : ℕ) (own : H → Fin R → Bool)
    (L base B C : ℝ) (lam : H → ℝ) (θ : H → H → ℝ)
    (T : Finset J) (a : J → ℝ)
    (hL : 1 ≤ L) (hbase : 3/4 ≤ base) (_hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hR : 200 ≤ R)
    (hmass : ∀ h, mass rate (directions h) = L * lam h)
    (hlam : ∀ h, 3/4 ≤ lam h)
    (hδ : ∀ h, |lam h - base| ≤ 1)
    (hδsum : (∑ h, |lam h - base|^2) ≤ C*B*Real.exp (L/100))
    (hcard : (Fintype.card H : ℝ) ≤ C*B^2)
    (hθ : ∀ h k, 0 ≤ θ h k) (hθmax : ∀ h k, θ h k ≤ 2)
    (hinter : ∀ h k, h ≠ k → mass rate (directions h ∩ directions k) = L * θ h k)
    (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ h k, 0 < θ h k → ∃ i ∈ T, a i ≤ θ h k ∧ θ h k ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : H × H => a i ≤ θ z.1 z.2)).card : ℝ) *
        a i^200 ≤ B^2*Real.exp (L*R/50)) :
    (∫ ω, (typicalScore Finset.univ directions (Real.exp (-L * base)) own ω)^2
      ∂scheduleMeasure rate R) ≤ B^2 *
    (C * (2 * Real.exp (-L * (3/4)))^R +
      (L^2 * Real.exp (-L * (3/4)))^R * 2^(R-1) *
        (C^2 * Real.exp (L/50) + (T.card : ℝ) * 2^R * Real.exp (L*R/50))) := by
  have hs : (∑ h, |lam h - base|^R) ≤ C*B*Real.exp (L/100) := by
    refine (Finset.sum_le_sum (fun h _ =>
      pow_le_pow_of_le_one (abs_nonneg _) (hδ h) (by omega : 2 ≤ R))).trans hδsum
  have hs2 : (∑ h, |lam h - base|^R)^2 ≤ B^2 * (C^2 * Real.exp (L/50)) := by
    calc
      _ ≤ (C*B*Real.exp (L/100))^2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun h _ => by positivity)) hs 2
      _ = _ := by rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; ring_nf
  have ht := higher_moment_le_of_cover (fun z : H × H => θ z.1 z.2) a T
    200 R (by decide) hR (B^2*Real.exp (L*R/50)) 2 (by positivity) (by norm_num)
    (fun z => hθ z.1 z.2) (fun z => hθmax z.1 z.2) ha
    (fun z => hcover z.1 z.2) hcount
  have ht' : (∑ h, ∑ k, (θ h k)^R) ≤ B^2 * ((T.card : ℝ)*2^R*Real.exp (L*R/50)) := by
    calc
      _ ≤ (T.card : ℝ)*2^200*(B^2*Real.exp (L*R/50))*2^(R-200) := by
        simpa only [Fintype.sum_prod_type] using ht
      _ = _ := by
        have hp : (2 : ℝ)^200*2^(R-200) = 2^R := by
          rw [← pow_add, Nat.add_sub_of_le hR]
        calc
          _ = B^2*((T.card : ℝ)*((2 : ℝ)^200*2^(R-200))*Real.exp (L*R/50)) := by ring
          _ = _ := by rw [hp]
  have hd := mul_le_mul_of_nonneg_right hcard
    (pow_nonneg (by positivity : 0 ≤ 2*Real.exp (-L*(3/4))) R)
  have hb := add_le_add hs2 ht'
  have hm := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ (L^2*Real.exp (-L*(3/4)))^R*2^(R-1))
  exact (second_moment_finite rate directions R own L base lam θ hL hbase
    hmass hlam hθ hinter).trans ((add_le_add hd hm).trans_eq (by ring))

lemma second_moment_exponent (L C N : ℝ) (R : ℕ) (hL : 0 ≤ L)
    (_hC : 0 ≤ C) (hN : 0 ≤ N)
    (hd : C*2^R ≤ Real.exp (L*R/20))
    (hp : (2*L^2)^R ≤ Real.exp (L*R/25))
    (hb : C^2*Real.exp (L/50) + N*2^R*Real.exp (L*R/50) ≤ Real.exp (L*R/20))
    (h2 : 2 ≤ Real.exp (L*R/20)) :
    C*(2*Real.exp (-L*(3/4)))^R +
      (L^2*Real.exp (-L*(3/4)))^R*2^(R-1)*
        (C^2*Real.exp (L/50)+N*2^R*Real.exp (L*R/50)) ≤ Real.exp (-(3/5)*(L*R)) := by
  have hP : 0 ≤ L*(R : ℝ) := mul_nonneg hL (Nat.cast_nonneg R)
  have he : (Real.exp (-L*(3/4)))^R = Real.exp (-(3/4)*(L*R)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hd' : C*(2*Real.exp (-L*(3/4)))^R ≤ Real.exp (-(13/20)*(L*R)) := by
    rw [mul_pow, he, ← mul_assoc]
    calc
      _ ≤ Real.exp (L*R/20)*Real.exp (-(3/4)*(L*R)) :=
        mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
      _ = Real.exp (-(7/10)*(L*R)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have ho : (L^2*Real.exp (-L*(3/4)))^R*2^(R-1) ≤
      (2*L^2)^R*Real.exp (-(3/4)*(L*R)) := by
    rw [mul_pow, he, mul_pow]
    have hh : (2 : ℝ)^(R-1) ≤ 2^R :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le R 1)
    nlinarith [mul_le_mul_of_nonneg_left hh
      (show 0 ≤ (L^2)^R*Real.exp (-(3/4)*(L*R)) by positivity)]
  have ht : (L^2*Real.exp (-L*(3/4)))^R*2^(R-1)*
      (C^2*Real.exp (L/50)+N*2^R*Real.exp (L*R/50)) ≤ Real.exp (-(13/20)*(L*R)) := by
    calc
      _ ≤ ((2*L^2)^R*Real.exp (-(3/4)*(L*R)))*Real.exp (L*R/20) :=
        mul_le_mul ho hb (by positivity) (by positivity)
      _ ≤ (Real.exp (L*R/25)*Real.exp (-(3/4)*(L*R)))*Real.exp (L*R/20) := by
        gcongr
      _ = Real.exp (-(33/50)*(L*R)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ 2*Real.exp (-(13/20)*(L*R)) := by linarith
    _ ≤ Real.exp (L*R/20)*Real.exp (-(13/20)*(L*R)) :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma numerical_budgets (L C N : ℝ) (R : ℕ) (hL : 0 ≤ L) (hR : 1 ≤ R)
    (hC : C ≤ Real.exp (L*R/100)) (hC2 : C^2 ≤ Real.exp (L*R/100))
    (hN : N ≤ Real.exp (L*R/100)) (hL2 : 2 ≤ Real.exp (L/100))
    (hLp : 2*L^2 ≤ Real.exp (L/25)) :
    C*2^R ≤ Real.exp (L*R/20) ∧
    (2*L^2)^R ≤ Real.exp (L*R/25) ∧
    C^2*Real.exp (L/50)+N*2^R*Real.exp (L*R/50) ≤ Real.exp (L*R/20) ∧
    2 ≤ Real.exp (L*R/20) := by
  have hLR : L ≤ L*(R : ℝ) := le_mul_of_one_le_right hL (by exact_mod_cast hR)
  have hP : 0 ≤ L*(R : ℝ) := mul_nonneg hL (Nat.cast_nonneg R)
  have h2 : (2 : ℝ)^R ≤ Real.exp (L*R/100) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL2 R
    rw [← Real.exp_nat_mul] at hh
    convert hh using 1
    congr 1
    ring
  have hsmall : 2 ≤ Real.exp (L*R/100) :=
    hL2.trans (Real.exp_le_exp.mpr (by linarith))
  have hfirst : C^2*Real.exp (L/50) ≤ Real.exp (L*R/25) := by
    calc
      _ ≤ Real.exp (L*R/100)*Real.exp (L*R/50) := by gcongr
      _ = Real.exp (3*(L*R)/100) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hsecond : N*2^R*Real.exp (L*R/50) ≤ Real.exp (L*R/25) := by
    calc
      _ ≤ Real.exp (L*R/100)*Real.exp (L*R/100)*Real.exp (L*R/50) := by
        gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  refine ⟨?_, ?_, ?_, hsmall.trans (Real.exp_le_exp.mpr (by nlinarith))⟩
  · calc
      _ ≤ Real.exp (L*R/100)*Real.exp (L*R/100) := by gcongr
      _ = Real.exp (L*R/50) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  · have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 2*L^2) hLp R
    rw [← Real.exp_nat_mul] at hh
    convert hh using 1
    congr 1
    ring
  · calc
      _ ≤ 2*Real.exp (L*R/25) := by linarith
      _ ≤ Real.exp (L*R/100)*Real.exp (L*R/25) :=
        mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end SharpLogRamsey.SecondMoment

namespace SharpLogRamsey.SecondMoment
open MeasureTheory SharpRamseyFive.PoissonScore
open scoped BigOperators NNReal
variable {ι H J : Type*} [Fintype ι] [DecidableEq ι] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in

theorem prepared_pencil_second_moment (rate : ι → ℝ≥0) (directions : H → Finset ι)
    (R : ℕ) (own : H → Fin R → Bool) (L base B C : ℝ)
    (lam : H → ℝ) (θ : H → H → ℝ) (T : Finset J) (a : J → ℝ)
    (hL : 1 ≤ L) (hbase : 3/4 ≤ base) (hB : 0 ≤ B) (hC : 0 ≤ C) (hR : 200 ≤ R)
    (hmass : ∀ h, mass rate (directions h) = L * lam h)
    (hlam : ∀ h, 3/4 ≤ lam h) (hδ : ∀ h, |lam h - base| ≤ 1)
    (hδsum : (∑ h, |lam h - base|^2) ≤ C*B*Real.exp (L/100))
    (hcard : (Fintype.card H : ℝ) ≤ C*B^2)
    (hθ : ∀ h k, 0 ≤ θ h k) (hθmax : ∀ h k, θ h k ≤ 2)
    (hinter : ∀ h k, h ≠ k → mass rate (directions h ∩ directions k) = L * θ h k)
    (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ h k, 0 < θ h k → ∃ i ∈ T, a i ≤ θ h k ∧ θ h k ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : H × H => a i ≤ θ z.1 z.2)).card : ℝ)*a i^200 ≤
        B^2*Real.exp (L*R/50))
    (hd : C*2^R ≤ Real.exp (L*R/20))
    (hp : (2*L^2)^R ≤ Real.exp (L*R/25))
    (hb : C^2*Real.exp (L/50)+(T.card : ℝ)*2^R*Real.exp (L*R/50) ≤ Real.exp (L*R/20))
    (h2 : 2 ≤ Real.exp (L*R/20)) :
    (∫ ω, (typicalScore Finset.univ directions (Real.exp (-L * base)) own ω)^2
      ∂scheduleMeasure rate R) ≤ B^2*Real.exp (-(3/5)*(L*R)) := by
  exact (second_moment_dyadic rate directions R own L base B C lam θ T a
    hL hbase hB hC hR hmass hlam hδ hδsum hcard hθ hθmax hinter ha hcover hcount).trans
    (mul_le_mul_of_nonneg_left (second_moment_exponent L C T.card R (by linarith)
      hC (Nat.cast_nonneg _) hd hp hb h2) (sq_nonneg B))

end SharpLogRamsey.SecondMoment

end

end OAI
