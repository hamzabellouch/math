import OAI.Combinatorics.SquareDifference.WalshMoments

namespace OAI

section
open Finset
open scoped BigOperators
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

lemma symmetrization_moment {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (F : Finset (Finset J)) (f : Finset J → (∀j, X j) → ℝ)
    (hf : ∀U∈F, ExactSupport U (f U))
    (k : ℕ) (hk : ∀U∈F, U.card ≤ k) (r : ℕ) (hr : 1 ≤ r) :
    (𝔼 x, (∑U∈F, f U x)^(2*r)) ≤
      (((4:ℝ)*(2:ℝ)^(2*r))^k)^r*(𝔼 x, (∑U∈F, f U x^2)^r) := by
  classical
  let D := fun U x y => copyDifference U (f U) x y
  let S := fun x => ∑U∈F, f U x^2
  let C : ℝ := (2:ℝ)^(2*r)
  let B : ℝ := (4*C)^k
  have hC : 1 ≤ C := one_le_pow₀ (by norm_num)
  have hB : 0 ≤ B := by positivity
  have hS : ∀x, 0 ≤ S x := fun x => sum_nonneg fun U _ => sq_nonneg (f U x)
  have hmean (x : ∀j, X j) : (𝔼 y, ∑U∈F, D U x y)=∑U∈F, f U x := by
    rw [expect_sum_comm]
    apply sum_congr rfl
    intro U hU
    exact copyDifference_mean U (f U) (hf U hU) x
  have hsign :
      (𝔼 x, 𝔼 y, (∑U∈F, D U x y)^(2*r))=
        𝔼 x, 𝔼 y, 𝔼 e : J → Bool,
          (walsh univ (fun U => if U∈F then D U x y else 0) e)^(2*r) := by
    have he (e : J → Bool) :
        (𝔼 x, 𝔼 y, (walsh univ (fun U => if U∈F then D U x y else 0) e)^(2*r))=
          𝔼 x, 𝔼 y, (∑U∈F, D U x y)^(2*r) := by
      simp only [walsh_family]
      have hp x y U : D U x y*boolChar U e=D U (hybrid e x y) (hybrid e y x) := by
        dsimp only [D]
        rw [copyDifference_swap, mul_comm]
      simp only [hp]
      exact expect_copySwap e (fun x y => (∑U∈F, D U x y)^(2*r))
    conv_rhs => arg 2; ext x; rw [expect_comm]
    conv_rhs => rw [expect_comm]
    simp only [he, Fintype.expect_const]
  have hpoint (x y : ∀j, X j) :
      (𝔼 e : J → Bool, (walsh univ (fun U => if U∈F then D U x y else 0) e)^(2*r)) ≤
        B^r*(𝔼 e : J → Bool, (S (hybrid e x y))^r) := by
    apply (walsh_hypercontractivity univ _ r hr).trans
    have he := difference_energy_bound F f k hk C hC x y
    calc
      _ ≤ (B*(𝔼 e : J → Bool, S (hybrid e x y)))^r :=
        pow_le_pow_left₀ (walshEnergy_nonneg _ _ (by positivity) _) he r
      _ = B^r*(𝔼 e : J → Bool, S (hybrid e x y))^r := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (expect_pow_le (fun e => S (hybrid e x y)) (fun e => hS _) r) (pow_nonneg hB _)
  change _ ≤ B^r*(𝔼 x, S x^r)
  calc
    _ ≤ (𝔼 x, 𝔼 y, (∑U∈F, D U x y)^(2*r)) := by
      apply expect_le_expect
      intro x _
      rw [← hmean x]
      exact expect_even_pow_le (fun y => ∑U∈F, D U x y) r
    _ = _ := hsign
    _ ≤ (𝔼 x, 𝔼 y, B^r*(𝔼 e : J → Bool, (S (hybrid e x y))^r)) := by
      apply expect_le_expect
      intro x _
      exact expect_le_expect fun y _ => hpoint x y
    _ = B^r*(𝔼 x, S x^r) := by
      simp only [← mul_expect]
      congr 1
      conv_lhs => arg 2; ext x; rw [expect_comm]
      rw [expect_comm]
      have he (e : J → Bool) : (𝔼 x, 𝔼 y, S (hybrid e x y)^r)=𝔼 x, S x^r :=
        expect_hybrid e (fun x => S x^r)
      simp only [he, Fintype.expect_const]

lemma sum_pow_tuples {I : Type*} [Fintype I] (a : I → ℝ) (r : ℕ) :
    (∑i, a i)^r=∑t : Fin r → I, ∏j, a (t j) := by
  have hh := Fintype.prod_sum (fun (_ : Fin r) (i : I) => a i)
  simpa only [prod_const, card_univ, Fintype.card_fin] using hh

lemma expect_condition {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (W : Finset J) (h g : (∀j, X j) → ℝ)
    (hh : ∀x y, (∀j∈W, x j=y j) → h x=h y) :
    (𝔼 x, h x*g x) = 𝔼 x, h x*(𝔼 y, g (hybrid (fun j => decide (j∈W)) x y)) := by
  have he x y : h (hybrid (fun j => decide (j∈W)) x y)=h x := by
    apply hh
    intro j hj
    simp [hybrid, hj]
  have hp := expect_hybrid (fun j => decide (j∈W)) (fun x => h x*g x)
  simp only [he, ← mul_expect] at hp
  exact hp.symm

lemma square_moment_step {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (U : I → Finset J) (f : I → (∀j, X j) → ℝ)
    (hf : ∀i, ∀x y, (∀j∈U i, x j=y j) → f i x=f i y)
    (k : ℕ) (hk : ∀i, (U i).card ≤ k)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hcond : ∀ (W : Finset J) x,
      (𝔼 y, ∑i, f i (hybrid (fun j => decide (j∈W)) x y)^2) ≤ A*D^W.card)
    (r : ℕ) :
    (𝔼 x, (∑i, f i x^2)^(r+1)) ≤ (A*D^(r*k))*(𝔼 x, (∑i, f i x^2)^r) := by
  classical
  let S := fun x => ∑i, f i x^2
  let h := fun (t : Fin r → I) x => ∏j, f (t j) x^2
  have hh t x : 0 ≤ h t x := prod_nonneg fun j _ => sq_nonneg _
  have hpow x : S x^r=∑t : Fin r → I, h t x := sum_pow_tuples _ r
  have hbound (t : Fin r → I) :
      (𝔼 x, h t x*S x) ≤ (A*D^(r*k))*(𝔼 x, h t x) := by
    let W : Finset J := univ.biUnion (fun j => U (t j))
    have hw : W.card ≤ r*k := by
      calc
        _ ≤ ∑j : Fin r, (U (t j)).card := card_biUnion_le
        _ ≤ ∑_j : Fin r, k := sum_le_sum fun j _ => hk (t j)
        _ = _ := by simp
    have hdep x y (hxy : ∀j∈W, x j=y j) : h t x=h t y := by
      apply prod_congr rfl
      intro j _
      rw [hf (t j) x y (fun a ha => hxy a (mem_biUnion.mpr ⟨j,mem_univ j,ha⟩))]
    calc
      _ = (𝔼 x, h t x*(𝔼 y, S (hybrid (fun j => decide (j∈W)) x y))) :=
        expect_condition W (h t) S hdep
      _ ≤ (𝔼 x, h t x*(A*D^(r*k))) := by
        apply expect_le_expect
        intro x _
        apply mul_le_mul_of_nonneg_left _ (hh t x)
        exact (hcond W x).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hw) hA)
      _ = _ := by rw [← expect_mul]; ring
  change (𝔼 x, S x^(r+1)) ≤ _*(𝔼 x, S x^r)
  calc
    _ = ∑t : Fin r → I, (𝔼 x, h t x*S x) := by
      simp only [pow_succ, hpow, sum_mul, expect_sum_comm]
    _ ≤ ∑t : Fin r → I, (A*D^(r*k))*(𝔼 x, h t x) :=
      sum_le_sum fun t _ => hbound t
    _ = (A*D^(r*k))*(𝔼 x, S x^r) := by
      rw [← mul_sum, ← expect_sum_comm]
      simp only [← hpow]

lemma square_moment_bound {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
    {X : J → Type*} [∀j, Fintype (X j)] [∀j, Nonempty (X j)]
    (U : I → Finset J) (f : I → (∀j, X j) → ℝ)
    (hf : ∀i, ∀x y, (∀j∈U i, x j=y j) → f i x=f i y)
    (k : ℕ) (hk : ∀i, (U i).card ≤ k)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hcond : ∀ (W : Finset J) x,
      (𝔼 y, ∑i, f i (hybrid (fun j => decide (j∈W)) x y)^2) ≤ A*D^W.card)
    (r : ℕ) :
    (𝔼 x, (∑i, f i x^2)^r) ≤ (A*D^(r*k))^r := by
  have hD0 : 0 ≤ D := by linarith
  have hbase : 0 ≤ A*D^(r*k) := mul_nonneg hA (pow_nonneg hD0 _)
  have hind (t : ℕ) (ht : t ≤ r) :
      (𝔼 x, (∑i, f i x^2)^t) ≤ (A*D^(r*k))^t := by
    induction t with
    | zero => simp only [pow_zero, Fintype.expect_const, le_refl]
    | succ t ih =>
      have ht' : t ≤ r := by omega
      have hi := ih ht'
      have he := square_moment_step U f hf k hk A D hA hD hcond t
      apply he.trans
      calc
        _ ≤ (A*D^(r*k))*(A*D^(r*k))^t := by
          apply mul_le_mul _ hi
            (expect_nonneg fun x _ => pow_nonneg (sum_nonneg fun i _ => sq_nonneg _) _) hbase
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.mul_le_mul_right k ht')) hA
        _ = _ := by rw [pow_succ]; ring
  exact hind r le_rfl

lemma synthesis_norm_sq_bound {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : I → E) (D δ : ℝ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖inner ℂ (v i) (v j)‖ ≤ (if i = j then D else 0) + δ)
    (a : I → ℂ) :
    ‖∑ i, a i • v i‖ ^ 2 ≤ (D + Fintype.card I * δ) * ∑ i, ‖a i‖ ^ 2 := by
  classical
  have hcs : (∑ i, ‖a i‖) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, ‖a i‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset I)
      (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
  calc
    ‖∑ i, a i • v i‖ ^ 2 =
        (∑ i, ∑ j, (starRingEnd ℂ) (a i) * a j * inner ℂ (v i) (v j)).re := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
      change (inner ℂ _ _).re = _
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_sum]
      rw [sum_comm]
      congr 1
      apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro j _
      ring
    _ ≤ ∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ‖inner ℂ (v i) (v j)‖ := by
      simp only [Complex.re_sum]
      apply sum_le_sum; intro i _
      apply sum_le_sum; intro j _
      simpa only [norm_mul, Complex.norm_conj] using
        Complex.re_le_norm ((starRingEnd ℂ) (a i) * a j * inner ℂ (v i) (v j))
    _ ≤ ∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ((if i = j then D else 0) + δ) := by
      apply sum_le_sum; intro i _
      apply sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_left (hgram i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (∑ i, ‖a i‖ ^ 2) + δ * (∑ i, ‖a i‖) ^ 2 := by
      simp_rw [mul_add, sum_add_distrib]
      simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
      simp only [← sum_mul, ← mul_sum]
      simp only [← sq]
      ring
    _ ≤ (D + Fintype.card I * δ) * ∑ i, ‖a i‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hcs hδ]

lemma analysis_of_synthesis {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : I → E) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ a : I → ℂ, ‖∑ i, a i • v i‖ ^ 2 ≤ C * ∑ i, ‖a i‖ ^ 2)
    (f : E) : ∑ i, ‖inner ℂ (v i) f‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  classical
  let a : I → ℂ := fun i => inner ℂ (v i) f
  let S : E := ∑ i, a i • v i
  let t : ℝ := ∑ i, ‖a i‖ ^ 2
  have ht : 0 ≤ t := sum_nonneg fun _ _ => sq_nonneg _
  have heq : (inner ℂ S f).re = t := by
    simp only [S, sum_inner, inner_smul_left, Complex.re_sum, t]
    change (∑ i, ((starRingEnd ℂ) (a i) * a i).re) = _
    apply sum_congr rfl; intro i _
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have htf : t ≤ ‖S‖ * ‖f‖ := by
    rw [← heq]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hs : ‖S‖ ^ 2 ≤ C * t := h a
  have hc : t ^ 2 ≤ C * t * ‖f‖ ^ 2 := by
    calc
      t ^ 2 ≤ (‖S‖ * ‖f‖) ^ 2 := pow_le_pow_left₀ ht htf 2
      _ = ‖S‖ ^ 2 * ‖f‖ ^ 2 := mul_pow _ _ _
      _ ≤ C * t * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  change t ≤ C * ‖f‖ ^ 2
  by_cases ht0 : t = 0
  · rw [ht0]
    exact mul_nonneg hC (sq_nonneg _)
  · exact le_of_mul_le_mul_left (by nlinarith [hc]) (lt_of_le_of_ne ht (Ne.symm ht0))

noncomputable def expPhase (t : ℝ) : ℂ := Real.fourierChar t

noncomputable def circleDistance (t : ℝ) : ℝ := |t - round t|

@[simp] lemma expPhase_zero : expPhase 0 = 1 := by simp [expPhase]
@[simp] lemma norm_expPhase (t : ℝ) : ‖expPhase t‖ = 1 := Circle.norm_coe _

lemma expPhase_add (s t : ℝ) : expPhase (s+t) = expPhase s * expPhase t := by
  simp [expPhase, AddChar.map_add_eq_mul]

lemma expPhase_neg (t : ℝ) : expPhase (-t) = conj (expPhase t) := by
  simp only [expPhase, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

lemma expPhase_sub (s t : ℝ) : expPhase (s-t) = expPhase s * conj (expPhase t) := by
  rw [sub_eq_add_neg, expPhase_add, expPhase_neg]

lemma expPhase_nat_mul (t : ℝ) (n : ℕ) : expPhase (n*t) = expPhase t^n := by
  simpa only [expPhase, nsmul_eq_mul, Circle.coe_pow] using congrArg (fun z : Circle => (z : ℂ))
    (AddChar.map_nsmul_eq_pow Real.fourierChar n t)

lemma expPhase_int (n : ℤ) : expPhase n = 1 := by
  change Complex.exp (↑(2 * Real.pi * (n : ℝ)) * Complex.I) = 1
  rw [show (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
    (n : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

lemma expPhase_sub_int (t : ℝ) (n : ℤ) : expPhase (t-n) = expPhase t := by
  rw [expPhase_sub, expPhase_int, map_one, mul_one]

lemma circleDistance_nonneg (t : ℝ) : 0 ≤ circleDistance t := abs_nonneg _

lemma circleDistance_le_half (t : ℝ) : circleDistance t ≤ 1/2 := abs_sub_round t

lemma circleDistance_le_abs_sub_int (t : ℝ) (n : ℤ) : circleDistance t ≤ |t-n| :=
  round_le t n

lemma circleDistance_le_abs (t : ℝ) : circleDistance t ≤ |t| := by
  simpa using circleDistance_le_abs_sub_int t 0

lemma circleDistance_sub_le (s t : ℝ) : circleDistance (s-t) ≤
    |(s-round s)-(t-round t)| := by
  convert circleDistance_le_abs_sub_int (s-t) (round s-round t) using 1
  push_cast
  congr 1
  ring

lemma expPhase_sub_one_lower (t : ℝ) : 4*circleDistance t ≤ ‖expPhase t-1‖ := by
  let u := t-(round t : ℝ)
  have hu : |u| ≤ 1/2 := abs_sub_round t
  have hp := Real.pi_pos
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi*u)
    (by rw [abs_mul, abs_of_pos hp]; nlinarith)
  rw [abs_mul, abs_of_pos hp] at hs
  have hmul : 2/Real.pi*(Real.pi*|u|)=2*|u| := by field_simp
  rw [hmul] at hs
  rw [← expPhase_sub_int t (round t)]
  change 4*|u| ≤ ‖Complex.exp (↑(2*Real.pi*u)*Complex.I)-1‖
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2*Real.pi*u/2=Real.pi*u by ring, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  linarith

lemma linear_phase_sum_trivial (t : ℝ) (L : ℕ) :
    ‖∑ m ∈ range L, expPhase (m*t)‖ ≤ L := by
  calc
    _ ≤ ∑ m ∈ range L, ‖expPhase (m*t)‖ := norm_sum_le _ _
    _ = L := by simp

lemma linear_phase_sum_distance (t : ℝ) (L : ℕ) (ht : 0 < circleDistance t) :
    ‖∑ m ∈ range L, expPhase (m*t)‖ ≤ 1 / (2*circleDistance t) := by
  have hz : expPhase t ≠ 1 := by
    intro he
    have := expPhase_sub_one_lower t
    rw [he, sub_self, norm_zero] at this
    linarith
  simp_rw [expPhase_nat_mul]
  rw [geom_sum_eq hz, norm_div]
  have hn : ‖expPhase t ^ L - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖expPhase t^L‖+‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp; norm_num
  calc
    _ ≤ 2 / (4*circleDistance t) :=
      div_le_div₀ (by positivity) hn (by positivity) (expPhase_sub_one_lower t)
    _ = 1 / (2*circleDistance t) := by ring

lemma finite_phase_analysis {I : Type*} [Fintype I] [DecidableEq I]
    (θ : I → ℝ) (L : ℕ) (d : ℝ) (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ circleDistance (θ j-θ i))
    (f : Fin L → ℂ) :
    (∑ i, ‖∑ n : Fin L, f n * expPhase (-(n : ℝ)*θ i)‖ ^ 2) ≤
      ((L : ℝ) + Fintype.card I / (2*d)) * ∑ n, ‖f n‖ ^ 2 := by
  let v : I → EuclideanSpace ℂ (Fin L) := fun i => WithLp.toLp 2
    (fun n : Fin L => expPhase ((n : ℝ)*θ i))
  let f' : EuclideanSpace ℂ (Fin L) := WithLp.toLp 2 f
  have hinner (i j : I) : inner ℂ (v i) (v j) =
      ∑ n ∈ range L, expPhase ((n : ℝ)*(θ j-θ i)) := by
    rw [PiLp.inner_apply]
    simp only [v, RCLike.inner_apply]
    simp_rw [← expPhase_sub, ← mul_sub]
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => expPhase ((n : ℝ)*(θ j-θ i))) L
  have hg (i j : I) : ‖inner ℂ (v i) (v j)‖ ≤
      (if i=j then (L : ℝ) else 0) + 1/(2*d) := by
    rw [hinner]
    by_cases hij : i=j
    · subst j
      simp only [sub_self, mul_zero, expPhase_zero, sum_const, card_range,
        nsmul_eq_mul, mul_one, Complex.norm_natCast, ite_true]
      exact le_add_of_nonneg_right (by positivity)
    · rw [ite_eq_right hij, zero_add]
      exact (linear_phase_sum_distance _ L (hd.trans_le (hsep i j hij))).trans
        (one_div_le_one_div_of_le (by positivity) (by linarith [hsep i j hij]))
  have hs : ∀ a : I → ℂ, ‖∑ i, a i • v i‖ ^ 2 ≤
      ((L : ℝ)+Fintype.card I*(1/(2*d))) * ∑ i, ‖a i‖ ^ 2 :=
    synthesis_norm_sq_bound v L (1/(2*d)) (by positivity) hg
  have h := analysis_of_synthesis v _ (by positivity) hs f'
  have he (i : I) : inner ℂ (v i) f' =
      ∑ n : Fin L, f n * expPhase (-(n : ℝ)*θ i) := by
    simp only [PiLp.inner_apply, f', v, RCLike.inner_apply]
    simp_rw [← expPhase_neg, neg_mul]
  rw [PiLp.norm_sq_eq_of_L2] at h
  simp only [he, f'] at h
  simpa only [div_eq_mul_inv, one_mul] using h

lemma finite_phase_analysis_average {I : Type*} [Fintype I] [DecidableEq I]
    (θ : I → ℝ) (L : ℕ) (hL : 0 < L) (d : ℝ) (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ circleDistance (θ j-θ i))
    (f : Fin L → ℂ) :
    (∑ i, ‖(L : ℂ)⁻¹ * ∑ n : Fin L, f n * expPhase (-(n : ℝ)*θ i)‖ ^ 2) ≤
      (1 + Fintype.card I / (2*d*L)) * ((L : ℝ)⁻¹ * ∑ n, ‖f n‖ ^ 2) := by
  have h := finite_phase_analysis θ L d hd hsep f
  simp only [norm_mul, norm_inv, Complex.norm_natCast, mul_pow, ← mul_sum]
  have hL' : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  calc
    _ ≤ (L : ℝ)⁻¹ ^ 2 * (((L : ℝ)+Fintype.card I/(2*d))*∑ n, ‖f n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by field_simp

lemma stdAddChar_eq_expPhase {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a=expPhase ((a.val : ℝ)/p) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  ring

lemma expPhase_sum {I : Type*} (s : Finset I) (f : I → ℝ) :
    expPhase (∑ i∈s, f i)=∏ i∈s, expPhase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [sum_insert hi, prod_insert hi, expPhase_add, ih]

variable {J : Type*} [Fintype J]

variable (p : J → ℕ) [∀ j, NeZero (p j)]

abbrev ResidueSpace := ∀ j, ZMod (p j)

noncomputable def prodChar (a z : ResidueSpace p) : ℂ :=
  ∏ j, ZMod.stdAddChar (a j*z j)

noncomputable def frequencyAngle (a : ResidueSpace p) : ℝ :=
  ∑ j, (a j).val/(p j : ℝ)

noncomputable def primeSupport (a : ResidueSpace p) : Finset J :=
  univ.filter fun j => a j ≠ 0

noncomputable def supportDenominator (a : ResidueSpace p) : ℕ :=
  ∏ j∈primeSupport p a, p j

@[simp] lemma prodChar_zero (z : ResidueSpace p) : prodChar p 0 z=1 := by
  simp [prodChar, AddChar.map_zero_eq_one]
@[simp] lemma prodChar_zero_right (a : ResidueSpace p) : prodChar p a 0=1 := by
  simp [prodChar, AddChar.map_zero_eq_one]
lemma prodChar_add (a b z : ResidueSpace p) :
    prodChar p (a+b) z=prodChar p a z*prodChar p b z := by
  simp only [prodChar, Pi.add_apply, add_mul, AddChar.map_add_eq_mul, prod_mul_distrib]
lemma prodChar_add_right (a z w : ResidueSpace p) :
    prodChar p a (z+w)=prodChar p a z*prodChar p a w := by
  simp only [prodChar, Pi.add_apply, mul_add, AddChar.map_add_eq_mul, prod_mul_distrib]
lemma prodChar_neg (a z : ResidueSpace p) : prodChar p (-a) z=conj (prodChar p a z) := by
  simp only [prodChar, Pi.neg_apply, neg_mul, AddChar.map_neg_eq_conj, map_prod]
lemma prodChar_sub (a b z : ResidueSpace p) :
    prodChar p (a-b) z=prodChar p a z*conj (prodChar p b z) := by
  rw [sub_eq_add_neg, prodChar_add, prodChar_neg]
lemma prodChar_symm (a z : ResidueSpace p) : prodChar p a z=prodChar p z a := by
  simp only [prodChar, mul_comm]
lemma norm_prodChar (a z : ResidueSpace p) : ‖prodChar p a z‖=1 := by
  simp only [prodChar, norm_prod, ZMod.stdAddChar_apply, Circle.norm_coe, prod_const_one]
lemma prodChar_nat_diagonal (a : ResidueSpace p) (n : ℕ) :
    prodChar p a (fun j => (n : ZMod (p j)))=expPhase (n*frequencyAngle p a) := by
  simp only [prodChar, frequencyAngle, mul_sum, expPhase_sum]
  apply prod_congr rfl; intro j _
  rw [expPhase_nat_mul, ← stdAddChar_eq_expPhase]
  simpa only [nsmul_eq_mul, Nat.cast_comm, mul_comm] using
    AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := p j)) n (a j)

lemma prodChar_one_diagonal (a : ResidueSpace p) :
    prodChar p a (fun _ => 1)=expPhase (frequencyAngle p a) := by
  simpa using prodChar_nat_diagonal p a 1

lemma prodChar_eq_one_iff (a : ResidueSpace p) :
    (∀ z, prodChar p a z=1) ↔ a=0 := by
  classical
  constructor
  · intro h
    funext j
    have hj := h (Pi.single j 1)
    have he : prodChar p a (Pi.single j 1)=ZMod.stdAddChar (a j) := by
      unfold prodChar
      rw [prod_eq_single j]
      · simp only [Pi.single_eq_same, mul_one]
      · intro i _ hij
        simp only [Pi.single_eq_of_ne hij, mul_zero, AddChar.map_zero_eq_one]
      · simp
    rw [he, ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := p j))] at hj
    exact ZMod.injective_stdAddChar hj
  · rintro rfl z
    exact prodChar_zero p z

lemma frequencyAngle_separates
    (hp : Pairwise fun i j => (p i).Coprime (p j)) (a b : ResidueSpace p)
    (he : expPhase (frequencyAngle p a-frequencyAngle p b)=1) : a=b := by
  classical
  let : NeZero (∏ j, p j) := ⟨prod_ne_zero_iff.mpr (fun j _ => NeZero.ne (p j))⟩
  have h1 : prodChar p (a-b) (fun j => (1 : ZMod (p j)))=1 := by
    rw [prodChar_sub, prodChar_one_diagonal, prodChar_one_diagonal]
    simpa only [← expPhase_sub] using he
  apply sub_eq_zero.mp
  apply (prodChar_eq_one_iff p (a-b)).mp
  intro z
  let e := ZMod.prodEquivPi p hp
  let n : ℕ := (e.symm z).val
  have hn : (fun j => (n : ZMod (p j)))=z := by
    have hz := e.apply_symm_apply z
    convert hz using 1
    funext j
    simp only [e, ZMod.prodEquivPi_apply]
    rw [← ZMod.natCast_zmod_val (e.symm z), map_natCast]
  rw [← hn, prodChar_nat_diagonal]
  rw [prodChar_one_diagonal] at h1
  rw [expPhase_nat_mul, h1, one_pow]

lemma complex_expect_prod_pi [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
    (f : ∀ j, X j → ℂ) :
    (𝔼 x : ∀ j, X j, ∏ j, f j (x j))=∏ j, (𝔼 t : X j, f j t) := by
  classical
  simp only [expect_eq_sum_div_card, card_univ, prod_div_distrib,
    Fintype.card_pi, Nat.cast_prod]
  rw [Fintype.prod_sum]

omit [Fintype J] in
lemma prime_char_expect (j : J) (a : ZMod (p j)) :
    (𝔼 z : ZMod (p j), ZMod.stdAddChar (a*z))=if a=0 then 1 else 0 := by
  rw [expect_eq_sum_div_card]
  simp_rw [mul_comm a]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (p j))]
  simp only [card_univ, ZMod.card]
  split_ifs <;> simp_all

lemma prodChar_expect [DecidableEq J] (a : ResidueSpace p) :
    (𝔼 z, prodChar p a z)=if a=0 then 1 else 0 := by
  classical
  unfold prodChar
  rw [complex_expect_prod_pi (fun j (z : ZMod (p j)) => ZMod.stdAddChar (a j*z))]
  simp_rw [prime_char_expect]
  by_cases ha : a=0
  · simp [ha]
  · rw [ite_eq_right ha]
    have hex : ∃ j, a j ≠ 0 := by
      by_contra! h
      exact ha (funext h)
    obtain ⟨j, hj⟩ := hex
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

lemma prodChar_orthogonal [DecidableEq J] (a b : ResidueSpace p) :
    (𝔼 z, prodChar p a z*conj (prodChar p b z))=if a=b then 1 else 0 := by
  simp_rw [← prodChar_sub]
  rw [prodChar_expect]
  simp only [sub_eq_zero]

noncomputable def supportNumerator (a : ResidueSpace p) : ℕ := by
  classical
  exact ∑ j∈primeSupport p a, (a j).val * ∏ i∈(primeSupport p a).erase j, p i

lemma supportDenominator_pos (a : ResidueSpace p) : 0 < supportDenominator p a := by
  unfold supportDenominator
  exact prod_pos fun j _ => Nat.pos_of_ne_zero (NeZero.ne (p j))

lemma frequencyAngle_numerator (a : ResidueSpace p) :
    frequencyAngle p a = (supportNumerator p a : ℝ)/supportDenominator p a := by
  classical
  have hp0 (j : J) : (p j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (p j))
  have hq : (supportDenominator p a : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (supportDenominator_pos p a))
  apply (eq_div_iff hq).mpr
  have hs : frequencyAngle p a = ∑ j∈primeSupport p a, (a j).val/(p j : ℝ) := by
    unfold frequencyAngle primeSupport
    symm
    apply sum_filter_of_ne
    intro j _ hj
    contrapose! hj
    simp [hj]
  rw [hs, sum_mul]
  unfold supportNumerator
  push_cast
  apply sum_congr rfl; intro j hj
  have he : supportDenominator p a = p j * ∏ i∈(primeSupport p a).erase j, p i :=
    (mul_prod_erase _ _ hj).symm
  rw [he]
  push_cast
  field_simp [hp0 j]

lemma frequencyAngle_difference (a b : ResidueSpace p) :
    frequencyAngle p a-frequencyAngle p b =
      ((supportNumerator p a : ℤ)*supportDenominator p b-
        supportNumerator p b*supportDenominator p a : ℤ)/
        ((supportDenominator p a*supportDenominator p b : ℕ) : ℝ) := by
  rw [frequencyAngle_numerator, frequencyAngle_numerator]
  have ha : (supportDenominator p a : ℝ) ≠ 0 := by positivity [supportDenominator_pos p a]
  have hb : (supportDenominator p b : ℝ) ≠ 0 := by positivity [supportDenominator_pos p b]
  push_cast
  field_simp [ha, hb]

lemma frequency_difference_not_dvd
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (a b : ResidueSpace p) (hab : a ≠ b) :
    ¬ ((supportDenominator p a*supportDenominator p b : ℕ) : ℤ) ∣
      ((supportNumerator p a : ℤ)*supportDenominator p b-
        supportNumerator p b*supportDenominator p a) := by
  rintro ⟨k, hk⟩
  apply hab
  apply frequencyAngle_separates p hp
  rw [frequencyAngle_difference, hk]
  have hq : ((supportDenominator p a*supportDenominator p b : ℕ) : ℝ) ≠ 0 := by
    positivity [supportDenominator_pos p a, supportDenominator_pos p b]
  push_cast at hq ⊢
  rw [mul_div_cancel_left₀ _ hq]
  exact expPhase_int k

lemma frequencyAngle_remainder (a : ResidueSpace p) :
    expPhase (frequencyAngle p a) =
      expPhase ((supportNumerator p a % supportDenominator p a : ℕ)/
        (supportDenominator p a : ℝ)) := by
  rw [frequencyAngle_numerator]
  have hq : (supportDenominator p a : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (supportDenominator_pos p a))
  have he : (supportNumerator p a : ℝ)/supportDenominator p a =
      (supportNumerator p a % supportDenominator p a : ℕ)/(supportDenominator p a : ℝ)+
        (supportNumerator p a / supportDenominator p a : ℕ) := by
    apply (div_eq_iff hq).mpr
    rw [add_mul, div_mul_cancel₀ _ hq]
    norm_cast
    simpa only [mul_comm] using (Nat.mod_add_div (supportNumerator p a) (supportDenominator p a)).symm
  rw [he, expPhase_add]
  have hi : expPhase ((supportNumerator p a / supportDenominator p a : ℕ) : ℝ)=1 := by
    exact_mod_cast expPhase_int (supportNumerator p a / supportDenominator p a : ℕ)
  rw [hi, mul_one]

lemma bounded_frequency_card
    (hp : Pairwise fun i j => (p i).Coprime (p j)) (Q : ℕ)
    (F : Finset (ResidueSpace p))
    (hF : ∀ a∈F, supportDenominator p a ≤ Q) : F.card ≤ Q^2 := by
  classical
  let e : F → Fin Q × Fin Q := fun a =>
    (⟨supportDenominator p a-1, by
      have := supportDenominator_pos p a
      have := hF a a.property
      omega⟩,
     ⟨supportNumerator p a % supportDenominator p a,
      (Nat.mod_lt _ (supportDenominator_pos p a)).trans_le (hF a a.property)⟩)
  have he : Function.Injective e := by
    intro a b hab
    have hq : supportDenominator p a=supportDenominator p b := by
      have h := congrArg (fun t : Fin Q × Fin Q => t.1.val) hab
      have := supportDenominator_pos p a
      have := supportDenominator_pos p b
      change supportDenominator p a-1=supportDenominator p b-1 at h
      omega
    have hn : supportNumerator p a % supportDenominator p a=
        supportNumerator p b % supportDenominator p b :=
      congrArg (fun t : Fin Q × Fin Q => t.2.val) hab
    apply Subtype.ext
    apply frequencyAngle_separates p hp
    rw [expPhase_sub, frequencyAngle_remainder, frequencyAngle_remainder, hn, hq]
    rw [Complex.mul_conj', norm_expPhase]
    norm_num
  have hcard := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, sq] using hcard

lemma rational_circleDistance_lower (k : ℤ) (q : ℕ) (hq : 0 < q)
    (hnd : ¬ (q : ℤ) ∣ k) : 1/(q : ℝ) ≤ circleDistance ((k : ℝ)/q) := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  let n := round ((k : ℝ)/q)
  have hn : k-(q : ℤ)*n ≠ 0 := by
    intro he
    apply hnd
    exact ⟨n, by linarith⟩
  have hI : (1 : ℤ) ≤ |k-(q : ℤ)*n| := by
    have := abs_pos.mpr hn
    omega
  have hR : (1 : ℝ) ≤ |(k : ℝ)-(q : ℝ)*(n : ℝ)| := by exact_mod_cast hI
  have he : |(k : ℝ)-(q : ℝ)*(n : ℝ)| = (q : ℝ)*circleDistance ((k : ℝ)/q) := by
    calc
      _ = |(q : ℝ)*((k : ℝ)/q-(n : ℝ))| := by congr 1; field_simp
      _ = _ := by rw [abs_mul, abs_of_pos hqR]; rfl
  rw [he] at hR
  exact (div_le_iff₀ hqR).mpr (by simpa only [mul_comm] using hR)

lemma frequency_spacing (hp : Pairwise fun i j => (p i).Coprime (p j))
    (a b : ResidueSpace p) (hab : a ≠ b) (Q : ℕ)
    (ha : supportDenominator p a ≤ Q) (hb : supportDenominator p b ≤ Q)
    (m : ℕ) (hma : m.Coprime (supportDenominator p a))
    (hmb : m.Coprime (supportDenominator p b)) :
    1/(Q : ℝ)^2 ≤ circleDistance (m*frequencyAngle p a-m*frequencyAngle p b) := by
  have hQ : 0 < Q := (supportDenominator_pos p a).trans_le ha
  let q := supportDenominator p a*supportDenominator p b
  let k : ℤ := (supportNumerator p a : ℤ)*supportDenominator p b-
    supportNumerator p b*supportDenominator p a
  have hq : 0 < q := Nat.mul_pos (supportDenominator_pos p a) (supportDenominator_pos p b)
  have hmk : ¬ (q : ℤ) ∣ (m : ℤ)*k := by
    intro h
    have hc : IsCoprime (q : ℤ) (m : ℤ) := (hma.mul_right hmb).symm.cast
    exact frequency_difference_not_dvd p hp a b hab (hc.dvd_of_dvd_mul_left h)
  have hr := rational_circleDistance_lower ((m : ℤ)*k) q hq hmk
  have he : m*frequencyAngle p a-m*frequencyAngle p b=((m : ℤ)*k : ℤ)/(q : ℝ) := by
    rw [← mul_sub, frequencyAngle_difference]
    dsimp only [k, q]
    push_cast
    ring
  rw [he]
  apply le_trans _ hr
  apply one_div_le_one_div_of_le (Nat.cast_pos.mpr hq)
  have hqq := Nat.mul_le_mul ha hb
  simpa only [q, sq, Nat.cast_mul] using (show (supportDenominator p a : ℝ)*(supportDenominator p b : ℝ) ≤ (Q : ℝ)*(Q : ℝ) by exact_mod_cast hqq)

lemma arithmetic_phase_analysis {I : Type*} [Fintype I] [DecidableEq I]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (a : I → ResidueSpace p) (hinj : Function.Injective a) (Q : ℕ) (hQ : 0 < Q)
    (ha : ∀ i, supportDenominator p (a i) ≤ Q)
    (m : ℕ) (hm : ∀ i, m.Coprime (supportDenominator p (a i)))
    (L : ℕ) (f : Fin L → ℂ) :
    (∑ i, ‖∑ n : Fin L, f n*expPhase (-(n : ℝ)*(m*frequencyAngle p (a i)))‖^2) ≤
      (L+(Q : ℝ)^4/2)*∑n, ‖f n‖^2 := by
  have hc : Fintype.card I ≤ Q^2 := by
    have hh := bounded_frequency_card p hp Q (univ.image a) (by
      intro b hb
      obtain ⟨i, _, rfl⟩ := mem_image.mp hb
      exact ha i)
    simpa only [card_image_of_injective _ hinj, card_univ] using hh
  have hs (i j : I) (hij : i ≠ j) :
      1/(Q : ℝ)^2 ≤ circleDistance (m*frequencyAngle p (a j)-m*frequencyAngle p (a i)) :=
    frequency_spacing p hp (a j) (a i) (fun h => hij (hinj h).symm) Q (ha j) (ha i) m (hm j) (hm i)
  have hh := finite_phase_analysis (fun i => m*frequencyAngle p (a i)) L (1/(Q : ℝ)^2)
    (by positivity) hs f
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  apply add_le_add_right
  have hQR : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  calc
    (Fintype.card I : ℝ)/(2*(1/(Q : ℝ)^2)) ≤ (Q : ℝ)^2/(2*(1/(Q : ℝ)^2)) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = (Q : ℝ)^4/2 := by field_simp

noncomputable def residueGate (q : ℕ) (x : ZMod q) : ℝ :=
  (if x=0 then (q : ℝ) else 0)-1

lemma sum_char_nonzero {q : ℕ} [NeZero q] (x : ZMod q) :
    (∑ a : ZMod q, if a≠0 then ZMod.stdAddChar (a*x) else 0)=
      (residueGate q x : ℂ) := by
  classical
  have hs := AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar q)
  have he : (∑ a : ZMod q, ZMod.stdAddChar (a*x))=
      (∑ a : ZMod q, if a≠0 then ZMod.stdAddChar (a*x) else 0)+1 := by
    calc
      _ = ∑ a : ZMod q, ((if a≠0 then ZMod.stdAddChar (a*x) else 0)+if a=0 then 1 else 0) := by
        apply sum_congr rfl; intro a _
        by_cases ha : a=0 <;> simp [ha, AddChar.map_zero_eq_one]
      _ = _ := by simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  have hs' : (∑ a : ZMod q, ZMod.stdAddChar (a*x))=if x=0 then (q : ℂ) else 0 := by
    simpa only [ZMod.card, apply_ite, Nat.cast_zero] using hs
  unfold residueGate
  push_cast
  rw [hs'] at he
  split_ifs at * <;> push_cast <;> linear_combination -he

omit [∀ j, NeZero (p j)] in
lemma exact_support_iff [DecidableEq J] (U : Finset J) (a : ResidueSpace p) :
    primeSupport p a=U ↔ ∀j, (a j≠0 ↔ j∈U) := by
  simp only [Finset.ext_iff, primeSupport, mem_filter, mem_univ, true_and]

lemma sum_char_exact [DecidableEq J] (U : Finset J) (z : ResidueSpace p) :
    (∑ a : ResidueSpace p, if primeSupport p a=U then prodChar p a z else 0)=
      ∏ j∈U, (residueGate (p j) (z j) : ℂ) := by
  classical
  let w := fun j (a : ZMod (p j)) =>
    if (if j∈U then a≠0 else a=0) then ZMod.stdAddChar (a*z j) else 0
  have he (a : ResidueSpace p) : (if primeSupport p a=U then prodChar p a z else 0)=∏j, w j (a j) := by
    by_cases ha : primeSupport p a=U
    · rw [ite_eq_left ha]
      apply prod_congr rfl; intro j _
      have hj := (exact_support_iff p U a).mp ha j
      by_cases hU : j∈U <;> simp_all [w]
    · rw [ite_eq_right ha]
      have hn : ∃j, ¬ (a j≠0 ↔ j∈U) := by
        simpa only [exact_support_iff, not_forall] using ha
      obtain ⟨j,hj⟩ := hn
      symm
      apply prod_eq_zero (mem_univ j)
      by_cases hU : j∈U <;> simp_all [w]
  simp only [he]
  rw [← Fintype.prod_sum]
  have hj (j : J) : (∑ a : ZMod (p j), w j a)=if j∈U then (residueGate (p j) (z j) : ℂ) else 1 := by
    by_cases hU : j∈U
    · simp only [w, hU, ite_true]
      exact sum_char_nonzero (z j)
    · simp only [w, hU, ite_false, sum_ite_eq', mem_univ, ite_true, zero_mul, AddChar.map_zero_eq_one]
  simp_rw [hj]
  rw [prod_ite_mem]
  simp

noncomputable def exactGate [DecidableEq J] (U : Finset J) (z : ResidueSpace p) : ℝ :=
  ∏j∈U, residueGate (p j) (z j)

lemma exactGate_fourier [DecidableEq J] (U : Finset J) (z : ResidueSpace p) :
    (exactGate p U z : ℂ) = ∑a∈univ.filter (fun a => primeSupport p a=U), prodChar p a z := by
  rw [sum_filter, sum_char_exact]
  simp only [exactGate, Complex.ofReal_prod]

lemma prodChar_neg_right (a z : ResidueSpace p) : prodChar p a (-z)=conj (prodChar p a z) := by
  rw [prodChar_symm, prodChar_neg, prodChar_symm]

lemma prodChar_sub_right (a z w : ResidueSpace p) :
    prodChar p a (z-w)=prodChar p a z*conj (prodChar p a w) := by
  rw [sub_eq_add_neg, prodChar_add_right, prodChar_neg_right]

noncomputable def fourierPolynomial [DecidableEq J] (c : ResidueSpace p → ℂ) (z : ResidueSpace p) : ℂ :=
  ∑a, c a*prodChar p a z

lemma prodChar_norm_sq (a z : ResidueSpace p) :
    prodChar p a z*conj (prodChar p a z)=1 := by
  rw [Complex.mul_conj', norm_prodChar]
  norm_num

lemma fourierPolynomial_parseval [DecidableEq J] (c : ResidueSpace p → ℂ) :
    (𝔼 z, ‖fourierPolynomial p c z‖^2)=∑a, ‖c a‖^2 := by
  have he : (𝔼 z, fourierPolynomial p c z*conj (fourierPolynomial p c z))=
      ∑a, c a*conj (c a) := by
    simp only [fourierPolynomial, map_sum, sum_mul, mul_sum, map_mul]
    rw [expect_sum_comm]
    apply sum_congr rfl; intro a _
    rw [expect_sum_comm]
    have he a b z : c a*prodChar p a z*(conj (c b)*conj (prodChar p b z))=
        c a*conj (c b)*(prodChar p a z*conj (prodChar p b z)) := by ring
    simp only [he, ← mul_expect, prodChar_orthogonal]
    simp
  apply Complex.ofReal_injective
  simpa only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_expect] using he

lemma fourierPolynomial_reconstruction [DecidableEq J] (f : ResidueSpace p → ℂ) (z : ResidueSpace p) :
    fourierPolynomial p (fun a => 𝔼 x, f x*conj (prodChar p a x)) z=f z := by
  classical
  unfold fourierPolynomial
  simp_rw [Finset.expect_mul]
  rw [← expect_sum_comm]
  have he x : (∑a, f x*conj (prodChar p a x)*prodChar p a z)=
      f x*(Fintype.card (ResidueSpace p))*(if z=x then 1 else 0) := by
    simp_rw [mul_assoc, mul_comm (conj _), ← prodChar_sub_right]
    rw [← mul_sum]
    have hs := prodChar_expect p (z-x)
    simp_rw [prodChar_symm p _ (z-x)]
    rw [expect_eq_sum_div_card] at hs
    have hc : (Fintype.card (ResidueSpace p) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hs' := (div_eq_iff hc).mp hs
    rw [hs']
    simp only [sub_eq_zero]
    ring
  simp only [he, expect_eq_sum_div_card, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_univ, ite_true, card_univ]
  exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

omit [Fintype J] in
lemma residue_crt [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j)) (B : Finset J) (z : ResidueSpace p) :
    ∃ a : ℕ, a < ∏j∈B, p j ∧ ∀n : ℕ,
      (∀j∈B, (n : ZMod (p j))=z j) ↔ n % (∏j∈B, p j)=a := by
  classical
  let q := ∏j : B, p j
  have hq : 0 < q := prod_pos fun j _ => Nat.pos_of_ne_zero (NeZero.ne (p j))
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hpB : Pairwise fun i j : B => (p i).Coprime (p j) := fun i j hij =>
    hp (Subtype.val_injective.ne hij)
  let e := ZMod.prodEquivPi (fun j : B => p j) hpB
  let w := e.symm (fun j : B => z j)
  have hval := ZMod.val_lt w
  have hqe : q=∏j∈B, p j := prod_coe_sort B p
  refine ⟨w.val, by simpa only [← hqe] using hval, ?_⟩
  intro n
  have he : (∀j∈B, (n : ZMod (p j))=z j) ↔ (n : ZMod q)=w := by
    constructor
    · intro h
      apply e.injective
      rw [e.apply_symm_apply]
      funext j
      simp only [e, ZMod.prodEquivPi_apply, map_natCast]
      exact h j j.property
    · intro h j hj
      have hh := congrArg (fun u => e u ⟨j,hj⟩) h
      have hw : e w=(fun j : B => z j) := e.apply_symm_apply _
      rw [hw] at hh
      simpa only [e, ZMod.prodEquivPi_apply, map_natCast] using hh
  rw [he, ← hqe]
  constructor
  · intro h
    simpa only [ZMod.val_natCast] using congrArg ZMod.val h
  · intro h
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast] using h

omit [∀j, NeZero (p j)] in
lemma support_coprime [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (B : Finset J) (a : ResidueSpace p) (hB : Disjoint B (primeSupport p a)) :
    (∏j∈B, p j).Coprime (supportDenominator p a) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  apply Nat.coprime_prod_right_iff.mpr
  intro j hj
  exact hp (fun he => (disjoint_left.mp hB hi) (he ▸ hj))

omit [∀j, NeZero (p j)] in
lemma product_indicator [DecidableEq J] (B : Finset J) (z : ResidueSpace p) (n : ℕ) :
    (∏j∈B, (if (n : ZMod (p j))=z j then (p j : ℂ) else 0))=
      (∏j∈B, p j : ℕ)*(if ∀j∈B, (n : ZMod (p j))=z j then 1 else 0) := by
  classical
  by_cases h : ∀j∈B, (n : ZMod (p j))=z j
  · rw [ite_eq_left h, mul_one]
    push_cast
    apply prod_congr rfl; intro j hj
    rw [ite_eq_left (h j hj)]
  · rw [ite_eq_right h, mul_zero]
    push Not at h
    obtain ⟨j,hj,he⟩ := h
    exact prod_eq_zero hj (ite_eq_right he)

omit [∀j, NeZero (p j)] in
lemma exactGate_expand [DecidableEq J] (B : Finset J) (z : ResidueSpace p) (n : ℕ) :
    (exactGate p B (z-fun j => (n : ZMod (p j))) : ℂ)=
      ∑S∈B.powerset, (-1 : ℂ)^(B\S).card*(∏j∈S, p j : ℕ)*
        (if ∀j∈S, (n : ZMod (p j))=z j then 1 else 0) := by
  classical
  simp only [exactGate, Complex.ofReal_prod]
  have he j : (residueGate (p j) ((z-fun j => (n : ZMod (p j))) j) : ℂ)=
      (if (n : ZMod (p j))=z j then (p j : ℂ) else 0)+(-1) := by
    dsimp only [residueGate, Pi.sub_apply]
    by_cases hn : (n : ZMod (p j))=z j
    · simp [hn, sub_eq_add_neg]
    · have hz : z j-(n : ZMod (p j))≠0 := fun h => hn (sub_eq_zero.mp h).symm
      simp [hn, hz]
  simp only [he]
  rw [prod_add]
  apply sum_congr rfl; intro S _
  rw [product_indicator]
  simp only [prod_const]
  ring

lemma vector_signed_sum_bound {I T : Type*} [Fintype I] [DecidableEq I]
    (S : Finset T) (v : T → I → ℂ) (sgn : T → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsgn : ∀t∈S, ‖sgn t‖ ≤ 1) (hv : ∀t∈S, (∑i, ‖v t i‖^2) ≤ C^2) :
    (∑i, ‖∑t∈S, sgn t*v t i‖^2) ≤ (S.card*C)^2 := by
  let w : T → EuclideanSpace ℂ I := fun t => sgn t • WithLp.toLp 2 (v t)
  have hw t (ht : t∈S) : ‖w t‖ ≤ C := by
    have hh : ‖(WithLp.toLp 2 (v t) : EuclideanSpace ℂ I)‖ ≤ C := by
      apply (sq_le_sq₀ (norm_nonneg _) hC).mp
      rw [PiLp.norm_sq_eq_of_L2]
      exact hv t ht
    exact (norm_smul_le _ _).trans (by nlinarith [hsgn t ht, norm_nonneg (sgn t)])
  have hh : ‖∑t∈S, w t‖ ≤ S.card*C := by
    calc
      _ ≤ ∑t∈S, ‖w t‖ := norm_sum_le _ _
      _ ≤ ∑_t∈S, C := sum_le_sum fun t ht => hw t ht
      _ = _ := by simp
  have he : (∑t∈S, w t)=(WithLp.toLp 2 (fun i => ∑t∈S, sgn t*v t i) : EuclideanSpace ℂ I) := by
    ext i
    simp only [w, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul]
  rw [he, ← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC), PiLp.norm_sq_eq_of_L2] at hh
  exact hh

lemma sum_residue_progression {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (L q a : ℕ) (hq : 0 < q) (ha : a < q) :
    (∑ n ∈ range L, if n%q=a then f n else 0)=
      ∑ t ∈ range (L/q+1), if a+q*t<L then f (a+q*t) else 0 := by
  classical
  rw [← sum_filter, ← sum_filter]
  symm
  apply sum_bij (fun t _ => a+q*t)
  · intro t ht
    obtain ⟨_, ht⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨mem_range.mpr ht, by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]⟩
  · intro t ht u hu he
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel he)
  · intro n hn
    obtain ⟨hn, hnq⟩ := mem_filter.mp hn
    have hnL := mem_range.mp hn
    have he : a+q*(n/q)=n := by rw [← hnq]; exact Nat.mod_add_div n q
    refine ⟨n/q, mem_filter.mpr ⟨mem_range.mpr ?_, by rwa [he]⟩, he⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hnL))
  · intro t _
    rfl

lemma progression_analysis {I : Type*} [Fintype I] [DecidableEq I]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (b : I → ResidueSpace p) (hinj : Function.Injective b) (Q : ℕ) (hQ : 0 < Q)
    (hb : ∀ i, supportDenominator p (b i) ≤ Q)
    (q : ℕ) (hq : 0 < q) (hcop : ∀ i, q.Coprime (supportDenominator p (b i)))
    (L a : ℕ) (ha : a < q) (f : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ n<L, ‖f n‖ ≤ M) :
    (∑ i, ‖∑ n∈range L, if n%q=a then f n*expPhase (-(n : ℝ)*frequencyAngle p (b i)) else 0‖^2) ≤
      ((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ)*M^2 := by
  let K := L/q+1
  let g : Fin K → ℂ := fun t => if a+q*t.val<L then f (a+q*t.val) else 0
  have hg t : ‖g t‖ ≤ M := by
    dsimp only [g]
    split_ifs with ht
    · exact hf _ ht
    · simpa using hM
  have hsum : ∑t, ‖g t‖^2 ≤ (K : ℝ)*M^2 := by
    calc
      _ ≤ ∑_t : Fin K, M^2 := sum_le_sum fun t _ => pow_le_pow_left₀ (norm_nonneg _) (hg t) 2
      _ = _ := by simp
  have hh := arithmetic_phase_analysis p hp b hinj Q hQ hb q hcop K g
  have he i : (∑ n∈range L, if n%q=a then f n*expPhase (-(n : ℝ)*frequencyAngle p (b i)) else 0)=
      expPhase (-(a : ℝ)*frequencyAngle p (b i))*
        ∑t : Fin K, g t*expPhase (-(t : ℝ)*(q*frequencyAngle p (b i))) := by
    rw [sum_residue_progression _ L q a hq ha, mul_sum]
    dsimp only [g]
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => expPhase (-(a : ℝ)*frequencyAngle p (b i))*
      ((if a+q*t<L then f (a+q*t) else 0)*expPhase (-(t : ℝ)*(q*frequencyAngle p (b i))))) K]
    apply sum_congr rfl; intro t _
    by_cases hn : a+q*t<L
    · simp only [hn, ite_true]
      push_cast
      rw [show -(a+q*t)*frequencyAngle p (b i) =
        -(a : ℝ)*frequencyAngle p (b i)+(-(t : ℝ)*(q*frequencyAngle p (b i))) by ring,
        expPhase_add]
      ring
    · simp only [hn, ite_false, zero_mul, mul_zero]
  simp only [he, norm_mul, norm_expPhase, one_mul]
  exact hh.trans (by
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    calc
      _ ≤ ((K : ℝ)+(Q : ℝ)^4/2)*((K : ℝ)*M^2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring)

lemma progression_normalized_bound {I : Type*} [Fintype I] [DecidableEq I]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (b : I → ResidueSpace p) (hinj : Function.Injective b) (Q : ℕ) (hQ : 0 < Q)
    (hb : ∀i, supportDenominator p (b i) ≤ Q)
    (q : ℕ) (hq : 0 < q) (hcop : ∀i, q.Coprime (supportDenominator p (b i)))
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(q : ℝ) ≤ L)
    (hsmall' : (q : ℝ)*Q^4 ≤ L) (a : ℕ) (ha : a<q)
    (f : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀n<L, ‖f n‖ ≤ M) :
    (∑i, ‖((q : ℂ)/L)*∑n∈range L,
      if n%q=a then f n*expPhase (-(n : ℝ)*frequencyAngle p (b i)) else 0‖^2) ≤ 4*M^2 := by
  have h := progression_analysis p hp b hinj Q hQ hb q hq hcop L a ha f M hM hf
  have hqR : (0 : ℝ)<q := Nat.cast_pos.mpr hq
  have hLR : (0 : ℝ)<L := Nat.cast_pos.mpr hL
  have hK : (q : ℝ)*(L/q+1 : ℕ) ≤ (3/2 : ℝ)*L := by
    push_cast
    have hd : ((L/q : ℕ) : ℝ) ≤ (L : ℝ)/q := Nat.cast_div_le
    have hh := mul_le_mul_of_nonneg_left hd (le_of_lt hqR)
    rw [mul_div_cancel₀ _ (ne_of_gt hqR)] at hh
    nlinarith
  have hQB : (q : ℝ)*((L/q+1 : ℕ)+(Q : ℝ)^4/2) ≤ 2*L := by nlinarith
  have hprod : (q : ℝ)^2*((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ) ≤ 4*(L : ℝ)^2 := by
    have hh := mul_le_mul hQB hK (by positivity : (0 : ℝ)≤(q : ℝ)*(L/q+1 : ℕ)) (by positivity : (0 : ℝ)≤2*L)
    nlinarith
  have hconst : ((q : ℝ)/L)^2*((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ) ≤ 4 := by
    rw [show ((q : ℝ)/L)^2*((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ) =
      ((q : ℝ)^2*((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ))/(L : ℝ)^2 by ring]
    exact (div_le_iff₀ (sq_pos_of_pos hLR)).mpr hprod
  simp only [norm_mul, norm_div, Complex.norm_natCast, mul_pow, ← mul_sum]
  calc
    _ ≤ ((q : ℝ)/L)^2*(((L/q+1 : ℕ)+(Q : ℝ)^4/2)*(L/q+1 : ℕ)*M^2) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ ≤ 4*M^2 := by nlinarith [mul_le_mul_of_nonneg_right hconst (sq_nonneg M)]

noncomputable def gateCoefficient [DecidableEq J] (L : ℕ) (f : ℕ → ℂ)
    (B : Finset J) (z a : ResidueSpace p) : ℂ :=
  (L : ℂ)⁻¹*∑n∈range L, f n*expPhase (-(n : ℝ)*frequencyAngle p a)*
    (exactGate p B (z-fun j => (n : ZMod (p j))) : ℂ)

omit [∀j, NeZero (p j)] in
lemma gateCoefficient_expand [DecidableEq J] (L : ℕ) (f : ℕ → ℂ)
    (B : Finset J) (z a : ResidueSpace p) :
    gateCoefficient p L f B z a=
      ∑S∈B.powerset, (-1 : ℂ)^(B\S).card*
        (((∏j∈S, p j : ℕ) : ℂ)/L)*
          (∑n∈range L, if ∀j∈S, (n : ZMod (p j))=z j then
            f n*expPhase (-(n : ℝ)*frequencyAngle p a) else 0) := by
  classical
  unfold gateCoefficient
  simp_rw [exactGate_expand, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro S _
  apply sum_congr rfl; intro n _
  split_ifs
  · simp only [mul_one]; ring
  · simp only [mul_zero]

lemma gateCoefficient_bound [DecidableEq J] {I : Type*} [Fintype I] [DecidableEq I]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (a : I → ResidueSpace p) (hinj : Function.Injective a) (Q : ℕ) (hQ : 0 < Q)
    (ha : ∀i, supportDenominator p (a i) ≤ Q)
    (B : Finset J) (hB : ∏j∈B, p j ≤ Q)
    (hdis : ∀i, Disjoint B (primeSupport p (a i))) (z : ResidueSpace p)
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ)^5 ≤ L) (f : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀n<L, ‖f n‖ ≤ M) :
    (∑i, ‖gateCoefficient p L f B z (a i)‖^2) ≤ 4*M^2*4^B.card := by
  classical
  let v := fun (S : Finset J) (i : I) => (((∏j∈S, p j : ℕ) : ℂ)/L)*
    ∑n∈range L, if ∀j∈S, (n : ZMod (p j))=z j then
      f n*expPhase (-(n : ℝ)*frequencyAngle p (a i)) else 0
  let sgn := fun S : Finset J => (-1 : ℂ)^(B\S).card
  have hv S (hS : S∈B.powerset) : (∑i, ‖v S i‖^2) ≤ (2*M)^2 := by
    have hSB := mem_powerset.mp hS
    have hq : 0 < ∏j∈S, p j := prod_pos fun j _ => Nat.pos_of_ne_zero (NeZero.ne (p j))
    have hqB : 0 < ∏j∈B, p j := prod_pos fun j _ => Nat.pos_of_ne_zero (NeZero.ne (p j))
    have hqQ : ∏j∈S, p j ≤ Q := (Nat.le_of_dvd hqB (prod_dvd_prod_of_subset S B p hSB)).trans hB
    have hqR : ((∏j∈S, p j : ℕ) : ℝ) ≤ Q := Nat.cast_le.mpr hqQ
    obtain ⟨b,hb,he⟩ := residue_crt p hp S z
    have hcp i : (∏j∈S,p j).Coprime (supportDenominator p (a i)) :=
      support_coprime p hp S (a i) ((hdis i).mono_left hSB)
    have h := progression_normalized_bound p hp a hinj Q hQ ha (∏j∈S,p j) hq hcp L hL
      (by linarith) (by nlinarith [mul_le_mul_of_nonneg_right hqR (pow_nonneg (Nat.cast_nonneg Q) 4)])
      b hb f M hM hf
    dsimp only [v]
    simp only [he]
    exact h.trans_eq (by ring)
  have hsgn S (_hS : S∈B.powerset) : ‖sgn S‖ ≤ 1 := by simp [sgn]
  have hh := vector_signed_sum_bound B.powerset v sgn (2*M) (by positivity) hsgn hv
  have he i : gateCoefficient p L f B z (a i)=∑S∈B.powerset, sgn S*v S i := by
    rw [gateCoefficient_expand]
    apply sum_congr rfl; intro S _
    dsimp only [sgn,v]
    ring
  simp only [he]
  apply hh.trans_eq
  rw [card_powerset, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm B.card 2, pow_mul]
  ring

noncomputable def coordinateFreeze [DecidableEq J] (W : Finset J)
    (z x : ResidueSpace p) : ResidueSpace p := fun j => if j∈W then z j else x j

omit [Fintype J] [∀j, NeZero (p j)] in
lemma exactGate_freeze [DecidableEq J] (U W : Finset J) (z x : ResidueSpace p) :
    exactGate p U (coordinateFreeze p W z x)=
      exactGate p (U∩W) z*exactGate p (U\W) x := by
  classical
  have he : U=(U∩W)∪(U\W) := by rw [union_comm, sdiff_union_inter]
  conv_lhs => rw [he]
  rw [exactGate, prod_union (disjoint_sdiff_inter U W).symm]
  congr 1
  · apply prod_congr rfl; intro j hj
    simp only [coordinateFreeze, (mem_inter.mp hj).2, ite_true]
  · apply prod_congr rfl; intro j hj
    simp only [coordinateFreeze, (mem_sdiff.mp hj).2, ite_false]

omit [Fintype J] [∀j, NeZero (p j)] in
lemma coordinateFreeze_sub [DecidableEq J] (W : Finset J) (z x t : ResidueSpace p) :
    coordinateFreeze p W z x-t=coordinateFreeze p W (z-t) (x-t) := by
  ext j
  by_cases hj : j∈W <;> simp [coordinateFreeze, hj]

noncomputable def liftPiece [DecidableEq J] (L : ℕ) (f : ℕ → ℝ)
    (U : Finset J) (z : ResidueSpace p) : ℝ :=
  (L : ℝ)⁻¹*∑n∈range L, f n*exactGate p U (z-fun j => (n : ZMod (p j)))

lemma liftPiece_freeze_fourier [DecidableEq J] (L : ℕ) (f : ℕ → ℝ)
    (U W : Finset J) (z x : ResidueSpace p) :
    (liftPiece p L f U (coordinateFreeze p W z x) : ℂ)=
      fourierPolynomial p (fun a => if primeSupport p a=U\W then
        gateCoefficient p L (fun n => (f n : ℂ)) (U∩W) z a else 0) x := by
  classical
  have he (n : ℕ) : (exactGate p U (coordinateFreeze p W z x-fun j => (n : ZMod (p j))) : ℂ)=
      (exactGate p (U∩W) (z-fun j => (n : ZMod (p j))) : ℂ)*
        ∑a∈univ.filter (fun a => primeSupport p a=U\W),
          prodChar p a x*conj (expPhase ((n : ℝ)*frequencyAngle p a)) := by
    rw [coordinateFreeze_sub, exactGate_freeze, Complex.ofReal_mul,
      exactGate_fourier p (U\W)]
    simp only [prodChar_sub_right, prodChar_nat_diagonal]
  simp only [liftPiece, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_sum, he]
  simp only [fourierPolynomial, gateCoefficient, ite_mul, zero_mul]
  rw [← sum_filter]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro a _
  rw [sum_mul]
  apply sum_congr rfl; intro n _
  rw [show expPhase (-(n : ℝ)*frequencyAngle p a)=
      conj (expPhase ((n : ℝ)*frequencyAngle p a)) by rw [neg_mul, expPhase_neg]]
  ring

lemma liftPiece_conditional_parseval [DecidableEq J] (L : ℕ) (f : ℕ → ℝ)
    (U W : Finset J) (z : ResidueSpace p) :
    (𝔼 x, liftPiece p L f U (coordinateFreeze p W z x)^2)=
      ∑a∈univ.filter (fun a => primeSupport p a=U\W),
        ‖gateCoefficient p L (fun n => (f n : ℂ)) (U∩W) z a‖^2 := by
  classical
  have hh := fourierPolynomial_parseval p (fun a => if primeSupport p a=U\W then
    gateCoefficient p L (fun n => (f n : ℂ)) (U∩W) z a else 0)
  simp_rw [← liftPiece_freeze_fourier p L f U W z, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at hh
  rw [sum_filter]
  convert hh using 1
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma liftPiece_fixed_intersection_bound [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (F : Finset (Finset J)) (W B : Finset J)
    (hF : ∀U∈F, U∩W=B) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀U∈F, ∏j∈U, p j ≤ Q) (z : ResidueSpace p)
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ)^5 ≤ L) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀n<L, |f n| ≤ M) :
    (∑U∈F, 𝔼 x, liftPiece p L f U (coordinateFreeze p W z x)^2) ≤
      4*M^2*4^B.card := by
  classical
  by_cases hne : F.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, sum_empty]
    positivity
  obtain ⟨U₀,hU₀⟩ := hne
  have hBU : B⊆U₀ := (hF U₀ hU₀) ▸ inter_subset_left
  have hB : ∏j∈B, p j ≤ Q :=
    (prod_le_prod_of_subset_of_one_le₀ hBU (fun _ _ => Nat.zero_le _)
      (fun j _ _ => Nat.pos_of_ne_zero (NeZero.ne (p j)))).trans (hden U₀ hU₀)
  let T := fun U : Finset J => univ.filter (fun a : ResidueSpace p => primeSupport p a=U\W)
  let Ω := F.biUnion T
  have memO (a : Ω) : ∃U∈F, primeSupport p a.val=U\W := by
    obtain ⟨U,hU,ha⟩ := mem_biUnion.mp a.property
    exact ⟨U,hU,(mem_filter.mp ha).2⟩
  have ha (a : Ω) : supportDenominator p a.val ≤ Q := by
    obtain ⟨U,hU,he⟩ := memO a
    unfold supportDenominator
    rw [he]
    exact (prod_le_prod_of_subset_of_one_le₀ sdiff_subset (fun _ _ => Nat.zero_le _)
      (fun j _ _ => Nat.pos_of_ne_zero (NeZero.ne (p j)))).trans (hden U hU)
  have hdis (a : Ω) : Disjoint B (primeSupport p a.val) := by
    obtain ⟨U,hU,he⟩ := memO a
    rw [← hF U hU, he]
    exact (disjoint_sdiff_inter U W).symm
  have hpair : (↑F : Set (Finset J)).PairwiseDisjoint T := by
    intro U hU V hV hUV
    apply disjoint_left.mpr
    intro a ha hb
    have hUV' : U\W=V\W := (mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2
    apply hUV
    calc
      U = (U\W)∪(U∩W) := (sdiff_union_inter U W).symm
      _ = (V\W)∪(V∩W) := by rw [hUV', hF U hU, hF V hV]
      _ = V := sdiff_union_inter V W
  have hh := gateCoefficient_bound p hp (fun a : Ω => a.val) Subtype.val_injective Q hQ ha
    B hB hdis z L hL hsmall hsmall' (fun n => (f n : ℂ)) M hM
    (fun n hn => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf n hn)
  rw [sum_coe_sort Ω (fun a => ‖gateCoefficient p L (fun n => (f n : ℂ)) B z a‖^2)] at hh
  calc
    _ = ∑U∈F, ∑a∈T U, ‖gateCoefficient p L (fun n => (f n : ℂ)) B z a‖^2 := by
      apply sum_congr rfl; intro U hU
      rw [liftPiece_conditional_parseval, hF U hU]
    _ = ∑a∈Ω, ‖gateCoefficient p L (fun n => (f n : ℂ)) B z a‖^2 := (sum_biUnion hpair).symm
    _ ≤ _ := hh

lemma liftPiece_conditional_square_sum [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (F : Finset (Finset J)) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀U∈F, ∏j∈U, p j ≤ Q)
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ)^5 ≤ L) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀n<L, |f n| ≤ M) (W : Finset J) (z : ResidueSpace p) :
    (𝔼 x, ∑U∈F, liftPiece p L f U (coordinateFreeze p W z x)^2) ≤
      4*M^2*5^W.card := by
  classical
  rw [expect_sum_comm]
  have hmap : ∀U∈F, U∩W∈W.powerset := fun U _ => mem_powerset.mpr inter_subset_right
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑B∈W.powerset, 4*M^2*4^B.card := by
      apply sum_le_sum; intro B _
      exact liftPiece_fixed_intersection_bound p hp (F.filter (fun U => U∩W=B)) W B
        (fun _ hU => (mem_filter.mp hU).2) Q hQ
        (fun U hU => hden U (mem_filter.mp hU).1) z L hL hsmall hsmall' f M hM hf
    _ = _ := by
      rw [← mul_sum]
      congr 1
      simpa only [one_pow, mul_one, show (4:ℝ)+1=5 by norm_num] using
        sum_pow_mul_eq_add_pow (4:ℝ) 1 W

omit [Fintype J] in
lemma residueGate_expect (j : J) (c : ZMod (p j)) :
    (𝔼 t : ZMod (p j), residueGate (p j) (t-c))=0 := by
  classical
  have he (t : ZMod (p j)) : residueGate (p j) (t-c)=
      (if t=c then (p j : ℝ) else 0)-1 := by simp [residueGate, sub_eq_zero]
  simp only [he, expect_eq_sum_div_card]
  simp [ZMod.card]

omit [Fintype J] in
lemma exactGate_update_mean [DecidableEq J] (U : Finset J) (j : J) (hj : j∈U)
    (x c : ResidueSpace p) :
    (𝔼 t : ZMod (p j), exactGate p U (Function.update x j t-c))=0 := by
  classical
  have he (t : ZMod (p j)) : exactGate p U (Function.update x j t-c)=
      residueGate (p j) (t-c j)*exactGate p (U.erase j) (x-c) := by
    rw [exactGate, ← mul_prod_erase U (fun a => residueGate (p a) ((Function.update x j t-c) a)) hj]
    simp only [Pi.sub_apply, Function.update_self]
    congr 1
    apply prod_congr rfl
    intro a ha
    rw [Function.update_of_ne (mem_erase.mp ha).1]
    rfl
  simp only [he, ← expect_mul, residueGate_expect, zero_mul]

omit [Fintype J] [∀j, NeZero (p j)] in
lemma exactGate_update_outside [DecidableEq J] (U : Finset J) (j : J) (hj : j∉U)
    (x c : ResidueSpace p) (t : ZMod (p j)) :
    exactGate p U (Function.update x j t-c)=exactGate p U (x-c) := by
  apply prod_congr rfl
  intro a ha
  have haj : a≠j := fun h => hj (h ▸ ha)
  simp only [Pi.sub_apply, Function.update_of_ne haj]

omit [Fintype J] in
lemma liftPiece_exactSupport [DecidableEq J] (L : ℕ) (f : ℕ → ℝ) (U : Finset J) :
    ExactSupport U (liftPiece p L f U) := by
  constructor
  · intro j hj x
    simp only [liftPiece, ← mul_expect, expect_sum_comm, exactGate_update_mean p U j hj,
      mul_zero, sum_const_zero]
  · intro j hj x t
    simp only [liftPiece, exactGate_update_outside p U j hj]

lemma liftPiece_moment [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (F : Finset (Finset J)) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀U∈F, ∏j∈U, p j ≤ Q)
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ)^5 ≤ L) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀n<L, |f n| ≤ M) (k : ℕ) (hk : ∀U∈F, U.card ≤ k)
    (r : ℕ) (hr : 1 ≤ r) :
    (𝔼 x, (∑U∈F, liftPiece p L f U x)^(2*r)) ≤
      (((4:ℝ)*(2:ℝ)^(2*r))^k)^r*(4*M^2*5^(r*k))^r := by
  classical
  apply (symmetrization_moment F (liftPiece p L f) (fun U _ => liftPiece_exactSupport p L f U)
    k hk r hr).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he x : (∑U∈F, liftPiece p L f U x^2) = ∑U : F, liftPiece p L f U.val x^2 :=
    (sum_coe_sort F _).symm
  simp only [he]
  apply square_moment_bound (fun U : F => U.val) (fun U => liftPiece p L f U.val)
    (fun U x y hxy => exactSupport_congr U.val _ (liftPiece_exactSupport p L f U.val) x y hxy)
    k (fun U => hk U.val U.property) (4*M^2) 5 (by positivity) (by norm_num)
  intro W x
  have h := liftPiece_conditional_square_sum p hp F Q hQ hden L hL hsmall hsmall' f M hM hf W x
  have hh (y : ResidueSpace p) : coordinateFreeze p W x y =
      hybrid (fun j => decide (j∈W)) x y := by
    ext j
    simp [coordinateFreeze, hybrid]
  simp_rw [hh] at h
  have hsum (y : ResidueSpace p) :
      (∑U∈F, liftPiece p L f U (hybrid (fun j => decide (j∈W)) x y)^2)=
      ∑U : F, liftPiece p L f U.val (hybrid (fun j => decide (j∈W)) x y)^2 :=
    (sum_coe_sort F _).symm
  simp_rw [hsum] at h
  exact h

lemma liftPiece_moment_small_loss [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j))
    (F : Finset (Finset J)) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀U∈F, ∏j∈U, p j ≤ Q)
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ)^5 ≤ L) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀n<L, |f n| ≤ M) (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 ≤ ε)
    (hprime : ∀j, (4:ℝ)*2^(2*r)*5^r ≤ (p j : ℝ)^(2*ε)) :
    (𝔼 x, (∑U∈F, liftPiece p L f U x)^(2*r)) ≤
      (2*M*(Q : ℝ)^ε)^(2*r) := by
  classical
  by_cases hF : F.Nonempty
  · obtain ⟨U,hU,hk⟩ := exists_mem_eq_sup F hF Finset.card
    let k := F.sup Finset.card
    have hcard : ∀U∈F, U.card ≤ k := fun U hU => le_sup hU
    have hb : ((4:ℝ)*2^(2*r)*5^r)^k ≤ (Q : ℝ)^(2*ε) := by
      rw [show k=U.card from hk]
      calc
        _ = ∏j∈U, ((4:ℝ)*2^(2*r)*5^r) := by simp
        _ ≤ ∏j∈U, (p j : ℝ)^(2*ε) := by
          apply prod_le_prod₀
          · intro j _; positivity
          · intro j _; exact hprime j
        _ = (∏j∈U, (p j : ℝ))^(2*ε) := by
          rw [Real.finsetProd_rpow]
          intro j _; positivity
        _ ≤ (Q : ℝ)^(2*ε) := by
          apply Real.rpow_le_rpow (by positivity) _ (by positivity)
          exact_mod_cast hden U hU
    have hh := liftPiece_moment p hp F Q hQ hden L hL hsmall hsmall' f M hM hf k hcard r hr
    calc
      _ ≤ (((4:ℝ)*2^(2*r))^k)^r*(4*M^2*5^(r*k))^r := hh
      _ = (2*M)^(2*r)*(((4:ℝ)*2^(2*r)*5^r)^k)^r := by
        rw [show (4:ℝ)=2^2 by norm_num]
        simp only [mul_pow, ← pow_mul, Nat.mul_assoc]
        ring
      _ ≤ (2*M)^(2*r)*((Q : ℝ)^(2*ε))^r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb r) (by positivity)
      _ = _ := by
        conv_rhs => rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast ((Q : ℝ)^(2*ε)) r,
          ← Real.rpow_mul (by positivity : 0 ≤ (Q : ℝ)),
          ← Real.rpow_natCast ((Q : ℝ)^ε) (2*r),
          ← Real.rpow_mul (by positivity : 0 ≤ (Q : ℝ))]
        congr 1
        push_cast
        ring
  · simp only [not_nonempty_iff_eq_empty.mp hF, sum_empty, zero_pow (by omega : 2*r≠0),
      Fintype.expect_const]
    positivity

lemma exponential_support_bound {I : Type*} [DecidableEq I]
    (U : Finset I) (p : I → ℕ) (hinj : Set.InjOn p (↑U : Set I))
    (hp : ∀i∈U, 1≤p i) (A : ℝ) (hA : 1≤A) (ε : ℝ) (hε : 0≤ε)
    (T : ℕ) (hT : ∀n : ℕ, T≤n → A≤(n : ℝ)^ε) :
    A^U.card ≤ A^T * (∏i∈U, (p i : ℝ))^ε := by
  classical
  let B := U.filter (fun i => p i<T)
  have hB : Set.InjOn p (↑B : Set I) := hinj.mono (filter_subset _ _)
  have hb : B.card≤T := by
    rw [← card_image_of_injOn hB]
    apply (card_le_card (show B.image p⊆range T from ?_)).trans_eq (card_range T)
    intro n hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    exact mem_range.mpr (mem_filter.mp hi).2
  have hpart : U.card=B.card+(U\B).card := by
    rw [card_sdiff_of_subset (filter_subset _ _)]
    exact (Nat.add_sub_of_le (card_le_card (filter_subset _ _))).symm
  calc
    A^U.card = A^B.card * A^(U\B).card := by rw [hpart,pow_add]
    _ ≤ A^T * ∏i∈U\B, (p i : ℝ)^ε := by
      apply mul_le_mul (pow_le_pow_right₀ hA hb) _ (by positivity) (by positivity)
      rw [← prod_const]
      apply prod_le_prod₀
      · intro i _; linarith
      · intro i hi
        apply hT
        have hni := (mem_sdiff.mp hi).2
        have hui := (mem_sdiff.mp hi).1
        have hn : ¬p i<T := by simpa only [B,mem_filter,hui,true_and] using hni
        omega
    _ ≤ A^T * ∏i∈U, (p i : ℝ)^ε := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply prod_le_prod_of_subset_of_one_le₀ sdiff_subset
      · intro i hi; positivity
      · intro i hi _
        exact Real.one_le_rpow (by exact_mod_cast hp i hi) hε
    _ = _ := by rw [Real.finsetProd_rpow]; intro i _; positivity

lemma exists_nat_power_threshold (A ε : ℝ) (hε : 0<ε) :
    ∃ T : ℕ, ∀n : ℕ, T≤n → A≤(n : ℝ)^ε := by
  have ht := (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_ge_atTop A))

lemma liftPiece_moment_uniform [DecidableEq J]
    (hp : Pairwise fun i j => (p i).Coprime (p j)) (hinj : Function.Injective p)
    (F : Finset (Finset J)) (Q : ℕ) (hQ : 0 < Q)
    (hden : ∀U∈F, ∏j∈U, p j ≤ Q)
    (L : ℕ) (hL : 0 < L) (hsmall : 2*(Q : ℝ) ≤ L)
    (hsmall' : (Q : ℝ)^5 ≤ L) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀n<L, |f n| ≤ M) (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 ≤ ε)
    (T : ℕ) (hT : ∀n : ℕ, T≤n → (4:ℝ)*2^(2*r)*5^r≤(n : ℝ)^(2*ε)) :
    (𝔼 x, (∑U∈F, liftPiece p L f U x)^(2*r)) ≤
      (2*M*((4:ℝ)*2^(2*r)*5^r)^T*(Q : ℝ)^ε)^(2*r) := by
  classical
  let A : ℝ := 4*2^(2*r)*5^r
  have hA : 1≤A := by
    dsimp [A]
    have htwo : (1 : ℝ)≤2^(2*r) := one_le_pow₀ (by norm_num)
    have hfive : (1 : ℝ)≤5^r := one_le_pow₀ (by norm_num)
    nlinarith
  by_cases hF : F.Nonempty
  · obtain ⟨U,hU,hk⟩ := exists_mem_eq_sup F hF Finset.card
    let k := F.sup Finset.card
    have hcard : ∀U∈F, U.card ≤ k := fun U hU => le_sup hU
    have hb : A^k ≤ A^T*(Q : ℝ)^(2*ε) := by
      rw [show k=U.card from hk]
      apply (exponential_support_bound U p hinj.injOn (fun i _ => Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p i)))
        A hA (2*ε) (by positivity) T hT).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact_mod_cast hden U hU
    have hh := liftPiece_moment p hp F Q hQ hden L hL hsmall hsmall' f M hM hf k hcard r hr
    have hc : A^T ≤ (A^T)^2 := by nlinarith [one_le_pow₀ hA (n:=T)]
    calc
      _ ≤ (((4:ℝ)*2^(2*r))^k)^r*(4*M^2*5^(r*k))^r := hh
      _ = (2*M)^(2*r)*(A^k)^r := by
        dsimp [A]
        rw [show (4:ℝ)=2^2 by norm_num]
        simp only [mul_pow, ← pow_mul, Nat.mul_assoc]
        ring
      _ ≤ (2*M)^(2*r)*((A^T)^2*(Q : ℝ)^(2*ε))^r := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        exact hb.trans (mul_le_mul_of_nonneg_right hc (by positivity))
      _ = _ := by
        change _=(2*M*A^T*(Q : ℝ)^ε)^(2*r)
        have hqr : (Q : ℝ)^(2*ε)=((Q : ℝ)^ε)^2 := by
          rw [←Real.rpow_natCast ((Q : ℝ)^ε) 2,
            ←Real.rpow_mul (by positivity : 0≤(Q : ℝ))]
          congr 1
          norm_num
          ring
        rw [hqr]
        simp only [mul_pow, ←pow_mul]
        ring
  · simp only [not_nonempty_iff_eq_empty.mp hF,sum_empty,zero_pow (by omega : 2*r≠0),
      Fintype.expect_const]
    positivity

lemma liftPiece_moment_subpower [DecidableEq J]
    (r : ℕ) (hr : 1≤r) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (_hp : Pairwise fun i j => (p i).Coprime (p j))
      (_hinj : Function.Injective p) (F : Finset (Finset J)) (Q : ℕ), 0<Q →
      (∀U∈F, ∏j∈U, p j ≤Q) → ∀L : ℕ, 0<L → 2*(Q : ℝ)≤L →
      (Q : ℝ)^5≤L → ∀(f : ℕ → ℝ) (M : ℝ), 0≤M →
      (∀n<L, |f n|≤M) →
      (𝔼 x, (∑U∈F, liftPiece p L f U x)^(2*r))≤(C*M*(Q : ℝ)^ε)^(2*r) := by
  obtain ⟨T,hT⟩ := exists_nat_power_threshold ((4:ℝ)*2^(2*r)*5^r) (2*ε) (by positivity)
  refine ⟨2*((4:ℝ)*2^(2*r)*5^r)^T, by positivity, ?_⟩
  intro hp hinj F Q hQ hden L hL hs hs' f M hM hf
  convert liftPiece_moment_uniform p hp hinj F Q hQ hden L hL hs hs' f M hM hf r hr ε hε.le T hT using 1
  congr 1
  ring

end SquareDifference

end LiftAnalysis
end

end OAI
