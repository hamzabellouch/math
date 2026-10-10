import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.TriangularLattice01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
namespace BoxPolynomialLines
open scoped BigOperators
open PolynomialWeyl
noncomputable section

def boxMean : (n N : ℕ) → ((Fin n → ℕ) → ℂ) → ℂ
  | 0, _, f => f Fin.elim0
  | n + 1, N, f => mean N (fun x => boxMean n N (fun y => f (Fin.cons x y)))

@[simp] theorem boxMean_zero (N : ℕ) (f : (Fin 0 → ℕ) → ℂ) :
    boxMean 0 N f = f Fin.elim0 := rfl
@[simp] theorem boxMean_succ (n N : ℕ) (f : (Fin (n + 1) → ℕ) → ℂ) :
    boxMean (n + 1) N f = mean N (fun x => boxMean n N (fun y => f (Fin.cons x y))) := rfl

theorem boxMean_sub (n N : ℕ) (f g : (Fin n → ℕ) → ℂ) :
    boxMean n N (fun x => f x - g x) = boxMean n N f - boxMean n N g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [boxMean_succ, ih, mean, Finset.expect_sub_distrib]

theorem boxMean_const (n : ℕ) {N : ℕ} (hN : 0 < N) (z : ℂ) :
    boxMean n N (fun _ => z) = z := by
  induction n with
  | zero => rfl
  | succ n ih => simp [boxMean_succ, ih, mean, Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)]

theorem boxMean_comm (n N H : ℕ) (f : (Fin n → ℕ) → ℕ → ℂ) :
    boxMean n N (fun x => mean H (f x)) = mean H (fun t => boxMean n N (fun x => f x t)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [boxMean_succ]
    simp_rw [ih]
    simp only [mean]
    rw [Finset.expect_comm]

theorem boxMean_norm_le (n : ℕ) {N : ℕ} (hN : 0 < N) (f : (Fin n → ℕ) → ℂ)
    (C : ℝ) (hf : ∀ x, (∀ i, x i < N) → ‖f x‖ ≤ C) : ‖boxMean n N f‖ ≤ C := by
  induction n with
  | zero => exact hf _ (fun i => Fin.elim0 i)
  | succ n ih =>
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))
    intro x hx
    apply ih
    intro y hy
    apply hf
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Finset.mem_range.mp hx
    · exact hy j

theorem exists_norm_ge (n : ℕ) {N : ℕ} (hN : 0 < N) (f : (Fin n → ℕ) → ℂ)
    {δ : ℝ} (hδ : δ ≤ ‖boxMean n N f‖) :
    ∃ x : Fin n → ℕ, (∀ i, x i < N) ∧ δ ≤ ‖f x‖ := by
  induction n with
  | zero => exact ⟨_, (fun i => Fin.elim0 i), hδ⟩
  | succ n ih =>
    have hle := hδ.trans (RCLike.norm_expect_le (K := ℂ))
    obtain ⟨x, hx, hh⟩ := Finset.exists_le_of_le_expect
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)) hle
    obtain ⟨y, hy, hyδ⟩ := ih (fun y => f (Fin.cons x y)) hh
    refine ⟨Fin.cons x y, ?_, hyδ⟩
    intro i
    exact Fin.cases (Finset.mem_range.mp hx) hy i

theorem cons_add (n : ℕ) (x : ℕ) (y : Fin n → ℕ) (h : Fin (n + 1) → ℕ) :
    Fin.cons x y + h = Fin.cons (x + h 0) (fun i => y i + h i.succ) := by
  ext i
  exact Fin.cases rfl (fun _ => rfl) i

attribute [irreducible] boxMean

theorem norm_mean_sub_le {N : ℕ} (hN : 0 < N) (f g : ℕ → ℂ) (C : ℝ)
    (hf : ∀ x < N, ‖f x - g x‖ ≤ C) : ‖mean N f - mean N g‖ ≤ C := by
  rw [mean, mean, ← Finset.expect_sub_distrib]
  exact (RCLike.norm_expect_le (K := ℂ)).trans
    (Finset.expect_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))
      (fun x hx => hf x (Finset.mem_range.mp hx)))

theorem tail_shift_bound (n N x : ℕ)
    (f : (Fin (n + 1) → ℕ) → ℂ) (h : Fin (n + 1) → ℕ) (C : ℝ)
    (ih : ‖boxMean n N (fun y => f (Fin.cons (x + h 0) (y + fun i => h i.succ))) -
      boxMean n N (fun y => f (Fin.cons (x + h 0) y))‖ ≤ C) :
    ‖boxMean n N (fun y => f (Fin.cons x y + h)) -
      boxMean n N (fun y => f (Fin.cons (x + h 0) y))‖ ≤ C := by
  have heq : (fun y : Fin n → ℕ => f (Fin.cons x y + h)) =
      (fun y : Fin n → ℕ => f (Fin.cons (x + h 0) (y + fun i => h i.succ))) := by
    funext y
    exact congrArg f (cons_add n x y h)
  rw [heq]
  exact ih

theorem shift_step (n : ℕ) {N : ℕ} (hN : 0 < N)
    (ih : ∀ (f : (Fin n → ℕ) → ℂ), (∀ x, ‖f x‖ ≤ 1) → ∀ (h : Fin n → ℕ),
      ‖boxMean n N (fun x => f (x + h)) - boxMean n N f‖ ≤
        2 * (∑ i, h i : ℕ) / N)
    (f : (Fin (n + 1) → ℕ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (h : Fin (n + 1) → ℕ) :
    ‖boxMean (n + 1) N (fun x => f (x + h)) - boxMean (n + 1) N f‖ ≤
      2 * (∑ i, h i : ℕ) / N := by
  let F (x : ℕ) := boxMean n N (fun y => f (Fin.cons x y))
  let A (x : ℕ) := boxMean n N (fun y => f (Fin.cons x y + h))
  let B (x : ℕ) := F (x + h 0)
  have hF (x : ℕ) : ‖F x‖ ≤ 1 := boxMean_norm_le n hN _ _ (fun y _ => hf _)
  have htail (x : ℕ) : ‖A x - B x‖ ≤ 2 * (∑ i : Fin n, h i.succ : ℕ) / N :=
    tail_shift_bound n N x f h _
      (ih (fun y => f (Fin.cons (x + h 0) y)) (fun y => hf _) (fun i => h i.succ))
  have he := norm_mean_sub_le hN A B _ (fun x _ => htail x)
  have hhead : ‖mean N B - mean N F‖ ≤ 2 * (h 0 : ℝ) / N :=
    norm_mean_shift_sub_le hN (h 0) F hF
  have htriangle : ‖mean N A - mean N F‖ ≤
      2 * (∑ i : Fin n, h i.succ : ℕ) / N + 2 * (h 0 : ℝ) / N :=
    (norm_sub_le_norm_sub_add_norm_sub (mean N A) (mean N B) (mean N F)).trans
      (add_le_add he hhead)
  have hs : (∑ i : Fin (n + 1), h i : ℕ) = h 0 + ∑ i : Fin n, h i.succ := Fin.sum_univ_succ _
  have hc : 2 * (∑ i : Fin n, h i.succ : ℕ) / (N : ℝ) + 2 * (h 0 : ℝ) / N =
      2 * (∑ i : Fin (n + 1), h i : ℕ) / N := by rw [hs, Nat.cast_add]; ring
  rw [hc] at htriangle
  rw [boxMean_succ, boxMean_succ]
  exact htriangle

theorem norm_shift_error (n : ℕ) {N : ℕ} (hN : 0 < N)
    (f : (Fin n → ℕ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (h : Fin n → ℕ) :
    ‖boxMean n N (fun x => f (x + h)) - boxMean n N f‖ ≤
      2 * (∑ i, h i : ℕ) / N := by
  induction n with
  | zero =>
    have he : (Fin.elim0 : Fin 0 → ℕ) + h = Fin.elim0 := by ext i; exact Fin.elim0 i
    rw [boxMean_zero, boxMean_zero, he, sub_self, norm_zero]
    simp
  | succ n ih => exact shift_step n hN ih f hf h

theorem mean_const {N : ℕ} (hN : 0 < N) (z : ℂ) : mean N (fun _ => z) = z := by
  simp [mean, Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)]

theorem line_average_error (n : ℕ) {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (f : (Fin n → ℕ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (v : Fin n → ℕ) :
    ‖boxMean n N (fun x => mean H (fun t => f (x + fun i => t * v i))) - boxMean n N f‖ ≤
      2 * (H : ℝ) * (∑ i, v i : ℕ) / N := by
  rw [boxMean_comm, ← mean_const hH (boxMean n N f)]
  apply norm_mean_sub_le hH
  intro t ht
  have hs : (∑ i, t * v i : ℕ) = t * ∑ i, v i := (Finset.mul_sum ..).symm
  have hb := norm_shift_error n hN f hf (fun i => t * v i)
  rw [hs, Nat.cast_mul] at hb
  rw [← mul_assoc] at hb
  exact hb.trans (by gcongr)

theorem exists_correlated_line (n : ℕ) {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (f : (Fin n → ℕ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (v : Fin n → ℕ)
    {δ : ℝ} (hδ : δ ≤ ‖boxMean n N f‖)
    (hshort : 2 * (H : ℝ) * (∑ i, v i : ℕ) / N ≤ δ / 2) :
    ∃ x : Fin n → ℕ, (∀ i, x i < N) ∧
      δ / 2 ≤ ‖mean H (fun t => f (x + fun i => t * v i))‖ := by
  apply exists_norm_ge n hN
  have herr := (line_average_error n hN hH f hf v).trans hshort
  let A := boxMean n N f
  let B := boxMean n N (fun x => mean H (fun t => f (x + fun i => t * v i)))
  have htriangle : ‖A‖ ≤ ‖A - B‖ + ‖B‖ := by
    simpa only [sub_add_cancel] using norm_add_le (A - B) B
  rw [norm_sub_rev] at herr
  change ‖A - B‖ ≤ δ / 2 at herr
  change δ ≤ ‖A‖ at hδ
  change δ / 2 ≤ ‖B‖
  linarith

end
end BoxPolynomialLines

namespace BoxCounting
open scoped BigOperators
open PolynomialWeyl BoxPolynomialLines Finset
noncomputable section

theorem mean_eq_fin (N : ℕ) (f : ℕ → ℂ) :
    mean N f = 𝔼 x : Fin N, f x := by
  classical
  symm
  apply Finset.expect_bij (fun x _ => x.val)
  · intro x _; exact mem_range.mpr x.isLt
  · intro x _; rfl
  · intro a _ b _ h; exact Fin.ext h
  · intro b hb; exact ⟨⟨b,mem_range.mp hb⟩,mem_univ _,rfl⟩

theorem boxMean_eq_fin (n N : ℕ) (f : (Fin n → ℕ) → ℂ) :
    boxMean n N f = 𝔼 x : Fin n → Fin N, f (fun i => (x i).val) := by
  classical
  induction n with
  | zero =>
    have he : (fun x : Fin 0 → Fin N => f (fun i => (x i).val)) = fun _ => f Fin.elim0 := by
      funext x
      congr 1
      funext i
      exact Fin.elim0 i
    rw [he]
    simp
  | succ n ih =>
    rw [BoxPolynomialLines.boxMean_succ]
    simp_rw [ih]
    rw [mean_eq_fin,← Finset.expect_product']
    apply Finset.expect_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Fin N))
    · intro x; simp
    · intro x _
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def indicator {α : Type*} (S : Set α) (x : α) : ℂ := by
  classical
  exact if x ∈ S then 1 else 0

def count (n N : ℕ) (S : Set (Fin n → ℕ)) : ℕ := by
  classical
  exact (univ.filter (fun x : Fin n → Fin N => (fun i => (x i).val) ∈ S)).card

 

theorem boxMean_indicator (n N : ℕ) (S : Set (Fin n → ℕ)) :
    ‖boxMean n N (indicator S)‖ = (count n N S:ℝ)/(N:ℝ)^n := by
  classical
  rw [boxMean_eq_fin,Finset.expect_eq_sum_div_card]
  simp only [indicator,Finset.sum_boole,Finset.card_univ,Fintype.card_fun,
    Fintype.card_fin]
  rw [norm_div]
  norm_cast

end
end BoxCounting

namespace DenseBoxModularPolynomial
open scoped BigOperators
open PolynomialWeyl BoxPolynomialLines PolynomialLineCoefficients TriangularLatticeRecovery
open MultivariateCoefficientRecovery Finset
noncomputable section

def eval {n d : ℕ} (a : Grid n d → ℝ) (x : Fin n → ℕ) : ℝ :=
  ∑ e, a e * ∏ i, (x i : ℝ) ^ (e i).val

theorem circleNorm_le_integer_error (a : ℝ) (m : ℤ) : circleNorm a ≤ |a - m| := by
  rw [circleNorm, UnitAddCircle.norm_eq]
  exact round_le a m

theorem circleNorm_le_one (a : ℝ) : circleNorm a ≤ 1 := by
  rw [circleNorm, UnitAddCircle.norm_eq]
  exact (abs_sub_round a).trans (by norm_num)

theorem division_length {N K : ℕ} (hK : 0 < K) (hKN : K ≤ N) :
    0 < N / K ∧ N / K * K ≤ N ∧ N ≤ 2 * K * (N / K) := by
  have hH : 0 < N / K := Nat.div_pos hKN hK
  have hmod := Nat.mod_lt N hK
  have heq := Nat.mod_add_div N K
  have hKH : K ≤ K * (N / K) := by nlinarith
  exact ⟨hH, Nat.div_mul_le_self N K, by nlinarith only [heq, hmod, hKH]⟩

theorem common_denominator {V : Type*} [Fintype V] (B : ℕ)
    (q : V → ℕ) (hq : ∀ v, 0 < q v) (hqB : ∀ v, q v ≤ B)
    (b : V → ℕ → ℝ) (N D : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ v j, 0 < j → j ≤ D → circleNorm ((q v : ℝ) * b v j) * (N : ℝ) ^ j ≤ A) :
    ∃ Q : ℕ, 0 < Q ∧ Q ≤ B ^ Fintype.card V ∧
      ∀ v j, 0 < j → j ≤ D →
        circleNorm ((Q : ℝ) * b v j) * (N : ℝ) ^ j ≤ (B ^ Fintype.card V : ℕ) * A := by
  classical
  let Q := ∏ v, q v
  have hQ : 0 < Q := Finset.prod_pos (fun v _ => hq v)
  have hQB : Q ≤ B ^ Fintype.card V := by
    calc
      _ ≤ ∏ _v : V, B := Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun v _ => hqB v)
      _ = _ := by simp
  refine ⟨Q, hQ, hQB, ?_⟩
  intro v j hj hjD
  have hd : q v ∣ Q := Finset.dvd_prod_of_mem q (Finset.mem_univ v)
  have hm : Q / q v ≤ B ^ Fintype.card V := (Nat.div_le_self ..).trans hQB
  have he : ((Q / q v : ℕ) : ℝ) * ((q v : ℝ) * b v j) = (Q : ℝ) * b v j := by
    rw [← mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel hd]
  have hh := scaled_nat_bound (Q / q v) ((q v : ℝ) * b v j) N A
    ((B ^ Fintype.card V : ℕ) : ℝ) j (Nat.cast_nonneg _) hA (Nat.cast_le.mpr hm) (hb v j hj hjD)
  simpa only [he] using hh

theorem line_scale_coeff {n d : ℕ} (a : Grid n d → ℝ) (x v : Fin n → ℕ) (q : ℝ) (j : ℕ) :
    (line (fun e => q * a e) x v).coeff j = q * (line a x v).coeff j := by
  simp only [line_coeff, Finset.mul_sum, mul_assoc]

def indicator {α : Type*} (S : Set α) (x : α) : ℂ := by
  classical
  exact if x ∈ S then 1 else 0

lemma norm_indicator {α : Type*} (S : Set α) (x : α) :
    ‖indicator S x‖ ≤ 1 := by
  classical
  by_cases h : x ∈ S <;> simp [indicator,h]

lemma mean_indicator {α : Type*} (S : Set α) [DecidablePred (· ∈ S)] (x : ℕ → α) (H : ℕ) :
    ‖mean H (fun t => indicator S (x t))‖ =
      ((range H).filter (fun t => x t ∈ S)).card / (H:ℝ) := by
  classical
  rw [mean,Finset.expect_eq_sum_div_card]
  simp only [indicator,Finset.card_range]
  rw [norm_div]
  norm_cast
  simp

lemma abs_multiplier (q : ℤ) (a : ℝ) :
    circleNorm ((q.natAbs:ℝ)*a) = circleNorm ((q:ℝ)*a) := by
  rw [Nat.cast_natAbs,Int.cast_abs]
  rcases le_total 0 (q:ℝ) with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,neg_mul,circleNorm,AddCircle.coe_neg,norm_neg]
    rfl

 

theorem line_test_constants (n d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B N₀ : ℕ, 0 < B ∧ 0 < N₀ ∧ ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
      ∀ S : Set (Fin n → ℕ), ∀ a : Grid n d → ℝ,
        (∀ x ∈ S, ∃ z : ℤ, |eval a x-z| ≤ ε) →
        δ ≤ ‖boxMean n N (indicator S)‖ → ∀ v : Grid n d,
        ∃ x : Fin n → ℕ, (∀ i, x i ≤ N) ∧ ∃ q : ℕ, 0 < q ∧ q ≤ B ∧
          ∀ j : ℕ, 0 < j → j ≤ n*d →
            circleNorm ((q:ℝ)*(line a x (fun i => (v i).val)).coeff j) *
              (N:ℝ)^j ≤ A*ε := by
  classical
  obtain ⟨B,hB,ε₀,hε₀,L,hL,hinv⟩ :=
    DenseModularPolynomial.lattice_inverse (n*d) (δ/2) (by positivity)
  obtain ⟨K,hK⟩ := exists_nat_gt (max (1:ℝ) (4*(n*d:ℕ)/δ))
  have hK₁ : (1:ℝ) ≤ K := (le_max_left _ _).trans hK.le
  have hK₀ : 0 < K := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hK₁)
  have hshortK : 4*(n*d:ℕ) ≤ δ*K := by
    have := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hK.le)
    nlinarith only [this]
  let A : ℝ := (B:ℝ)*(2*K:ℕ)^(n*d)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨B,K*L,hB,Nat.mul_pos hK₀ hL,ε₀,A,hε₀,hA,?_⟩
  intro N hN₀N ε hε hεsmall S a hgood hlarge v
  have hKN : K ≤ N := (by nlinarith : K ≤ K*L).trans hN₀N
  have hN : 0 < N := hK₀.trans_le hKN
  let H := N/K
  obtain ⟨hH,hHK,hNH⟩ := division_length hK₀ hKN
  have hLH : L ≤ H := (Nat.le_div_iff_mul_le hK₀).mpr (by simpa [Nat.mul_comm] using hN₀N)
  have hsum : (∑ i, (v i).val : ℕ) ≤ n*d := totalDegree_le v
  have hshort : 2*(H:ℝ)*(∑ i, (v i).val : ℕ)/N ≤ δ/2 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
    have hHK' : (H:ℝ)*K ≤ N := by exact_mod_cast hHK
    have hsum' : ((∑ i, (v i).val : ℕ):ℝ) ≤ (n*d:ℕ) := by exact_mod_cast hsum
    have h₁ := mul_le_mul_of_nonneg_left hshortK (Nat.cast_nonneg H : (0:ℝ) ≤ H)
    have h₂ := mul_le_mul_of_nonneg_left hHK' hδ.le
    have h₃ := mul_le_mul_of_nonneg_left hsum' (Nat.cast_nonneg H : (0:ℝ) ≤ H)
    nlinarith only [h₁,h₂,h₃]
  obtain ⟨x,hx,hline⟩ := exists_correlated_line n hN hH (indicator S)
    (norm_indicator S) (fun i => (v i).val) hlarge hshort
  rw [mean_indicator] at hline
  let T := (range H).filter (fun t => x + (fun i => t*(v i).val) ∈ S)
  have hT : δ/2*(H:ℝ) ≤ (T.card:ℝ) :=
    (le_div_iff₀ (Nat.cast_pos.mpr hH)).mp hline
  have hTgood : ∀ k ∈ T, ∃ z : ℤ,
      |(line a x (fun i => (v i).val)).eval (k:ℝ)-z| ≤ ε := by
    intro k hk
    have hh := hgood _ (mem_filter.mp hk).2
    simpa only [line_eval,eval,Pi.add_apply] using hh
  obtain ⟨q,hq,hqB,m,hm⟩ := hinv H hLH ε hε hεsmall T
    (filter_subset _ _) hT (line a x (fun i => (v i).val)) (line_degree ..) hTgood
  have hqabs : 0 < q.natAbs := Int.natAbs_pos.mpr hq
  have hqabsB : q.natAbs ≤ B := by
    rw [← Int.natCast_natAbs] at hqB
    exact_mod_cast hqB
  refine ⟨x,(fun i => (hx i).le),q.natAbs,hqabs,hqabsB,?_⟩
  intro j hj hjd
  rw [abs_multiplier]
  have hc := (circleNorm_le_integer_error ((q:ℝ)*(line a x (fun i => (v i).val)).coeff j)
    (m j)).trans (hm j hj hjd)
  have hpow : (N:ℝ)^j ≤ (2*K:ℕ)^(n*d)*(H:ℝ)^j := by
    have hNH' : (N:ℝ) ≤ (2*K:ℕ)*(H:ℝ) := by exact_mod_cast hNH
    calc
      _ ≤ ((2*K:ℕ)*(H:ℝ))^j := pow_le_pow_left₀ (by positivity) hNH' _
      _ = (2*K:ℕ)^j*(H:ℝ)^j := mul_pow _ _ _
      _ ≤ (2*K:ℕ)^(n*d)*(H:ℝ)^j := by
        gcongr
        exact_mod_cast (by omega : 1 ≤ 2*K)
  calc
    _ ≤ ((B:ℝ)*ε/(H:ℝ)^j) * ((2*K:ℕ)^(n*d)*(H:ℝ)^j) :=
      mul_le_mul hc hpow (by positivity) (by positivity)
    _ = A*ε := by
      dsimp [A]
      field_simp [ne_of_gt (Nat.cast_pos.mpr hH : (0:ℝ) < H)]

 

theorem lattice_inverse (n d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C N₀ : ℕ, 0 < C ∧ 0 < N₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
      ∀ S : Set (Fin n → ℕ), ∀ a : Grid n d → ℝ,
        (∀ x ∈ S, ∃ z : ℤ, |eval a x-z| ≤ ε) →
        δ ≤ ‖boxMean n N (indicator S)‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ C ∧ ∀ e : Grid n d, 0 < totalDegree e →
          circleNorm ((q:ℝ)*a e)*(N:ℝ)^totalDegree e ≤ (C:ℝ)*ε := by
  classical
  obtain ⟨B,N₀,hB,hN₀,ε₀,A,hε₀,hA,htest⟩ := line_test_constants n d δ hδ
  obtain ⟨R,T,hR,hT,hrec⟩ := recovery_constants n d
  let B' := B ^ Fintype.card (Grid n d)
  have hB' : 0 < B' := pow_pos hB _
  obtain ⟨C,hC⟩ := exists_nat_gt (max ((R*B':ℕ):ℝ) ((T:ℝ)*B'*A))
  have hRC : R*B' ≤ C := by exact_mod_cast (le_max_left _ _).trans hC.le
  have hTC : (T:ℝ)*B'*A ≤ C := (le_max_right _ _).trans hC.le
  have hCpos : 0 < C := (Nat.mul_pos hR hB').trans_le hRC
  refine ⟨C,N₀,hCpos,hN₀,ε₀,hε₀,?_⟩
  intro N hN₀N ε hε hεsmall S a hgood hlarge
  have hN : 0 < N := hN₀.trans_le hN₀N
  have ht := htest N hN₀N ε hε hεsmall S a hgood hlarge
  choose x hx q hq hqB hb using ht
  obtain ⟨q',hq',hqB',happrox⟩ := common_denominator B q hq hqB
    (fun v j => (line a (x v) (fun i => (v i).val)).coeff j) N (n*d) (A*ε)
    (by positivity) hb
  have hrec' := hrec N hN x hx (fun e => (q':ℝ)*a e) ((B':ℝ)*(A*ε))
    (by positivity) (by
      intro v j hj hjd
      rw [line_scale_coeff]
      exact happrox v j hj hjd)
  refine ⟨R*q',Nat.mul_pos hR hq',(Nat.mul_le_mul_left R hqB').trans hRC,?_⟩
  intro e he
  have hh := hrec' e he
  simp only [Nat.cast_mul]
  rw [mul_assoc]
  exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hTC hε)

 

theorem lattice_inverse_cardinal (n d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C N₀ : ℕ, 0 < C ∧ 0 < N₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
      ∀ S : Set (Fin n → ℕ), ∀ a : Grid n d → ℝ,
        (∀ x ∈ S, ∃ z : ℤ, |eval a x-z| ≤ ε) →
        δ*(N:ℝ)^n ≤ (BoxCounting.count n N S:ℝ) →
        ∃ q : ℕ, 0 < q ∧ q ≤ C ∧ ∀ e : Grid n d, 0 < totalDegree e →
          circleNorm ((q:ℝ)*a e)*(N:ℝ)^totalDegree e ≤ (C:ℝ)*ε := by
  obtain ⟨C,N₀,hC,hN₀,ε₀,hε₀,h⟩ := lattice_inverse n d δ hδ
  refine ⟨C,N₀,hC,hN₀,ε₀,hε₀,?_⟩
  intro N hN ε hε hεsmall S a hgood hcount
  apply h N hN ε hε hεsmall S a hgood
  change δ ≤ ‖boxMean n N (BoxCounting.indicator S)‖
  rw [BoxCounting.boxMean_indicator]
  exact (le_div_iff₀ (pow_pos (Nat.cast_pos.mpr (hN₀.trans_le hN)) _)).mpr hcount

end
end DenseBoxModularPolynomial

end
end
end
end

end OAI
