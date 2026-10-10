import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalFactor01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
end
 

 
section
open scoped BigOperators
noncomputable section
namespace RationalFactorPeriods
open CubeFaces CubePolynomials
variable {G : Type*} [Group G]

lemma orderedWord_mem {H : Filtration G} {k l : ℕ} (a : Fin l → G) (j : Fin l → ℕ)
    (ha : ∀ i, a i ∈ H.level (j i+k)) : orderedWord a j ∈ polynomials H k := by
  have hs : ((List.finRange l).map (fun i => (fun n : ℤ => a i ^ Ring.choose n (j i)))).prod
      ∈ polynomials H k := by
    apply Subgroup.list_prod_mem
    intro f hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    exact NilpotentTaylor.binomial_mem (j i) k (a i) (ha i)
  convert hs using 1
  funext n
  simp [orderedWord,Pi.list_prod_apply,List.map_map,Function.comp_def]

lemma orderedWord_character (χ : G →* Multiplicative ℝ) {l : ℕ}
    (a : Fin l → G) (j : Fin l → ℕ) (n : ℤ) :
    (χ (orderedWord a j n)).toAdd = ∑ i, ((Ring.choose n (j i) : ℤ) : ℝ) * (χ (a i)).toAdd := by
  rw [orderedWord_map]
  simp only [orderedWord,toAdd_list_sum,List.map_map,Function.comp_def,toAdd_zpow,zsmul_eq_mul]
  exact (Fin.sum_univ_def (fun i : Fin l => ((Ring.choose n (j i) : ℤ) : ℝ) * (χ (a i)).toAdd)).symm

lemma List.prod_finRange_castSucc {d : ℕ} (f : Fin (d+1) → G) :
    ((List.finRange (d+1)).map f).prod =
      ((List.finRange d).map (fun i => f i.castSucc)).prod * f (Fin.last d) := by
  rw [List.finRange_succ_last,List.map_append,List.prod_append]
  simp [List.map_map,Function.comp_def]

lemma word_eq_orderedWord (a : ℕ → G) (d : ℕ) :
    NilpotentTaylor.word a d = orderedWord (fun i : Fin d => a i.val) (fun i => i.val) := by
  induction d with
  | zero => funext n; simp [NilpotentTaylor.word,orderedWord]
  | succ d ih =>
    funext n
    simp only [NilpotentTaylor.word,Pi.mul_apply,ih,orderedWord,List.prod_finRange_castSucc]
    rfl

end RationalFactorPeriods
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace NilpotentTaylor
open CubeFaces CubePolynomials RationalFactorPeriods
variable {G : Type*} [Group G]

lemma word_zero (a : ℕ → G) (d : ℕ) : word a (d+1) 0 = a 0 := by
  induction d with
  | zero => simp [word]
  | succ d ih => simpa [word,Ring.choose_zero_succ] using ih

lemma choose_one_high {d : ℕ} (hd : 2 ≤ d) : Ring.choose (1:ℤ) d = 0 := by
  rw [← Int.natCast_one,Ring.choose_natCast,Nat.choose_eq_zero_of_lt (by omega : 1 < d),Nat.cast_zero]

lemma word_one (a : ℕ → G) (d : ℕ) : word a (d+2) 1 = a 0 * a 1 := by
  induction d with
  | zero => simp [word]
  | succ d ih =>
    change word a (d+2) 1 * a (d+2) ^ Ring.choose (1:ℤ) (d+2) = _
    rw [choose_one_high (by omega),zpow_zero,mul_one,ih]

lemma word_tail_two (a : ℕ → G) (d : ℕ) (h0 : a 0=1) (h1 : a 1=1) :
    word a (d+2) = orderedWord (fun i : Fin d => a (i.val+2)) (fun i => i.val+2) := by
  induction d with
  | zero => funext n; simp [word,orderedWord,h0,h1]
  | succ d ih =>
    funext n
    change word a (d+2) n * a (d+2) ^ Ring.choose n (d+2) = _
    rw [ih]
    simp only [orderedWord,RationalFactorPeriods.List.prod_finRange_castSucc]
    rfl

 

theorem normalized_taylor (H : Filtration G) (s : ℕ) (hbot : H.level s = ⊥)
    (g : ℤ → G) (hg : g ∈ polynomials H 0) (h0 : g 0=1) (h1 : g 1=1) :
    ∃ a : Fin s → G, (∀ i, a i ∈ H.level (i.val+2)) ∧
      g = orderedWord a (fun i => i.val+2) := by
  have hb : H.level ((s+2)+0) = ⊥ := by
    apply le_bot_iff.mp
    simpa [hbot] using H.antitone (show s ≤ (s+2)+0 by omega)
  obtain ⟨a,ha,he⟩ := exists_taylor hb hg
  have ha0 : a 0=1 := by
    have hx := congrFun he 0
    rw [h0,show s+2=(s+1)+1 by omega,word_zero] at hx
    exact hx.symm
  have ha1 : a 1=1 := by
    have hx := congrFun he 1
    rw [h1,word_one,ha0,one_mul] at hx
    exact hx.symm
  refine ⟨fun i => a (i.val+2),fun i => ?_,?_⟩
  · simpa using ha (i.val+2) (by omega)
  · exact he.trans (word_tail_two a s ha0 ha1)

 

theorem normalized_subgroup_taylor (H : Filtration G) (s : ℕ) (hbot : H.level s = ⊥)
    (g : ℤ → G) (hg : g ∈ polynomials H 0) (h0 : g 0=1)
    (h1 : g 1 ∈ H.level 1) :
    ∃ a : Fin s → H.level 2,
      (∀ i, (a i).val ∈ H.level (i.val+2)) ∧
      ∀ z, g z = (orderedWord a (fun i => i.val+2) z).val * g 1 ^ z := by
  let lin : ℤ → G := fun z => g 1 ^ z
  have hlin : lin ∈ polynomials H 0 := by
    simpa [lin] using binomial_mem (H:=H) 1 0 (g 1) h1
  let f : ℤ → G := g * lin⁻¹
  have hf : f ∈ polynomials H 0 := (polynomials H 0).mul_mem hg ((polynomials H 0).inv_mem hlin)
  have hf0 : f 0=1 := by simp [f,lin,h0]
  have hf1 : f 1=1 := by simp [f,lin]
  obtain ⟨a,ha,he⟩ := normalized_taylor H s hbot f hf hf0 hf1
  let a' : Fin s → H.level 2 := fun i => ⟨a i,H.antitone (by omega : 2 ≤ i.val+2) (ha i)⟩
  refine ⟨a',ha,fun z => ?_⟩
  have hz := congrFun he z
  change g z * (g 1 ^ z)⁻¹ = orderedWord a (fun i => i.val+2) z at hz
  have hm := orderedWord_map (H.level 2).subtype a' (fun i => i.val+2) z
  change ((orderedWord a' (fun i => i.val+2) z : H.level 2):G) = orderedWord a _ z at hm
  rw [hm,←hz]
  group

end NilpotentTaylor
end
end
 

 
section

 

namespace PolynomialWeyl
open scoped BigOperators ComplexConjugate
noncomputable section

 
def mean (N : ℕ) (f : ℕ → ℂ) : ℂ := 𝔼 x ∈ Finset.range N, f x

def derivative (a b : ℕ) (f : ℕ → ℂ) (x : ℕ) : ℂ :=
  f (x + a) * conj (f (x + b))

theorem norm_mean_le_one {N : ℕ} (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖mean N f‖ ≤ 1 := by
  by_cases hN : N = 0
  · simp [mean, hN]
  · exact (RCLike.norm_expect_le (K := ℂ)).trans
      (Finset.expect_le (Finset.nonempty_range_iff.mpr hN)
        (fun x _ => hf x))

theorem norm_derivative_le_one (a b : ℕ) (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∀ x, ‖derivative a b f x‖ ≤ 1 := by
  intro x
  simp only [derivative, norm_mul, RCLike.norm_conj]
  calc
    _ ≤ 1 * 1 := mul_le_mul (hf (x + a)) (hf (x + b)) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

 
theorem norm_mean_shift_sub_le {N : ℕ} (hN : 0 < N) (h : ℕ) (f : ℕ → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖mean N (fun x => f (x + h)) - mean N f‖ ≤ 2 * (h : ℝ) / N := by
  have hs : (∑ x ∈ Finset.range N, f (x + h)) - (∑ x ∈ Finset.range N, f x) =
      (∑ x ∈ Finset.range h, f (x + N)) - (∑ x ∈ Finset.range h, f x) := by
    have h₁ := Finset.sum_range_add f N h
    have h₂ := Finset.sum_range_add f h N
    rw [Nat.add_comm h N] at h₂
    have e₁ : (∑ x ∈ Finset.range h, f (N + x)) = ∑ x ∈ Finset.range h, f (x + N) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.add_comm N x]
    have e₂ : (∑ x ∈ Finset.range N, f (h + x)) = ∑ x ∈ Finset.range N, f (x + h) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.add_comm h x]
    rw [e₁] at h₁
    rw [e₂] at h₂
    linear_combination h₁ - h₂
  have hb (k : ℕ) : ‖∑ x ∈ Finset.range h, f (x + k)‖ ≤ (h : ℝ) := by
    calc
      _ ≤ ∑ x ∈ Finset.range h, ‖f (x + k)‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ Finset.range h, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hf (x + k))
      _ = _ := by simp
  have hb₀ : ‖∑ x ∈ Finset.range h, f x‖ ≤ (h : ℝ) := by simpa using hb 0
  rw [mean, mean, Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  simp only [Finset.card_range, ← sub_div, hs, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr hN).le
  calc
    _ ≤ ‖∑ x ∈ Finset.range h, f (x + N)‖ + ‖∑ x ∈ Finset.range h, f x‖ := norm_sub_le _ _
    _ ≤ 2 * (h : ℝ) := by linarith [hb N]

 
theorem norm_expect_sq_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖𝔼 i ∈ s, f i‖ ^ 2 ≤ 𝔼 i ∈ s, ‖f i‖ ^ 2 := by
  classical
  by_cases hs : s.Nonempty
  · have h₁ := RCLike.norm_expect_le (K := ℂ) (s := s) (f := f)
    have h₂ := Finset.expect_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.expect_const hs] at h₂
    nlinarith [norm_nonneg (𝔼 i ∈ s, f i)]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

 
theorem shift_average_error {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(𝔼 x ∈ Finset.range N, 𝔼 h ∈ Finset.range H, f (x + h)) - mean N f‖ ≤
      2 * (H : ℝ) / N := by
  rw [Finset.expect_comm]
  conv_lhs => rhs; rw [← Finset.expect_const (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hH)) (mean N f)]
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hH))
  intro h hh
  apply (norm_mean_shift_sub_le hN h f hf).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have : (h : ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp hh).le
  linarith

 
theorem norm_expect_sq_eq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖𝔼 i ∈ s, f i‖ ^ 2 = (𝔼 a ∈ s, 𝔼 b ∈ s, f a * conj (f b)).re := by
  simp_rw [← Finset.mul_expect, ← map_expect (starRingEnd ℂ)]
  rw [← Finset.expect_mul, Complex.mul_conj]
  rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq]

 

theorem van_der_corput {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖mean N f‖ ^ 2 ≤
      (𝔼 a ∈ Finset.range H, 𝔼 b ∈ Finset.range H, ‖mean N (derivative a b f)‖) +
      4 * (H : ℝ) / N := by
  let z := 𝔼 x ∈ Finset.range N, 𝔼 h ∈ Finset.range H, f (x + h)
  have hz : ‖z‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))
    intro x _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact Finset.expect_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hH)) (fun h _ => hf (x + h))
  have hm := norm_mean_le_one f hf (N := N)
  have he := shift_average_error hN hH f hf
  have ht : ‖mean N f‖ - ‖z‖ ≤ 2 * (H : ℝ) / N := by
    have ht := norm_sub_norm_le (mean N f) z
    rw [norm_sub_rev] at ht
    exact ht.trans he
  have hs : ‖mean N f‖ ^ 2 ≤ ‖z‖ ^ 2 + 4 * (H : ℝ) / N := by
    have he₀ : 0 ≤ 2 * (H : ℝ) / N := by positivity
    have he₁ := mul_le_mul_of_nonneg_right ht (show 0 ≤ ‖mean N f‖ + ‖z‖ by positivity)
    have he₂ := mul_le_mul_of_nonneg_left (show ‖mean N f‖ + ‖z‖ ≤ 2 by linarith) he₀
    have hr : 2 * (H : ℝ) / N * 2 = 4 * H / N := by ring
    rw [hr] at he₂
    nlinarith
  apply hs.trans
  apply add_le_add _ le_rfl
  calc
    ‖z‖ ^ 2 ≤ 𝔼 x ∈ Finset.range N, ‖𝔼 h ∈ Finset.range H, f (x + h)‖ ^ 2 :=
      norm_expect_sq_le _ _
    _ = (𝔼 a ∈ Finset.range H, 𝔼 b ∈ Finset.range H,
        mean N (derivative a b f)).re := by
      simp only [norm_expect_sq_eq, ← Complex.re_expect]
      congr 1
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro a _
      rw [Finset.expect_comm]
      rfl
    _ ≤ _ := by
      rw [Complex.re_expect]
      apply Finset.expect_le_expect
      intro a _
      rw [Complex.re_expect]
      exact Finset.expect_le_expect (fun b _ => Complex.re_le_norm _)

 
theorem pow_le_pow_add_error {x y e : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) (he : 0 ≤ e) (hxy : x ≤ y + e) (n : ℕ) :
    x ^ n ≤ y ^ n + n * e := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hy := pow_le_one₀ hy₀ hy₁ (n := n)
    have hp := pow_nonneg hy₀ n
    have hn : 0 ≤ (n : ℝ) * e := mul_nonneg (Nat.cast_nonneg _) he
    have h₁ := mul_le_mul_of_nonneg_right ih hx₀
    have h₂ := mul_le_mul_of_nonneg_left hxy hp
    have h₃ := mul_le_mul_of_nonneg_right hy he
    have h₄ := mul_le_mul_of_nonneg_left hx₁ hn
    rw [pow_succ, pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

 
theorem expect_pow_two_pow_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (k : ℕ) :
    (𝔼 i ∈ s, f i) ^ (2 ^ k) ≤ 𝔼 i ∈ s, (f i) ^ (2 ^ k) := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    have hcs := Finset.expect_mul_sq_le_sq_mul_sq s f (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.expect_const hs] at hcs
    calc
      _ = ((𝔼 i ∈ s, f i) ^ 2) ^ (2 ^ k) := by rw [← pow_mul]; congr 1; omega
      _ ≤ (𝔼 i ∈ s, (f i) ^ 2) ^ (2 ^ k) := pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ ≤ 𝔼 i ∈ s, ((f i) ^ 2) ^ (2 ^ k) := ih _
      _ = _ := by
        apply Finset.expect_congr rfl
        intro i _
        rw [← pow_mul]
        congr 1
        omega

 

def differencedMean (N H : ℕ) : ℕ → (ℕ → ℂ) → ℝ
  | 0, f => ‖mean N f‖
  | k + 1, f => 𝔼 a ∈ Finset.range H, 𝔼 b ∈ Finset.range H,
      differencedMean N H k (derivative a b f)

theorem differencedMean_nonneg (N H k : ℕ) (f : ℕ → ℂ) :
    0 ≤ differencedMean N H k f := by
  induction k generalizing f with
  | zero => exact norm_nonneg _
  | succ k ih =>
    exact Finset.expect_nonneg (fun a _ => Finset.expect_nonneg (fun b _ => ih _))

theorem differencedMean_le_one (N H k : ℕ) (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    differencedMean N H k f ≤ 1 := by
  induction k generalizing f with
  | zero => exact norm_mean_le_one f hf
  | succ k ih =>
    by_cases hH : H = 0
    · simp [differencedMean, hH]
    · exact Finset.expect_le (Finset.nonempty_range_iff.mpr hH) (fun a _ =>
        Finset.expect_le (Finset.nonempty_range_iff.mpr hH) (fun b _ =>
          ih _ (norm_derivative_le_one a b f hf)))

 

theorem iterated_van_der_corput {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (k : ℕ) (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖mean N f‖ ^ (2 ^ k) ≤
      differencedMean N H k f + ((2 : ℝ) ^ k - 1) * (4 * H / N) := by
  induction k generalizing f with
  | zero => simp [differencedMean]
  | succ k ih =>
    let u (a b : ℕ) := ‖mean N (derivative a b f)‖
    let v := 𝔼 a ∈ Finset.range H, 𝔼 b ∈ Finset.range H, u a b
    have hs := Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hH)
    have hv₀ : 0 ≤ v := Finset.expect_nonneg (fun a _ =>
      Finset.expect_nonneg (fun b _ => norm_nonneg _))
    have hv₁ : v ≤ 1 := Finset.expect_le hs (fun a _ => Finset.expect_le hs
      (fun b _ => norm_mean_le_one _ (norm_derivative_le_one a b f hf)))
    have hf₁ := norm_mean_le_one f hf (N := N)
    have hf₀ := norm_nonneg (mean N f)
    have hn : (‖mean N f‖ ^ 2) ≤ 1 := by nlinarith
    have he : 0 ≤ 4 * (H : ℝ) / N := by positivity
    have hpow := pow_le_pow_add_error (sq_nonneg _) hn hv₀ hv₁ he
      (van_der_corput hN hH f hf) (2 ^ k)
    calc
      _ = (‖mean N f‖ ^ 2) ^ (2 ^ k) := by rw [← pow_mul]; congr 1; omega
      _ ≤ v ^ (2 ^ k) + (2 ^ k : ℕ) * (4 * (H : ℝ) / N) := hpow
      _ ≤ (𝔼 a ∈ Finset.range H, 𝔼 b ∈ Finset.range H, (u a b) ^ (2 ^ k)) +
          (2 ^ k : ℕ) * (4 * (H : ℝ) / N) := by
        apply add_le_add _ le_rfl
        exact (expect_pow_two_pow_le _ hs _ k).trans
          (Finset.expect_le_expect (fun a _ => expect_pow_two_pow_le _ hs _ k))
      _ ≤ (𝔼 a ∈ Finset.range H, 𝔼 b ∈ Finset.range H,
          (differencedMean N H k (derivative a b f) +
            ((2 : ℝ) ^ k - 1) * (4 * H / N))) +
          (2 ^ k : ℕ) * (4 * (H : ℝ) / N) := by
        apply add_le_add _ le_rfl
        exact Finset.expect_le_expect (fun a _ => Finset.expect_le_expect (fun b _ =>
          ih _ (norm_derivative_le_one a b f hf)))
      _ = _ := by
        simp only [Finset.expect_add_distrib, Finset.expect_const hs,
          differencedMean, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
        ring

 
def phase (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

@[simp] theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

@[simp] theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, mul_add, Complex.ofReal_add, Complex.exp_add, add_mul]

@[simp] theorem phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  rw [phase, phase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.ofReal_neg]
  ring

@[simp] theorem phase_sub (x y : ℝ) : phase (x - y) = phase x * conj (phase y) := by
  rw [sub_eq_add_neg, phase_add, phase_neg]

@[simp] theorem phase_nat_mul (x : ℝ) (n : ℕ) : phase ((n : ℝ) * x) = (phase x) ^ n := by
  rw [phase, phase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

 
def polynomialPhase (p : Polynomial ℝ) (x : ℕ) : ℂ := phase (p.eval (x : ℝ))

 
def polynomialDifference (a b : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.taylor (a : ℝ) p - Polynomial.taylor (b : ℝ) p

@[simp] theorem polynomialPhase_difference (a b : ℕ) (p : Polynomial ℝ) :
    polynomialPhase (polynomialDifference a b p) = derivative a b (polynomialPhase p) := by
  funext x
  simp [polynomialPhase, polynomialDifference, derivative, Polynomial.taylor_eval,
    Nat.cast_add]

 
theorem taylor_coeff_top (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (a : ℝ) :
    (Polynomial.taylor a p).coeff d = p.coeff d := by
  by_cases hd : p.natDegree = d
  · subst d
    exact Polynomial.coeff_taylor_natDegree a p
  · have hl : p.natDegree < d := lt_of_le_of_ne hp hd
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hl,
      Polynomial.coeff_eq_zero_of_natDegree_lt]
    rwa [Polynomial.natDegree_taylor]

 

theorem polynomialDifference_degree (a b : ℕ) (p : Polynomial ℝ) (d : ℕ)
    (hp : p.natDegree ≤ d + 1) :
    (polynomialDifference a b p).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  simp only [polynomialDifference, Polynomial.coeff_sub]
  by_cases he : n = d + 1
  · subst n
    rw [taylor_coeff_top p _ hp, taylor_coeff_top p _ hp, sub_self]
  · have hlt : p.natDegree < n := by omega
    have h₁ : (Polynomial.taylor (a : ℝ) p).natDegree < n := by
      rwa [Polynomial.natDegree_taylor]
    have h₂ : (Polynomial.taylor (b : ℝ) p).natDegree < n := by
      rwa [Polynomial.natDegree_taylor]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt h₁,
      Polynomial.coeff_eq_zero_of_natDegree_lt h₂, sub_self]

 
theorem taylor_coeff_below_top (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d + 1) (a : ℝ) :
    (Polynomial.taylor a p).coeff d = p.coeff d + (d + 1 : ℕ) * p.coeff (d + 1) * a := by
  rw [Polynomial.taylor_coeff]
  have hdeg : ((Polynomial.hasseDeriv d) p).natDegree < 2 := by
    have h := Polynomial.natDegree_hasseDeriv_le p d
    omega
  rw [Polynomial.eval_eq_sum_range' hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Polynomial.hasseDeriv_coeff, Nat.choose_self, Nat.cast_one,
    one_mul, pow_zero, mul_one, pow_one]
  rw [Nat.add_comm 1 d, Nat.choose_succ_self_right]

 
theorem polynomialDifference_coeff (a b : ℕ) (p : Polynomial ℝ) (d : ℕ)
    (hp : p.natDegree ≤ d + 1) :
    (polynomialDifference a b p).coeff d =
      (d + 1 : ℕ) * p.coeff (d + 1) * ((a : ℝ) - b) := by
  simp only [polynomialDifference, Polynomial.coeff_sub, taylor_coeff_below_top p d hp]
  ring

 
def linearBound (N : ℕ) (α : ℝ) : ℝ :=
  if phase α = 1 then 1 else min 1 (2 / ((N : ℝ) * ‖phase α - 1‖))

theorem norm_linear_mean_le {N : ℕ} (hN : 0 < N) (α β : ℝ) :
    ‖mean N (fun x => phase (α * x + β))‖ ≤ linearBound N α := by
  have hunit : ∀ x : ℕ, ‖phase (α * x + β)‖ ≤ 1 := by simp
  have h₁ := norm_mean_le_one _ hunit (N := N)
  unfold linearBound
  split_ifs with hα
  · exact h₁
  · apply le_min h₁
    have heq : mean N (fun x => phase (α * x + β)) =
        phase β * (∑ x ∈ Finset.range N, (phase α) ^ x) / (N : ℂ) := by
      simp only [mean, Finset.expect_eq_sum_div_card, Finset.card_range]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [phase_add, mul_comm α, phase_nat_mul, mul_comm]
    rw [heq, norm_div, norm_mul, norm_phase, one_mul, Complex.norm_natCast,
      geom_sum_eq hα, norm_div]
    have hb : ‖(phase α) ^ N - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖(phase α) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by simp only [norm_pow, norm_phase, one_pow, norm_one]; norm_num
    calc
      _ ≤ (2 / ‖phase α - 1‖) / N :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hb (norm_nonneg _))
          (Nat.cast_pos.mpr hN).le
      _ = _ := by ring

 

def weylBound (N H : ℕ) : ℕ → ℝ → ℝ
  | 0, α => linearBound N α
  | d + 1, α => 𝔼 a ∈ Finset.range H, 𝔼 b ∈ Finset.range H,
      weylBound N H d ((d + 2 : ℕ) * α * ((a : ℝ) - b))

theorem differencedMean_polynomial_le {N : ℕ} (hN : 0 < N) (H d : ℕ)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ d + 1) :
    differencedMean N H d (polynomialPhase p) ≤ weylBound N H d (p.coeff (d + 1)) := by
  induction d generalizing p with
  | zero =>
    have he (x : ℕ) : p.eval (x : ℝ) = p.coeff 1 * x + p.coeff 0 := by
      rw [Polynomial.eval_eq_sum_range' (show p.natDegree < 2 by omega)]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        pow_zero, mul_one, pow_one]
      ring
    change ‖mean N (fun x => phase (p.eval (x : ℝ)))‖ ≤ linearBound N (p.coeff 1)
    simp_rw [he]
    exact norm_linear_mean_le hN (p.coeff 1) (p.coeff 0)
  | succ d ih =>
    apply Finset.expect_le_expect
    intro a _
    apply Finset.expect_le_expect
    intro b _
    have h := ih (polynomialDifference a b p) (polynomialDifference_degree a b p (d + 1) hp)
    rwa [polynomialPhase_difference, polynomialDifference_coeff a b p (d + 1) hp] at h

 

theorem polynomial_weyl_inequality {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (d : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ d + 1) :
    ‖mean N (polynomialPhase p)‖ ^ (2 ^ d) ≤
      weylBound N H d (p.coeff (d + 1)) + ((2 : ℝ) ^ d - 1) * (4 * H / N) := by
  apply (iterated_van_der_corput hN hH d (polynomialPhase p) (fun x => by simp [polynomialPhase])).trans
  exact add_le_add (differencedMean_polynomial_le hN H d p hp) le_rfl

@[simp] theorem phase_int (m : ℤ) : phase (m : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I m using 1
  congr 1
  push_cast
  ring

 

theorem exists_int_close_of_phase (α : ℝ) :
    ∃ m : ℤ, |α - m| ≤ ‖phase α - 1‖ / 4 := by
  let m : ℤ := ⌊α + 1 / 2⌋
  let t : ℝ := α - m
  have ht : |t| ≤ 1 / 2 := by
    apply abs_le.mpr
    have h₁ := Int.floor_le (α + 1 / 2)
    have h₂ := Int.lt_floor_add_one (α + 1 / 2)
    dsimp [t, m]
    constructor <;> linarith
  have he : phase t = phase α := by simp [t]
  have hnorm : ‖phase t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
    unfold phase
    rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
    have harg : 2 * Real.pi * t / 2 = Real.pi * t := by ring
    rw [harg, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbound : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hbound
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hsim : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by field_simp
  rw [hsim] at hs
  refine ⟨m, ?_⟩
  change |t| ≤ _
  rw [← he, hnorm]
  linarith

theorem linear_inverse {N : ℕ} (hN : 0 < N) (α β δ : ℝ)
    (hδ : 0 < δ) (hlarge : δ ≤ ‖mean N (fun x => phase (α * x + β))‖) :
    ∃ m : ℤ, |α - m| ≤ 1 / (δ * N) := by
  obtain ⟨m, hm⟩ := exists_int_close_of_phase α
  refine ⟨m, hm.trans ?_⟩
  have hNp : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  by_cases hα : phase α = 1
  · simp only [hα, sub_self, norm_zero, zero_div]
    positivity
  · have hnorm : 0 < ‖phase α - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hα)
    have hl := norm_linear_mean_le hN α β
    simp only [linearBound, ite_eq_right hα] at hl
    have hd : δ ≤ 2 / ((N : ℝ) * ‖phase α - 1‖) := hlarge.trans (hl.trans (min_le_right _ _))
    have hd' := (le_div_iff₀ (mul_pos hNp hnorm)).mp hd
    apply (le_div_iff₀ (mul_pos hδ hNp)).mpr
    nlinarith

end
end PolynomialWeyl

 

end
end
end
end

end OAI
