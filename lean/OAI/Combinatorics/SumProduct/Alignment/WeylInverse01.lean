import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.NearLattice01
import OAI.Combinatorics.SumProduct.Alignment.PolynomialWeyl01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
namespace WeylInverse
open scoped BigOperators ComplexConjugate
open PolynomialWeyl NearLattice
noncomputable section

 

theorem density_of_large_average {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : ∀ x ∈ S, f x ≤ 1)
    (havg : 2 * t ≤ 𝔼 x ∈ S, f x) :
    t * S.card ≤ ((S.filter (fun x => t ≤ f x)).card : ℝ) := by
  classical
  have h : (∑ x ∈ S, f x) ≤ ∑ x ∈ S, (t + if t ≤ f x then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro x hx
    split_ifs with htx
    · linarith [hf x hx]
    · linarith
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole] at h
  rw [Finset.expect_eq_sum_div_card] at havg
  have hc : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have havg' := (le_div_iff₀ hc).mp havg
  nlinarith

 
theorem exists_dense_fiber (S : Finset ℕ) (A : ℕ) (hA : 0 < A) (q : ℕ → ℕ)
    (hq : ∀ n ∈ S, q n ∈ Finset.Icc 1 A) :
    ∃ a ∈ Finset.Icc 1 A,
      (S.card : ℝ) / A ≤ ((S.filter (fun n => q n = a)).card : ℝ) := by
  have hs : (Finset.Icc 1 A).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hA⟩⟩
  have he : (𝔼 a ∈ Finset.Icc 1 A, ((S.filter (fun n => q n = a)).card : ℝ)) =
      (S.card : ℝ) / A := by
    rw [Finset.expect_eq_sum_div_card]
    have hsum : (∑ a ∈ Finset.Icc 1 A, ((S.filter (fun n => q n = a)).card : ℝ)) = S.card := by
      exact_mod_cast (Finset.card_eq_sum_card_fiberwise hq).symm
    rw [hsum]
    simp
  exact Finset.exists_le_of_le_expect hs he.ge

 

theorem exists_dense_derivatives {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hlarge : δ ≤ ‖mean N f‖) (hboundary : 4 * (H : ℝ) / N ≤ δ ^ 2 / 2) :
    ∃ b ∈ Finset.range H, ∃ S : Finset ℕ,
      (∀ a ∈ S, a < H) ∧ δ ^ 2 / 4 * H ≤ (S.card : ℝ) ∧
      (∀ a ∈ S, δ ^ 2 / 4 ≤ ‖mean N (derivative a b f)‖) := by
  classical
  have hv := van_der_corput hN hH f hf
  rw [Finset.expect_comm] at hv
  have havg : δ ^ 2 / 2 ≤
      𝔼 b ∈ Finset.range H, 𝔼 a ∈ Finset.range H, ‖mean N (derivative a b f)‖ := by
    nlinarith [norm_nonneg (mean N f)]
  have hs := Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hH)
  obtain ⟨b, hb, hbavg⟩ := Finset.exists_le_of_le_expect hs havg
  let t := δ ^ 2 / 4
  let S := (Finset.range H).filter (fun a => t ≤ ‖mean N (derivative a b f)‖)
  refine ⟨b, hb, S, ?_, ?_, ?_⟩
  · intro a ha
    exact Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  · have h := density_of_large_average (Finset.range H) hs
      (fun a => ‖mean N (derivative a b f)‖) t (by dsimp [t]; positivity)
      (fun a _ => norm_mean_le_one _ (norm_derivative_le_one a b f hf))
      (by dsimp [t]; linarith)
    simpa only [Finset.card_range] using h
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

 

def LeadingInverse (d : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ A : ℕ, 0 < A ∧
    ∀ N : ℕ, 0 < N → ∀ p : Polynomial ℝ, p.natDegree ≤ d →
      δ ≤ ‖mean N (polynomialPhase p)‖ →
      ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∃ m : ℤ,
        |(q : ℝ) * p.coeff d - m| ≤ (A : ℝ) / (N : ℝ) ^ d

 
theorem leading_inverse_one : LeadingInverse 1 := by
  intro δ hδ
  obtain ⟨A, hA⟩ := exists_nat_gt (1 / δ)
  have hA₀ : 0 < A := by
    have : (0 : ℝ) < A := lt_trans (one_div_pos.mpr hδ) hA
    exact_mod_cast this
  refine ⟨A, hA₀, ?_⟩
  intro N hN p hp hlarge
  have he (x : ℕ) : p.eval (x : ℝ) = p.coeff 1 * x + p.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range' (show p.natDegree < 2 by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, mul_one, pow_one]
    ring
  change δ ≤ ‖mean N (fun x => phase (p.eval (x : ℝ)))‖ at hlarge
  simp_rw [he] at hlarge
  obtain ⟨m, hm⟩ := linear_inverse hN (p.coeff 1) (p.coeff 0) δ hδ hlarge
  refine ⟨1, by omega, hA₀, m, ?_⟩
  simp only [Nat.cast_one, one_mul, pow_one]
  apply hm.trans
  calc
    1 / (δ * N) = (1 / δ) / N := by ring
    _ ≤ (A : ℝ) / N := div_le_div_of_nonneg_right hA.le (Nat.cast_nonneg _)

 

theorem leading_inverse_step_at_length (d : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (A K L N H : ℕ) (hA : 0 < A) (hK : 0 < K) (hN : 0 < N)
    (hH : 0 < H)
    (hboundary : 4 * (H : ℝ) / N ≤ δ ^ 2 / 2)
    (hdensity : (1 : ℝ) / K ≤ δ ^ 2 / (4 * A))
    (hHsize : 32 * K ^ 2 ≤ H)
    (hεsmall : (A : ℝ) / (N : ℝ) ^ d ≤ 1 / (16 * K))
    (hHL : (N : ℝ) ≤ (H : ℝ) * L)
    (hprev : ∀ p : Polynomial ℝ, p.natDegree ≤ d →
      δ ^ 2 / 4 ≤ ‖mean N (polynomialPhase p)‖ →
      ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∃ m : ℤ,
        |(q : ℝ) * p.coeff d - m| ≤ (A : ℝ) / (N : ℝ) ^ d)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ d + 1)
    (hlarge : δ ≤ ‖mean N (polynomialPhase p)‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2 * K * A * (d + 1) ∧ ∃ m : ℤ,
      |(q : ℝ) * p.coeff (d + 1) - m| ≤
        (16 * (K : ℝ) ^ 2 * A * L) / (N : ℝ) ^ (d + 1) := by
  classical
  obtain ⟨b, _, S, hSH, hScard, hSlarge⟩ := exists_dense_derivatives hN hH
    (polynomialPhase p) (fun x => by simp [polynomialPhase]) δ hδ hlarge hboundary
  have hall : ∀ a : ℕ, ∃ q : ℕ, ∃ m : ℤ, a ∈ S →
      0 < q ∧ q ≤ A ∧
      |(q : ℝ) * (polynomialDifference a b p).coeff d - m| ≤
        (A : ℝ) / (N : ℝ) ^ d := by
    intro a
    by_cases ha : a ∈ S
    · obtain ⟨q, hq, hqA, m, hm⟩ := hprev (polynomialDifference a b p)
        (polynomialDifference_degree a b p d hp)
        (by simpa only [polynomialPhase_difference] using hSlarge a ha)
      exact ⟨q, m, fun _ => ⟨hq, hqA, hm⟩⟩
    · exact ⟨1, 0, fun h => (ha h).elim⟩
  choose q m hqm using hall
  obtain ⟨a, ha, hafiber⟩ := exists_dense_fiber S A hA q
    (fun n hn => Finset.mem_Icc.mpr ⟨(hqm n hn).1, (hqm n hn).2.1⟩)
  have ha₀ : 0 < a := (Finset.mem_Icc.mp ha).1
  have haA : a ≤ A := (Finset.mem_Icc.mp ha).2
  let T := S.filter (fun n => q n = a)
  have hTK : (H : ℝ) / K ≤ (T.card : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg H)
    have h₂ := div_le_div_of_nonneg_right hScard (Nat.cast_nonneg A)
    change (S.card : ℝ) / A ≤ (T.card : ℝ) at hafiber
    have he : δ ^ 2 / 4 * H / A = δ ^ 2 / (4 * A) * H := by ring
    rw [he] at h₂
    have he' : (1 : ℝ) / K * H = (H : ℝ) / K := by ring
    rw [he'] at h₁
    exact h₁.trans (h₂.trans hafiber)
  let α : ℝ := (a : ℝ) * (d + 1 : ℕ) * p.coeff (d + 1)
  obtain ⟨u, hu₀, huK, z, hz⟩ := vinogradov_inverse T H K hK hHsize
    α (-α * b) ((A : ℝ) / (N : ℝ) ^ d) (by positivity) hεsmall
    (fun n hn => hSH n (Finset.mem_filter.mp hn).1) hTK (by
      intro n hn
      obtain ⟨hnS, hnq⟩ := Finset.mem_filter.mp hn
      refine ⟨m n, ?_⟩
      have hm := (hqm n hnS).2.2
      rw [hnq, polynomialDifference_coeff n b p d hp] at hm
      have heq : α * n + (-α * b) - m n =
          (a : ℝ) * ((d + 1 : ℕ) * p.coeff (d + 1) * ((n : ℝ) - b)) - m n := by
        dsimp [α]
        ring
      rw [heq]
      exact hm)
  refine ⟨u * a * (d + 1), by positivity,
    Nat.mul_le_mul_right _ (Nat.mul_le_mul huK haA), z, ?_⟩
  have he : ((u * a * (d + 1) : ℕ) : ℝ) * p.coeff (d + 1) = α * u := by
    dsimp [α]
    push_cast
    ring
  rw [he]
  apply hz.trans
  have hN₀ : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hH₀ : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hi : (1 : ℝ) / H ≤ (L : ℝ) / N := by
    apply (div_le_div_iff₀ hH₀ hN₀).mpr
    nlinarith only [hHL]
  calc
    16 * (K : ℝ) ^ 2 * ((A : ℝ) / (N : ℝ) ^ d) / H =
        (16 * (K : ℝ) ^ 2 * A / (N : ℝ) ^ d) * (1 / H) := by ring
    _ ≤ (16 * (K : ℝ) ^ 2 * A / (N : ℝ) ^ d) * (L / N) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [pow_succ]; ring

 

theorem leading_inverse_succ (d : ℕ) (hd : 0 < d)
    (ih : LeadingInverse d) : LeadingInverse (d + 1) := by
  intro δ hδ
  obtain ⟨A, hA, hprev⟩ := ih (δ ^ 2 / 4) (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_gt (16 / δ ^ 2)
  obtain ⟨K, hK⟩ := exists_nat_gt (4 * (A : ℝ) / δ ^ 2)
  have hM₀ : 0 < (M : ℝ) := lt_trans (by positivity) hM
  have hK₀ : 0 < (K : ℝ) := lt_trans (by positivity) hK
  have hMnat : 0 < M := Nat.cast_pos.mp hM₀
  have hKnat : 0 < K := Nat.cast_pos.mp hK₀
  have hMδ : 16 ≤ (M : ℝ) * δ ^ 2 :=
    ((div_lt_iff₀ (by positivity : 0 < δ ^ 2)).mp hM).le
  have hKδ : 4 * (A : ℝ) ≤ (K : ℝ) * δ ^ 2 :=
    ((div_lt_iff₀ (by positivity : 0 < δ ^ 2)).mp hK).le
  let T := M * (32 * K ^ 2 + 1) + 16 * K * A + 2 * M + 1
  let Q := 2 * K * A * (d + 1)
  let C := 32 * K ^ 2 * A * M
  let B := Q + C + T ^ (d + 1) + 1
  have hB : 0 < B := by dsimp [B]; omega
  have hQB : Q ≤ B := by dsimp [B]; omega
  have hCB : C ≤ B := by dsimp [B]; omega
  have hTB : T ^ (d + 1) ≤ B := by dsimp [B]; omega
  refine ⟨B, hB, ?_⟩
  intro N hN p hp hlarge
  have hN₀ : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  by_cases hNT : N < T
  · refine ⟨1, by omega, hB, ⌊p.coeff (d + 1)⌋, ?_⟩
    simp only [Nat.cast_one, one_mul]
    calc
      |p.coeff (d + 1) - (⌊p.coeff (d + 1)⌋ : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
        linarith [Int.lt_floor_add_one (p.coeff (d + 1))]
      _ ≤ (B : ℝ) / (N : ℝ) ^ (d + 1) := by
        apply (le_div_iff₀ (pow_pos hN₀ _)).mpr
        simp only [one_mul]
        exact_mod_cast (Nat.pow_le_pow_left hNT.le (d + 1)).trans hTB
  · have hTN : T ≤ N := Nat.le_of_not_gt hNT
    let H := N / M
    have hHsize : 32 * K ^ 2 ≤ H := by
      apply (Nat.le_div_iff_mul_le hMnat).mpr
      have he : M * (32 * K ^ 2 + 1) = 32 * K ^ 2 * M + M := by ring
      dsimp [T] at hTN
      rw [he] at hTN
      omega
    have hH : 0 < H := lt_of_lt_of_le (by positivity) hHsize
    have h16 : 16 * K * A ≤ N := by dsimp [T] at hTN; omega
    have hHM : (H : ℝ) * M ≤ N := by
      exact_mod_cast (Nat.div_mul_le_self N M)
    have hboundary : 4 * (H : ℝ) / N ≤ δ ^ 2 / 2 := by
      calc
        4 * (H : ℝ) / N ≤ 4 / (M : ℝ) := by
          apply (div_le_div_iff₀ hN₀ hM₀).mpr
          nlinarith only [hHM]
        _ ≤ δ ^ 2 / 2 := by
          apply (div_le_iff₀ hM₀).mpr
          nlinarith only [hMδ]
    have hdensity : (1 : ℝ) / K ≤ δ ^ 2 / (4 * A) := by
      apply (div_le_div_iff₀ hK₀ (by positivity : 0 < 4 * (A : ℝ))).mpr
      nlinarith only [hKδ]
    have heps : (A : ℝ) / (N : ℝ) ^ d ≤ 1 / (16 * K) := by
      have hpow : (N : ℝ) ≤ (N : ℝ) ^ d :=
        le_self_pow₀ (by exact_mod_cast hN) (Nat.ne_of_gt hd)
      have h16' : 16 * (K : ℝ) * A ≤ N := by exact_mod_cast h16
      apply (div_le_div_iff₀ (pow_pos hN₀ _) (by positivity : 0 < 16 * (K : ℝ))).mpr
      nlinarith only [hpow, h16']
    have hHL : (N : ℝ) ≤ (H : ℝ) * (2 * M : ℕ) := by
      have hrem := Nat.mod_lt N hMnat
      have he := Nat.div_add_mod N M
      have hmH : M ≤ H * M := by nlinarith only [Nat.mul_le_mul_right M hH]
      have hh : N ≤ H * (2 * M) := by dsimp [H] at hmH ⊢; nlinarith only [he, hrem, hmH]
      exact_mod_cast hh
    obtain ⟨q, hq, hqQ, m, hm⟩ := leading_inverse_step_at_length d δ hδ A K (2 * M)
      N H hA hKnat hN hH hboundary hdensity hHsize heps hHL
      (hprev N hN) p hp hlarge
    refine ⟨q, hq, hqQ.trans hQB, m, hm.trans ?_⟩
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hCB' : (C : ℝ) ≤ B := by exact_mod_cast hCB
    simp only [C, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hCB' ⊢
    nlinarith only [hCB']

 

theorem leading_inverse (d : ℕ) (hd : 0 < d) : LeadingInverse d := by
  induction d using Nat.case_strong_induction_on with
  | hz => omega
  | hi d ih =>
    by_cases he : d = 0
    · subst d
      exact leading_inverse_one
    · exact leading_inverse_succ d (Nat.pos_of_ne_zero he)
        (ih d (by omega) (Nat.pos_of_ne_zero he))

end
end WeylInverse

end
end
end
end

end OAI
