import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumIntegralError
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.EnergyLeGram

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset

namespace OrdinaryLogIntegral
open Finset OrdinaryLogDifferencing

noncomputable def logCorrelation (t a : ℝ) (N h k : ℕ) : ℝ :=
  ‖∑ n ∈ range N, logPhase t (a+(n+h : ℕ)) * star (logPhase t (a+(n+k : ℕ)))‖

lemma logCorrelation_comm (t a : ℝ) (N h k : ℕ) :
    logCorrelation t a N h k = logCorrelation t a N k h := by
  unfold logCorrelation
  calc
    _ = ‖star (∑ n ∈ range N, logPhase t (a+(n+h : ℕ)) * star (logPhase t (a+(n+k : ℕ))))‖ := (norm_star _).symm
    _ = _ := by simp only [star_sum, star_mul, star_star]

lemma logCorrelation_diagonal (t a : ℝ) (N h : ℕ) :
    logCorrelation t a N h h ≤ N := by
  unfold logCorrelation
  apply (norm_sum_le _ _).trans
  simp only [norm_mul, norm_star, norm_logPhase, mul_one, sum_const, card_range,
    nsmul_eq_mul, mul_one, le_refl]

lemma shifted_log_correlation (t a : ℝ) (N h k : ℕ) (hkh : k ≤ h) :
    logCorrelation t a N h k =
      ‖∑ n ∈ range N, differencePhase t (h-k : ℕ) ((a+k)+n)‖ := by
  unfold logCorrelation
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [differencePhase_eq]
  have he₁ : a+(n+h : ℕ) = ((a+k)+n)+(h-k : ℕ) := by
    rw [Nat.cast_sub hkh]
    push_cast
    ring
  have he₂ : a+(n+k : ℕ) = (a+k)+n := by push_cast; ring
  rw [he₁, he₂]

lemma logCorrelation_upper (t a : ℝ) (N H h k : ℕ) (ha : 0 < a)
    (hhH : h < H) (hkH : k < H) (hkh : k < h) (ht : t ≠ 0) :
    logCorrelation t a N h k ≤
      (7 * (a+N+H)^2 / |t|) / (h-k : ℕ) +
        ((N : ℝ)*|t| / a^2) * (h-k : ℕ) := by
  rw [shifted_log_correlation t a N h k hkh.le]
  have hd : (0 : ℝ) < (h-k : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hkh
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hkH' : (k : ℝ) ≤ H := by exact_mod_cast hkH.le
  have hdH : (h-k : ℕ) ≤ H := Nat.le_trans (Nat.sub_le _ _) hhH.le
  have hdH' : ((h-k : ℕ) : ℝ) ≤ H := by exact_mod_cast hdH
  let B : ℝ := a+N+H
  have hB : 0 < B := by dsimp [B]; positivity
  have hx : 0 < a+k := by positivity
  have hxB : a+k ≤ B := by dsimp [B]; linarith
  have hxNB : a+k+N ≤ B := by dsimp [B]; linarith
  have hNB : (N : ℝ) ≤ B := by dsimp [B]; linarith [Nat.cast_nonneg (α := ℝ) H]
  have hdB : ((h-k : ℕ) : ℝ) ≤ B := by dsimp [B]; linarith
  have hnum : (a+k+N)*(a+k+N+(h-k : ℕ)) + (a+k)*(a+k+(h-k : ℕ)) +
      (2*(a+k+N)+(h-k : ℕ))*N ≤ 7*B^2 := by
    have h₁ := mul_le_mul hxNB (show a+k+N+(h-k : ℕ) ≤ 2*B by linarith)
      (by positivity : (0 : ℝ) ≤ a+k+N+(h-k : ℕ)) hB.le
    have h₂ := mul_le_mul hxB (show a+k+(h-k : ℕ) ≤ 2*B by linarith)
      (by positivity : (0 : ℝ) ≤ a+k+(h-k : ℕ)) hB.le
    have h₃ := mul_le_mul (show 2*(a+k+N)+(h-k : ℕ) ≤ 3*B by linarith) hNB
      hN0 (by positivity : 0 ≤ 3*B)
    nlinarith
  have hden : a^2 ≤ (a+k)^2 := by nlinarith
  calc
    _ ≤ ((a+k+N)*(a+k+N+(h-k : ℕ)) + (a+k)*(a+k+(h-k : ℕ)) +
        (2*(a+k+N)+(h-k : ℕ))*N)/(|t| * (h-k : ℕ)) +
        (N : ℝ) * (|t| * (h-k : ℕ)/(a+k)^2) :=
      difference_sum_bound t (h-k : ℕ) (a+k) N hx hd ht
    _ ≤ 7*B^2/(|t| * (h-k : ℕ)) + (N : ℝ) * (|t| * (h-k : ℕ)/a^2) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right hnum (by positivity)
      · apply mul_le_mul_of_nonneg_left _ hN0
        exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ha) hden
    _ = _ := by dsimp [B]; field_simp

lemma logCorrelation_offDiagonal (t a : ℝ) (N H h k : ℕ) (ha : 0 < a)
    (hhH : h < H) (hkH : k < H) (hne : h ≠ k) (ht : t ≠ 0) :
    logCorrelation t a N h k ≤
      (7 * (a+N+H)^2 / |t|) / (Nat.dist h k : ℝ) +
        ((N : ℝ)*|t| / a^2) * (Nat.dist h k : ℝ) := by
  rcases lt_or_gt_of_ne hne with hhk | hkh
  · rw [logCorrelation_comm t a N h k, Nat.dist_eq_sub_of_le hhk.le]
    exact logCorrelation_upper t a N H k h ha hkH hhH hhk ht
  · rw [Nat.dist_eq_sub_of_le_right hkh.le]
    exact logCorrelation_upper t a N H h k ha hhH hkH hkh ht

lemma sum_nat_Icc_le_sq (H : ℕ) :
    (∑ d ∈ Icc 1 H, (d : ℝ)) ≤ (H : ℝ)^2 := by
  calc
    _ ≤ ∑ d ∈ Icc 1 H, (H : ℝ) := sum_le_sum (fun d hd => by
      exact_mod_cast (mem_Icc.mp hd).2)
    _ = _ := by simp; ring

theorem discrete_logphase_bound (t a : ℝ) (N H : ℕ) (ha : 0 < a) (ht : t ≠ 0) :
    (H : ℝ)^2 * ‖∑ n ∈ range N, logPhase t (a+n)‖^2 ≤
      2 * N * ((H : ℝ)*N + 2*H *
        ((7*(a+N+H)^2/|t|) * (∑ d ∈ Icc 1 H, (d : ℝ)⁻¹) +
          ((N : ℝ)*|t|/a^2)*(H : ℝ)^2)) + 8*(H : ℝ)^4 := by
  let A : ℝ := 7*(a+N+H)^2/|t|
  let B : ℝ := (N : ℝ)*|t|/a^2
  let f : ℕ → ℝ := fun d => A/(d : ℝ) + B*d
  have hf (d : ℕ) : 0 ≤ f d := by dsimp [f, A, B]; positivity
  have hb := correlation_envelope H (logCorrelation t a N) (N : ℝ) f hf
    (fun h _ => logCorrelation_diagonal t a N h)
    (fun h hh k hk hne => logCorrelation_offDiagonal t a N H h k ha hh hk hne ht)
  have hs : (∑ d ∈ Icc 1 H, f d) ≤
      A * (∑ d ∈ Icc 1 H, (d : ℝ)⁻¹) + B*(H : ℝ)^2 := by
    simp only [f, div_eq_mul_inv, sum_add_distrib, ← mul_sum]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (sum_nat_Icc_le_sq H)
      (by dsimp [B]; positivity)) _
  have hb' := hb.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2*H)) _)
  have hfd := finite_differencing (fun n => logPhase t (a+n))
    (fun n => (norm_logPhase t (a+n)).le) N H
  exact hfd.trans (add_le_add_left (mul_le_mul_of_nonneg_left hb' (by positivity)) _)

end OrdinaryLogIntegral

end

end OAI
