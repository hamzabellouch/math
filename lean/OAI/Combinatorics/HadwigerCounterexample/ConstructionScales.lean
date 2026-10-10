import OAI.Combinatorics.HadwigerCounterexample.RawFrameLaws

namespace OAI

/-! # Construction Scales -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Filter

theorem card_full (p : Shape) (n : ℕ) :
    Fintype.card (Full p n) = psize p * (1+(p.g*p.g+3)*n) + p.h := by
  calc
    _ = Fintype.card (Row p n) + Fintype.card (Fin p.h) :=
      Fintype.card_sum ..
    _ = _ := by rw [card_row, Fintype.card_fin]

theorem full_linear (p : Shape) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 0 < n →
    num (Full p n) ≤ B*n := by
  let b := psize p*(1+(p.g*p.g+3)) + p.h
  refine ⟨↑b,Nat.cast_nonneg b, fun n hn => ?_⟩
  have h1 : 1 ≤ n := hn
  have h2 : Fintype.card (Full p n) ≤ b*n := by
    rw [card_full]
    unfold b
    calc _ ≤ psize p * (n+(p.g*p.g+3)*n) + p.h*n :=
           add_le_add (Nat.mul_le_mul_left _ (by omega)) (by nlinarith)
         _ = _ := by ring
  exact_mod_cast h2

theorem unit_size (p : Shape) (n N : ℕ) :
    num (UnitType p n N) = bp (num (Comp p.g) * 4 * N * num (Full p n)) := by
  have hc :
      (Fintype.card (UnitType p n N)) =
        ((Fintype.card (Mat (Fin N) (Full p n)))^2)^(Fintype.card (Comp p.g)) *
        ((Fintype.card (Mat (Fin N) (Full p n)))^2)^(Fintype.card (Comp p.g)) := by
    simp [UnitType, Orient, Oframe, RawFrame, pow_two]
  unfold num
  rw [hc]
  push_cast
  rw [card_space,dim_mat,Fintype.card_fin]
  push_cast
  simp only [← bp_mul_nat,← bp_add]
  push_cast; ring_nf

/-- Fixed linear and constant expenses become any fixed small fraction of N. -/
theorem have_budget {δ : ℝ} (hd : 0 < δ) (a b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ, 1 ≤ n → a*n+b ≤ δ*(M*n : ℕ) := by
  have h : Tendsto (fun M : ℕ => δ*M) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hd).mpr tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually (eventually_ge_atTop (a+b))] with M hM n hn
  change a+b ≤ δ*M at hM
  push_cast
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  nlinarith only [mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg n : (0:ℝ)≤n),
    mul_le_mul_of_nonneg_right hn' hb]

theorem columns_budget (p : Shape) {δ : ℝ} (hd : 0 < δ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ, 1 ≤ n →
      a*num (Full p n) + b ≤ δ*(M*n:ℕ) := by
  obtain ⟨B,hB,h⟩ := full_linear p
  filter_upwards [have_budget hd (a*B) b hb] with M hM n hn
  refine le_trans ?_ (hM n hn)
  rw [mul_assoc]
  exact add_le_add_left (mul_le_mul_of_nonneg_left (h _ hn) ha) _

theorem raw_ready (p : Shape) {δ : ℝ} (hd : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ n : ℕ in atTop, let N := M*n;
      num (UnitType p n N) ≤ bp ((4*num (Comp p.g))*N^ (2 : ℕ)) ∧
      ∀ m : Mixer p n, IsLaw (raw m N) ∧ ∀ a : Pin p n N,
        pr (pairW (raw m N) (raw m N)) a.agree ≤ bp (-(1-δ)*(planRank a.sp)*N) := by
  have hd' : 0 < δ/2 := by positivity
  filter_upwards [columns_budget p hd' 2 (4*num (Comp p.g)) (by norm_num)
    (by unfold num; positivity),
    columns_budget p (δ:=1) (by norm_num) 2 1 (by norm_num) (by norm_num)] with M ha hb
  filter_upwards [eventually_ge_atTop 1] with n hn
  specialize ha n hn
  specialize hb n hn
  let N := M*n
  have hi : 0 ≤ num (Comp p.g) := Nat.cast_nonneg _
  have hj : 0 ≤ num (Full p n) := Nat.cast_nonneg _
  rw [one_mul] at hb
  have hh : 2*num (Full p n)<N := by unfold N; linarith only [hb]
  dsimp only
  constructor
  · rw [unit_size]
    apply bp_le
    have hf : num (Full p n) ≤ N := by linarith

    exact le_trans (mul_le_mul_of_nonneg_left hf (by positivity))
      (le_of_eq (by unfold N; push_cast; ring))
  · intro m
    refine ⟨raw_law m hh, fun a => reference_cap _ a hd ?_ ?_ ?_⟩ <;> linarith
end HadwigerCounterexample

end

end OAI
