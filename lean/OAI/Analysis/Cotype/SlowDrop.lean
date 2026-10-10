import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace Cotype

theorem exists_slow_block (w : ℕ → ℝ) (m K a n : ℕ) (c : ℝ)
    (hanti : Antitone w) (hpos : 0 < w n) (han : n ≤ a)
    (hK : 1 < (2 : ℝ)^K * c) (hend : c*w n ≤ w (a+2*m*K)) :
    ∃ j < K, w (a+2*m*j) ≤ 2*w (a+2*m*(j+1)) := by
  by_contra h
  push Not at h
  have hb : ∀ l ≤ K, (2 : ℝ)^l * w (a+2*m*l) ≤ w a := by
    intro l
    induction l with
    | zero => intro hl; simp
    | succ l ih =>
      intro hl
      have hs := le_of_lt (h l (by omega))
      calc
        (2 : ℝ)^(l+1) * w (a+2*m*(l+1)) =
            (2 : ℝ)^l * (2*w (a+2*m*(l+1))) := by rw [pow_succ]; ring
        _ ≤ (2 : ℝ)^l * w (a+2*m*l) := mul_le_mul_of_nonneg_left hs (by positivity)
        _ ≤ w a := ih (by omega)
  have hlow := mul_le_mul_of_nonneg_left hend (show 0 ≤ (2 : ℝ)^K by positivity)
  have hstrict := mul_lt_mul_of_pos_right hK hpos
  have hupper := (hb K le_rfl).trans (hanti han)
  nlinarith

theorem next_slow_point (w : ℕ → ℝ) (m K L n : ℕ) (c : ℝ)
    (_hm : 0 < m) (hanti : Antitone w) (hpos : 0 < w n)
    (hK : 1 < (2 : ℝ)^K * c) (hn : L+2*m*K+4*m ≤ n)
    (hgrowth : c*w n ≤ w (2*(n-2*m))) :
    ∃ t, n+L ≤ t ∧ t ≤ 2*(n-2*m) ∧ w (t-2*m) ≤ 2*w t ∧ c*w n ≤ w t := by
  have he : n+L+2*m*K ≤ 2*(n-2*m) := by omega
  have hend : c*w n ≤ w (n+L+2*m*K) := hgrowth.trans (hanti he)
  obtain ⟨j,hj,hslow⟩ := exists_slow_block w m K (n+L) n c hanti hpos (by omega) hK hend
  let t := n+L+2*m*(j+1)
  have hte : t ≤ n+L+2*m*K := by dsimp [t]; nlinarith
  refine ⟨t,by dsimp [t]; omega,hte.trans he,?_,hend.trans (hanti hte)⟩
  have ht : t-2*m = n+L+2*m*j := by dsimp [t]; simp only [Nat.mul_add, Nat.mul_one]; omega
  rw [ht]
  exact hslow

theorem uniform_drop_of_growth (m : ℕ) (hm : 0 < m) (c q : ℝ)
    (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ n₀ : ℕ, 4*m < n₀ ∧ ∀ w : ℕ → ℝ,
      (∀ n, 0 < w n) → Antitone w →
      (∃ D : ℝ, ∀ n, w n ≤ D*q^n) →
      (∀ n, 4*m < n → w (n-2*m) ≤ 2*w n → c*w n ≤ w (2*(n-2*m))) →
      ∀ n, n₀ ≤ n → 2*w n < w (n-2*m) := by
  obtain ⟨K,hK0⟩ := exists_nat_gt (1/c)
  have hpow : (K : ℝ) < (2 : ℝ)^K := by exact_mod_cast Nat.lt_two_pow_self
  have hK : 1 < (2 : ℝ)^K*c := (div_lt_iff₀ hc).mp (hK0.trans hpow)
  obtain ⟨L,hL⟩ := exists_pow_lt_of_lt_one (show 0 < c/2 by positivity) hq1
  let n₀ := L+2*m*K+4*m+1
  refine ⟨n₀,by dsimp [n₀]; omega,?_⟩
  intro w hw hanti hbound hgrowth n hn
  by_contra hdrop
  have hslow : w (n-2*m) ≤ 2*w n := le_of_not_gt hdrop
  let S : Set ℝ := {z | ∃ i, n₀ ≤ i ∧ w (i-2*m) ≤ 2*w i ∧ z = w i/q^i}
  have hne : S.Nonempty := ⟨w n/q^n,n,hn,hslow,rfl⟩
  obtain ⟨D,hD⟩ := hbound
  have hbd : BddAbove S := by
    refine ⟨D,?_⟩
    rintro z ⟨i,hi,hs,rfl⟩
    exact (div_le_iff₀ (pow_pos hq0 i)).mpr (hD i)
  have hsup : 0 < sSup S := (div_pos (hw n) (pow_pos hq0 n)).trans_le
    (le_csSup hbd ⟨n,hn,hslow,rfl⟩)
  obtain ⟨z,hz,hzgt⟩ := exists_lt_of_lt_csSup hne (show sSup S/2 < sSup S by linarith)
  obtain ⟨i,hi,hs,rfl⟩ := hz
  have hin : L+2*m*K+4*m ≤ i := by dsimp [n₀] at hi; omega
  have hi4 : 4*m < i := by dsimp [n₀] at hi; omega
  obtain ⟨t,htgap,htupper,htslow,htval⟩ := next_slow_point w m K L i c hm hanti (hw i) hK hin
    (hgrowth i hi4 hs)
  have hqt : q^t ≤ (c/2)*q^i := by
    calc
      _ ≤ q^(i+L) := pow_le_pow_of_le_one (le_of_lt hq0) (le_of_lt hq1) htgap
      _ = q^L*q^i := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_of_lt hL) (le_of_lt (pow_pos hq0 i))
  have hratio : 2*(w i/q^i) ≤ w t/q^t := by
    apply (le_div_iff₀ (pow_pos hq0 t)).mpr
    calc
      _ ≤ (2*(w i/q^i))*((c/2)*q^i) :=
        mul_le_mul_of_nonneg_left hqt
          (mul_nonneg (by norm_num) (le_of_lt (div_pos (hw i) (pow_pos hq0 i))))
      _ = c*w i := by field_simp [ne_of_gt hq0]
      _ ≤ w t := htval
  have hts : w t/q^t ≤ sSup S := le_csSup hbd ⟨t,by omega,htslow,rfl⟩
  linarith

end Cotype

end

end OAI
