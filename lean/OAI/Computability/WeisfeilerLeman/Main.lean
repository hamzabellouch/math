import OAI.Computability.WeisfeilerLeman.RAMBounds

namespace OAI

namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 theorem ram_integer_lower (k : ℕ) (hk : 100000000  ≤  k) (c : Convention) (p : InputClass) (A : RAM)
    (hA : Decides (.ram A) c k p) :
    ∃ n₀,∀ n  ≥  n₀,n^(k/1000) < worstTime (.ram A) p n := by
  let s := k/16
  let d := 3*s+6
  let q := k-d-conventionShift c
  let U := Universal.machine s
  let C := coefficient U d q (d+q+2)
  have hshift : 1  ≤  conventionShift c ∧ conventionShift c  ≤  2 := by cases c <;> decide
  have hs : 1  ≤  s := by dsimp [s]; omega
  have hdim : k=d+q+conventionShift c := by dsimp [d,q,s]; omega
  have hq : d+3  ≤  q := by dsimp [q,d,s]; omega
  have ha : 2*max 2400 (16*(k/1000)+45)+3  ≤  s := by
    rcases max_cases 2400 (16*(k/1000)+45) with ⟨he,_⟩ | ⟨he,_⟩ <;> rw [he] <;> dsimp [s] <;> omega
  have hCpos : 1  ≤  C := coefficient_pos U d q
  obtain ⟨mfit,hfit⟩ := RAMWriter.designation_small A U d q
  obtain ⟨mword,hword⟩ := RAMWriter.word_cost_small A
  let m₀ := mfit+384*C^3+128+C+(body U d q).charge+RAMWriter.consumerFactor U d q A+
    mword+(8*((Universal.boundedProgram s).scratch+Fintype.card Universal.Reg+1)*1200^2)+18*s
  refine ⟨baseOrder U d q m₀,?_⟩
  intro n hn
  let m := Numeric.chooseOrder C n
  have hchoice := Numeric.chooseOrder_bounds C n m₀ hCpos hn
  have hm : m₀  ≤  m := hchoice.1
  have hbase : baseOrder U d q m  ≤  n := hchoice.2.1
  have hmn : n  ≤  m^8 := Numeric.order_polynomial C n m hCpos (by dsimp [m₀] at hm; omega) hchoice.2.2
  apply lt_of_not_ge
  exact ram_pointwise s d q k (k/1000) n m c p A hA hdim
    (by dsimp [m₀] at hm; omega) hs rfl hq ha hbase hmn
    (hfit m (by dsimp [m₀] at hm; omega) n hmn)
    (by change C ≤  m; dsimp only [m₀] at hm; omega)
    (by change (body U d q).charge ≤  m; dsimp only [m₀] at hm; omega)
    (by change RAMWriter.consumerFactor U d q A ≤  m; dsimp only [m₀] at hm; omega)
    (hword m (by dsimp [m₀] at hm; omega) n hmn)
    (by dsimp [m₀] at hm; omega)
    (by dsimp [m₀] at hm; omega)

end WLTime
namespace WLTime
 theorem ram_real_lower (k : ℕ) (hk : 100000000  ≤  k) (c : Convention) (p : InputClass) (A : RAM)
    (hA : Decides (.ram A) c k p) :
    ∃ n₀ : ℕ,∀ n : ℕ, n  ≥  n₀ → (n : ℝ)^((1/2000 : ℝ)*(k : ℝ))  ≤  (worstTime (.ram A) p n : ℝ) := by
  obtain ⟨n₀,hn₀⟩ := ram_integer_lower k hk c p A hA
  refine ⟨n₀+1,?_⟩
  intro n hn
  have hint := hn₀ n (by omega)
  have hexp : (1/2000 : ℝ)*(k : ℝ)  ≤  (k/1000 : ℕ) := by
    have h : k  ≤  2000*(k/1000) := by omega
    have hr : (k : ℝ)  ≤  2000*((k/1000 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  calc
    _  ≤  (n : ℝ)^((k/1000 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1  ≤  n by omega)) hexp
    _ = (n : ℝ)^(k/1000) := Real.rpow_natCast _ _
    _  ≤  (worstTime (.ram A) p n : ℝ) := by exact_mod_cast hint.le
end WLTime

theorem WLTime.unconditional_time_lower_bound : WLTime.MainClaim := by
  refine ⟨1/2000, by norm_num, 100000000, ?_⟩
  intro k hk convention p A hA
  cases A with
  | turing M => exact WLTime.tm_real_lower k hk convention p M hA
  | ram M => exact WLTime.ram_real_lower k hk convention p M hA

end OAI
