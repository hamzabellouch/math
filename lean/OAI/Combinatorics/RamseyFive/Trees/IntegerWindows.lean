import Mathlib

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section
lemma integral_floor_half {x : ℝ} (hx : 2≤x) :
    0<⌊x⌋₊ ∧ x/2≤(⌊x⌋₊:ℝ) ∧ (⌊x⌋₊:ℝ)≤x := by
  have hh:=Nat.lt_floor_add_one x
  exact ⟨Nat.floor_pos.mpr (by linarith),by linarith,Nat.floor_le (by linarith)⟩
lemma integral_window_packing (m n : ℕ) (hn : 0<n) (hm : 4*n≤ m) :
    let w:= m/(4*n)
    0<w ∧ w*(4*n)≤ m ∧ (m:ℝ)/8≤w*n ∧ (w:ℝ)*n≤ m/4 := by
  dsimp only
  have hw : 1≤ m/(4*n) := (Nat.one_le_div_iff (by omega)).mpr hm
  have hh:=Nat.div_mul_le_self m (4*n)
  have hh' : m<(m/(4*n)+1)*(4*n) := by simpa only [mul_comm] using Nat.lt_mul_div_succ m (show 0<4*n by omega)
  have hw' : (1:ℝ)≤((m/(4*n):ℕ):ℝ) := by exact_mod_cast hw
  have hhR : ((m/(4*n):ℕ):ℝ)*(4*n)≤ m := by exact_mod_cast hh
  have hhR' : (m:ℝ)<(((m/(4*n):ℕ):ℝ)+1)*(4*n) := by exact_mod_cast hh'
  have hnR : (0:ℝ)≤n := by positivity
  have hh2 : ((m/(4*n):ℕ):ℝ)+1≤2*((m/(4*n):ℕ):ℝ) := by linarith
  have hh3:= mul_le_mul_of_nonneg_right hh2 (by positivity : (0:ℝ)≤4*n)
  refine ⟨by omega,hh,?_,?_⟩ <;> nlinarith
lemma integral_round_packing {x : ℝ} (hx : 2≤x) (n : ℕ) (hxhi : 2*x≤n) :
    let T:=⌊x⌋₊
    let rem:=n-T
    0<T ∧ 0<rem ∧ n≤2*rem ∧ rem+T≤n ∧ (n:ℝ)/2≤rem ∧ x/2≤T := by
  obtain ⟨hT,hlo,hhi⟩:=integral_floor_half hx
  have h2T : 2*⌊x⌋₊≤n := by exact_mod_cast (show (2:ℝ)*⌊x⌋₊≤n by linarith)
  have ht : ⌊x⌋₊≤n := by omega
  dsimp only
  refine ⟨hT,by omega,by omega,by omega,?_,hlo⟩
  rw [Nat.cast_sub ht]
  exact (by linarith [show (2:ℝ)*⌊x⌋₊≤n by exact_mod_cast h2T])
lemma integer_window_length {q D a m : ℝ} (hq : 0<q) (_hD : 0<D) (ha : 0<a)
    (hx : 2≤q*D*a) (mn : ℕ) (hm : (mn:ℝ)= m) (hfit : 8*(q*D*a)≤ m) :
    let n:=⌊q*D*a⌋₊
    let w:= mn/(4*n)
    0<n ∧ 0<w ∧ w*(4*n)≤ mn ∧ m/8≤(w:ℝ)*n ∧
      m/(8*q*a)≤(w:ℝ)*D ∧ (w:ℝ)*D≤ m/(2*q*a) := by
  dsimp only
  obtain ⟨hn,hnlo,hnhi⟩:=integral_floor_half hx
  have hfit' : 4*⌊q*D*a⌋₊≤ mn := by
    exact_mod_cast (show (4:ℝ)*⌊q*D*a⌋₊≤ mn by rw [hm];linarith)
  obtain ⟨hw,hpack,hlo,hhi⟩:=integral_window_packing mn ⌊q*D*a⌋₊ hn hfit'
  rw [hm] at hlo hhi
  refine ⟨hn,hw,hpack,hlo,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : 0<8*q*a)).mpr
    have := mul_le_mul_of_nonneg_left hnhi (show (0:ℝ)≤ mn/(4*⌊q*D*a⌋₊) by positivity)
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0<2*q*a)).mpr
    have := mul_le_mul_of_nonneg_left hnlo (show (0:ℝ)≤ mn/(4*⌊q*D*a⌋₊) by positivity)
    nlinarith
end
end SharpRamseyFive.ParameterHierarchy

end OAI
