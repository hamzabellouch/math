import OAI.NumberTheory.TwoPoint.Halasz.HalaszIterationConstants

namespace OAI

/-! Polynomial-in-the-degree control of the logarithm of the explicit
iteration constant. The absolute prime-supply threshold is retained. -/
namespace TwoPointCorrelations

private lemma four_terms {b e a c d f : ℕ} (hb : 4≤b)
    (ha : a≤b^e) (hc : c≤b^e) (hd : d≤b^e) (hf : f≤b^e) :
    a+c+d+f≤b^(e+1) := by
  rw [pow_succ]
  have hh := Nat.mul_le_mul_left (b^e) hb
  omega

lemma halasz_iteration_threshold_growth {R₀ k : ℕ} (hk : 2≤k) :
    halaszIterationThreshold R₀ k≤(R₀+k+32)^(10*k) := by
  let b := R₀+k+32
  have hb : 32≤b := by omega
  have hb1 : 1≤b := by omega
  have hkb : k≤b := by omega
  have hRb : R₀≤b := by omega
  have h3 : 1≤b^3 := Nat.one_le_pow _ _ hb1
  have hm : 2*(k^2*k)+1≤b^4 := by
    have hk3 : k^2*k≤b^3 := by simpa [pow_succ] using Nat.pow_le_pow_left hkb 3
    have hfour : b^3*3≤b^3*b := Nat.mul_le_mul_left _ (by omega)
    rw [← pow_succ] at hfour
    change b^3*3≤b^4 at hfour
    omega
  have hm2 : (2*(k^2*k)+1)^2≤b^8 := by
    simpa [← pow_mul] using Nat.pow_le_pow_left hm 2
  have hbe : b≤b^8 := by simpa using pow_le_pow_right₀ hb1 (by decide : 1≤8)
  have hT : halaszIterationRootThreshold R₀ k≤b^9 := by
    exact four_terms (by omega) (hRb.trans hbe) hm2 (hkb.trans hbe)
      ((show 2≤b by omega).trans hbe)
  have hp : (halaszIterationRootThreshold R₀ k)^k≤b^(9*k) := by
    simpa [← pow_mul] using Nat.pow_le_pow_left hT k
  have hs : (4*k^2)^2≤b^8 := by
    have hkk := Nat.pow_le_pow_left hkb 2
    have hb2 : 4≤b^2 := by nlinarith
    have hmul := Nat.mul_le_mul hb2 hkk
    have ht : 4*k^2≤b^4 := by simpa [← pow_add] using hmul
    simpa [← pow_mul] using Nat.pow_le_pow_left ht 2
  have hs' : (4*k^2)^2≤b^(9*k) := hs.trans (pow_le_pow_right₀ hb1 (by omega))
  have htwo : 2^k≤b^(9*k) := (Nat.pow_le_pow_left (by omega : 2≤b) k).trans
    (pow_le_pow_right₀ hb1 (by omega))
  have hone : 1≤b^(9*k) := Nat.one_le_pow _ _ hb1
  exact (four_terms (by omega) hp hs' htwo hone).trans
    (pow_le_pow_right₀ hb1 (by omega))

lemma halasz_iteration_base_growth {R₀ k : ℕ} (hk : 2≤k) :
    halaszIterationBase R₀ k≤(R₀+k+32)^(11*k^3) := by
  let b := R₀+k+32
  have hb : 32≤b := by omega
  have hb1 : 1≤b := by omega
  have hkb : k≤b := by omega
  have hk1 : 1≤k := by omega
  have hk3 : k≤k^3 := by simpa using pow_le_pow_right₀ hk1 (by decide : 1≤3)
  have htri : k*(k-1)/2≤k^2 := (Nat.div_le_self _ _).trans (by
    simpa [pow_two] using Nat.mul_le_mul_left k (Nat.sub_le k 1))
  have hK : k+k*(k-1)/2≤k^2 := by
    have he := Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one k)
    have hsub : k*(k-1)=k^2-k := by
      rw [Nat.mul_sub_left_distrib,pow_two,mul_one]
    rw [hsub] at he ⊢
    have hkk : k≤k^2 := by simpa using pow_le_pow_right₀ hk1 (by decide : 1≤2)
    omega
  have hH : (halaszIterationThreshold R₀ k)^(k+k*(k-1)/2)≤b^(10*k^3) := by
    have hh := Nat.pow_le_pow_left (halasz_iteration_threshold_growth (R₀ := R₀) hk) (k+k*(k-1)/2)
    rw [← pow_mul] at hh
    apply hh.trans (pow_le_pow_right₀ hb1 _)
    nlinarith
  have hfact : k.factorial≤b^(10*k^3) := (Nat.factorial_le_pow k).trans
    ((Nat.pow_le_pow_left hkb k).trans (pow_le_pow_right₀ hb1 (by omega)))
  have h3 : 1≤b^3 := Nat.one_le_pow _ _ hb1
  have hm : 2*(k^2*k)+1≤b^4 := by
    have hk3b : k^2*k≤b^3 := by simpa [pow_succ] using Nat.pow_le_pow_left hkb 3
    have hfour : b^3*3≤b^3*b := Nat.mul_le_mul_left _ (by omega)
    rw [← pow_succ] at hfour
    change b^3*3≤b^4 at hfour
    omega
  have hstep : 2*(2*(k^2*k)+1)*k^k*32^(k*(k-1)/2)≤b^(10*k^3) := by
    have hh := Nat.mul_le_mul (Nat.mul_le_mul
      (Nat.mul_le_mul (show 2≤b by omega) hm) (Nat.pow_le_pow_left hkb k))
      (Nat.pow_le_pow_left hb (k*(k-1)/2))
    have hh' : 2*(2*(k^2*k)+1)*k^k*32^(k*(k-1)/2)≤b^(5+k+k*(k-1)/2) := by
      convert hh using 1
      simp only [pow_add,pow_succ]
      ring
    apply hh'.trans (pow_le_pow_right₀ hb1 _)
    have hk2 : k^2≤k^3 := pow_le_pow_right₀ hk1 (by decide : 2≤3)
    have hk32 : 2≤k^3 := (show 2≤k from hk).trans hk3
    omega
  have hone : 1≤b^(10*k^3) := Nat.one_le_pow _ _ hb1
  exact (four_terms (by omega) hfact hH hstep hone).trans
    (pow_le_pow_right₀ hb1 (by nlinarith))

/-- The constant at the selected moment has logarithm `O(k^4 log k)`.
No endpoint-dependent constant is hidden. -/
theorem halasz_selected_constant_growth {R₀ k : ℕ} (hk : 2≤k) :
    halaszIterationConstant R₀ k (10*k)≤(R₀+k+32)^(256*k^4) := by
  let b := R₀+k+32
  have hb : 32≤b := by omega
  have hb1 : 1≤b := by omega
  have hk1 : 1≤k := by omega
  have h1 := Nat.pow_le_pow_left (halasz_iteration_base_growth (R₀ := R₀) hk) (10*k+1)
  have h2 := Nat.pow_le_pow_left hb (k*(10*k)*(10*k+1))
  have hmul := Nat.mul_le_mul h1 h2
  unfold halaszIterationConstant
  apply hmul.trans
  rw [← pow_mul,← pow_add]
  apply pow_le_pow_right₀ hb1
  have h34 : k^3≤k^4 := pow_le_pow_right₀ hk1 (by decide : 3≤4)
  have h24 : k^2≤k^4 := pow_le_pow_right₀ hk1 (by decide : 2≤4)
  have he : 11*k^3*(10*k+1)+k*(10*k)*(10*k+1)=110*k^4+111*k^3+10*k^2 := by ring
  rw [he]
  omega

end TwoPointCorrelations

end OAI
