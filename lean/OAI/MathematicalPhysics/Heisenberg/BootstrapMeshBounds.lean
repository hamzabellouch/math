import OAI.MathematicalPhysics.Heisenberg.RegularPin

namespace OAI

section

noncomputable section
namespace Heisenberg.Bootstrap

lemma mesh_floor (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) (hδs : δ ≤ s/2) :
    0 < ⌊s/δ⌋₊ ∧ s/2 ≤ δ*(⌊s/δ⌋₊:ℝ) ∧ δ*(⌊s/δ⌋₊:ℝ) ≤ s := by
  have hsd : 0 ≤ s/δ := div_nonneg hs.le hδ.le
  have hfloor:=Nat.floor_le hsd
  have hceil:=Nat.lt_floor_add_one (s/δ)
  have hlow : s-δ < δ*(⌊s/δ⌋₊:ℝ) := by
    have hh:=(div_lt_iff₀ hδ).mp hceil
    nlinarith
  have hup : δ*(⌊s/δ⌋₊:ℝ) ≤ s := by
    have hh:=(le_div_iff₀ hδ).mp hfloor
    nlinarith
  refine ⟨?_,by linarith,hup⟩
  by_contra hn
  have he : ⌊s/δ⌋₊=0 := by omega
  rw [he,Nat.cast_zero,mul_zero] at hlow
  linarith

lemma period_room (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) (hδs : δ ≤ s/2)
    (N Q : ℕ) (hperiod : 5*s ≤ (N:ℝ)*δ) :
    2*(⌊s/δ⌋₊+1)*Q ≤ N*Q := by
  have hh:=(mesh_floor s δ hs hδ hδs).2.2
  have hb : ((2*(⌊s/δ⌋₊+1):ℕ):ℝ)*δ ≤ (N:ℝ)*δ := by
    push_cast
    nlinarith
  have hn : 2*(⌊s/δ⌋₊+1) ≤ N := by
    exact_mod_cast (mul_le_mul_iff_left₀ hδ).mp hb
  exact Nat.mul_le_mul_right Q hn

lemma round_clock_bound (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) (R : ℕ)
    (hδR : δ ≤ s/(R+2)) : ((⌊s/δ⌋₊+2+R:ℕ):ℝ)*δ ≤ 2*s := by
  have hh:=(le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hs.le hδ.le))
  have hR : (0:ℝ) < R+2 := by positivity
  have hsmall:=(le_div_iff₀ hR).mp hδR
  push_cast
  nlinarith

lemma mesh_remainder (p s δ ε : ℝ) (hp : 0 < p) (hs : 0 < s) (hδ : 0 < δ)
    (V q n k : ℕ) (hk : 1 ≤ k) (hn : (n:ℝ)*δ ≤ s)
    (heps : ε=p/(16*s*((V:ℝ)+1))) (hsmall : δ ≤ p/(16*s*((q:ℝ)^2+1))) :
    (n:ℝ)*(ε*δ*V+δ^2*q^2) ≤ p/4*k := by
  have hV : 0 < (V:ℝ)+1 := by positivity
  have hq : 0 < (q:ℝ)^2+1 := by positivity
  have h16 : 0 < 16*s := by positivity
  have hε : 0 < ε := heps ▸ div_pos hp (mul_pos h16 hV)
  have he : ε*(16*s*((V:ℝ)+1))=p := by rw [heps]; field_simp
  have hδq : δ*(16*s*((q:ℝ)^2+1)) ≤ p := (le_div_iff₀ (mul_pos h16 hq)).mp hsmall
  have hr1 : s*ε*V ≤ p/16 := by nlinarith [mul_nonneg hs.le hε.le]
  have hr2 : s*δ*q^2 ≤ p/16 := by nlinarith [mul_nonneg hs.le hδ.le]
  have h1:=mul_le_mul_of_nonneg_right hn (mul_nonneg hε.le (Nat.cast_nonneg V))
  have h2:=mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ δ*(q:ℝ)^2)
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

lemma leakage_arithmetic (p s δ F ρ tail : ℝ) (n R k : ℕ)
    (_hp : 0 < p) (hs : 0 < s) (_hδ : 0 < δ) (hF : 0 ≤ F)
    (ht : tail ≤ 1/(1+(R:ℝ))) (hn : s/2 ≤ δ*(n:ℝ))
    (herr : 2*(ρ+1/(1+(R:ℝ)))+8*F*(1+(R:ℝ))^((1:ℝ)/100)/s < p/4)
    (rem : ℝ) (hrem : rem ≤ p/4*k) :
    (1-p/2)*(k:ℝ) ≤ (k:ℝ)-2*((ρ+tail)*k)-
      2*(F*(1+(R:ℝ))^((1:ℝ)/100)*k)/((δ/2)*(n:ℝ))-rem := by
  have hnpos : 0 < δ*(n:ℝ) := lt_of_lt_of_le (by linarith) hn
  have hdpos : 0 < (δ/2)*(n:ℝ) := by nlinarith
  have hflow : 2*(F*(1+(R:ℝ))^((1:ℝ)/100)*k)/((δ/2)*(n:ℝ)) ≤
      (8*F*(1+(R:ℝ))^((1:ℝ)/100)/s)*(k:ℝ) := by
    rw [div_le_iff₀ hdpos]
    have hmul:=mul_le_mul_of_nonneg_left hn
      (by positivity : 0 ≤ 4*F*(1+(R:ℝ))^((1:ℝ)/100)*k/s)
    have hs0 : s≠0 := hs.ne'
    field_simp at hmul ⊢
    nlinarith
  have htail:=mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg k)
  have herror:=mul_le_mul_of_nonneg_right herr.le (Nat.cast_nonneg k)
  nlinarith

end Heisenberg.Bootstrap
end
end

end OAI
