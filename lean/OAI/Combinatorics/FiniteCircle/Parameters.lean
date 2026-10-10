import OAI.Combinatorics.FiniteCircle.Distortion

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem StandingPrimes.small_prime {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) (k : Fin h) :
    p l k ≤ h^4 := by
  apply (hp.atLevel l hl hlh k).2.2.trans
  calc
    2*h^3 ≤ h*h^3 := Nat.mul_le_mul_right _ hh
    _ = h^4 := by ring

 theorem StandingPrimes.period_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) :
    period h p l ≤ h^(4*h) := by
  calc
    _ ≤ ∏ _k : Fin h, h^4 := Finset.prod_le_prod (fun k _ => hp.small_prime hh l hl hlh k)
    _ = _ := by simp [← pow_mul]

 theorem StandingPrimes.circle_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) : circleSize h p ≤ h^(5*h^2) := by
  calc
    _ ≤ h*(∏ _l : Fin h, h^(4*h)) := Nat.mul_le_mul hh
      (Finset.prod_le_prod (fun l _ => hp.period_bound hh (l.val+1) (by omega) (by omega)))
    _ = h^(4*h^2+1) := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

 theorem StandingPrimes.log_circle_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) : Nat.log 2 (circleSize h p)+1 ≤ 6*h^3 := by
  have ht : h ≤ 2^h := (Nat.lt_two_pow_self (n:=h)).le
  have hm : circleSize h p ≤ 2^(5*h^3) := by
    calc
      _ ≤ h^(5*h^2) := hp.circle_bound hh
      _ ≤ (2^h)^(5*h^2) := Nat.pow_le_pow_left ht _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hn := Nat.log_mono_right hm (b:=2)
  rw [Nat.log_pow (by norm_num : 1<2)] at hn
  have hp3 : 0<h^3 := pow_pos (by omega) _
  nlinarith

 theorem StandingPrimes.tags_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) :
    (maskTags h p l).length ≤ h^5 := by
  rw [length_maskTags]
  calc
    _ ≤ ∑ _k : Fin h, h^4 := Finset.sum_le_sum (fun k _ => hp.small_prime hh l hl hlh k)
    _ = _ := by simp; ring

 theorem StandingPrimes.tag_card_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) :
    Fintype.card (MaskTag h p l) ≤ h^5 := by
  simpa [Fintype.card_sigma, MaskTag, length_maskTags] using hp.tags_bound hh l hl hlh

 theorem recursive_length_bound (h M : ℕ) (P T L : ℕ → ℕ) (hh : 3≤h)
    (h0 : L 0=M) (hs : ∀ l, L (l+1)=(h^(2*h)*P (l+1))*(T (l+1)*L l))
    (hP : ∀ l, 1≤l → l≤h → P l≤h^(4*h))
    (hT : ∀ l, 1≤l → l≤h → T l≤h^5) :
    ∀ l, l≤h → L l ≤ M*h^(8*h*l) := by
  intro l
  induction l with
  | zero => intro _; simp [h0]
  | succ l ih =>
    intro hl
    rw [hs]
    calc
      _ ≤ (h^(2*h)*h^(4*h))*(h^5*(M*h^(8*h*l))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (hP _ (by omega) hl))
          (Nat.mul_le_mul (hT _ (by omega) hl) (ih (by omega)))
      _ = M*h^(2*h+4*h+5+8*h*l) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by nlinarith))

 theorem StandingPrimes.mask_length_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 3≤h) :
    maskLength h p (h^(2*h)) (circleSize h p) h ≤ h^(13*h^2) := by
  have ht := recursive_length_bound h (circleSize h p) (period h p)
    (fun l => (maskTags h p l).length) (maskLength h p (h^(2*h)) (circleSize h p)) hh rfl
    (fun _ => rfl) (hp.period_bound (by omega)) (hp.tags_bound (by omega)) h (le_refl _)
  calc
    _ ≤ circleSize h p*h^(8*h*h) := ht
    _ ≤ h^(5*h^2)*h^(8*h*h) := Nat.mul_le_mul_right _ (hp.circle_bound (by omega))
    _ = _ := by ring

 theorem StandingPrimes.excluded_length_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 3≤h) :
    excludedLength h p (h^(2*h)) (circleSize h p) h ≤ h^(13*h^2) := by
  have ht := recursive_length_bound h (circleSize h p) (period h p)
    (fun _ => h) (excludedLength h p (h^(2*h)) (circleSize h p)) hh rfl
    (fun l => by simp only [excludedLength,length_excludedTags]) (hp.period_bound (by omega))
    (fun _ _ _ => le_self_pow₀ (by omega) (by norm_num)) h (le_refl _)
  calc
    _ ≤ circleSize h p*h^(8*h*h) := ht
    _ ≤ h^(5*h^2)*h^(8*h*h) := Nat.mul_le_mul_right _ (hp.circle_bound (by omega))
    _ = _ := by ring

 theorem StandingPrimes.mask_alphabet_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2≤h) :
    Fintype.card (MaskAlphabet h p h) ≤ h^(6*h^2) := by
  have hc : ∀ l, l≤h → Fintype.card (MaskAlphabet h p l) ≤ 2*h^(5*l) := by
    intro l
    induction l with
    | zero => intro _; change Fintype.card Bool ≤ 2*h^(5*0); norm_num
    | succ l ih =>
      intro hl
      calc
        _ = Fintype.card (MaskTag h p (l+1))*Fintype.card (MaskAlphabet h p l) := Fintype.card_prod _ _
        _ ≤ h^5*(2*h^(5*l)) := Nat.mul_le_mul (hp.tag_card_bound hh _ (by omega) hl) (ih (by omega))
        _ = _ := by ring
  calc
    _ ≤ 2*h^(5*h) := hc h (le_refl _)
    _ ≤ h*h^(5*h) := Nat.mul_le_mul_right _ hh
    _ = h^(5*h+1) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

 theorem StandingPrimes.excluded_alphabet_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2≤h) :
    Fintype.card (ExcludedAlphabet h (circleSize h p) h) ≤ h^(6*h^2) := by
  have hc : ∀ l, Fintype.card (ExcludedAlphabet h (circleSize h p) l) = h^l*(circleSize h p*2) := by
    intro l
    induction l with
    | zero => change Fintype.card (Fin (circleSize h p) × Bool) = 1*(circleSize h p*2); simp
    | succ l ih => change Fintype.card (Fin h × ExcludedAlphabet h (circleSize h p) l) = _
                   rw [Fintype.card_prod,Fintype.card_fin,ih]; ring
  rw [hc]
  calc
    _ ≤ h^h*(h^(5*h^2)*h) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (hp.circle_bound hh) hh)
    _ = h^(5*h^2+h+1) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

 theorem StandingPrimes.mask_alphabet_ge {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 1≤h) (l : ℕ) : 2≤Fintype.card (MaskAlphabet h p l) := by
  have hT (l : ℕ) : 1≤Fintype.card (MaskTag h p l) := by
    have ht : h≤∑ k : Fin h, p l k := by
      calc
        _ = ∑ _k : Fin h, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun k _ => hp.positive l k)
    simpa only [MaskTag,Fintype.card_sigma,Fintype.card_fin] using hh.trans ht
  induction l with
  | zero => change 2≤Fintype.card Bool; norm_num
  | succ l ih =>
    change 2≤Fintype.card (MaskTag h p (l+1) × MaskAlphabet h p l)
    rw [Fintype.card_prod]
    nlinarith [hT (l+1)]

 theorem StandingPrimes.excluded_alphabet_ge {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 1≤h) (l : ℕ) :
    2≤Fintype.card (ExcludedAlphabet h (circleSize h p) l) := by
  induction l with
  | zero =>
    change 2≤Fintype.card (Fin (circleSize h p) × Bool)
    rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    have ht := hp.circle_pos
    omega
  | succ l ih =>
    change 2≤Fintype.card (Fin h × ExcludedAlphabet h (circleSize h p) l)
    rw [Fintype.card_prod,Fintype.card_fin]
    nlinarith

 theorem StandingPrimes.mask_length_pos {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 1≤h) {R : ℕ} (hR : 0<R) (l : ℕ) :
    0 < maskLength h p R (circleSize h p) l := by
  induction l with
  | zero => exact hp.circle_pos
  | succ l ih =>
    have hT : h≤(maskTags h p (l+1)).length := by
      rw [length_maskTags]
      calc
        _ = ∑ _k : Fin h, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun k _ => hp.positive _ k)
    exact Nat.mul_pos (Nat.mul_pos hR (hp.period_pos _)) (Nat.mul_pos (by omega) ih)

 theorem StandingPrimes.excluded_length_pos {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 1≤h) {R : ℕ} (hR : 0<R) (l : ℕ) :
    0<excludedLength h p R (circleSize h p) l := by
  induction l with
  | zero => exact hp.circle_pos
  | succ l ih =>
    simp only [excludedLength,length_excludedTags]
    exact Nat.mul_pos (Nat.mul_pos hR (hp.period_pos _)) (Nat.mul_pos (by omega) ih)

 theorem logarithmic_width_bound {h A w : ℕ} (hh : 100000000≤h) (hA : 0<A)
    (hAb : A≤h^(6*h^2)) (hw : (w:ℝ)≤67108928*Real.log (2*(A:ℝ))) :
    w≤h^(7*h^2) := by
  have hn : Real.log (2*(A:ℝ))≤2*A := by
    have ht := Real.log_le_sub_one_of_pos (show 0<2*(A:ℝ) by positivity)
    linarith
  have hwr : (w:ℝ)≤67108928*(2*A) := hw.trans (mul_le_mul_of_nonneg_left hn (by norm_num))
  have hwn : w≤67108928*(2*A) := by exact_mod_cast hwr
  calc
    _ ≤ 67108928*(2*A) := hwn
    _ ≤ h*(h*h^(6*h^2)) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) hAb)
    _ = h^(6*h^2+2) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

 theorem coded_length_cap {h A w L : ℕ} (hh : 100000000≤h) (hA : 0<A)
    (hAb : A≤h^(6*h^2)) (hw : (w:ℝ)≤67108928*Real.log (2*(A:ℝ)))
    (hL : L≤h^(13*h^2)) : w*L≤h^(32*h^2) := by
  calc
    _ ≤ h^(7*h^2)*h^(13*h^2) := Nat.mul_le_mul (logarithmic_width_bound hh hA hAb hw) hL
    _ = h^(20*h^2) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

 theorem StandingPrimes.log_circle_fourth {n : ℕ} (hn : 1000000≤n) {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes (n^4) p) : Nat.log 2 (circleSize (n^4) p)+1≤n^13 := by
  have nh : 2≤n^4 := (show 2≤n by omega).trans (le_self_pow₀ (by omega) (by norm_num))
  calc
    _ ≤ 6*(n^4)^3 := hp.log_circle_bound nh
    _ ≤ n*(n^4)^3 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

 theorem lower_coefficient_budget {n k J : ℕ} (hn : 1000000≤n) (hk : n^4=4*k)
    (hJ : J≤n^13) :
    (n:ℝ)^k * (4*(n^4:ℕ)/((n^4:ℕ):ℝ)^(2*n^4)+
        2*J/(((n^4:ℕ):ℝ)/2)^(n^4)) ≤ (1/268435456)/(n:ℝ)^(3*n^4) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hnp : (0:ℝ)<n := lt_of_lt_of_le zero_lt_one hn1
  have hk16 : 16≤k := by
    have hh : 64≤n^4 := by
      have ht := Nat.pow_le_pow_left (show 3≤n by omega) 4
      norm_num at ht ⊢
      omega
    omega
  have hp : 0<(n:ℝ)^(14*k) := pow_pos hnp _
  have hn4 : (n:ℝ)^4≤(n:ℝ)^13 := pow_le_pow_right₀ hn1 (by norm_num)
  have h14 : (n:ℝ)^(14*k) ≤ ((n^4:ℕ):ℝ)^(2*n^4) := by
    push_cast
    rw [← pow_mul]
    apply pow_le_pow_right₀ hn1
    omega
  have hbbase : (n:ℝ)^7 ≤ (((n^4:ℕ):ℝ)/2)^2 := by
    have hn4r : (4:ℝ)≤n := by exact_mod_cast (show 4≤n by omega)
    have ht := mul_le_mul_of_nonneg_right hn4r (pow_nonneg hnp.le 7)
    push_cast
    nlinarith [show (n:ℝ)*(n:ℝ)^7=(n:ℝ)^8 by ring]
  have hb : (n:ℝ)^(14*k) ≤ (((n^4:ℕ):ℝ)/2)^(n^4) := by
    calc
      _ = ((n:ℝ)^7)^(2*k) := by rw [← pow_mul]; congr 1; ring
      _ ≤ ((((n^4:ℕ):ℝ)/2)^2)^(2*k) := pow_le_pow_left₀ (by positivity) hbbase _
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hc : (4*((n^4:ℕ):ℝ)/((n^4:ℕ):ℝ)^(2*n^4)+
      2*(J:ℝ)/(((n^4:ℕ):ℝ)/2)^(n^4)) ≤ 6*(n:ℝ)^13/(n:ℝ)^(14*k) := by
    have hJr : (J:ℝ)≤(n:ℝ)^13 := by exact_mod_cast hJ
    calc
      _ ≤ (4*(n:ℝ)^13)/(n:ℝ)^(14*k)+(2*(n:ℝ)^13)/(n:ℝ)^(14*k) := by
        apply add_le_add
        · exact div_le_div₀ (by positivity) (by push_cast; linarith) hp h14
        · exact div_le_div₀ (by positivity) (by linarith) hp hb
      _ = _ := by ring
  have hconst : (6*268435456:ℝ)≤(n:ℝ)^3 := by
    have hr : (1000000:ℝ)≤n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n:ℝ)-1000000)]
  have hpow : (6*268435456:ℝ)*(n:ℝ)^(13*k+13) ≤ (n:ℝ)^(14*k) := by
    calc
      _ ≤ (n:ℝ)^3*(n:ℝ)^(13*k+13) := mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = (n:ℝ)^(13*k+16) := by rw [← pow_add]; congr 1; ring
      _ ≤ _ := pow_le_pow_right₀ hn1 (by omega)
  have hlast : (n:ℝ)^k*(6*(n:ℝ)^13/(n:ℝ)^(14*k)) ≤ (1/268435456)/(n:ℝ)^(3*n^4) := by
    apply (le_div_iff₀ (pow_pos hnp _)).mpr
    rw [div_eq_mul_inv]
    have he : (n:ℝ)^k*(6*(n:ℝ)^13*((n:ℝ)^(14*k))⁻¹)*(n:ℝ)^(3*n^4) =
        6*(n:ℝ)^(13*k+13)/(n:ℝ)^(14*k) := by
      rw [hk]
      ring
    rw [he]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans hlast

 theorem lower_numeric {n k M : ℕ} (hn : 1000000≤n) (hk : n^4=4*k)
    (hJ : Nat.log 2 M+1≤n^13) {w : ℕ} (hw : 0<w) (t : ℝ)
    (ht : (1/268435456)*(w:ℝ)/(n:ℝ)^(3*n^4) ≤ t*w*
      (4*(n^4:ℕ)/((n^4:ℕ):ℝ)^(2*n^4)+2*(Nat.log 2 M+1:ℕ)/(((n^4:ℕ):ℝ)/2)^(n^4))) :
    (n:ℝ)^k ≤ t := by
  let q : ℝ := 4*(n^4:ℕ)/((n^4:ℕ):ℝ)^(2*n^4)+2*(Nat.log 2 M+1:ℕ)/(((n^4:ℕ):ℝ)/2)^(n^4)
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hq : 0<q := by dsimp [q]; positivity
  have hwq : 0<(w:ℝ)*q := mul_pos (by exact_mod_cast hw) hq
  apply (mul_le_mul_iff_left₀ hwq).mp
  calc
    _ = w*((n:ℝ)^k*q) := by ring
    _ ≤ w*((1/268435456)/(n:ℝ)^(3*n^4)) :=
      mul_le_mul_of_nonneg_left (lower_coefficient_budget hn hk hJ) (by positivity)
    _ = (1/268435456)*w/(n:ℝ)^(3*n^4) := by ring
    _ ≤ t*w*q := ht
    _ = _ := by ring

end FiniteCircle

end OAI
