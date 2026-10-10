import OAI.Analysis.FourierLLogL.Compress.Theorem
import OAI.Analysis.FourierLLogL.Compress.Params
/-! # The compression lemma, asymptotic scales -/
open Set Function Filter
open scoped Topology BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Real Law Params

lemma log_ticket (r j : ℕ) (hr : 1 ≤ r) (h : r ≤ 2^j) (hj : 1 ≤ j) :
    log (Fintype.card (Ticket r (2*r)) : ℝ) ≤ 1 + r*(2*(j:ℝ)) := by
  have hp : 0 < (r:ℝ) := by exact_mod_cast hr
  have hcard : Fintype.card (Fin r ↪ Fin (2*r)) ≤ (2*r)^r := by
    have hi := Fintype.card_le_of_injective
      (fun (e : Fin r ↪ Fin (2*r)) => (e : Fin r → Fin (2*r))) (by intro a b hab; ext i : 1; exact congrFun hab i)
    simpa using hi
  have hl2 := log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  have hx : log (2*(r:ℝ)) ≤ 2*(j:ℝ) := by
    rw [log_mul (by norm_num) hp.ne']
    have h1 := Real.log_le_log hp (show (r:ℝ) ≤ 2^j by exact_mod_cast h)
    rw [log_pow] at h1
    have hJ : (1:ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  unfold Ticket
  rw [Fintype.card_option]
  have ht : 0 < ((Fintype.card (Fin r ↪ Fin (2*r)) + 1:ℕ):ℝ) := by positivity
  apply le_trans (Real.log_le_log ht (y:=2*(2*(r:ℝ))^r) ?_) ?_
  · have h1 : Fintype.card (Fin r ↪ Fin (2*r)) + 1 ≤ 2*(2*r)^r := by
      have hp : 0 < (2*r)^r := pow_pos (by omega) _
      omega
    exact_mod_cast h1
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
  nlinarith

private lemma approx_error {d h F D T m j : ℝ} (hh : 1 ≤ h) (hj : h ≤ j)
    (hd : 0 < d) (hm : 0 < m) (hD : 1 ≤ D)
    (hF : d/h^2 ≤ F) (hFd : F ≤ D*d)
    (Ht : d=4*T*h^6)
    (H : 1024*D*j^16 ≤ m) (H' : m^4 ≤ d) :
    (2*m*√F/T)*(d*j^2) ≤ F := by
  have hh' : 0 < h := by linarith
  have hF' : 0 < F := lt_of_lt_of_le (by positivity) hF
  have hp : 0 < T := pos_of_mul_pos_left (show 0 < T*(4*h^6) by
    calc 0 < d := hd
         _ = T*(4*h^6) := by rw [Ht]; ring) (by positivity)
  have hw : 8*D*(j^2*h^8) ≤ m := by
    apply le_trans _ H
    have hj1 : 1 ≤ j := hh.trans hj
    calc
      _ ≤ 8*D*(j^2*j^8) := by gcongr
      _ ≤ 1024*D*j^16 := by
        have HH : j^10 ≤ j^16 := pow_le_pow_right₀ hj1 (by omega)
        rw [← pow_add]; gcongr; norm_num
  have hsr : √F ≤ D*√d := by
    have Hx := sq_sqrt hF'.le
    have Hy := sq_sqrt hd.le
    have Hh : D*d ≤ (D*√d)^2 := by
      rw [mul_pow,Hy]; gcongr; nlinarith
    nlinarith [hFd.trans Hh,sqrt_nonneg F, show 0 ≤ D*√d by positivity]
  have hQ : m^2 ≤ √d := by
    have Ht := sq_sqrt hd.le
    nlinarith [show m^4=(m^2)^2 by ring,sqrt_nonneg d,sq_nonneg (m^2-√d)]
  have hz : 8*m*√F*j^2*h^8 ≤ d := by
    calc
      _ ≤ m * √d * (8*D*(j^2*h^8)) := by
        calc
          _ ≤ 8*m*(D*√d)*j^2*h^8 := by gcongr
          _ = _ := by ring
      _ ≤ m*√d*m := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = m^2*√d := by ring
      _ ≤ √d*√d := mul_le_mul_of_nonneg_right hQ (sqrt_nonneg _)
      _ = d := by rw [← sq,sq_sqrt hd.le]
  apply le_trans (b:=d/h^2) _ hF
  apply (le_div_iff₀ (pow_pos hh' 2)).mpr

  have hle : 2*m*√F*j^2*h^2 ≤ T := by
    rw [Ht] at hz
    refine le_of_mul_le_mul_right ?_ (show 0 < 4*h^6 by positivity)
    calc
      _ = 8*m*√F*j^2*h^8 := by ring
      _ ≤ 4*T*h^6 := hz
      _ = T*(4*h^6) := by ring
  calc
    _ = (2*m*√F*j^2*h^2)/T*d := by ring
    _ ≤ 1*d := mul_le_mul_of_nonneg_right ((div_le_one hp).mpr hle) hd.le
    _ = d := one_mul d

private lemma size_bound {d h F D T a : ℝ} (hh : 1 ≤ h) (hd : 0 < d) (hT : 0 < T)
    (hD : 1 ≤ D) (hp : 0 < F) (hF : F ≤ D*d)
    (Ht : d=4*T*h^6)
    (H : D*h^8 ≤ d) (ha : a ≤ 66/h^2) :
    8*(3*(F/T)+a*(20*D*d)*(20*D*d)/F)+2 ≤ 300000*D^2*d^2/(F*h^2) := by
  have hh' : 0 < h := by linarith
  have hc : 0 < 20*D*d := by positivity
  apply (le_div_iff₀ (by positivity : 0 < F*h^2)).mpr
  let x := D^2*d^2
  have hx : 0 ≤ x := by unfold x; positivity
  have hF1 : F^2 ≤ x := by unfold x; rw [← mul_pow]; gcongr
  have hT1 : h^2 ≤ 4*T := by
    have H1 : h^8 ≤ d := le_trans (le_mul_of_one_le_left (by positivity) hD) H
    rw [Ht,show h^8=h^2*h^6 by ring] at H1
    exact le_of_mul_le_mul_right H1 (by positivity)
  have he1 : F/T*(F*h^2) ≤ 4*x := calc
    _ ≤ F/T*(F*(4*T)) := by gcongr
    _ = 4*F^2 := by field_simp
    _ ≤ 4*x := by gcongr
  have he2 : a*(20*D*d)*(20*D*d)/F*(F*h^2) ≤ (66*400)*x := by
    calc
      _ ≤ (66/h^2)*(20*D*d)*(20*D*d)/F*(F*h^2) := by gcongr
      _ = _ := by unfold x; field_simp; ring
  have HH : h^2 ≤ h^8 := pow_le_pow_right₀ hh (by norm_num)
  have he3 : F*h^2 ≤ x := by
    have h1 : h^8 ≤ d := le_trans (le_mul_of_one_le_left (by positivity) hD) H
    calc
      _ ≤ (D*d)*(D*d) := by gcongr; nlinarith
      _ = _ := by unfold x; ring
  calc
    _ = 24*(F/T*(F*h^2))+8*(a*(20*D*d)*(20*D*d)/F*(F*h^2))+2*(F*h^2) := by ring
    _ ≤ 300000*x := by linarith
    _ = _ := by unfold x; ring

/-- Compression at the scales in terms of d=2^j. -/
theorem entropy_compression (D : ℝ) (hD : 1 ≤ D) :
    ∀ᶠ j : ℕ in atTop, ∀ (A G Θ : Type)
      (_ : Fintype A) (_ : Fintype G) (_ : Fintype Θ) (_ : Nonempty A)
      (_ : DecidableEq G) (_ : AddCommGroup G)
      (tag : A → G), Injective tag → ∀ (q : Law G), (∀ x, 0 < q x) →
      ∀ (c : G → ℝ), (∀ x, 0 ≤ c x) → c 0=0 →
      ∀ (Q : Law Θ) (χ : Θ → AddChar G ℂ),
        (∀ t x, ‖χ t x‖=1) →
        (∀ g, (↑(exp (-c g)):ℂ)=Q.Cx (fun t => χ t g)) →
        (∀ g, -log (q g) = -log (q 0) + c g) →
        -log (q 0) ≤ D*height j →
        (∀ n : ℕ, n ≤ 2^(2*j) → lnS (Fin n) tag ≤ height j * j^2) →
        ∀ F : ℝ, height j/(slow j:ℝ)^2 ≤ F → F ≤ D*height j →
        (∀ p : Law A, exp (-F) ≤ heatMoment (Fin (sLen j)) p tag c) →
        ∃ (a : A) (s : Finset A), s.Nonempty ∧
          log (Fintype.card A)-log (s.card:ℝ) ≤
            300000*D^2*(height j)^2/(F*(slow j:ℝ)^2) ∧
          small_defects tag χ Q (long j) s a (350*F) := by
  filter_upwards [array_spec,big_t_real,below_base 16 (1024*D),
    slow_le_j,slow_tendsto.eventually (eventually_ge_atTop 4),t_expr] with j hs ht hb hj h4 hjt
  intro A G Θ _ _ _ _ _ _ tag hi q hq c hc hc0 Q χ hn hrq hlog hq0 hv F hF hFd h
  let d := height j; let t : ℝ := slow j
  have h4' : 4 ≤ t := by unfold t; exact_mod_cast h4
  have htj : t ≤ j := by unfold t; exact_mod_cast hj
  have hd : 0 < d := by unfold d height; positivity
  let N := sSeg j
  have hpN : (0:ℝ) < N := by
    unfold N; exact_mod_cast pow_pos_nat (j-6*ell j-2)
  obtain ⟨hT,hsm,hmd,hil,horder⟩ := hs
  change d=4*N*t^6 ∧ _ at ht
  have hb' : (base j:ℝ) ≤ cap j := by exact_mod_cast base_le_cap j
  have hj1 : (1:ℝ) ≤ (j:ℝ) := by linarith
  have hh : D*t^8 ≤ d := by
    have h1 : (cap j:ℝ) ≤ d := by unfold d height; exact_mod_cast hmd
    calc
      _ ≤ 1024*D*(j:ℝ)^16 := by
        have hx : t^8 ≤ (j:ℝ)^16 := le_trans (pow_le_pow_left₀ (by linarith) htj _) (pow_le_pow_right₀ hj1 (by norm_num))
        gcongr; nlinarith
      _ ≤ _ := hb.trans (hb'.trans h1)
  have h44 : t^2 ≤ d := by
    calc
      t^2 ≤ t^8 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ ≤ _ := le_trans (le_mul_of_one_le_left (by positivity) hD) hh
  have htp : 0 < t := by linarith
  have he : 1 ≤ F := le_trans (b := d / t^2) ((le_div_iff₀ (sq_pos_of_pos htp)).mpr (by simpa)) hF
  let S := searchSched j h4
  obtain ⟨a,s,h1,h2,h3⟩ := compress_arrays tag hi q hq c hc hc0 Q χ hn hrq hlog
    F (long j) (20*D*d) he (by unfold long; positivity)
    (sLen j) N (cap j) (pow_pos_nat _) hsm hT S (stepLow j) (stepHigh j) (stepRows j)
    (by
      intro i _
      have hh := hil i
      exact ⟨hh.1,hh.2.1,pow_pos_nat _,pow_pos_nat _,hh.2.2.1.le,hh.2.2.2.1⟩)
    (by intro i k hik hk; exact horder i k hik hk) h (by dsimp only [d] at *; linarith)
    (fun i _ => pow_pos_nat _) (by
      have hn' : N ≤ 2^j := by unfold N sSeg; apply Nat.pow_le_pow_right <;> omega
      have hErr := approx_error (by linarith : (1:ℝ) ≤ t) htj hd
        (show (0:ℝ) < cap j by exact_mod_cast pow_pos_nat (capE j))
        hD hF hFd ht.1 (hb.trans hb') ht.2
      intro i _
      let l := stepLow j i; let r := stepRows j i
      have hlo := hil i
      have hjt : 2^j ≤ 2^(2*j) := Nat.pow_le_pow_right (by omega) (by omega)
      let ε := 2*(cap j:ℝ)*√F/N
      have hε : 0 ≤ ε := by unfold ε; positivity
      have hz (k : ℕ) (hh : k ≤ 2^j) : ε * lnS (Fin k) tag ≤ F :=
        (mul_le_mul_of_nonneg_left (hv k (hh.trans hjt)) hε).trans hErr
      have hp : 0 < r := pow_pos_nat _
      have hl : 0 < l := pow_pos_nat _
      have hqr : 2*r*l=N := hlo.2.2.1
      have hiN : r*l ≤ N := by nlinarith
      have hiR : r ≤ N := le_trans (Nat.le_mul_of_pos_right r hl) hiN
      have HR := hz (r*l) (hiN.trans hn')
      refine ⟨hz _ (hlo.2.1.trans hmd),?_⟩
      have H1 := log_ticket r j hp (hiR.trans hn') (by omega)
      have hb'' : (base j:ℝ) ≤ l := by exact_mod_cast hlo.2.2.2.2
      have hlB : 4*(j:ℝ)*t^2 ≤ l := by
        apply le_trans _ (hb.trans hb'')
        calc
          _ ≤ 4*((j:ℝ)*(j:ℝ)^2) := by rw [mul_assoc]; gcongr
          _ ≤ _ := by
            rw [show (j:ℝ)*(j:ℝ)^2=(j:ℝ)^3 by ring]
            have HH : (j:ℝ)^3 ≤ (j:ℝ)^16 := pow_le_pow_right₀ hj1 (by norm_num)
            gcongr; linarith
      have hND : (N:ℝ) ≤ d := by unfold d height; exact_mod_cast hn'
      have hRN : (r:ℝ)*l ≤ N := by exact_mod_cast hiN
      have hrD : (r:ℝ)*(4*(j:ℝ)) ≤ F := by
        apply le_trans _ hF
        apply (le_div_iff₀ (by positivity : 0 < t^2)).mpr
        rw [mul_assoc]
        exact (mul_le_mul_of_nonneg_left hlB (by positivity)).trans (hRN.trans hND)
      change log _+(r:ℝ)+ 2 * ε*lnS (Fin (r*l)) tag ≤ _
      nlinarith [show (0:ℝ) ≤ r by positivity])
  exact ⟨a,s,h1,h2.trans
    (size_bound (by linarith : (1:ℝ) ≤ t) hd hpN hD (by linarith) hFd ht.1 hh (searchSched_loss _ h4)),h3⟩
end FourierLLogL.Compress

end OAI
