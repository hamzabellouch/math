import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.SourceTrainingScales

namespace OAI

section
namespace SharpLogRamsey.LearningScalar
open Real
noncomputable section

lemma power_ratio_bound {B t P c : ℝ} (p : ℕ) (hB : 0≤B) (ht : 0<t)
    (hr : B/t≤exp (P/100)) :
    B^p*exp (-c*((p:ℝ)*P))/t^p≤exp ((p:ℝ)*(P/100-c*P)) := by
  calc
    _ = (B/t)^p*exp (-c*((p:ℝ)*P)) := by rw [div_pow]; ring
    _ ≤ (exp (P/100))^p*exp (-c*((p:ℝ)*P)) := by gcongr
    _ = _ := by rw [←exp_nat_mul,←exp_add]; congr 1; ring

theorem short_row_lower {σ P B N Q W b e : ℝ} {p : ℕ}
    (_hσ : 1≤σ) (hP : 100000000000000≤P) (hPu : P≤σ)
    (hB : 0<B) (hN : 1≤N) (hQ : 0≤Q) (hQu : Q≤2*exp (3*σ))
    (_hW : 0≤W) (hWu : W≤20804*exp σ*B)
    (hb : 0≤b) (_he : 0≤e) (hloss : b+e≤P/1000000)
    (hp : 10000*σ≤(p:ℝ)*P) :
    let z := exp σ*B*exp (-b-e)/8
    let t := z/(10*exp σ)
    let εs := B^2*exp (-(3/5:ℝ)*P)/t^2
    let εa := B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p
    exp (-e)/4≤exp (-e)/2-W*exp (-P/1000)/((1/1000:ℝ)*z)-
      N*εs/(N/100)-Q*εa/N-2*exp (-(exp σ*P)/3) := by
  let z := exp σ*B*exp (-b-e)/8
  let t := z/(10*exp σ)
  have hN0 : 0<N := by linarith
  have hP0 : 0≤P := by linarith
  have hz : 0<z := by dsimp [z]; positivity
  have ht : 0<t := by dsimp [t]; positivity
  have heP : e≤P := by linarith
  have ha : 80≤exp (P/200) := by have hh := add_one_le_exp (P/200); linarith
  have ha' : 80*exp (b+e)≤exp (P/100) := by
    calc
      _ ≤ exp (P/200)*exp (b+e) := mul_le_mul_of_nonneg_right ha (exp_pos _).le
      _ = _ := (exp_add _ _).symm
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hr : B/t≤exp (P/100) := by
    have hh : B/t=80*exp (b+e) := by
      dsimp [t,z]
      have hx : exp (-b-e)*exp (b+e)=1 := by rw [←exp_add]; ring_nf; exact exp_zero
      field_simp
      nlinarith only [hx]
    rw [hh]
    exact ha'
  have hεs : B^2*exp (-(3/5:ℝ)*P)/t^2≤exp (-29*P/50) := by
    have hh := power_ratio_bound 2 hB.le ht hr (c:=3/10)
    norm_num only [Nat.cast_ofNat] at hh
    rw [show -(3/10:ℝ)*(2*P)=-(3/5:ℝ)*P by ring,
      show (2:ℝ)*(P/100-3/10*P)=-29*P/50 by ring] at hh
    exact hh
  have hεa : B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p≤exp (-9*(p:ℝ)*P/100) := by
    have hh := power_ratio_bound p hB.le ht hr (c:=1/10)
    rw [show (p:ℝ)*(P/100-1/10*P)=-9*(p:ℝ)*P/100 by ring] at hh
    exact hh
  have hwerr : W*exp (-P/1000)/((1/1000:ℝ)*z)≤exp (-e)/16 := by
    have hc : 2662912000≤exp (P/2000) := by
      have hh := add_one_le_exp (P/2000)
      linarith
    have hh : 166432000*exp (b+e-P/1000)≤exp (-e)/16 := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
      calc
        _ = 2662912000*exp (b+e-P/1000) := by ring
        _ ≤ exp (P/2000)*exp (b+e-P/1000) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
        _ = _ := (exp_add _ _).symm
        _ ≤ _ := exp_le_exp.mpr (by linarith)
    apply le_trans _ hh
    have hh' := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hWu (exp_pos (-P/1000)).le)
      (show 0≤(1/1000:ℝ)*z by positivity)
    apply hh'.trans_eq
    dsimp [z]
    have hx : exp (-P/1000)=exp (b+e-P/1000)*exp (-b-e) := by
      rw [←exp_add]; congr 1; ring
    rw [hx]
    field_simp
    ring
  have hserr : N*(B^2*exp (-(3/5:ℝ)*P)/t^2)/(N/100)≤exp (-e)/16 := by
    have hc : 1600≤exp (P/2) := by have hh := add_one_le_exp (P/2); linarith
    calc
      _ = 100*(B^2*exp (-(3/5:ℝ)*P)/t^2) := by field_simp
      _ ≤ 100*exp (-29*P/50) := mul_le_mul_of_nonneg_left hεs (by norm_num)
      _ ≤ exp (-e)/16 := by
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
        calc
          _ = 1600*exp (-29*P/50) := by ring
          _ ≤ exp (P/2)*exp (-29*P/50) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
          _ = _ := (exp_add _ _).symm
          _ ≤ _ := exp_le_exp.mpr (by linarith)
  have haerr : Q*(B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p)/N≤exp (-e)/16 := by
    have hc : 32≤exp (896*σ) := by have hh := add_one_le_exp (896*σ); linarith
    calc
      _ ≤ Q*exp (-9*(p:ℝ)*P/100)/N := by gcongr
      _ ≤ (2*exp (3*σ))*exp (-900*σ) := by
        have hex : exp (-9*(p:ℝ)*P/100)≤exp (-900*σ) := exp_le_exp.mpr (by linarith only [hp])
        calc
          _ ≤ Q*exp (-9*(p:ℝ)*P/100) := div_le_self (by positivity) hN
          _ ≤ _ := mul_le_mul hQu hex (exp_pos _).le (by positivity)
      _ = 2*exp (-897*σ) := by rw [mul_assoc,←exp_add]; congr 2; ring
      _ ≤ exp (-e)/16 := by
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
        calc
          _ = 32*exp (-897*σ) := by ring
          _ ≤ exp (896*σ)*exp (-897*σ) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
          _ = exp (-σ) := by rw [←exp_add]; congr 1; ring
          _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hcut : 2*exp (-(exp σ*P)/3)≤exp (-e)/16 := by
    have hc : 32≤exp (P/4) := by have hh := add_one_le_exp (P/4); linarith
    have hq : 1≤exp σ := one_le_exp_iff.mpr (by linarith)
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
    calc
      _ = 32*exp (-(exp σ*P)/3) := by ring
      _ ≤ exp (P/4)*exp (-(exp σ*P)/3) := mul_le_mul_of_nonneg_right hc (exp_pos _).le
      _ = _ := (exp_add _ _).symm
      _ ≤ _ := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hq hP0])
  dsimp only
  change exp (-e)/4≤exp (-e)/2-W*exp (-P/1000)/((1/1000:ℝ)*z)-
    N*(B^2*exp (-(3/5:ℝ)*P)/t^2)/(N/100)-
    Q*(B^p*exp (-(1/10:ℝ)*((p:ℝ)*P))/t^p)/N-2*exp (-(exp σ*P)/3)
  linarith only [hwerr,hserr,haerr,hcut]

lemma row_capture {N X P : ℝ} (hN : 0≤N) (hP : 100000≤P)
    (hX : X≤N*exp (-P/200)+N/10000) :
    N/2≤N-X-N/100-(10*((1/1000:ℝ)+1/1000))*N := by
  have he : 100≤exp (P/200) := by
    have hh := add_one_le_exp (P/200)
    linarith
  have he' : exp (-P/200)≤1/100 := by
    rw [show -P/200=-(P/200) by ring,exp_neg]
    exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by simpa using he)
  have hh := mul_le_mul_of_nonneg_left he' hN
  linarith

lemma row_size {N q P D b e : ℝ} (hN : 0<N) (hq : 0<q)
    (hP : 100000≤P) (hloss : b+e≤P) (hsmall : 2*q*P≤N)
    (hD : D≤2*N+N*exp (5*P)) (j : ℕ) :
    2*q*P+D+N+100*q^(j+1)/(q*(q^j/N)*exp (-b-e)/8)≤N*exp (6*P) := by
  have hqB : 100*q^(j+1)/(q*(q^j/N)*exp (-b-e)/8)=800*N*exp (b+e) := by
    rw [pow_succ]
    have hx : exp (-b-e)*exp (b+e)=1 := by
      rw [←exp_add,show -b-e+(b+e)=0 by ring,exp_zero]
    field_simp
    nlinarith only [hx]
  rw [hqB]
  have he : 804≤exp P := by have hh := add_one_le_exp P; linarith
  have h1 : 1≤exp (5*P) := one_le_exp_iff.mpr (by linarith)
  have hbe : exp (b+e)≤exp (5*P) := exp_le_exp.mpr (by linarith)
  calc
    _ ≤ N*(4+exp (5*P)+800*exp (b+e)) := by linarith only [hsmall,hD]
    _ ≤ 804*N*exp (5*P)+N*exp (5*P) := by nlinarith
    _ ≤ N*exp (6*P) := by
      have he' : 805≤exp P := by have hh := add_one_le_exp P; linarith
      calc
        _ = N*(805*exp (5*P)) := by ring
        _ ≤ N*(exp P*exp (5*P)) := by gcongr
        _ = _ := by rw [←exp_add]; congr 2; ring

end
end SharpLogRamsey.LearningScalar

end

end OAI
