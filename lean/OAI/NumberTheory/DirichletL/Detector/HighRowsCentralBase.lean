import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralTerms

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma rowBaseFinite_central_remainder (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j e l : ℕ) (hj : j<6)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let T := fun k m=>rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l k m
    ‖rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-
      (if e=1 ∧ l=0 then T 1 0 else 0)‖≤16*Q^(1/2-x.re) := by
  dsimp only
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  let T := fun k m=>rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l k m
  have hpow : 0≤Q^(1/2-x.re) := by positivity
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z (by rw [hz]))
  have ht (k m : ℕ) (hk : k≤1) (hstrict : ¬(e=1 ∧ l=0 ∧ k=1 ∧ m=0)) :
      ‖T k m‖≤2*Q^(1/2-x.re) := by
    have ht0 : e+3*l≠0 := by rcases hf with h|h|h|h <;> omega
    dsimp only [T,Q]
    simp only [Complex.ofReal_natCast]
    rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k m ht0]
    exact sourceRowTerm_central_nonstrict p hp hg hc eta a rho x w z alpha eps
      heta ha hρ halpha halpha1 heps heps1 hx hw hz j e l k m hj hk hf hstrict
  have hd (k : ℕ) (hk : k≤1) : ‖T k 2/(1-coordV Q z)‖≤4*Q^(1/2-x.re) := by
    rw [div_eq_mul_inv,norm_mul]
    exact (mul_le_mul (ht k 2 hk (by omega)) hv (norm_nonneg _) (by positivity)).trans_eq (by ring)
  by_cases hb : e=1 ∧ l=0
  · rw [ite_eq_left hb]
    have hid : rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-T 1 0=
        ((T 0 0+T 0 1+T 0 2/(1-coordV Q z))+T 1 1)+T 1 2/(1-coordV Q z) := by
      simp only [rowBaseFinite,Fin.sum_univ_two]
      dsimp only [T]
      norm_num only [Fin.val_zero,Fin.val_one]
      ring
    change ‖rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-T 1 0‖≤_
    rw [hid]
    have h00 := ht 0 0 (by omega) (by omega)
    have h01 := ht 0 1 (by omega) (by omega)
    have h11 := ht 1 1 (by omega) (by omega)
    have hn := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h00 h01)) (hd 0 (by omega)))) h11)) (hd 1 (by omega)))
    exact hn.trans (by linarith)
  · rw [ite_eq_right hb,sub_zero]
    unfold rowBaseFinite
    apply (norm_sum_le _ _).trans
    calc
      _≤∑ _k : Fin 2,8*Q^(1/2-x.re) := by
        apply Finset.sum_le_sum
        intro k hk
        have h0 := ht k.val 0 (by omega) (by tauto)
        have h1 := ht k.val 1 (by omega) (by omega)
        exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h0 h1)) (hd k.val (by omega)))).trans_eq (by ring)
      _=16*Q^(1/2-x.re) := by simp;ring

include hc in
theorem rowClosedMarked_central_remainder (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let R := evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z)
    let T := rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j 1 0 1 0
    ‖rowClosedMarked p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j-T/(1-R)‖≤
      128*Q^(1/2-x.re) := by
  dsimp only
  have h02 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 0 2 hj (by omega)
  have h10 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 1 0 hj (by omega)
  have h01 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 0 1 hj (by omega)
  have h11 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 1 1 hj (by omega)
  dsimp only at h02 h10 h01 h11
  norm_num only [and_true,true_and,and_false,false_and,Nat.reduceEqDiff,ite_true,ite_false,sub_zero] at h02 h10 h01 h11
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by rw [hx];linarith) (by rw [hz]))
  simp only [Complex.ofReal_natCast] at *
  unfold rowClosedMarked
  rw [←sub_div,div_eq_mul_inv,norm_mul]
  have heq (A B C D T : ℂ) : A+B+C+D-T=A+(B-T)+C+D := by ring
  rw [heq]
  apply (mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  calc
    _≤(16*(_ : ℝ)+16*_+16*_+16*_)*2 := mul_le_mul_of_nonneg_left hr (by positivity)
    _=_ := by ring
end SevenEighths.ProbeEuler
end

end OAI
