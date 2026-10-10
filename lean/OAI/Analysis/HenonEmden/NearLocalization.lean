import OAI.Analysis.HenonEmden.RadialTaylor

namespace OAI

universe uE uE2

section NearLocalization

open Set Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap

@[fun_prop] lemma measurable_radialFactor (n : ℕ) : Measurable (radialFactor : Space n × Space n → ℝ) := by
  unfold radialFactor; fun_prop
@[fun_prop] lemma measurable_fluxFactor (n : ℕ) : Measurable (fluxFactor n : Space n × Space n → ℝ) := by
  unfold fluxFactor X
  have hη := (continuous_eta n (E := Space n)).measurable
  fun_prop

lemma eta_nonneg {E : Type uE} [NormedAddCommGroup E] (n : ℕ) (x : E) : 0 ≤ eta n x :=
  pow_nonneg (baseProfile_nonneg ‖x‖) _

lemma eta_gap_bounds {E : Type uE2} [NormedAddCommGroup E] (n : ℕ) (x : E) :
    d x^(N n) ≤ eta n x ∧ eta n x ≤ 3^(N n)*d x^(N n) := etaProfile_bounds n ‖x‖

def pairGap {n : ℕ} (z : Space n × Space n) : ℝ := max (d z.1) (d z.2)
def localError {n : ℕ} (z : Space n × Space n) : ℝ :=
  |fluxFactor n z-eta n z.1+w n z.1*radialFactor z|+|eta n z.1-eta n z.2|
def closeConstant (n : ℕ) : ℝ := (2*secondConstant n+4*derivativeConstant n)*2^(N n)

lemma pairGap_bounds {n : ℕ} (z : Space n × Space n) : 0 ≤ pairGap z ∧ pairGap z ≤ 1 :=
  ⟨(d_nonneg z.1).trans (le_max_left _ _),max_le (d_le_one z.1) (d_le_one z.2)⟩
lemma pairGap_power_le {n : ℕ} (z : Space n × Space n) :
    pairGap z^(N n) ≤ eta n z.1+eta n z.2 := by
  rcases le_total (d z.1) (d z.2) with h | h
  · rw [pairGap,max_eq_right h]
    exact (eta_gap_bounds n z.2).1.trans (le_add_of_nonneg_left (eta_nonneg n z.1))
  · rw [pairGap,max_eq_left h]
    exact (eta_gap_bounds n z.1).1.trans (le_add_of_nonneg_right (eta_nonneg n z.2))

lemma close_pair_gaps {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/4)
    {x y : Space n} (hs : 0 < pairGap (x,y)) (hxy : ‖x-y‖ ≤ δ*pairGap (x,y)^(m n)) :
    0 < d x ∧ 0 < d y ∧ d x+dist x y ≤ 2*pairGap (x,y) ∧ ‖x-y‖ ≤ δ*pairGap (x,y) := by
  have hb := pairGap_bounds (x,y)
  have hp : pairGap (x,y)^(m n) ≤ pairGap (x,y) := by
    simpa only [pow_one] using pow_le_pow_of_le_one hb.1 hb.2 (by simp [m] : 1 ≤ m n)
  have hL := hxy.trans (mul_le_mul_of_nonneg_left hp hδ)
  have hd := abs_le.mp (d_oscillation x y)
  rw [dist_eq_norm] at hd
  have hmax : pairGap (x,y) = d x ∨ pairGap (x,y) = d y := max_choice _ _
  have hx := le_max_left (d x) (d y)
  have hy := le_max_right (d x) (d y)
  change d x ≤ pairGap (x,y) at hx
  change d y ≤ pairGap (x,y) at hy
  have hm : δ*pairGap (x,y) ≤ pairGap (x,y)/4 := by nlinarith
  refine ⟨?_,?_,?_,hL⟩
  · rcases hmax with h | h <;> nlinarith
  · rcases hmax with h | h <;> nlinarith
  · rw [dist_eq_norm]; linarith

lemma close_power_bound {n j : ℕ} {s δ L : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hδ : 0 ≤ δ) (hL : L ≤ δ*s^(m n)) (hj : j ≤ N n) (hjm : N n ≤ j+m n) :
    (2*s)^j*L ≤ 2^(N n)*δ*s^(N n) := by
  rw [mul_pow]
  calc
    _ ≤ (2^j*s^j)*(δ*s^(m n)) := mul_le_mul_of_nonneg_left hL (by positivity)
    _ = 2^j*δ*s^(j+m n) := by rw [pow_add]; ring
    _ ≤ 2^(N n)*δ*s^(N n) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj) hδ
      · exact pow_le_pow_of_le_one hs hs1 hjm
      · positivity
      · positivity

lemma flux_close_estimate {n : ℕ} (hn : 1 ≤ n) {x y : Space n} (hx : (1:ℝ)/2 ≤ ‖x‖)
    (hy : ‖y‖ ≤ 2) (hxy : x ≠ y) {D : ℝ} (hD : 0 ≤ D)
    (hseg : ∀ t ∈ uIcc ‖x‖ ‖y‖, gapProfile t ≤ D) :
    |fluxFactor n (x,y)-eta n x+w n x*radialFactor (x,y)| ≤
      (2*secondConstant n*D^(N n-2)+3*derivativeConstant n*D^(N n-1))*‖x-y‖ := by
  obtain ⟨hDc,hSc,hWc⟩ := constants_nonneg n
  have hr : 0 < ‖x‖ := by linarith
  have hL : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hD1 : |derivativeProfile n ‖x‖| ≤ derivativeConstant n*D^(N n-1) :=
    (derivativeProfile_bound n ‖x‖).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (gapProfile_nonneg _) (hseg _ left_mem_uIcc) _) (constants_nonneg n).1)
  have hJ : |inner ℝ (x-y) y| ≤ 2*‖x-y‖ :=
    (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (x-y)])
  have hI : |inner ℝ x (x-y)| ≤ ‖x‖*‖x-y‖ := abs_real_inner_le_norm _ _
  have he := eta_radial_taylor hn hx y hD hseg
  rw [flux_linearization_identity (norm_pos_iff.mp hr) hxy]
  apply (abs_sub_le _ 0 _).trans
  simp only [sub_zero,zero_sub,abs_neg,abs_div,abs_mul,abs_of_nonneg (norm_nonneg x),abs_of_nonneg (sq_nonneg ‖x-y‖)]
  have hfirst : |eta n x-eta n y-derivativeProfile n ‖x‖*inner ℝ x (x-y)/‖x‖| *
      |inner ℝ (x-y) y|/‖x-y‖^2 ≤
      2*(secondConstant n*D^(N n-2)+derivativeConstant n*D^(N n-1))*‖x-y‖ := by
    apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    have hh := mul_le_mul he hJ (abs_nonneg _) (by positivity)
    nlinarith [hh]
  have hsecond : |derivativeProfile n ‖x‖| *|inner ℝ x (x-y)|/‖x‖ ≤ derivativeConstant n*D^(N n-1)*‖x-y‖ := by
    apply (div_le_iff₀ hr).mpr
    have hh := mul_le_mul hD1 hI (abs_nonneg _) (by positivity)
    nlinarith [hh]
  linarith

lemma localError_close {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/4)
    {x y : Space n} (hs : 0 < pairGap (x,y)) (hxy : ‖x-y‖ ≤ δ*pairGap (x,y)^(m n)) (hne : x ≠ y) :
    localError (x,y) ≤ closeConstant n*δ*(eta n x+eta n y) := by
  obtain ⟨hxpos,hypos,hseg,hL⟩ := close_pair_gaps hδ hδ1 hs hxy
  have hs0 := pairGap_bounds (x,y)
  obtain ⟨hDc,hSc,hWc⟩ := constants_nonneg n
  have hC : 0 ≤ closeConstant n := by unfold closeConstant; positivity
  by_cases hx : ‖x‖ ≤ 1/2
  · have hy : ‖y‖ ≤ 1 := by
      have hh := norm_le_norm_add_norm_sub x y
      have hm : δ*pairGap (x,y) ≤ 1/4 := mul_le_of_le_one_right hδ (hs0.2) |>.trans hδ1
      linarith
    have hx1 : ‖x‖ ≤ 1 := by linarith
    have hflux : fluxFactor n (x,y)=1 := by
      simp only [fluxFactor,X,eta_eq_one hx1,eta_eq_one hy,one_smul,real_inner_self_eq_norm_sq]
      exact div_self (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))))
    simp only [localError,hflux,eta_eq_one hx1,eta_eq_one hy,w_inner n hx1,zero_mul,
      sub_self,add_zero,abs_zero]
    positivity
  · have hD : 0 ≤ 2*pairGap (x,y) := by positivity
    have hf := flux_close_estimate hn (le_of_not_ge hx) ((d_pos_iff y).mp hypos).le hne hD
      (fun _ ht => (norm_segment_gap hseg ht).2)
    have he := eta_oscillation n hD hseg
    rw [abs_sub_comm,dist_eq_norm] at he
    have hN := N_ge_two n
    have hP := close_power_bound hs0.1 hs0.2 hδ hxy (by omega : N n-2 ≤ N n) (by simp [m]; omega : N n ≤ N n-2+m n)
    have hP' := close_power_bound hs0.1 hs0.2 hδ hxy (by omega : N n-1 ≤ N n) (by simp [m]; omega : N n ≤ N n-1+m n)
    unfold localError
    calc
      _ ≤ (2*secondConstant n)*((2*pairGap (x,y))^(N n-2)*‖x-y‖)+
        (4*derivativeConstant n)*((2*pairGap (x,y))^(N n-1)*‖x-y‖) := by linarith
      _ ≤ (2*secondConstant n+4*derivativeConstant n)*(2^(N n)*δ*pairGap (x,y)^(N n)) := by
        have hh := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 2*secondConstant n)
        have hh' := mul_le_mul_of_nonneg_left hP' (by positivity : 0 ≤ 4*derivativeConstant n)
        nlinarith
      _ = closeConstant n*δ*pairGap (x,y)^(N n) := by unfold closeConstant; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pairGap_power_le (x,y)) (mul_nonneg hC hδ)

end HenonLaneEmden
end
end NearLocalization

end OAI
