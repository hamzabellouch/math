import OAI.Analysis.FourierLLogL.Thermal.Packing
import OAI.Analysis.FourierLLogL.Thermal.Obtain

/-! # The packing consequence for weighted update choices -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period Compress.Params

variable {M l : ℕ}
open scoped Classical

private lemma most_delta {s : Finset (Grid l)} (hh : s.Nonempty) (P : Law (Grid l))
    (he : evenly s P) (hl : l ≤ M) (A : Form M) (x : Grid l) (r : ℝ) (hr : 0 < r)
    (H : 4*(label A).Ex (form (averageCost hl P x)) ≤ r^2) :
    ∃ u : Finset (Grid l), u⊆s ∧ s.card ≤ 2*u.card ∧ ∀ y∈u, delta A (raise hl (y-x)) ≤ r := by
  classical
  let f := fun y : Grid l => delta A (raise hl (y-x))
  have hH : 2*P.Ex (fun i => f i^2) ≤ r^2 := by
    have he (i : Grid l) : f i^2 = (label A).Ex (fun y => 2*cost (raise hl (i-x)) y) := by
      rw [Ex_lmul,cred_cost]; exact delta_sq A _
    rw [funext (average_form hl P x)] at H
    rw [Ex_swap (label A) P] at H
    simp_rw [he,Ex_lmul]
    linarith
  let u := s.filter (fun i => f i ≤ r)
  refine ⟨u,Finset.filter_subset _ _,?_,fun y hy => (Finset.mem_filter.mp hy).2⟩
  have hs : (0:ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hh
  have HE : ((s\u).card:ℝ)/s.card*r^2 ≤ P.Ex (fun i => f i^2) := calc
    _ = ∑ i∈(s\u), (s.card:ℝ)⁻¹*r^2 := by simp; ring
    _ ≤ ∑ i∈(s\u), P i*f i^2 := Finset.sum_le_sum fun i hi => by
      obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp hi
      rw [he i h1]
      have hi' : r < f i := lt_of_not_ge (fun hh => h2 (Finset.mem_filter.mpr ⟨h1,hh⟩))
      gcongr
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => mul_nonneg (P.nonneg _) (sq_nonneg _)
  have hu : (2:ℝ)*(s\u).card ≤ s.card := by
    field_simp at HE
    by_contra! ht
    have hQ : 0 < r^2 := pow_pos hr _
    nlinarith
  have h1 : 2*(s\u).card ≤ s.card := by exact_mod_cast hu
  rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)] at h1
  unfold u; omega

def stepRad (C : ℝ) (j : ℕ) := sepRad j/(10*C*H j)
def track (C : ℝ) (j n : ℕ) := sepRad j/4 + n*stepRad C j

lemma spacing (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j : ℕ in atTop,
      let η := stepRad C j
      0 < sig j ∧ sig j ≤ 1/4 ∧ 4*sig j ≤ η ∧
        0 < sepRad j ∧ sepRad j ≤ 1 ∧
        4*(400*reserve C/H j^200) ≤ (η/2)^2 ∧
        200-log (sig j) ≤ height j/H j^2 := by
  filter_upwards [h_large (10^8*reserve C),hpoly 1000 3] with j h h'
  intro eta; let a := H j; let s := sig j; let r := sepRad j; let D := reserve C
  have hp : 0 < a := H_pos j; have hh : 1 ≤ a := H_ge j
  have hD : 1 ≤ D := reserve_ge hC
  change 10^8*D ≤ a at h
  have he : s=1/a^40 := rfl
  have hr : r=1/a^30 := rfl
  have hi : eta=1/(10*C*a^31) := by
    unfold eta stepRad; change (1/a^30)/(10*C*a) = _
    ring
  have hC' : 0 < C := by linarith
  have hl : C ≤ D := by unfold D reserve; linarith
  have hx : 100*C ≤ a := by nlinarith
  have h_a (n : ℕ) (ht : 1 ≤ n) : a ≤ a^n := by
    simpa using pow_le_pow_right₀ hh ht
  change 0 < s ∧ s ≤ 1/4 ∧ 4*s ≤ eta ∧
    0 < r ∧ r ≤ 1 ∧ 4*(400*D/a^200) ≤ (eta/2)^2 ∧ 200-log s ≤ _/a^2
  rw [he, hr,hi]
  refine ⟨by positivity, ?_, ?_,by positivity,div_le_self (by norm_num) (one_le_pow₀ hh), ?_, ?_⟩
  · apply one_div_le_one_div_of_le (by norm_num) _
    linarith [h_a 40 (by omega)]
  · have ht : 40*C ≤ a^9 := by linarith [h_a 9 (by omega)]
    rw [show a^40=a^9*a^31 by ring]
    rw [← mul_div_assoc,mul_one]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ a^31)
    nlinarith
  · have ht : 10000*D ≤ a := by linarith
    have hZ : 640000*C^2*D ≤ a^138 := by
      apply le_trans (b:=a^3) _ (pow_le_pow_right₀ hh (by omega))
      calc
        _ ≤ 640000*(a/100)^2*(a/10000) := by gcongr <;> linarith
        _ ≤ _ := by nlinarith [show 0 ≤ a^3 by positivity]
    rw [show a^200 = a^138*(a^31)^2 by ring]
    field_simp
    nlinarith
  rw [log_div (by norm_num) (by positivity),log_one,log_pow]
  apply (le_div_iff₀ (by positivity : 0 < a^2)).mpr
  have he := log_le_sub_one_of_pos hp
  change 1000*a^3 ≤ _ at h'
  push_cast
  nlinarith

lemma r_steps {C : ℝ} (hC : 1 ≤ C) (j n : ℕ) (h : (n:ℝ) ≤ C*H j) :
    0 ≤ track C j n ∧ track C j n ≤ sepRad j / 2 := by
  have hp : 0 < H j := H_pos j
  have he : 0 ≤ sepRad j := by change 0 ≤ 1/H j^30; positivity
  have hC' : 0 < C := by linarith
  unfold track stepRad
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ sepRad j/4 + (C*H j)*(sepRad j/(10*C*H j)) := by gcongr
    _ = sepRad j/4 + sepRad j/10 := by field_simp
    _ ≤ _ := by linarith

lemma step_gap (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ (M l : ℕ) (hl : l ≤ M) (p : Node), p.ok M →
      ∀ (A V : Form M), 0 ≤ A → A+place p M ≤ V →
      ∀ (x : Grid l) (P : Law (Grid l)) (mult t r : ℝ),
      height j/H j^2 ≤ t → t ≤ reserve C*height j →
      height j*H j^200 ≤ mult → (label V).Ex (form (averageCost hl P x)) ≤ 400*t/mult →
      F V-F (A+place p M) ≤ 400*t → 0 ≤ r → r ≤ sepRad j/2 →
      gap V (r+stepRad C j) - gap A r ≤ 402*t ∧
        (∀ (s : Finset (Grid l)) (k : ℝ),
          s.Nonempty → separated (raise hl) A (sepRad j) (sig j*p.invlen/2) s →
          evenly s P → 4*k/5 ≤ log (s.card:ℝ) → t = eps*k →
          gap V (r+stepRad C j) -gap A r ≤ -(k/2)) := by
  classical
  filter_upwards [spacing C hC] with j h
  intro M l hl p hp A V hA hV x P mult t r ht hD hF hG hE hr hr'
  obtain ⟨hs,hs',he,hh,hh',hq,hS⟩ := h
  have hR : 2*r ≤ 1 := by linarith
  have hη : 0 < stepRad C j := by linarith
  have hI := H_pos j; have hI' := d_pos j
  have hT : 0 < t := lt_of_lt_of_le (by positivity) ht
  constructor
  · let f := fun _ : Grid l => (0:Grid M)
    have hw := gap_packing hp hr hR hs hs' he hA hV f {x} ⟨_,Finset.mem_singleton_self x⟩
      (by intro i hi j hj hn; simp_all)
      (fun i hi => by unfold f; rw [delta_zero]; linarith)
    simp only [Finset.card_singleton,Nat.cast_one,log_one,sub_zero] at hw
    linarith
  intro s k h1 h2 h3 h4 h5
  obtain ⟨u,hu,hcard,hdelta⟩ :=
    most_delta h1 P h3 hl V x (stepRad C j/2) (by linarith) (by
      apply le_trans _ hq
      have hz : 0 < height j* H j^200 := by positivity
      have hY : 400*t/mult ≤ 400*reserve C/H j^200 := calc
        _ ≤ 400*(reserve C*height j)/(height j*H j^200) := by have H := lt_of_lt_of_le zero_lt_one (reserve_ge hC); gcongr
        _ = _ := by field_simp
      linarith)
  have hn : u.Nonempty := Finset.card_pos.mp (by have HH := Finset.card_pos.mpr h1; omega)
  let f := fun i : Grid l => raise hl (i-x)
  have hi : separated f A (2*r) (sig j*p.invlen/2) u := by
    intro i hi b hb H H'
    obtain ⟨v,hv,hR⟩ := H'
    apply h2 _ (hu hi) _ (hu hb) H
    use v
    refine ⟨by linarith,?_⟩
    unfold f at hR; simp only [map_sub, sub_sub_sub_cancel_right] at hR; exact hR
  have hw := gap_packing hp hr hR hs hs' he hA hV f u hn hi hdelta
  have hu0 : (0:ℝ)<u.card := by exact_mod_cast Finset.card_pos.mpr hn
  have hv0 : (0:ℝ)<s.card := by exact_mod_cast Finset.card_pos.mpr h1
  have ht' := log_le_log hv0 (show (s.card:ℝ) ≤ 2*u.card by exact_mod_cast hcard)
  rw [Real.log_mul (by norm_num) hu0.ne'] at ht'
  unfold eps at h5
  linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

end FourierLLogL.Dyadic.Thermal

end OAI
