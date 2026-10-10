import OAI.Analysis.FourierLLogL.Procedure.Rating

/-! # Weight of transfers to static processing -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Real Node Period Compress.Params Thermal Fund Scene Fork Road Event Journal Memory

variable {M J j : ℕ} {s : Scene M}
open scoped Classical

namespace Road
def prior (M : ℕ) : Memory M := ⟨[(0,0)],0⟩
lemma prior_ready (j M : ℕ) : Ready (prior M) j (initial M) := by
  constructor <;> simp [prior,initial]
lemma prior_tempered (j : ℕ) (f : Grid M → ℝ) (x) :
    tempered (prior M) j (beginPlay f true) x := by
  simp [prior,tempered,initial,beginPlay,sumE,form_zero]
lemma prior_weight (x : Grid M) : prefixE (prior M).profile root x = 1 := by
  have h : x ∈ root.block M := (mem_group _ _).mp (by rw [group_top]; exact Finset.mem_univ _)
  unfold prefixE; simp [h,tune,prior,sumE,form_zero]

theorem rating_bound :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, 1000*((2:ℝ)^J) ≤ 2^M →
      ∀ f : Grid M → ℝ, (∀ x, f x ≤ exp (height j)) →
      let s := beginPlay f true
      ∀ t : Road j M s, Trusted J f t → 1/H j ≤ s.mass →
      t.expHike (fun l _ => exp (rating s l)) ≤ H j * exp (height j) := by
  filter_upwards [stake_upper,stake_lower] with j hi h M J hJ f hF s t ht hm
  have hv := rootSafe ht
  have he := H_pos j
  have hx : 0 < s.mass := lt_of_lt_of_le (by positivity : 0<1/H j) hm
  let m := prior M
  have hu : expU (t.score m) ≤ 1 := by
    have H := hi M J hJ _ f t ht m (prior_ready j M)
    have HC : prefixE m.profile s.here = fun _ => 1 := funext prior_weight
    simp_rw [HC,one_mul,expU_ex,Ex_const] at H
    exact (expU_ex _).le.trans H
  let F := fun x => t.score m x
  have HX (x) : s.actor x ≤ (H j * exp (height j))* side M := by
    have H := mass_actor (s:=s) hv.within hv.positive x
    have HH : x∈s.here.block M := (mem_group _ _).mp (by
      change x∈root.group M; rw [group_top]; exact Finset.mem_univ _)
    rw [dice_apply hv.within,ite_eq_left HH,show s.here=root from rfl,len_top,inv_one,mul_one] at H
    apply le_of_mul_le_mul_left _ hx
    have h0 := side_pos M; have h1 := exp_pos (height j)
    calc
      _ ≤ side M*exp (height j) :=
        H.le.trans (mul_le_mul_of_nonneg_left (hF _) h0.le)
      _ = (1/Thermal.H j)*(Thermal.H j*exp (height j)*side M) := by field_simp
      _ ≤ _ := by gcongr
  have HN : s.actor.Ex F ≤ H j* exp (height j) := calc
    _ ≤ ∑ i, Thermal.H j * exp (height j) * side M * F i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (HX _) (score_nonneg _ _ _)
    _ = (H j * exp (height j)) * expU F := by
      simp [expU,smul_eq_mul,Finset.mul_sum,mul_assoc]
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hu
  unfold expHike
  apply le_trans _ HN
  exact Ex_mono_mem _ fun x hh =>
    h M J s f t ht m (prior_ready _ _) hx x hh (prior_tempered _ _ _)

theorem rare :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, 1000*((2:ℝ)^J) ≤ 2^M →
      ∀ f : Grid M → ℝ, (∀ x, f x ≤ exp (height j)) →
      let s := beginPlay f true
      ∀ t : Road j M s, Trusted J f t → 1/H j ≤ s.mass →
      s.actor.prob (fun x => (t.hike x).froze = true) ≤ 1/H j^10 := by
  classical
  let C := limitC
  have hC : 1 ≤ C := by unfold C limitC; norm_num
  filter_upwards [rating_bound,mem_budget,log_mass_budget,hpoly capA 1,hpoly (1000*C) 11]
    with j hi hh h ht h' M J hJ f hx s t hT hm
  let a := H j; let d := height j
  have he : 1 ≤ a := H_ge _
  have hp : 0 < a := H_pos _
  have hd : 0 < d := d_pos _
  let Q := s.actor
  have hM : 0 < s.mass := lt_of_lt_of_le (by positivity : 0<1/a) hm
  let V (x : Grid M) := (t.hike x).membership
  let W (x : Grid M) := max (-log (t.hike x).done.mass) 0
  let Y (x : Grid M) := rating s (t.hike x)
  have HE (x : Grid M) (hv : 0 < Q x) :
      (if (t.hike x).froze = true then (1:ℝ) else 0) ≤
        (V x^2+W x^2)*(d^2)⁻¹ + exp (-4*d)*exp (Y x) := by
    split_ifs with H
    · obtain ⟨h1,h2,h3,h4,h5,H6⟩ := final_sound hT hM hv
      rcases (h2 H).2 with Hh|Hh
      · by_cases HB : d ≤ V x
        · apply le_trans (b:=(V x^2+W x^2)*(d^2)⁻¹)
          · rw [← div_eq_mul_inv]
            apply (le_div_iff₀ (by positivity)).mpr; nlinarith [sq_nonneg (W x)]
          linarith [show 0 ≤ exp (-4*d)*exp (Y x) by positivity]
        apply le_trans (b:= exp (-4*d)*exp (Y x))
        · rw [←exp_add]
          apply one_le_exp
          unfold Y rating
          have hX := h1.capital.under
          rw [pow_one] at ht
          change capA*a ≤ d at ht
          change 1000*d < _ at Hh
          change -4*d+(((_-0)/8 - V x)-_) ≥ 0
          rw [show s.fund.uses=0 from rfl,Nat.cast_zero] at h5
          unfold a d at *; unfold V at *; linarith
        exact le_add_of_nonneg_left (by positivity)
      · apply le_trans (b:=(V x^2+W x^2)*(d^2)⁻¹)
        · unfold W
          let v := log (t.hike x).done.mass
          have he' : d ≤ max (-v) 0 := by
            apply le_trans _ (le_max_left _ _)
            have hh := log_lt_log h3 Hh
            rw [Real.log_exp] at hh
            unfold v d; linarith
          rw [← div_eq_mul_inv]
          apply (le_div_iff₀ (by positivity)).mpr
          change _ ≤ _+max (-v) 0 ^2
          nlinarith [sq_nonneg (V x)]
        linarith [show 0 ≤ exp (-4*d)*exp (Y x) by positivity]
    positivity
  have hV : Q.Ex (fun x => V x^2) ≤ (C*a)^2 := (hh M J s f t hT hM).1
  have hW : Q.Ex (fun x => W x^2) ≤ (10*C*a)^2 := h M J s f t hT hm
  have hY : Q.Ex (fun x => exp (Y x)) ≤ a * exp d := hi M J hJ f hx t hT hm
  have hZ := Q.Ex_mono_mem HE
  have HH :
      (Q.Ex (fun x => V x^2) + Q.Ex (fun x => W x^2))*(d^2)⁻¹ ≤ (1/2)/a^10 := by
    have Hp := add_le_add hV hW
    refine (mul_le_mul_of_nonneg_right Hp (by positivity)).trans ?_
    change 1000*C*a^11 ≤ d at h'
    have hv : 1000*C*a^6 ≤ d :=
      (calc
       _ ≤ 1000*C*a^11 := by gcongr; norm_num
       _ ≤ _ := h')
    rw [← div_eq_mul_inv]
    field_simp
    nlinarith [show 0 ≤ C*a^6 by positivity,
      pow_le_pow_left₀ (show 0 ≤ 1000*C*a^6 by positivity) hv 2]
  have HY : exp (-4*d)*Q.Ex (fun x => exp (Y x)) ≤ (1/2)/a^10 := by
    change 1000*C*a^11 ≤ d at h'
    calc
      _ ≤ exp (-4*d)*(a*exp d) := mul_le_mul_of_nonneg_left hY (exp_nonneg _)
      _ = a*(exp (3*d))⁻¹ := by
        rw [mul_left_comm,←exp_add,←Real.exp_neg]; congr 2; ring
      _ ≤ _ := by
        rw [← div_eq_mul_inv]
        apply (div_le_div_iff₀ (exp_pos _) (by positivity)).mpr
        have hz := add_one_le_exp (3*d)
        nlinarith [show 0 ≤ a^11 by positivity]
  unfold prob

  have HZ : Q.prob (fun x => (t.hike x).froze=true)=
      Q.Ex (fun x => if (t.hike x).froze=true then 1 else 0) := by rw [prob_eq]; simp [Ex]
  change Q.prob _ ≤ _
  rw [HZ]
  rw [Ex_add,Ex_mul,Ex_add,Ex_lmul] at hZ
  apply hZ.trans
  apply (add_le_add HH HY).trans
  exact le_of_eq (by unfold a; ring)

end Road
end FourierLLogL.Dyadic.Procedure

end OAI
