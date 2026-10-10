import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ConeMotion

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology

namespace RVM

lemma selected_coefficient_exponent_bound
    {P α z c b y H Δ : ℝ} (hP : 1 < P)
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z+c=1) (hΔ : Δ=(α+b+y+H)/100000)
    (hnear : 2*α+H/2+2*y < z+Δ)
    (hfar₁ : H ≤ 2*c → b < H/2-α+Δ)
    (hfar₂ : 2*c < H → b < H-c-α+Δ)
    (hactual : (623/1000 : ℝ) < min z (1-α)-y →
      b < H/2-min α c+y+(2/1000 : ℝ)*z)
    (himproved : (7/10 : ℝ) ≤ z → (7/10 : ℝ) ≤ 1-α →
      (16/100 : ℝ)*max z (1-α) ≤ y →
      y ≤ (49/100 : ℝ)*min z (1-α) →
      b < H/2-min α c+(29/50 : ℝ)*y+Δ) :
    min (P^(-z-2*H+3*b)) (P^(-z-b+H+2*y)) ≤ P^(-z/2-Δ) := by
  by_contra hbad
  have hbad' := lt_of_not_ge hbad
  have hl := (Real.rpow_lt_rpow_left_iff hP).mp
    (hbad'.trans_le (min_le_left _ _))
  have hr := (Real.rpow_lt_rpow_left_iff hP).mp
    (hbad'.trans_le (min_le_right _ _))
  have hu₁ : 2*H/3+z/6-Δ/3 < b := by linarith
  have hu₂ : b < H+2*y-z/2+Δ := by linarith
  obtain ⟨hzp,hd,_,hlow,_,_,_,hm₁,hm₂⟩ :=
    unsafe_selected_actual_margins hα hz hc hy hH hzc hΔ hnear hfar₁ hfar₂ hu₁
  have ham : (623/1000 : ℝ) < min z (1-α)-y := by
    rw [← min_sub_sub_right]; exact lt_min hm₁ hm₂
  obtain ⟨hz',hpa',hyl,hyu⟩ := unsafe_selected_improved_window
    hα hz hc hy hH hzc hΔ hnear hfar₁ hfar₂ hu₁ hu₂ (hactual ham)
  exact unsafe_selected_improved_contradiction hα hzp hc hd hlow hnear hu₁
    (himproved (by linarith) (by linarith) hyl.le hyu.le)

lemma max_growth_bound {P c H E : ℝ} (hP : 1 < P)
    (hHc : 2*c ≤ H) (hE : 2*c ≤ E) :
    max 1 (max (P^(-2*c)*P^E) (P^(-H)*P^E)) ≤ P^(-2*c+E) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  refine max_le ?_ (max_le ?_ ?_)
  · exact Real.one_le_rpow hP.le (by linarith)
  · rw [← Real.rpow_add hP0]
  · rw [← Real.rpow_add hP0]
    exact (Real.rpow_le_rpow_left_iff hP).mpr (by linarith)

lemma selected_coefficient_power_table
    {P C₀ α z c b y H Δ k Λ : ℝ} (hP : 1 < P)
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z+c=1) (hΔ : Δ=(α+b+y+H)/100000)
    (hnear : 2*α+H/2+2*y < z+Δ)
    (hk : 0 ≤ k) (hfar : P^(α+b-H-Δ) < k)
    (henergy : k^2 ≤ P^(-min (2*c) H))
    (hC₀ : C₀ ≤ P^(3/10 : ℝ))
    (hΛ : (66/100 : ℝ) < z → Λ^2 ≤ P^(2*max α c+2*y+2*z/1000))
    (hactual : C₀ < P^(min z (1-α)-y) →
      k^2 ≤ P^(-H)*max 1 (max (P^(-2*c)*Λ^2) (P^(-H)*Λ^2)))
    (himproved : (7/10 : ℝ) ≤ z → (7/10 : ℝ) ≤ 1-α →
      (16/100 : ℝ)*max z (1-α) ≤ y →
      y ≤ (49/100 : ℝ)*min z (1-α) →
      k^2 ≤ P^(-H+(29/25 : ℝ)*y)*
        max 1 (max (P^(-2*c)*P^(2*max α c)) (P^(-H)*P^(2*max α c)))) :
    min (P^(-z-2*H+3*b)) (P^(-z-b+H+2*y)) ≤ P^(-z/2-Δ) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hkfar : P^((α+b-H-Δ)*2) < k^2 := by
    rw [Real.rpow_mul hP0.le, Real.rpow_two]
    exact (sq_lt_sq₀ (Real.rpow_nonneg hP0.le _) hk).mpr hfar
  have hfarE := (Real.rpow_lt_rpow_left_iff hP).mp (hkfar.trans_le henergy)
  have hfar₁ : H ≤ 2*c → b < H/2-α+Δ := by
    intro hh
    rw [min_eq_right hh] at hfarE
    linarith
  have hfar₂ : 2*c < H → b < H-c-α+Δ := by
    intro hh
    rw [min_eq_left hh.le] at hfarE
    linarith
  by_contra hbad
  have hb' := lt_of_not_ge hbad
  have hl := (Real.rpow_lt_rpow_left_iff hP).mp
    (hb'.trans_le (min_le_left _ _))
  have hr := (Real.rpow_lt_rpow_left_iff hP).mp
    (hb'.trans_le (min_le_right _ _))
  have hu₁ : 2*H/3+z/6-Δ/3 < b := by linarith
  have hu₂ : b < H+2*y-z/2+Δ := by linarith
  obtain ⟨hzp,hd,hHc,hlow,_,hzlarge,_,hm₁,hm₂⟩ :=
    unsafe_selected_actual_margins hα hz hc hy hH hzc hΔ hnear hfar₁ hfar₂ hu₁
  have ham : (623/1000 : ℝ) < min z (1-α)-y := by
    rw [← min_sub_sub_right]; exact lt_min hm₁ hm₂
  have hC : C₀ < P^(min z (1-α)-y) :=
    hC₀.trans_lt ((Real.rpow_lt_rpow_left_iff hP).mpr (by linarith))
  have hΛ' := hΛ (by linarith)
  have hmax : max 1 (max (P^(-2*c)*Λ^2) (P^(-H)*Λ^2)) ≤
      P^(-2*c+(2*max α c+2*y+2*z/1000)) := by
    calc
      _ ≤ max 1 (max (P^(-2*c)*P^(2*max α c+2*y+2*z/1000))
          (P^(-H)*P^(2*max α c+2*y+2*z/1000))) := by gcongr
      _ ≤ _ := max_growth_bound hP hHc.le (by have := le_max_right α c; linarith)
  have hka := (hactual hC).trans
    (mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg hP0.le _))
  rw [← Real.rpow_add hP0] at hka
  have hfa := (Real.rpow_lt_rpow_left_iff hP).mp (hkfar.trans_le hka)
  have hmaxmin : max α c + min α c = α+c := max_add_min α c
  have hactual' : b < H/2-min α c+y+(2/1000 : ℝ)*z := by linarith
  obtain ⟨hz',hpa',hyl,hyu⟩ := unsafe_selected_improved_window
    hα hz hc hy hH hzc hΔ hnear hfar₁ hfar₂ hu₁ hu₂ hactual'
  have hki := (himproved (by linarith) (by linarith) hyl.le hyu.le).trans
    (mul_le_mul_of_nonneg_left
      (max_growth_bound hP hHc.le (by have := le_max_right α c; linarith))
      (Real.rpow_nonneg hP0.le _))
  rw [← Real.rpow_add hP0] at hki
  have hfi := (Real.rpow_lt_rpow_left_iff hP).mp (hkfar.trans_le hki)
  have himproved' : b < H/2-min α c+(29/50 : ℝ)*y+Δ := by linarith
  exact unsafe_selected_improved_contradiction hα hzp hc hd hlow hnear hu₁ himproved'

lemma eventually_selection_constants (C₀ C₁ M A : ℝ)
    (hC₁ : 0 ≤ C₁) (hA : 0 ≤ A) :
    ∀ᶠ P : ℝ in atTop, 1 < P ∧ C₀ ≤ P^(3/10 : ℝ) ∧
      C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ) := by
  have he : (0 : ℝ) < 66/100000 := by norm_num
  have hconst : (fun _ : ℝ => C₁*M) =o[atTop]
      (fun P : ℝ => P^(66/100000 : ℝ)) :=
    (Asymptotics.isLittleO_const_id_atTop _).comp_tendsto (tendsto_rpow_atTop he)
  have hsqrt := (isLittleO_log_rpow_rpow_atTop (1/2 : ℝ) he).const_mul_left
    (C₁*Real.sqrt (2*A))
  have hsum := hconst.add hsqrt
  filter_upwards [hsum.bound (by norm_num : (0 : ℝ) < 1),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/10)).eventually_ge_atTop C₀,
    eventually_ge_atTop (2 : ℝ)] with P hsum hC₀ hP
  have hP0 : 0 < P := by linarith
  refine ⟨by linarith,hC₀,?_⟩
  have hlog : Real.log (2+P) ≤ 2*Real.log P := by
    calc
      _ ≤ Real.log (P^2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hs : Real.sqrt (A*Real.log (2+P)) ≤
      Real.sqrt (2*A)*Real.sqrt (Real.log P) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*A)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hb : C₁*M+(C₁*Real.sqrt (2*A))*Real.log P^(1/2 : ℝ) ≤ P^(66/100000 : ℝ) := by
    have := (le_abs_self (C₁*M+(C₁*Real.sqrt (2*A))*Real.log P^(1/2 : ℝ))).trans hsum
    simpa only [Real.norm_eq_abs, one_mul, abs_of_pos (Real.rpow_pos_of_pos hP0 _)] using this
  rw [← Real.sqrt_eq_rpow] at hb
  nlinarith

def selectionWeight (P θ φ h : ℝ) : ℝ :=
  (P*θ)^(-1/100000 : ℝ)*φ^(1/100000 : ℝ)*h^(1/100000 : ℝ)

def receiverCoefficient (w p θ φ h : ℝ) : ℝ :=
  w⁻¹ * min (h^2*(p*θ)^3) ((p*θ*h*φ^2)⁻¹)

def stabilityRate (P C₁ M A p w φ : ℝ) : ℝ :=
  C₁*(P/min p w)*(M/φ+Real.sqrt (A*Real.log (2+P)/φ))

def stabilityLength (P C₁ M A p w φ : ℝ) : ℝ :=
  (stabilityRate P C₁ M A p w φ)⁻¹ ^ 2

lemma div_stabilityLength (P C₁ M A p w φ t : ℝ) :
    t/stabilityLength P C₁ M A p w φ =
      t*(stabilityRate P C₁ M A p w φ)^2 := by
  simp [stabilityLength, div_eq_mul_inv, inv_pow]

lemma sqrt_div_le_small_denominator {a x : ℝ} (ha : 0 ≤ a)
    (hx : 0 < x) (hx₁ : x ≤ 1) : Real.sqrt (a/x) ≤ Real.sqrt a/x := by
  rw [Real.sqrt_div ha]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg a) hx
    (Real.le_sqrt_self_iff.mpr hx₁)

lemma rpow_min_exponent {P a b : ℝ} (hP : 1 < P) :
    min (P^a) (P^b) = P^(min a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left ((Real.rpow_le_rpow_left_iff hP).mpr h)]
  · rw [min_eq_right h, min_eq_right ((Real.rpow_le_rpow_left_iff hP).mpr h)]

lemma sqrt_rpow_base {P : ℝ} (hP : 0 ≤ P) (a : ℝ) :
    Real.sqrt (P^a) = P^(a/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP]
  congr 1
  ring

lemma stabilityRate_power_bound {P C₁ M A p w φ α z c y : ℝ}
    (hP : 1 < P) (hC₁ : 0 ≤ C₁) (hA : 0 ≤ A)
    (hp : p=P^(1-α)) (hw : w=P^z) (hφ : φ=P^(-y))
    (hφ₁ : φ ≤ 1) (hzc : z+c=1) (hz : (66/100 : ℝ) < z)
    (hconst : C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ)) :
    stabilityRate P C₁ M A p w φ ≤ P^(max α c+y+z/1000) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hφ0 : 0 < φ := hφ ▸ Real.rpow_pos_of_pos hP0 _
  have hm : min p w = P^(1-max α c) := by
    rw [hp,hw,rpow_min_exponent hP]
    congr 1
    rcases le_total α c with hh | hh
    · rw [max_eq_right hh,min_eq_right (by linarith)]; linarith
    · rw [max_eq_left hh,min_eq_left (by linarith)]
  have hm0 : 0 < min p w := hm ▸ Real.rpow_pos_of_pos hP0 _
  have hAL : 0 ≤ A*Real.log (2+P) := mul_nonneg hA (Real.log_nonneg (by linarith))
  have hs := sqrt_div_le_small_denominator hAL hφ0 hφ₁
  have hfactor : P/min p w/φ = P^(max α c+y) := by
    rw [hm,hφ]
    nth_rw 1 [← Real.rpow_one P]
    rw [← Real.rpow_sub hP0,← Real.rpow_sub hP0]
    congr 1
    ring
  calc
    _ ≤ C₁*(P/min p w)*(M/φ+Real.sqrt (A*Real.log (2+P))/φ) := by
      unfold stabilityRate
      gcongr
    _ = (C₁*(M+Real.sqrt (A*Real.log (2+P)))) * P^(max α c+y) := by
      rw [← hfactor]
      ring
    _ ≤ P^(66/100000 : ℝ) * P^(max α c+y) := by gcongr
    _ = P^((66/100000 : ℝ)+(max α c+y)) := (Real.rpow_add hP0 _ _).symm
    _ ≤ _ := (Real.rpow_le_rpow_left_iff hP).mpr (by linarith)

lemma nat_pow_rpow_base {P : ℝ} (hP : 0 ≤ P) (a : ℝ) (n : ℕ) :
    (P^a)^n = P^(a*n) := (Real.rpow_mul_natCast hP a n).symm

lemma selectionWeight_power {P p θ φ h α b y H : ℝ} (hP : 0 < P)
    (hp : p=P^(1-α)) (hpθ : p*θ=P^b) (hφ : φ=P^(-y)) (hh : h=P^(-H)) :
    selectionWeight P θ φ h = P^(-(α+b+y+H)/100000) := by
  have hp0 : p ≠ 0 := hp ▸ (Real.rpow_pos_of_pos hP _).ne'
  have hPθ : P*θ = P^(α+b) := by
    calc
      _ = (P*(p*θ))/p := by field_simp
      _ = (P*P^b)/P^(1-α) := by rw [hpθ,hp]
      _ = P^(1+b)/P^(1-α) := by rw [Real.rpow_add hP,Real.rpow_one]
      _ = P^((1+b)-(1-α)) := (Real.rpow_sub hP _ _).symm
      _ = _ := by congr 1; ring
  unfold selectionWeight
  rw [hPθ,hφ,hh,← Real.rpow_mul hP.le,← Real.rpow_mul hP.le,
    ← Real.rpow_mul hP.le,← Real.rpow_add hP,← Real.rpow_add hP]
  congr 1
  ring

lemma receiverCoefficient_power {P w p θ φ h z b y H : ℝ} (hP : 0 < P)
    (hw : w=P^z) (hpθ : p*θ=P^b) (hφ : φ=P^(-y)) (hh : h=P^(-H)) :
    receiverCoefficient w p θ φ h =
      min (P^(-z-2*H+3*b)) (P^(-z-b+H+2*y)) := by
  unfold receiverCoefficient
  rw [hw,hpθ,hφ,hh,mul_min_of_nonneg _ _ (inv_nonneg.mpr (Real.rpow_nonneg hP.le _)),
    ← Real.rpow_neg hP.le, nat_pow_rpow_base hP.le, nat_pow_rpow_base hP.le,
    nat_pow_rpow_base hP.le]
  norm_num only [Nat.cast_ofNat]
  simp only [← Real.rpow_add hP,← Real.rpow_neg hP.le]
  congr 2 <;> ring

lemma selected_near_far_powers
    {P p w θ φ h I μ α z c b y H Δ : ℝ} (hP : 1 < P)
    (hp : p=P^(1-α)) (hw : w=P^z) (hpθ : p*θ=P^b)
    (hφ : φ=P^(-y)) (hh : h=P^(-H))
    (hzc : z+c=1) (hΔ : Δ=(α+b+y+H)/100000)
    (hI0 : 0 < I) (hI : I ≤ (w/P)^2)
    (hselected : P*Real.sqrt I*selectionWeight P θ φ h <
      min (I*Real.sqrt h*p^2*φ^2) (Real.sqrt I*Real.sqrt (p*μ)/(θ*h))) :
    2*α+H/2+2*y < z+Δ ∧ P^(α+b-H-Δ) < Real.sqrt (p*μ) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hp0 : 0 < p := hp ▸ Real.rpow_pos_of_pos hP0 _
  have hθ0 : 0 < θ := (mul_pos_iff.mp (hpθ ▸ Real.rpow_pos_of_pos hP0 _)).resolve_right
    (by rintro ⟨hh,_⟩; linarith) |>.2
  have hh0 : 0 < h := hh ▸ Real.rpow_pos_of_pos hP0 _
  have hWI : selectionWeight P θ φ h = P^(-Δ) := by
    rw [selectionWeight_power hP0 hp hpθ hφ hh,hΔ,neg_div]
  have hI' : I ≤ P^(-2*c) := by
    calc
      I ≤ (w/P)^2 := hI
      _ = (P^(z-1))^2 := by rw [Real.rpow_sub hP0,Real.rpow_one,hw]
      _ = P^(-2*c) := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; linarith
  have hsI : 0 < Real.sqrt I := Real.sqrt_pos.mpr hI0
  have hsI' : Real.sqrt I ≤ P^(-c) := by
    calc
      _ ≤ Real.sqrt (P^(-2*c)) := Real.sqrt_le_sqrt hI'
      _ = _ := by rw [sqrt_rpow_base hP0.le]; congr 1; ring
  have hθeq : θ=P^(α+b-1) := by
    calc
      θ = (p*θ)/p := by field_simp
      _ = P^b/P^(1-α) := by rw [hpθ,hp]
      _ = P^(b-(1-α)) := (Real.rpow_sub hP0 _ _).symm
      _ = _ := by congr 1; ring
  have hn := hselected.trans_le (min_le_left _ _)
  have hf := hselected.trans_le (min_le_right _ _)
  have hn' : P*selectionWeight P θ φ h < Real.sqrt I*Real.sqrt h*p^2*φ^2 := by
    apply (mul_lt_mul_iff_right₀ hsI).mp
    calc
      _ = P*Real.sqrt I*selectionWeight P θ φ h := by ring
      _ < _ := hn
      _ = (Real.sqrt I)^2*Real.sqrt h*p^2*φ^2 := by rw [Real.sq_sqrt hI0.le]
      _ = _ := by ring
  have hnb : P^(1-Δ) < P^(-c-H/2+2*(1-α)-2*y) := by
    calc
      _ = P*selectionWeight P θ φ h := by
        rw [hWI,Real.rpow_sub hP0,Real.rpow_one,Real.rpow_neg hP0.le,div_eq_mul_inv]
      _ < _ := hn'
      _ ≤ P^(-c)*Real.sqrt h*p^2*φ^2 := by gcongr
      _ = _ := by
        rw [hh,hp,hφ,sqrt_rpow_base hP0.le,nat_pow_rpow_base hP0.le,nat_pow_rpow_base hP0.le]
        norm_num only [Nat.cast_ofNat]
        simp only [← Real.rpow_add hP0]
        congr 1
        ring
  have hne := (Real.rpow_lt_rpow_left_iff hP).mp hnb
  have hf' : P*selectionWeight P θ φ h*(θ*h) < Real.sqrt (p*μ) := by
    have ht := (lt_div_iff₀ (mul_pos hθ0 hh0)).mp hf
    apply (mul_lt_mul_iff_right₀ hsI).mp
    convert ht using 1; ring
  have hfb : P*selectionWeight P θ φ h*(θ*h) = P^(α+b-H-Δ) := by
    rw [hWI,hθeq,hh]
    have ee : P*P^(-Δ)=P^(1-Δ) := by
      rw [Real.rpow_sub hP0,Real.rpow_one,Real.rpow_neg hP0.le,div_eq_mul_inv]
    rw [ee,← Real.rpow_add hP0,← Real.rpow_add hP0]
    congr 1
    ring
  exact ⟨by linarith, hfb ▸ hf'⟩

def ImprovedWindow (P p w φ : ℝ) : Prop :=
  P^(7/10 : ℝ) ≤ p ∧ P^(7/10 : ℝ) ≤ w ∧
  p^(-49/100 : ℝ) ≤ φ ∧ φ ≤ p^(-16/100 : ℝ) ∧
  w^(-49/100 : ℝ) ≤ φ ∧ φ ≤ w^(-16/100 : ℝ)

def PureOccupationBounds (P C₀ C₁ M A p w φ h I μ : ℝ) : Prop :=
  μ ≤ max I h/p ∧
  (C₀/min p w < φ → μ ≤ (h/p)*max 1
    (max (I/stabilityLength P C₁ M A p w φ) (h/stabilityLength P C₁ M A p w φ))) ∧
  (ImprovedWindow P p w φ → μ ≤ (h/p)*φ^(-29/25 : ℝ)*
    max 1 (max (I/(min p w/P)^2) (h/(min p w/P)^2)))

lemma improvedWindow_of_powers {P p w φ α z y : ℝ} (hP : 1 < P)
    (hp : p=P^(1-α)) (hw : w=P^z) (hφ : φ=P^(-y))
    (hp' : (7/10 : ℝ) ≤ 1-α) (hw' : (7/10 : ℝ) ≤ z)
    (hyl : (16/100 : ℝ)*max z (1-α) ≤ y)
    (hyu : y ≤ (49/100 : ℝ)*min z (1-α)) : ImprovedWindow P p w φ := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hzlo := le_max_left z (1-α)
  have hplo := le_max_right z (1-α)
  have hzup := min_le_left z (1-α)
  have hpup := min_le_right z (1-α)
  unfold ImprovedWindow
  rw [hp,hw,hφ]
  refine ⟨(Real.rpow_le_rpow_left_iff hP).mpr hp',
    (Real.rpow_le_rpow_left_iff hP).mpr hw',?_,?_,?_,?_⟩ <;>
    rw [← Real.rpow_mul hP0.le] <;>
    apply (Real.rpow_le_rpow_left_iff hP).mpr <;> linarith

lemma pureOccupationBounds_power_table
    {P C₀ C₁ M A p w φ h I μ α z c y H : ℝ} (hP : 1 < P)
    (hp : p=P^(1-α)) (hw : w=P^z) (hφ : φ=P^(-y)) (hh : h=P^(-H))
    (hzc : z+c=1) (hμ : 0 ≤ μ) (hI : I ≤ (w/P)^2)
    (hbounds : PureOccupationBounds P C₀ C₁ M A p w φ h I μ) :
    (Real.sqrt (p*μ))^2 ≤ P^(-min (2*c) H) ∧
    (C₀ < P^(min z (1-α)-y) →
      (Real.sqrt (p*μ))^2 ≤ P^(-H)*max 1
        (max (P^(-2*c)*(stabilityRate P C₁ M A p w φ)^2)
          (P^(-H)*(stabilityRate P C₁ M A p w φ)^2))) ∧
    ((7/10 : ℝ) ≤ z → (7/10 : ℝ) ≤ 1-α →
      (16/100 : ℝ)*max z (1-α) ≤ y → y ≤ (49/100 : ℝ)*min z (1-α) →
      (Real.sqrt (p*μ))^2 ≤ P^(-H+(29/25 : ℝ)*y)*
        max 1 (max (P^(-2*c)*P^(2*max α c)) (P^(-H)*P^(2*max α c)))) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hp0 : 0 < p := hp ▸ Real.rpow_pos_of_pos hP0 _
  have hw0 : 0 < w := hw ▸ Real.rpow_pos_of_pos hP0 _
  have hm0 : 0 < min p w := lt_min hp0 hw0
  have hh0 : 0 < h := hh ▸ Real.rpow_pos_of_pos hP0 _
  have hI' : I ≤ P^(-2*c) := by
    calc
      I ≤ (w/P)^2 := hI
      _ = (P^(z-1))^2 := by rw [Real.rpow_sub hP0,Real.rpow_one,hw]
      _ = P^(-2*c) := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; linarith
  have hm : min p w = P^(1-max α c) := by
    rw [hp,hw,rpow_min_exponent hP]
    congr 1
    rcases le_total α c with hh | hh
    · rw [max_eq_right hh,min_eq_right (by linarith)]; linarith
    · rw [max_eq_left hh,min_eq_left (by linarith)]
  have hIm : (min p w/P)^2 = P^(-2*max α c) := by
    calc
      _ = (P^((1-max α c)-1))^2 := by rw [Real.rpow_sub hP0,Real.rpow_one,hm]
      _ = _ := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; ring
  have hmp : min p w*φ = P^(min z (1-α)-y) := by
    rw [hp,hw,hφ,rpow_min_exponent hP,← Real.rpow_add hP0,min_comm]
    congr 1
  rw [Real.sq_sqrt (mul_nonneg hp0.le hμ)]
  rcases hbounds with ⟨he,ha,hi⟩
  refine ⟨?_,?_,?_⟩
  · calc
      p*μ ≤ p*(max I h/p) := mul_le_mul_of_nonneg_left he hp0.le
      _ = max I h := by field_simp
      _ ≤ P^(-min (2*c) H) := by
        apply max_le
        · exact hI'.trans ((Real.rpow_le_rpow_left_iff hP).mpr (by have := min_le_left (2*c) H; linarith))
        · rw [hh]; exact (Real.rpow_le_rpow_left_iff hP).mpr (by have := min_le_right (2*c) H; linarith)
  · intro hC
    have hC' : C₀/min p w < φ := (div_lt_iff₀ hm0).mpr (by rw [mul_comm,hmp]; exact hC)
    calc
      p*μ ≤ p*((h/p)*max 1 (max (I/stabilityLength P C₁ M A p w φ)
        (h/stabilityLength P C₁ M A p w φ))) := mul_le_mul_of_nonneg_left (ha hC') hp0.le
      _ = h*max 1 (max (I*(stabilityRate P C₁ M A p w φ)^2)
          (h*(stabilityRate P C₁ M A p w φ)^2)) := by
        rw [div_stabilityLength,div_stabilityLength]
        field_simp
      _ ≤ _ := by rw [hh]; gcongr
  · intro hz' hp' hyl hyu
    have hi' := hi (improvedWindow_of_powers hP hp hw hφ hp' hz' hyl hyu)
    calc
      p*μ ≤ p*((h/p)*φ^(-29/25 : ℝ)*max 1 (max (I/(min p w/P)^2) (h/(min p w/P)^2))) :=
        mul_le_mul_of_nonneg_left hi' hp0.le
      _ = (h*φ^(-29/25 : ℝ))*max 1 (max (I*P^(2*max α c)) (h*P^(2*max α c))) := by
        rw [hIm,show -2*max α c = -(2*max α c) by ring,Real.rpow_neg hP0.le]
        simp only [div_inv_eq_mul]
        field_simp
      _ ≤ (h*φ^(-29/25 : ℝ))*max 1 (max (P^(-2*c)*P^(2*max α c)) (h*P^(2*max α c))) := by
        gcongr
        exact mul_nonneg hh0.le (Real.rpow_nonneg (hφ ▸ Real.rpow_nonneg hP0.le _) _)
      _ = _ := by
        rw [hh,hφ,← Real.rpow_mul hP0.le,← Real.rpow_add hP0]
        congr 2
        ring

lemma selected_receiverCoefficient_of_powers
    {P C₀ C₁ M A p w θ φ h I μ α z c b y H : ℝ}
    (hP : 1 < P) (hC₁ : 0 ≤ C₁) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hp : p=P^(1-α)) (hw : w=P^z) (hpθ : p*θ=P^b)
    (hφ : φ=P^(-y)) (hh : h=P^(-H)) (hφ₁ : φ ≤ 1)
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z+c=1) (hμ : 0 ≤ μ) (hI0 : 0 < I) (hI : I ≤ (w/P)^2)
    (hC₀ : C₀ ≤ P^(3/10 : ℝ))
    (hconst : C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ))
    (hbounds : PureOccupationBounds P C₀ C₁ M A p w φ h I μ)
    (hselected : P*Real.sqrt I*selectionWeight P θ φ h <
      min (I*Real.sqrt h*p^2*φ^2) (Real.sqrt I*Real.sqrt (p*μ)/(θ*h))) :
    receiverCoefficient w p θ φ h ≤ w^(-1/2 : ℝ)*selectionWeight P θ φ h := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  let Δ := (α+b+y+H)/100000
  obtain ⟨hn,hf⟩ := selected_near_far_powers hP hp hw hpθ hφ hh hzc (show Δ=_ from rfl)
    hI0 hI hselected
  obtain ⟨he,ha,hi⟩ := pureOccupationBounds_power_table hP hp hw hφ hh hzc hμ hI hbounds
  have hr0 : 0 ≤ stabilityRate P C₁ M A p w φ := by
    have hp0 : 0 < p := hp ▸ Real.rpow_pos_of_pos hP0 _
    have hw0 : 0 < w := hw ▸ Real.rpow_pos_of_pos hP0 _
    have hm0 : 0 < min p w := lt_min hp0 hw0
    have hφ0 : 0 < φ := hφ ▸ Real.rpow_pos_of_pos hP0 _
    unfold stabilityRate
    positivity
  have hr : (66/100 : ℝ) < z → (stabilityRate P C₁ M A p w φ)^2 ≤
      P^(2*max α c+2*y+2*z/1000) := by
    intro hz'
    have hrate := stabilityRate_power_bound hP hC₁ hA hp hw hφ hφ₁ hzc hz' hconst
    calc
      _ ≤ (P^(max α c+y+z/1000))^2 := (sq_le_sq₀ hr0 (Real.rpow_nonneg hP0.le _)).mpr hrate
      _ = _ := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; ring
  have hb := selected_coefficient_power_table hP hα hz hc hy hH hzc (show Δ=_ from rfl)
    hn (Real.sqrt_nonneg _) hf he hC₀ hr ha hi
  rw [receiverCoefficient_power hP0 hw hpθ hφ hh,
    selectionWeight_power hP0 hp hpθ hφ hh,hw,← Real.rpow_mul hP0.le,← Real.rpow_add hP0]
  convert hb using 1
  dsimp [Δ]
  congr 1
  ring

lemma selected_receiverCoefficient
    {P C₀ C₁ M A p w θ φ h I μ : ℝ}
    (hP : 1 < P) (hC₁ : 0 ≤ C₁) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hp0 : 0 < p) (hpP : p ≤ P) (hw1 : 1 ≤ w) (hwP : w ≤ P)
    (hθ : 0 < θ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hμ : 0 ≤ μ) (hI0 : 0 < I) (hI : I ≤ (w/P)^2)
    (hC₀ : C₀ ≤ P^(3/10 : ℝ))
    (hconst : C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ))
    (hbounds : PureOccupationBounds P C₀ C₁ M A p w φ h I μ)
    (hselected : P*Real.sqrt I*selectionWeight P θ φ h <
      min (I*Real.sqrt h*p^2*φ^2) (Real.sqrt I*Real.sqrt (p*μ)/(θ*h))) :
    receiverCoefficient w p θ φ h ≤ w^(-1/2 : ℝ)*selectionWeight P θ φ h := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hp' : p=P^(1-(1-Real.logb P p)) := by
    rw [sub_sub_cancel,Real.rpow_logb hP0 hP.ne' hp0]
  have hw' : w=P^(Real.logb P w) := (Real.rpow_logb hP0 hP.ne' (zero_lt_one.trans_le hw1)).symm
  have hpθ' : p*θ=P^(Real.logb P (p*θ)) := (Real.rpow_logb hP0 hP.ne' (mul_pos hp0 hθ)).symm
  have hφ' : φ=P^(-(-Real.logb P φ)) := by rw [neg_neg,Real.rpow_logb hP0 hP.ne' hφ]
  have hh' : h=P^(-(-Real.logb P h)) := by rw [neg_neg,Real.rpow_logb hP0 hP.ne' hh]
  have hα : 0 ≤ 1-Real.logb P p := sub_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP hp0).mpr (by simpa using hpP))
  have hc : 0 ≤ 1-Real.logb P w := sub_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP (zero_lt_one.trans_le hw1)).mpr (by simpa using hwP))
  have hy : 0 ≤ -Real.logb P φ := neg_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP hφ).mpr (by simpa using hφ1))
  have hH : 0 ≤ -Real.logb P h := neg_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP hh).mpr (by simpa using hh1))
  exact selected_receiverCoefficient_of_powers hP hC₁ hM hA hp' hw' hpθ' hφ' hh' hφ1
    hα (Real.logb_nonneg hP hw1) hc hy hH (by ring) hμ hI0 hI hC₀ hconst hbounds hselected

def pureOccupationEnvelope (P C₀ C₁ M A p w φ h I : ℝ) : ℝ := by
  classical
  exact let e := max I h/p
  let a := (h/p)*max 1
    (max (I/stabilityLength P C₁ M A p w φ) (h/stabilityLength P C₁ M A p w φ))
  let b := (h/p)*φ^(-29/25 : ℝ)*
    max 1 (max (I/(min p w/P)^2) (h/(min p w/P)^2))
  min (if C₀/min p w < φ then min e a else e)
    (if ImprovedWindow P p w φ then min e b else e)

lemma pureOccupationEnvelope_bounds (P C₀ C₁ M A p w φ h I : ℝ) :
    PureOccupationBounds P C₀ C₁ M A p w φ h I
      (pureOccupationEnvelope P C₀ C₁ M A p w φ h I) := by
  classical
  unfold PureOccupationBounds pureOccupationEnvelope
  dsimp only
  refine ⟨?_,?_,?_⟩
  · exact (min_le_left _ _).trans (by split_ifs <;> simp only [min_le_left,le_refl])
  · intro ha
    rw [ite_eq_left ha]
    exact (min_le_left _ _).trans (min_le_right _ _)
  · intro hb
    rw [ite_eq_left hb]
    exact (min_le_right _ _).trans (min_le_right _ _)

lemma pureOccupationEnvelope_nonneg
    {P C₀ C₁ M A p w φ h I : ℝ} (hp : 0 ≤ p) (hφ : 0 ≤ φ)
    (hh : 0 ≤ h) (hI : 0 ≤ I) :
    0 ≤ pureOccupationEnvelope P C₀ C₁ M A p w φ h I := by
  classical
  unfold pureOccupationEnvelope
  dsimp only
  split_ifs <;> positivity

theorem receiverCoefficient_on_selected_bins
    (C₀ C₁ M A : ℝ) (hC₁ : 0 ≤ C₁) (hM : 0 ≤ M) (hA : 0 ≤ A) :
    ∀ᶠ P in atTop, ∀ p w θ φ h I : ℝ,
      0 < p → p ≤ P → 1 ≤ w → w ≤ P → 0 < θ →
      0 < φ → φ ≤ 1 → 0 < h → h ≤ 1 → 0 < I → I ≤ (w/P)^2 →
      P*Real.sqrt I*selectionWeight P θ φ h <
        min (I*Real.sqrt h*p^2*φ^2)
          (Real.sqrt I*Real.sqrt (p*pureOccupationEnvelope P C₀ C₁ M A p w φ h I)/(θ*h)) →
      receiverCoefficient w p θ φ h ≤ w^(-1/2 : ℝ)*selectionWeight P θ φ h := by
  filter_upwards [eventually_selection_constants C₀ C₁ M A hC₁ hA] with P hP
  intro p w θ φ h I hp hpP hw hwP hθ hφ hφ1 hh hh1 hI0 hI hselected
  exact selected_receiverCoefficient hP.1 hC₁ hM hA hp hpP hw hwP hθ hφ hφ1 hh hh1
    (pureOccupationEnvelope_nonneg hp.le hφ.le hh.le hI0.le) hI0 hI hP.2.1 hP.2.2
    (pureOccupationEnvelope_bounds ..) hselected

end RVM

end

end OAI
