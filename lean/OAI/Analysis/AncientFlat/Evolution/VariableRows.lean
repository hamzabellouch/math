import OAI.Analysis.AncientFlat.Evolution.VariableTimeCancellation
import OAI.Analysis.AncientFlat.Regularity.SchauderJet

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff BoundedContinuousFunction SchwartzMap
namespace VariableSchauder
open SourceFrozenRows SourceFrozenCancellation SchwartzTimeScale
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def jet (K : SchwartzMap V ℂ) (A : V → ℝ) (t : ℝ) (f : V →ᵇ ℂ) (j : ℕ) :=
  row K A (t^(1/4 : ℝ)) f j
lemma quarter_power {t γ : ℝ} (ht : 0<t) (ht1 : t≤1) (hγ : γ≤1) :
    t^(1/4 : ℝ)≤(t^(1/4 : ℝ))^γ := by
  have hr : 0<t^(1/4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hr1 : t^(1/4 : ℝ)≤1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr hr1 hγ
lemma radius_power {t : ℝ} (ht : 0<t) (γ : ℝ) (j : ℕ) :
    ((t^(1/4 : ℝ))⁻¹)^j*(t^(1/4 : ℝ))^γ=t^((γ-j)/4) := by
  rw [←Real.rpow_natCast,←Real.rpow_neg ht.le,←Real.rpow_mul ht.le,
    ←Real.rpow_mul ht.le,←Real.rpow_add ht]
  congr 1; ring
lemma bound_combine {C D F H M L r : ℝ} (hC : 0≤C) (hD : 0≤D) (hF : 0≤F)
    (hH : 0≤H) (hM : 0≤M) (hL : 0≤L) (hFM : F≤M) {γ : ℝ}
    (hr : 0≤r) (hrr : r≤r^γ) :
    H*r^γ*C+F*L*r*D≤(C+D*L)*(H+M)*r^γ := by
  calc
    _ ≤ H*r^γ*C+F*L*r^γ*D := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrr (mul_nonneg hF hL)) hD)
    _ ≤ H*r^γ*C+M*L*r^γ*D := by gcongr
    _ ≤ _ := by
      have h1 := mul_nonneg (mul_nonneg hC hM) (Real.rpow_nonneg hr γ)
      have h2 := mul_nonneg (mul_nonneg (mul_nonneg hD hL) hH) (Real.rpow_nonneg hr γ)
      nlinarith
lemma exists_jet_bound (K : SchwartzMap V ℂ) (j : ℕ) (hj : 0<j)
    (α β γ L : ℝ) (hα : 0<α) (hγ : 0≤γ) (hγ1 : γ≤1) (hL : 0≤L) :
    ∃ C : ℝ, 0≤C ∧ ∀ (A : V → ℝ), Continuous A → (∀ y, A y∈Icc α β) →
      (∀ x y, ‖A x-A y‖≤L*‖x-y‖) → ∀ (f : V →ᵇ ℂ) (H M : ℝ), 0≤H → 0≤M → ‖f‖≤M →
      (∀ x y, ‖f x-f y‖≤H*‖x-y‖^γ) → ∀ t : ℝ, 0<t → t≤1 → ∀ x,
      ‖jet K A t f j x‖≤C*(H+M)*t^((γ-j)/4) := by
  obtain ⟨C,D,hC,hD,hb⟩ := exists_row_holder_bound K j hj α β hα γ hγ hγ1
  refine ⟨C+D*L,by positivity,fun A hA hAr hAL f H M hH hM hfn hf t ht ht1 x => ?_⟩
  have hb' := hb A hA hAr L hL hAL f H hH hf (t^(1/4 : ℝ)) (by positivity) x
  calc
    _ ≤ ((t^(1/4 : ℝ))⁻¹)^j*(H*(t^(1/4 : ℝ))^γ*C+‖f‖*L*(t^(1/4 : ℝ))*D) := hb'
    _ ≤ ((t^(1/4 : ℝ))⁻¹)^j*((C+D*L)*(H+M)*(t^(1/4 : ℝ))^γ) :=
      mul_le_mul_of_nonneg_left (bound_combine hC hD (norm_nonneg f) hH hM hL hfn
        (Real.rpow_nonneg ht.le _) (quarter_power ht ht1 hγ1)) (by positivity)
    _ = (C+D*L)*(H+M)*(((t^(1/4 : ℝ))⁻¹)^j*(t^(1/4 : ℝ))^γ) := by ring
    _ = _ := by rw [radius_power ht]
lemma exists_jet_lipschitz (K : SchwartzMap V ℂ) (j : ℕ)
    (α β γ L : ℝ) (hα : 0<α) (hγ : 0≤γ) (hγ1 : γ≤1) (hL : 0≤L) :
    ∃ C : ℝ, 0≤C ∧ ∀ (A : V → ℝ), Continuous A → (∀ y, A y∈Icc α β) →
      (∀ x y, ‖A x-A y‖≤L*‖x-y‖) → ∀ (f : V →ᵇ ℂ) (H M : ℝ), 0≤H → 0≤M → ‖f‖≤M →
      (∀ x y, ‖f x-f y‖≤H*‖x-y‖^γ) → ∀ t : ℝ, 0<t → t≤1 → ∀ x y,
      ‖jet K A t f j x-jet K A t f j y‖≤C*(H+M)*t^((γ-(j+1))/4)*‖x-y‖ := by
  obtain ⟨C,hC,hb⟩ := exists_jet_bound K (j+1) (Nat.zero_lt_succ _) α β γ L hα hγ hγ1 hL
  refine ⟨C,hC,fun A hA hAr hAL f H M hH hM hfn hf t ht ht1 x y => ?_⟩
  apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (s := (univ : Set V)) (fun z _ => (hasFDerivAt_row K A hA α β hα hAr _
      (Real.rpow_pos_of_pos ht _) f j z).hasFDerivWithinAt) (fun z _ => ?_)
    convex_univ (mem_univ y) (mem_univ x)
  rw [LinearIsometryEquiv.norm_map]
  simpa only [jet,Nat.cast_add,Nat.cast_one] using hb A hA hAr hAL f H M hH hM hfn hf t ht ht1 z
lemma jet_parameter (K : SchwartzMap V ℂ) (A : V → ℝ) (hAp : ∀ x, 0<A x)
    (b t : ℝ) (hb : 0<b) (ht : 0<t) (f : V →ᵇ ℂ) (j : ℕ) :
    jet K A t f j=row K (fun y => (t/b)*A y) (b^(1/4 : ℝ)) f j := by
  unfold jet row
  congr 1
  funext y
  have he : b^(1/4 : ℝ)*(t/b)^(1/4 : ℝ)=t^(1/4 : ℝ) := by
    rw [←Real.mul_rpow hb.le (div_pos ht hb).le,mul_div_cancel₀ _ hb.ne']
  rw [Real.mul_rpow (div_pos ht hb).le (hAp y).le,←mul_assoc,he]
lemma exists_jet_time_increment (K : SchwartzMap V ℂ) (j : ℕ) (hj : 0<j)
    (α β γ L : ℝ) (hα : 0<α) (hαβ : α≤β) (hγ : 0≤γ) (hγ1 : γ≤1) (hL : 0≤L) :
    ∃ C : ℝ, 0≤C ∧ ∀ (A : V → ℝ), Continuous A → (∀ y, A y∈Icc α β) →
      (∀ x y, ‖A x-A y‖≤L*‖x-y‖) → ∀ (f : V →ᵇ ℂ) (H M : ℝ), 0≤H → 0≤M → ‖f‖≤M →
      (∀ x y, ‖f x-f y‖≤H*‖x-y‖^γ) → ∀ b e : ℝ, 0<b → b≤1 → 0≤e → e≤b → ∀ x,
      ‖jet K A (b+e) f j x-jet K A b f j x‖≤C*(H+M)*e*b^((γ-j-4)/4) := by
  let K' := SchwartzDerivatives.iterated K j
  have hz : ∫ z,K' z=0 := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    simp only [K',SchwartzDerivatives.iterated_apply]
    exact SchwartzDerivatives.integral_iterated K n
  obtain ⟨C,D,hC,hD,hd⟩ := exists_normalized_variable_time_diff K' (Module.finrank ℝ V+j)
    hz α β γ hα hαβ hγ hγ1
  refine ⟨C+D*L,by positivity,fun A hA hAr hAL f H M hH hM hfn hf b e hb hb1 he heb x => ?_⟩
  have hc : (b+e)/b∈Icc (1:ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hb).2; linarith
    · apply (div_le_iff₀ hb).2; linarith
  have hdelta : (b+e)/b-1=e/b := by field_simp; ring
  have hAp : ∀ y, 0<A y := fun y => hα.trans_le (hAr y).1
  have hr : 0<b^(1/4 : ℝ) := Real.rpow_pos_of_pos hb _
  have ht : 0<b+e := by positivity
  rw [jet_parameter K A hAp b (b+e) hb ht f j]
  change ‖row K (fun y => ((b+e)/b)*A y) (b^(1/4 : ℝ)) f j x-row K A (b^(1/4 : ℝ)) f j x‖≤_
  rw [row_normalized K _ (fun y => mul_pos (div_pos ht hb) (hAp y)) _ hr f j x,
    row_normalized K A hAp _ hr f j x]
  erw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hh := hd ((b+e)/b) hc A hA hAr L hL hAL f H hH hf (b^(1/4 : ℝ)) hr x
  rw [hdelta] at hh
  have hcomb := bound_combine hC hD (norm_nonneg f) hH hM hL hfn hr.le (quarter_power hb hb1 hγ1)
  have hp : (((b^(1/4 : ℝ))⁻¹)^j*(b^(1/4 : ℝ))^γ)/b=b^((γ-j-4)/4) := by
    rw [radius_power hb,div_eq_mul_inv,←Real.rpow_neg_one,←Real.rpow_add hb]
    congr 1; ring
  calc
    _ ≤ ((b^(1/4 : ℝ))⁻¹)^j*((e/b)*(H*(b^(1/4 : ℝ))^γ*C+‖f‖*L*(b^(1/4 : ℝ))*D)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ ((b^(1/4 : ℝ))⁻¹)^j*((e/b)*((C+D*L)*(H+M)*(b^(1/4 : ℝ))^γ)) := by gcongr
    _ = (C+D*L)*(H+M)*e*((((b^(1/4 : ℝ))⁻¹)^j*(b^(1/4 : ℝ))^γ)/b) := by ring
    _ = _ := by rw [hp]
end VariableSchauder

end

end OAI
