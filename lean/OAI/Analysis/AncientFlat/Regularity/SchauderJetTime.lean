import OAI.Analysis.AncientFlat.Regularity.SchauderJet
import OAI.Analysis.AncientFlat.Regularity.SchauderCancel

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff BoundedContinuousFunction SchwartzMap
namespace ParabolicSchauder
open SourceFrozenRows SchwartzTimeScale
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma jet_parameter (K : SchwartzMap V ℂ) (b t : ℝ) (hb : 0<b) (ht : 0<t)
    (f : V →ᵇ ℂ) (j : ℕ) :
    jet K t f j = row K (fun _ => t/b) (b^(1/4 : ℝ)) f j := by
  have he : b^(1/4 : ℝ)*(t/b)^(1/4 : ℝ)=t^(1/4 : ℝ) := by
    rw [← Real.mul_rpow hb.le (div_pos ht hb).le,mul_div_cancel₀ _ hb.ne']
  unfold jet row
  simp only [Real.one_rpow,mul_one,he]
lemma exists_jet_time_increment (K : SchwartzMap V ℂ) (j : ℕ) (hj : 0<j)
    (α : ℝ) (hα : 0≤α) (hα1 : α≤1) :
    ∃ D : ℝ, 0≤D ∧ ∀ (f : V →ᵇ ℂ) (H : ℝ), 0≤H →
      (∀ x y, ‖f x-f y‖≤H*‖x-y‖^α) → ∀ b e : ℝ, 0<b → 0≤e → e≤b → ∀ x,
      ‖jet K (b+e) f j x-jet K b f j x‖≤D*H*e*b^((α-j-4)/4) := by
  let K' := SchwartzDerivatives.iterated K j
  have hz : ∫ z,K' z=0 := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    simp only [K',SchwartzDerivatives.iterated_apply]
    exact SchwartzDerivatives.integral_iterated K n
  obtain ⟨D,hD,hd⟩ := exists_normalized_time_diff K' (Module.finrank ℝ V+j) hz α hα hα1
  refine ⟨D,hD,fun f H hH hf b e hb he heb x => ?_⟩
  have hc : (b+e)/b ∈ Icc (1:ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hb).2; linarith
    · apply (div_le_iff₀ hb).2; linarith
  have h1 : (1:ℝ)∈Icc (1:ℝ) 2 := ⟨le_rfl,by norm_num⟩
  have hb' : 0<b+e := by linarith
  have hcpos : 0<(b+e)/b := div_pos hb' hb
  have hnorm : ‖(b+e)/b-1‖=e/b := by
    rw [Real.norm_eq_abs,show (b+e)/b-1=e/b by field_simp; ring,abs_of_nonneg (div_nonneg he hb.le)]
  have hp : ((b^(1/4 : ℝ))⁻¹)^j*(b^(1/4 : ℝ))^α/b=b^((α-j-4)/4) := by
    rw [div_eq_mul_inv,← Real.rpow_natCast,← Real.rpow_neg hb.le,
      ← Real.rpow_mul hb.le,← Real.rpow_mul hb.le,← Real.rpow_add hb,
      ← Real.rpow_neg_one,← Real.rpow_add hb]
    congr 1
    ring
  rw [jet_parameter K b (b+e) hb hb' f j]
  change ‖row K (fun _ => (b+e)/b) (b^(1/4 : ℝ)) f j x-
    row K (fun _ => 1) (b^(1/4 : ℝ)) f j x‖≤_
  rw [row_normalized K _ (fun _ => hcpos) _ (Real.rpow_pos_of_pos hb _) f j x,
    row_normalized K _ (fun _ => zero_lt_one) _ (Real.rpow_pos_of_pos hb _) f j x]
  erw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hh := hd ((b+e)/b) hc 1 h1 f H hH hf (b^(1/4 : ℝ)) (Real.rpow_pos_of_pos hb _) x
  rw [hnorm] at hh
  calc
    _ ≤ ((b^(1/4 : ℝ))⁻¹)^j*(D*H*(b^(1/4 : ℝ))^α*(e/b)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = D*H*e*(((b^(1/4 : ℝ))⁻¹)^j*(b^(1/4 : ℝ))^α/b) := by ring
    _ = _ := by rw [hp]
end ParabolicSchauder

end

end OAI
