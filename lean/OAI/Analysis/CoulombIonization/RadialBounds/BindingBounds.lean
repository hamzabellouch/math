import Mathlib
import OAI.Analysis.CoulombIonization.Variational.BindingWeightContinuous

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

namespace CoulombAtom

lemma capped_radius_sum {R a b d : ℝ} (hR : 0 < R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d) (ht : d ≤ a+b) :
    R*d/(R+d) ≤ R*a/(R+a)+R*b/(R+b) := by
  calc
    _ ≤ R*(a+b)/(R+a+b) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr ht)]
    _ = R*a/(R+a+b)+R*b/(R+a+b) := by ring
    _ ≤ _ := add_le_add
      (div_le_div_of_nonneg_left (mul_nonneg hR.le ha) (by positivity) (by linarith))
      (div_le_div_of_nonneg_left (mul_nonneg hR.le hb) (by positivity) (by linarith))

lemma bindingWeight_pair_lower {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (x y : Space) (hxy : x ≠ y) :
    1 ≤ (bindingWeight R ε x+bindingWeight R ε y)/‖x-y‖+
      (bindingWeight R ε x+bindingWeight R ε y)/R := by
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h := capped_radius_sum hR (regularizedRadius_pos hε x).le
    (regularizedRadius_pos hε y).le hd
    ((norm_sub_le x y).trans (add_le_add (norm_le_regularizedRadius ε x)
      (norm_le_regularizedRadius ε y)))
  change R*‖x-y‖/(R+‖x-y‖) ≤ bindingWeight R ε x+bindingWeight R ε y at h
  have hh := (div_le_iff₀ (by positivity : 0 < R+‖x-y‖)).mp h
  rw [div_add_div _ _ hd.ne' hR.ne']
  exact (le_div_iff₀ (mul_pos hd hR)).mpr (by nlinarith)

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  bindingTotalMultiplier

lemma bindingWeight_pair_integral {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i j : Fin N) (hij : i ≠ j) {f : Configuration N → ℂ} (hf : MemLp f 2)
    (hp : Integrable (fun x => ‖f x‖^2/‖x i-x j‖)) :
    (∫ x, ‖f x‖^2) ≤
      ((∫ x, bindingWeight R ε (x i)*(‖f x‖^2/‖x i-x j‖))+
        R⁻¹*(∫ x, bindingWeight R ε (x i)*‖f x‖^2))+
      ((∫ x, bindingWeight R ε (x j)*(‖f x‖^2/‖x j-x i‖))+
        R⁻¹*(∫ x, bindingWeight R ε (x j)*‖f x‖^2)) := by
  have hpr : Integrable (fun x => ‖f x‖^2/‖x j-x i‖) := by
    simpa only [norm_sub_rev (a := _)] using hp
  have hi := bindingWeight_integrable hR hε i hp
  have hj := bindingWeight_integrable hR hε j hpr
  have hmi := bindingWeight_integrable hR hε i hf.norm.integrable_sq
  have hmj := bindingWeight_integrable hR hε j hf.norm.integrable_sq
  rw [← integral_const_mul,← integral_const_mul,← integral_add hi (hmi.const_mul R⁻¹),
    ← integral_add hj (hmj.const_mul R⁻¹)]
  rw [← integral_add
    (f := fun x => bindingWeight R ε (x i)*(‖f x‖^2/‖x i-x j‖)+R⁻¹*(bindingWeight R ε (x i)*‖f x‖^2))
    (g := fun x => bindingWeight R ε (x j)*(‖f x‖^2/‖x j-x i‖)+R⁻¹*(bindingWeight R ε (x j)*‖f x‖^2))
    (hi.add (hmi.const_mul R⁻¹)) (hj.add (hmj.const_mul R⁻¹))]
  apply integral_mono_ae hf.norm.integrable_sq
    ((hi.add (hmi.const_mul R⁻¹)).add (hj.add (hmj.const_mul R⁻¹)))
  filter_upwards [configuration_pair_ne i j hij] with x hx
  have hh := mul_le_mul_of_nonneg_right (bindingWeight_pair_lower hR hε (x i) (x j) hx)
    (sq_nonneg ‖f x‖)
  dsimp only [Pi.add_apply]
  rw [norm_sub_rev (x j)]
  convert hh using 1 <;> ring

lemma bindingWeight_nuclear_integral {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i : Fin N) {f : Configuration N → ℂ} (hf : MemLp f 2)
    (hn : Integrable (fun x => ‖f x‖^2/‖x i‖)) :
    (∫ x, bindingWeight R ε (x i)*(‖f x‖^2/‖x i‖)) ≤
      (∫ x, ‖f x‖^2)+ε*(∫ x, ‖f x‖^2/‖x i‖) := by
  rw [← integral_const_mul,← integral_add hf.norm.integrable_sq (hn.const_mul ε)]
  apply integral_mono (bindingWeight_integrable hR hε i hn)
    (hf.norm.integrable_sq.add (hn.const_mul ε))
  intro x
  dsimp only [Pi.add_apply]
  have hb := (bindingWeight_le_radius hR hε (x i)).trans (regularizedRadius_le_add hε.le (x i))
  by_cases hx : ‖x i‖=0
  · simp only [hx,div_zero,mul_zero,add_zero]
    positivity
  · have hx0 : 0 < ‖x i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have hm := mul_le_mul_of_nonneg_right hb (div_nonneg (sq_nonneg ‖f x‖) hx0.le)
    have hcancel : ‖x i‖*(‖f x‖^2/‖x i‖)=‖f x‖^2 := mul_div_cancel₀ _ hx
    nlinarith

end CoulombAtom

end

end OAI
