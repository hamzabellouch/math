import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianEstimates
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityWeight

namespace OAI

/-! # An integrable logarithmic majorant for positive regularized densities -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem abs_log_le_power_add_lower {l u ε : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hε : 0 < ε) : |Real.log u| ≤ u^ε/ε+|Real.log l| := by
  have hu : 0 < u := hl.trans_le hlu
  have hlow := Real.log_le_log hl hlu
  have hup := Real.log_le_rpow_div hu.le hε
  have hp : 0 ≤ u^ε/ε := div_nonneg (Real.rpow_nonneg hu.le ε) hε.le
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log l)],by
    linarith [abs_nonneg (Real.log l)]⟩

def logarithmicMajorant (q B p δ : ℝ) (v : Velocity) : ℝ :=
  (B^(p-1)/(p-1))*H q v^p+
    (|Real.log δ|+|-(3/2:ℝ)*Real.log (2*Real.pi)|+(5/2:ℝ)*‖v‖^2)*H q v

theorem logarithmicMajorant_integrable {q B p δ : ℝ} (hq : q < 2)
    (hp : Integrable (fun v : Velocity => H q v^p)) :
    Integrable (logarithmicMajorant q B p δ) := by
  have h := (hp.const_mul (B^(p-1)/(p-1))).add
    (((integrable_H hq).const_mul (|Real.log δ|+|-(3/2:ℝ)*Real.log (2*Real.pi)|)).add
      ((integrable_even_moment_H hq 1).const_mul (5/2:ℝ)))
  convert h using 1
  funext v
  simp only [logarithmicMajorant,Nat.reduceMul,Pi.add_apply]
  ring

theorem logarithm_weight_bound {q B p δ u : ℝ} (hB : 0 ≤ B) (hp : 1 < p)
    (hδ : 0 < δ) (v : Velocity)
    (hl : δ*Real.exp (-2*‖v‖^2) ≤ u) (hu : u ≤ B*H q v) :
    |Real.log (u/maxwellian v)| *H q v ≤ logarithmicMajorant q B p δ v := by
  have hp' : 0 < p-1 := sub_pos.mpr hp
  have hl' : 0 < δ*Real.exp (-2*‖v‖^2) := mul_pos hδ (Real.exp_pos _)
  have hu' : 0 < u := hl'.trans_le hl
  have hlb := abs_log_le_power_add_lower hl' hl hp'
  have hlogl : Real.log (δ*Real.exp (-2*‖v‖^2)) = Real.log δ-2*‖v‖^2 := by
    rw [Real.log_mul hδ.ne' (Real.exp_ne_zero _),Real.log_exp]
    ring
  rw [hlogl] at hlb
  have hlabs : |Real.log δ-2*‖v‖^2| ≤ |Real.log δ|+2*‖v‖^2 := by
    exact (abs_sub (Real.log δ) (2*‖v‖^2)).trans_eq
      (congrArg (fun x : ℝ => |Real.log δ|+x)
        (abs_of_nonneg (show 0 ≤ 2*‖v‖^2 by positivity)))
  have hmabs : |Real.log (maxwellian v)| ≤
      |-(3/2:ℝ)*Real.log (2*Real.pi)|+‖v‖^2/2 := by
    rw [log_maxwellian]
    exact (abs_sub (-(3/2:ℝ)*Real.log (2*Real.pi)) (‖v‖^2/2)).trans_eq
      (congrArg (fun x : ℝ => |-(3/2:ℝ)*Real.log (2*Real.pi)|+x)
        (abs_of_nonneg (show 0 ≤ ‖v‖^2/2 by positivity)))
  have hpow : u^(p-1) ≤ B^(p-1)*H q v^(p-1) := by
    rw [← Real.mul_rpow hB (H_nonneg q v)]
    exact Real.rpow_le_rpow hu'.le hu hp'.le
  have hlog : |Real.log (u/maxwellian v)| ≤
      B^(p-1)*H q v^(p-1)/(p-1)+
        (|Real.log δ|+|-(3/2:ℝ)*Real.log (2*Real.pi)|+(5/2:ℝ)*‖v‖^2) := by
    rw [Real.log_div hu'.ne' (maxwellian_pos v).ne']
    have ha := abs_sub (Real.log u) (Real.log (maxwellian v))
    have hd := div_le_div_of_nonneg_right hpow hp'.le
    linarith
  have hpower : H q v^(p-1)*H q v = H q v^p := by
    rw [← Real.rpow_add_one (H_pos q v).ne']
    congr 1
    ring
  calc
    _ ≤ (B^(p-1)*H q v^(p-1)/(p-1)+
        (|Real.log δ|+|-(3/2:ℝ)*Real.log (2*Real.pi)|+(5/2:ℝ)*‖v‖^2))*H q v :=
      mul_le_mul_of_nonneg_right hlog (H_nonneg q v)
    _ = logarithmicMajorant q B p δ v := by
      unfold logarithmicMajorant
      rw [add_mul]
      congr 1
      calc
        _ = (B^(p-1)/(p-1))*(H q v^(p-1)*H q v) := by ring
        _ = _ := by rw [hpower]

theorem integrable_logarithm_weight {q B δ : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hB : 0 ≤ B) (hδ : 0 < δ) {u : Velocity → ℝ} (hum : Measurable u)
    (hl : ∀ v, δ*Real.exp (-2*‖v‖^2) ≤ u v) (hu : ∀ v, u v ≤ B*H q v) :
    Integrable (fun v => Real.log (u v/maxwellian v)*H q v) := by
  obtain ⟨p,hp,hpi⟩ := exists_integrable_rpow_H hq₁ hq₂
  have hm : Measurable maxwellian := by unfold maxwellian; fun_prop
  have hH : Measurable (H q) := by unfold H singularity transverse; fun_prop
  apply (logarithmicMajorant_integrable (B := B) (δ := δ) hq₂ hpi).mono'
    (((hum.div hm).log).mul hH).aestronglyMeasurable
  filter_upwards [] with v
  simp only [Pi.mul_apply,Pi.div_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (H_nonneg q v)]
  exact logarithm_weight_bound hB hp hδ v (hl v) (hu v)

end BoltzmannNonuniqueness

end

end OAI
