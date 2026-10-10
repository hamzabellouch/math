import OAI.MathematicalPhysics.Boltzmann.Branching.HalfGaussianMoment
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialJointAnalytic
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialSecondMismatch
import OAI.MathematicalPhysics.Boltzmann.Collision.SheetIntervals
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityWeight
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricMesh

namespace OAI

section

/-! # Uniform polynomial velocity moments of the limiting background -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.AxialBackground

theorem axial_velocity_norm_le {σ α γ μ t z : ℝ} (hα : 0 ≤ α) (hσ : |σ| = 1) :
    ‖PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)‖ ≤ 1+α := by
  have hs := PlaneChart.norm_join_sq 0 (AxialFlow.velocity σ α γ μ t z)
  simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add] at hs
  have he : ‖PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)‖ =
      |AxialFlow.velocity σ α γ μ t z| := by
    nlinarith [norm_nonneg (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)),
      abs_nonneg (AxialFlow.velocity σ α γ μ t z),sq_abs (AxialFlow.velocity σ α γ μ t z)]
  rw [he]
  simpa only [hσ] using AxialAtomicSheet.velocity_abs_le (σ := σ) (γ := γ)
    (μ := μ) (t := t) (z := z) hα

theorem integral_cell_abs_le {K α γ μ t C : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (z : ℝ) (ψ : Velocity → ℝ)
    (hψ : ∀ v, ‖v‖ ≤ 1+α → |ψ v| ≤ C) :
    |∫ v, ψ v ∂cell K α γ μ t z| ≤
      2*((1/4)*((K*max 1 (α*γ)⁻¹)/(μ+t)))*C := by
  let B := (1/4)*((K*max 1 (α*γ)⁻¹)/(μ+t))
  have hB : 0 ≤ B := by
    apply mul_nonneg (by norm_num)
    exact div_nonneg (mul_nonneg hK (le_max_of_le_left zero_le_one)) (by linarith)
  have hs (σ : ℝ) (hσ : |σ| = 1) :
      |weight K α γ μ t σ z*ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))| ≤ B*C := by
    rw [abs_mul,abs_of_nonneg (weight_nonneg hK hα.le hγ.le hμ ht σ z)]
    exact mul_le_mul (weight_bound hK hα hγ hμ ht σ z)
      (hψ _ (axial_velocity_norm_le hα.le hσ)) (abs_nonneg _) hB
  rw [integral_cell hK hα.le hγ.le hμ ht]
  apply (abs_add_le _ _).trans
  have h := add_le_add (hs 1 (by norm_num)) (hs (-1) (by norm_num))
  simpa only [← two_mul,mul_assoc,B] using h

theorem moment_cell_bound {K α γ μ t : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (z : ℝ) (k : ℕ) :
    (∫ v, (1+‖v‖)^k ∂cell K α γ μ t z) ≤
      2*((1/4)*((K*max 1 (α*γ)⁻¹)/(μ+t)))*(2+α)^k := by
  apply (le_abs_self _).trans
  apply integral_cell_abs_le hK hα hγ hμ ht z
  intro v hv
  rw [abs_of_nonneg (pow_nonneg (by positivity : 0 ≤ 1+‖v‖) k)]
  exact pow_le_pow_left₀ (by positivity) (by linarith) k

end BoltzmannNonuniqueness.AxialBackground

namespace BoltzmannNonuniqueness.GeometricBackground

theorem moment_bound {θ η l K α γ t : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (ht : 0 < t)
    (x : JetPrototype.Space) (k : ℕ) :
    (∫ v, (1+‖v‖)^k ∂background θ η l K α γ t x) ≤
      2*((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t)))*(2+α)^k := by
  classical
  have hcoef : 0 ≤ K*max 1 (α*γ)⁻¹ :=
    mul_nonneg hK (le_max_of_le_left zero_le_one)
  by_cases ha : active θ η l x.1
  · rw [background,ite_eq_left ha]
    apply (AxialBackground.moment_cell_bound hK hα hγ (scale_pos hθ η x.1) ht.le x.2 k).trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) k)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact div_le_div_of_nonneg_left hcoef (by linarith) (by linarith [ha.1])
  · rw [background,ite_eq_right ha,integral_zero_measure]
    positivity

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Measurable velocity averages of the limiting atomic background -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialBackground

theorem clamped_weight_measurable {α γ μ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (K σ : ℝ) :
    Measurable (fun p : ℝ × ℝ => weight K α γ μ (max 0 p.1) σ p.2) := by
  have hf := (AxialFlow.clamped_foot_continuous (σ := σ) hα hγ hμ).measurable
  have hS : Measurable (fun p : ℝ × ℝ => S (γ*AxialFlow.foot σ α γ μ (max 0 p.1) p.2/μ)) :=
    continuous_S.measurable.comp ((hf.const_mul γ).div_const μ)
  exact ((hS.const_mul K).div (measurable_const.add
    ((((measurable_const.max measurable_fst).mul_const α).mul_const γ).mul hS))).const_mul (1/4)

theorem clamped_atom_test_measurable {K α γ μ : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ)
    (σ : ℝ) {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun p : ℝ × ℝ => ∫ v, ψ v ∂atom K α γ μ (max 0 p.1) σ p.2) := by
  have hv := (AxialFlow.clamped_velocity_continuous (σ := σ) hα hγ hμ).measurable
  have hj : Measurable (fun p : ℝ × ℝ =>
      PlaneChart.join 0 (AxialFlow.velocity σ α γ μ (max 0 p.1) p.2)) :=
    VelocityWeight.split.symm.measurable.comp (hv.prodMk measurable_const)
  have he : (fun p : ℝ × ℝ => ∫ v, ψ v ∂atom K α γ μ (max 0 p.1) σ p.2) =
      (fun p => weight K α γ μ (max 0 p.1) σ p.2*
        ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ (max 0 p.1) p.2))) := by
    funext p
    exact integral_atom hK hα hγ hμ (le_max_left 0 p.1) σ p.2 ψ
  rw [he]
  exact (clamped_weight_measurable hα hγ hμ K σ).mul (hψ.comp hj)

theorem clamped_cell_test_measurable {K α γ μ : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun p : ℝ × ℝ => ∫ v, ψ v ∂cell K α γ μ (max 0 p.1) p.2) := by
  have he : (fun p : ℝ × ℝ => ∫ v, ψ v ∂cell K α γ μ (max 0 p.1) p.2) =
      (fun p => (∫ v, ψ v ∂atom K α γ μ (max 0 p.1) 1 p.2)+
        ∫ v, ψ v ∂atom K α γ μ (max 0 p.1) (-1) p.2) := by
    funext p
    exact integral_add_measure (integrable_atom _ _ _ _ _ _ _ _)
      (integrable_atom _ _ _ _ _ _ _ _)
  rw [he]
  exact (clamped_atom_test_measurable hK hα hγ hμ 1 hψ).add
    (clamped_atom_test_measurable hK hα hγ hμ (-1) hψ)

end BoltzmannNonuniqueness.AxialBackground

namespace BoltzmannNonuniqueness.GeometricBackground

theorem clamped_background_test_measurable {θ K α γ : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (η l : ℝ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun p : ℝ × JetPrototype.Space =>
      ∫ v, ψ v ∂background θ η l K α γ (max 0 p.1) p.2) := by
  let f : ℤ × (ℝ × ℝ) → ℝ := fun p =>
    ∫ v, ψ v ∂AxialBackground.cell K α γ (GeometricMesh.point θ η p.1) (max 0 p.2.1) p.2.2
  have hf : Measurable f := measurable_from_prod_countable_right (fun k =>
    AxialBackground.clamped_cell_test_measurable hK hα hγ (GeometricMesh.point_pos hθ η k) hψ)
  have hi : Measurable (fun p : ℝ × JetPrototype.Space =>
      (GeometricMesh.index (‖p.2.1‖/θ) η,(p.1,p.2.2))) := by
    unfold GeometricMesh.index
    fun_prop
  have hm := hf.comp hi
  have ha : MeasurableSet {p : ℝ × JetPrototype.Space | active θ η l p.2.1} :=
    (active_measurableSet θ η l).preimage measurable_snd.fst
  have he : (fun p : ℝ × JetPrototype.Space =>
      ∫ v, ψ v ∂background θ η l K α γ (max 0 p.1) p.2) =
      {p : ℝ × JetPrototype.Space | active θ η l p.2.1}.indicator
        (fun p => f (GeometricMesh.index (‖p.2.1‖/θ) η,(p.1,p.2.2))) := by
    funext p
    by_cases hp : active θ η l p.2.1 <;> simp [background,hp,f,scale]
  rw [he]
  exact hm.indicator ha

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The loss frequency of the limiting atomic medium -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.GeometricBackground

def frequency (θ η l K α γ t : ℝ) (x : JetPrototype.Space) (v : Velocity) : ℝ :=
  2*Real.pi*∫ p, ‖v-p‖ ∂background θ η l K α γ t x

theorem frequency_nonneg (θ η l K α γ t : ℝ) (x : JetPrototype.Space) (v : Velocity) :
    0 ≤ frequency θ η l K α γ t x v :=
  mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _))

theorem integrable_test (θ η l K α γ t : ℝ) (x : JetPrototype.Space) (ψ : Velocity → ℝ) :
    Integrable ψ (background θ η l K α γ t x) := by
  classical
  unfold background
  split_ifs
  · exact (AxialBackground.integrable_atom _ _ _ _ _ _ _ _).add_measure
      (AxialBackground.integrable_atom _ _ _ _ _ _ _ _)
  · exact integrable_zero_measure

theorem frequency_bound {θ η l K α γ t : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (ht : 0 < t)
    (x : JetPrototype.Space) (v : Velocity) :
    frequency θ η l K α γ t x v ≤
      (2*Real.pi)*(2*((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t))))*(‖v‖+1+α) := by
  classical
  have hcoef : 0 ≤ K*max 1 (α*γ)⁻¹ :=
    mul_nonneg hK (le_max_of_le_left zero_le_one)
  by_cases ha : active θ η l x.1
  · unfold frequency
    rw [background,ite_eq_left ha]
    have hc := AxialBackground.integral_cell_abs_le hK hα hγ (scale_pos hθ η x.1)
      ht.le x.2 (fun p => ‖v-p‖) (C := ‖v‖+1+α) (fun p hp => by
        rw [abs_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le v p).trans (by linarith))
    have hi := (le_abs_self _).trans hc
    have hm : (K*max 1 (α*γ)⁻¹)/(scale θ η x.1+t) ≤
        (K*max 1 (α*γ)⁻¹)/(l+t) :=
      div_le_div_of_nonneg_left hcoef (by positivity) (by linarith [ha.1])
    calc
      _ ≤ (2*Real.pi)*(2*((1/4)*((K*max 1 (α*γ)⁻¹)/(scale θ η x.1+t)))*(‖v‖+1+α)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ ≤ (2*Real.pi)*(2*((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t)))*(‖v‖+1+α)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hm (by norm_num)) (by norm_num)
      _ = _ := by ring
  · rw [frequency,background,ite_eq_right ha,integral_zero_measure,mul_zero]
    positivity

private theorem cell_distance_measurable {K α γ μ : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) :
    Measurable (fun p : (ℝ × ℝ) × Velocity =>
      ∫ w, ‖p.2-w‖ ∂AxialBackground.cell K α γ μ (max 0 p.1.1) p.1.2) := by
  have ha (σ : ℝ) : Measurable (fun p : (ℝ × ℝ) × Velocity =>
      AxialBackground.weight K α γ μ (max 0 p.1.1) σ p.1.2 *
        ‖p.2-PlaneChart.join 0 (AxialFlow.velocity σ α γ μ (max 0 p.1.1) p.1.2)‖) := by
    have hw := (AxialBackground.clamped_weight_measurable hα hγ hμ K σ).comp
      (measurable_fst : Measurable (fun p : (ℝ × ℝ) × Velocity => p.1))
    have hv := (AxialFlow.clamped_velocity_continuous (σ := σ) hα hγ hμ).measurable.comp
      (measurable_fst : Measurable (fun p : (ℝ × ℝ) × Velocity => p.1))
    have hj : Measurable (fun p : (ℝ × ℝ) × Velocity =>
        PlaneChart.join 0 (AxialFlow.velocity σ α γ μ (max 0 p.1.1) p.1.2)) :=
      VelocityWeight.split.symm.measurable.comp (hv.prodMk measurable_const)
    exact hw.mul ((measurable_snd.sub hj).norm)
  have he : (fun p : (ℝ × ℝ) × Velocity =>
      ∫ w, ‖p.2-w‖ ∂AxialBackground.cell K α γ μ (max 0 p.1.1) p.1.2) =
      (fun p => AxialBackground.weight K α γ μ (max 0 p.1.1) 1 p.1.2 *
        ‖p.2-PlaneChart.join 0 (AxialFlow.velocity 1 α γ μ (max 0 p.1.1) p.1.2)‖ +
        AxialBackground.weight K α γ μ (max 0 p.1.1) (-1) p.1.2 *
        ‖p.2-PlaneChart.join 0 (AxialFlow.velocity (-1) α γ μ (max 0 p.1.1) p.1.2)‖) := by
    funext p
    exact AxialBackground.integral_cell hK hα hγ hμ (le_max_left 0 p.1.1) p.1.2 _
  rw [he]
  exact (ha 1).add (ha (-1))

theorem clamped_frequency_measurable {θ K α γ : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (η l : ℝ) :
    Measurable (fun p : (ℝ × JetPrototype.Space) × Velocity =>
      frequency θ η l K α γ (max 0 p.1.1) p.1.2 p.2) := by
  let f : ℤ × ((ℝ × ℝ) × Velocity) → ℝ := fun p =>
    ∫ w, ‖p.2.2-w‖ ∂AxialBackground.cell K α γ (GeometricMesh.point θ η p.1)
      (max 0 p.2.1.1) p.2.1.2
  have hf : Measurable f := by
    apply measurable_from_prod_countable_right
    intro k
    change Measurable (fun p : (ℝ × ℝ) × Velocity =>
      ∫ w, ‖p.2-w‖ ∂AxialBackground.cell K α γ (GeometricMesh.point θ η k)
        (max 0 p.1.1) p.1.2)
    exact cell_distance_measurable (K := K) (α := α) (γ := γ)
      (μ := GeometricMesh.point θ η k) hK hα hγ (GeometricMesh.point_pos hθ η k)
  have hi : Measurable (fun p : (ℝ × JetPrototype.Space) × Velocity =>
      (GeometricMesh.index (‖p.1.2.1‖/θ) η,((p.1.1,p.1.2.2),p.2))) := by
    unfold GeometricMesh.index
    fun_prop
  have ha : MeasurableSet {p : (ℝ × JetPrototype.Space) × Velocity |
      active θ η l p.1.2.1} :=
    (active_measurableSet θ η l).preimage measurable_fst.snd.fst
  have he : (fun p : (ℝ × JetPrototype.Space) × Velocity =>
      frequency θ η l K α γ (max 0 p.1.1) p.1.2 p.2) =
      (fun p => 2*Real.pi * {p : (ℝ × JetPrototype.Space) × Velocity |
        active θ η l p.1.2.1}.indicator
          (fun p => f (GeometricMesh.index (‖p.1.2.1‖/θ) η,((p.1.1,p.1.2.2),p.2))) p) := by
    funext p
    by_cases hp : active θ η l p.1.2.1 <;> simp [frequency,background,hp,f,scale]
  rw [he]
  exact ((hf.comp hi).indicator ha).const_mul (2*Real.pi)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Relative weights of the actual compressed cold beams -/

noncomputable section

open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialBackground

theorem compressed_scalar_error {R a s : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |R*s/(1+a*s)-1| ≤ |R-1|+R*(1-s+a) := by
  have hd : 0 < 1+a*s := by positivity
  have hq0 : 0 ≤ s/(1+a*s) := div_nonneg hs hd.le
  have hq1 : s/(1+a*s) ≤ 1 := (div_le_one hd).mpr (by nlinarith)
  have hsq : s^2 ≤ 1 := by nlinarith
  have hsq' := mul_le_mul_of_nonneg_left hsq ha
  have hq : s-s/(1+a*s) ≤ a := by
    have he : (s-a)*(1+a*s) ≤ s := by nlinarith [mul_nonneg (sq_nonneg a) hs]
    have hh := (le_div_iff₀ hd).mpr he
    linarith
  have he : R*s/(1+a*s)-1 = (R-1)+R*(s/(1+a*s)-1) := by ring
  rw [he]
  calc
    _ ≤ |R-1|+|R*(s/(1+a*s)-1)| := abs_add_le _ _
    _ = |R-1|+R*(1-s/(1+a*s)) := by
      rw [abs_mul,abs_of_nonneg hR,abs_of_nonpos (sub_nonpos.mpr hq1)]
      ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith) hR)

def relativeWeight (r α γ μ t σ z : ℝ) : ℝ :=
  r/μ * S (γ*AxialFlow.foot σ α γ μ t z/μ) /
    (1+(t*α*γ/μ)*S (γ*AxialFlow.foot σ α γ μ t z/μ))

theorem weight_eq_relative {r α γ μ t : ℝ} (hr : 0 < r) (hμ : 0 < μ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (K σ z : ℝ) :
    weight K α γ μ t σ z = (K/(4*r))*relativeWeight r α γ μ t σ z := by
  have hS := (S_pos (γ*AxialFlow.foot σ α γ μ t z/μ)).le
  have hprod : 0 ≤ t*α*γ*S (γ*AxialFlow.foot σ α γ μ t z/μ) := by positivity
  have hd : μ+t*α*γ*S (γ*AxialFlow.foot σ α γ μ t z/μ) ≠ 0 := by linarith
  have hd' : 1+(t*α*γ/μ)*S (γ*AxialFlow.foot σ α γ μ t z/μ) ≠ 0 := by positivity
  unfold weight JetCoreDensity.compressed relativeWeight
  field_simp

theorem relativeWeight_error {r α γ μ t : ℝ} (hr : 0 ≤ r) (hμ : 0 < μ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (σ z : ℝ) :
    |relativeWeight r α γ μ t σ z-1| ≤ |r/μ-1|+
      (r/μ)*(1-S (γ*AxialFlow.foot σ α γ μ t z/μ)+t*α*γ/μ) :=
  compressed_scalar_error (div_nonneg hr hμ.le) (by positivity)
    (S_pos _).le (S_le_one _)

theorem foot_abs_bound {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t)
    (σ γ μ z : ℝ) : |AxialFlow.foot σ α γ μ t z| ≤ |z|+t*(|σ|+α) := by
  have hv := AxialFlow.velocity_sub_center_le (σ := σ) (γ := γ) (s := μ) (t := t) (z := z) hα
  have hb : |AxialFlow.velocity σ α γ μ t z| ≤ |σ|+α := by
    have hh := abs_add_le (AxialFlow.velocity σ α γ μ t z-σ) σ
    rw [sub_add_cancel] at hh
    linarith
  unfold AxialFlow.foot
  calc
    _ ≤ |z|+|t*AxialFlow.velocity σ α γ μ t z| := abs_sub _ _
    _ = |z|+t*|AxialFlow.velocity σ α γ μ t z| := by rw [abs_mul,abs_of_nonneg ht]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hb ht)

end BoltzmannNonuniqueness.AxialBackground

end

end

section

/-! # The limiting medium as a measurable finite kernel on positive-time slabs -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.GeometricBackground

theorem background_finite (θ η l K α γ t : ℝ) (x : JetPrototype.Space) :
    IsFiniteMeasure (background θ η l K α γ t x) :=
  (integrable_const_iff_isFiniteMeasure (by norm_num : (1:ℝ) ≠ 0)).mp
    (integrable_test θ η l K α γ t x (fun _ => 1))

theorem clamped_background_measurable {θ K α γ : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (η l : ℝ) :
    Measurable (fun p : ℝ × JetPrototype.Space =>
      background θ η l K α γ (max 0 p.1) p.2) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hm := (clamped_background_test_measurable hθ hK hα hγ η l
    (measurable_const.indicator hs : Measurable (s.indicator (fun _ : Velocity => (1:ℝ))))).ennreal_ofReal
  convert hm using 1
  funext p
  let _ := background_finite θ η l K α γ (max 0 p.1) p.2
  rw [integral_indicator_const (1:ℝ) hs]
  simp only [smul_eq_mul,mul_one]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ s)).symm

def slabKernel {a θ K α γ : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (η l : ℝ) : Kernel (ℝ × JetPrototype.Space) Velocity where
  toFun p := background θ η l K α γ (max a p.1) p.2
  measurable' := by
    have hi : Measurable (fun p : ℝ × JetPrototype.Space => (max a p.1,p.2)) :=
      (measurable_const.max measurable_fst).prodMk measurable_snd
    have hm := (clamped_background_measurable hθ hK hα.le hγ.le η l).comp hi
    convert hm using 1
    funext p
    change background θ η l K α γ (max a p.1) p.2 =
      background θ η l K α γ (max 0 (max a p.1)) p.2
    rw [max_eq_right (ha.le.trans (le_max_left a p.1))]

theorem slabKernel_finite {a θ K α γ l : ℝ} (ha : 0 < a) (hθ : 0 < θ)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (η : ℝ) (hl : 0 ≤ l) :
    IsFiniteKernel (slabKernel ha hθ hK hα hγ η l) := by
  let C := 2*((1/4)*((K*max 1 (α*γ)⁻¹)/a))
  refine ⟨⟨ENNReal.ofReal C,ENNReal.ofReal_lt_top,fun p => ?_⟩⟩
  let _ := background_finite θ η l K α γ (max a p.1) p.2
  have hb := moment_bound (η := η) hθ hl hK hα hγ (ha.trans_le (le_max_left a p.1)) p.2 0
  simp only [pow_zero,mul_one] at hb
  rw [integral_const] at hb
  simp only [smul_eq_mul,mul_one] at hb
  have hc : 2*((1/4)*((K*max 1 (α*γ)⁻¹)/(l+max a p.1))) ≤ C := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha
      (by linarith [le_max_left a p.1])
  change background θ η l K α γ (max a p.1) p.2 univ ≤ ENNReal.ofReal C
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ univ)]
  exact ENNReal.ofReal_le_ofReal (hb.trans hc)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Cancellation of the inverse-time sheet bound by the hot cap -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

def gainCoefficient (K α γ q : ℝ) : ℝ≥0∞ :=
  2*(ENNReal.ofReal ((1/4)*(K*max 1 (α*γ)⁻¹))*
    SheetTotal.bound q (Real.exp (8*(1+α)^2)))

theorem gainCoefficient_lt_top (K α γ q : ℝ) : gainCoefficient K α γ q < ⊤ := by
  exact ENNReal.mul_lt_top (by norm_num)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (SheetTotal.bound_lt_top _ _))

theorem capped_chartGain_bound {θ η l K α γ t q : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (ht : 0 < t) (hq₁ : 1 < q) (hq₂ : q < 2) (x : JetPrototype.Space)
    {h : Velocity → ℝ} (hh : ∀ w, h w ≤ (l+t)*H q w)
    {v : Velocity} (hv : transverse v ≠ 0) :
    chartGain (background θ η l K α γ t x) (fun w => ENNReal.ofReal (h w)) v ≤
      ENNReal.ofReal (H q v)*gainCoefficient K α γ q := by
  have hlt : 0 < l+t := add_pos_of_nonneg_of_pos hl ht
  have hdom (w) : ENNReal.ofReal (h w) ≤
      ENNReal.ofReal (l+t)*ENNReal.ofReal (H q w) := by
    rw [← ENNReal.ofReal_mul hlt.le]
    exact ENNReal.ofReal_le_ofReal (hh w)
  have he : ENNReal.ofReal (l+t)*
      ENNReal.ofReal ((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t))) =
      ENNReal.ofReal ((1/4)*(K*max 1 (α*γ)⁻¹)) := by
    rw [← ENNReal.ofReal_mul hlt.le]
    congr 1
    field_simp
  calc
    _ ≤ chartGain (background θ η l K α γ t x)
        (fun w => ENNReal.ofReal (l+t)*ENNReal.ofReal (H q w)) v :=
      chartGain_mono_right hdom v
    _ = ENNReal.ofReal (l+t)*(ENNReal.ofReal (H q v)*
        normalizedChartGain (background θ η l K α γ t x) q v) := by
      rw [SheetApplication.gain_const_mul_right _ _ _ ENNReal.ofReal_ne_top,
        SheetApplication.gain_H_eq]
    _ ≤ ENNReal.ofReal (l+t)*(ENNReal.ofReal (H q v)*
        (2*(ENNReal.ofReal ((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t)))*
          SheetTotal.bound q (Real.exp (8*(1+α)^2))))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl
        (background_gain_bound hθ hl hK hα hγ ht hq₁ hq₂ x hv))
    _ = ENNReal.ofReal (H q v)*(2*((ENNReal.ofReal (l+t)*
        ENNReal.ofReal ((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t))))*
          SheetTotal.bound q (Real.exp (8*(1+α)^2)))) := by ac_rfl
    _ = _ := by rw [he]; rfl

theorem capped_chartGain_ae_bound {θ η l K α γ t q : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (ht : 0 < t) (hq₁ : 1 < q) (hq₂ : q < 2) (x : JetPrototype.Space)
    {h : Velocity → ℝ} (hh : ∀ w, h w ≤ (l+t)*H q w) :
    ∀ᵐ v ∂volume,
      chartGain (background θ η l K α γ t x) (fun w => ENNReal.ofReal (h w)) v ≤
        ENNReal.ofReal (H q v)*gainCoefficient K α γ q := by
  filter_upwards [SheetApplication.ae_transverse_ne_zero] with v hv
  exact capped_chartGain_bound hθ hl hK hα hγ ht hq₁ hq₂ x hh hv

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Gaussian moment of the finite atomic limiting medium -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.GeometricBackground

theorem gaussian_moment_bound {θ η l K α γ t : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (ht : 0 < t)
    (x : JetPrototype.Space) :
    (∫⁻ v, ENNReal.ofReal (weight v) ∂background θ η l K α γ t x) ≤
      ENNReal.ofReal (2*((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t)))*
        Real.exp ((1+α)^2/2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_test θ η l K α γ t x weight) (ae_of_all _ (fun v => (weight_pos v).le))]
  apply ENNReal.ofReal_le_ofReal
  apply (le_abs_self _).trans
  classical
  by_cases ha : active θ η l x.1
  · rw [background,ite_eq_left ha]
    apply (AxialBackground.integral_cell_abs_le hK hα hγ (scale_pos hθ η x.1)
      ht.le x.2 weight (C := Real.exp ((1+α)^2/2)) ?_).trans
    · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one))
        (by linarith) (by linarith [ha.1])
    · intro v hv
      rw [abs_of_pos (weight_pos v)]
      apply Real.exp_le_exp.mpr
      nlinarith [norm_nonneg v]
  · rw [background,ite_eq_right ha,integral_zero_measure,abs_zero]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (by norm_num)
        (div_nonneg (mul_nonneg hK (le_max_of_le_left zero_le_one)) (by linarith))))
      (Real.exp_pos _).le

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A quantitative positive cold weight on bounded time and scale intervals -/

noncomputable section

open Set
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialBackground

theorem S_lower_of_abs_le {R x : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) : S R ≤ S x := by
  have hc : Real.cosh x ≤ Real.cosh R :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg hR] using hx)
  have hi : (Real.cosh R)⁻¹ ≤ (Real.cosh x)⁻¹ :=
    (inv_le_inv₀ (Real.cosh_pos _) (Real.cosh_pos _)).mpr hc
  unfold S
  nlinarith [inv_nonneg.mpr (Real.cosh_pos x).le,inv_nonneg.mpr (Real.cosh_pos R).le]

def compactWeightLower (K α γ m M T Z : ℝ) : ℝ :=
  (1/4)*(K*S (γ*(Z+T*(1+α))/m)/(M+T*α*γ))

theorem compactWeightLower_pos {K α γ m M T Z : ℝ}
    (hK : 0 < K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hM : 0 < M) (hT : 0 ≤ T) :
    0 < compactWeightLower K α γ m M T Z := by
  unfold compactWeightLower
  exact mul_pos (by norm_num) (div_pos (mul_pos hK (S_pos _)) (by positivity))

theorem compactWeightLower_le {K α γ m M T Z μ t σ z : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hm : 0 < m)
    (hT : 0 ≤ T) (hZ : 0 ≤ Z) (hμ : μ ∈ Icc m M) (ht : t ∈ Icc 0 T)
    (hσ : |σ| = 1) (hz : |z| ≤ Z) :
    compactWeightLower K α γ m M T Z ≤ weight K α γ μ t σ z := by
  have ht0 : 0 ≤ t := ht.1
  have hμ0 : 0 < μ := hm.trans_le hμ.1
  have hM : 0 < M := hμ0.trans_le hμ.2
  have hfoot : |AxialFlow.foot σ α γ μ t z| ≤ Z+T*(1+α) := by
    have hh := foot_abs_bound hα ht.1 σ γ μ z
    rw [hσ] at hh
    exact hh.trans (add_le_add hz (mul_le_mul_of_nonneg_right ht.2 (by positivity)))
  have harg : |γ*AxialFlow.foot σ α γ μ t z/μ| ≤ γ*(Z+T*(1+α))/m := by
    rw [abs_div,abs_mul,abs_of_nonneg hγ,abs_of_pos hμ0]
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfoot hγ) hμ0.le).trans
    exact div_le_div_of_nonneg_left (by positivity) hm hμ.1
  have hS := S_lower_of_abs_le (show 0 ≤ γ*(Z+T*(1+α))/m by positivity) harg
  have hden : μ+t*α*γ*S (γ*AxialFlow.foot σ α γ μ t z/μ) ≤ M+T*α*γ := by
    have hs : t*α*γ*S (γ*AxialFlow.foot σ α γ μ t z/μ) ≤ t*α*γ :=
      mul_le_of_le_one_right (by positivity) (S_le_one _)
    have ht' : t*α*γ ≤ T*α*γ := by gcongr; exact ht.2
    linarith [hμ.2]
  have hden0 : 0 < μ+t*α*γ*S (γ*AxialFlow.foot σ α γ μ t z/μ) := by
    have hS0 := (S_pos (γ*AxialFlow.foot σ α γ μ t z/μ)).le
    positivity
  unfold compactWeightLower weight JetCoreDensity.compressed
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS hK) (by positivity)).trans
  exact div_le_div_of_nonneg_left (mul_nonneg hK (S_pos _).le) hden0 hden

end BoltzmannNonuniqueness.AxialBackground

end

end

section

/-! # The hot cap cancels the inverse-time background loss coefficient -/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

def lossCoefficient (K α γ : ℝ) : ℝ :=
  (2*Real.pi)*(2*((1/4)*(K*max 1 (α*γ)⁻¹)))

theorem lossCoefficient_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ : ℝ) :
    0 ≤ lossCoefficient K α γ := by
  unfold lossCoefficient
  positivity

theorem capped_loss_bound {θ η l K α γ t q h : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (ht : 0 < t) (x : JetPrototype.Space) (v : Velocity)
    (hh : h ≤ (l+t)*H q v) :
    h*frequency θ η l K α γ t x v ≤
      lossCoefficient K α γ*(‖v‖+1+α)*H q v := by
  have hlt : 0 < l+t := add_pos_of_nonneg_of_pos hl ht
  calc
    _ ≤ ((l+t)*H q v)*
        ((2*Real.pi)*(2*((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t))))*(‖v‖+1+α)) :=
      mul_le_mul hh (frequency_bound hθ hl hK hα hγ ht x v)
        (frequency_nonneg _ _ _ _ _ _ _ _ _) (mul_nonneg hlt.le (H_nonneg q v))
    _ = _ := by
      unfold lossCoefficient
      field_simp

theorem frequency_slab_bound {θ η l K α γ a t : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (ha : 0 < a) (hat : a ≤ t) (x : JetPrototype.Space) (v : Velocity) :
    frequency θ η l K α γ t x v ≤
      (lossCoefficient K α γ/a)*(‖v‖+1+α) := by
  apply (frequency_bound hθ hl hK hα hγ (ha.trans_le hat) x v).trans
  have hb : (K*max 1 (α*γ)⁻¹)/(l+t) ≤ (K*max 1 (α*γ)⁻¹)/a :=
    div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha (by linarith)
  calc
    _ ≤ (2*Real.pi)*(2*((1/4)*((K*max 1 (α*γ)⁻¹)/a)))*(‖v‖+1+α) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by norm_num)) (by norm_num)
    _ = _ := by unfold lossCoefficient; ring

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
