import OAI.Analysis.IrrationalRotation.Analysis.OrbitFiberNull
import OAI.Analysis.IrrationalRotation.Product.ProductBaseDynamics
import OAI.Analysis.IrrationalRotation.Product.ProductLogIntegral

namespace OAI

noncomputable section
open MeasureTheory Set Function
open scoped ENNReal

namespace Invariant233.ProductModel

private def orbitPerm (θ : ℕ → ℝ) : Equiv.Perm Base :=
  Equiv.addRight (fun i => (θ i : Circle))

private theorem orbitPerm_apply (θ : ℕ → ℝ) (x : Base) :
    orbitPerm θ x = rotation θ x := rfl

private theorem orbitPerm_zpow (θ : ℕ → ℝ) (n : ℤ) (x : Base) :
    (orbitPerm θ ^ n) x = rotationIterate θ n x := by
  cases n with
  | ofNat n =>
    change ((Equiv.addRight (fun i => (θ i : Circle))) ^ n) x = _
    rw [Equiv.Perm.coe_pow]
    change (fun x : Base => x + fun i => (θ i : Circle))^[n] x = _
    rw [add_right_iterate]
    ext i
    change x i + n • (θ i : Circle) = x i + (((n : ℤ) : ℝ) * θ i : ℝ)
    rw [← AddCircle.coe_nsmul]
    simp [nsmul_eq_mul]
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    change ((Equiv.addRight (fun i => (θ i : Circle))).symm ^ (n + 1)) x = _
    rw [Equiv.addRight_symm, Equiv.Perm.coe_pow]
    change (fun x : Base => x + -(fun i => (θ i : Circle)))^[n + 1] x = _
    rw [add_right_iterate]
    ext i
    change x i + (n + 1) • (-(θ i : Circle)) =
      x i + (((Int.negSucc n : ℤ) : ℝ) * θ i : ℝ)
    rw [← AddCircle.coe_neg, ← AddCircle.coe_nsmul]
    congr 2
    simp [nsmul_eq_mul]
    ring

theorem rotation_joint_fiber_measure_zero
    {Y : Type*} [MeasurableSpace Y] [Nonempty Y]
    [MeasurableSpace.CountablySeparated Y] [MeasurableSingletonClass Y]
    {θ : ℕ → ℝ} (hθ : JointlyRationallyIndependent θ)
    {f : Base → Y} (hf : Measurable f)
    (hnonconstant : ¬ ∃ c : Y, f =ᵐ[baseMeasure] Function.const Base c)
    (z : ℤ → Y) :
    baseMeasure {x | ∀ n : ℤ, f (rotationIterate θ n x) = z n} = 0 := by
  have hm : Measurable (orbitPerm θ) := (measurePreserving_rotation θ).measurable
  have hi : Measurable (orbitPerm θ).symm := by
    change Measurable (fun x : Base => x - fun i => (θ i : Circle))
    fun_prop
  have he : ∀ n : ℕ, 0 < n → Ergodic (orbitPerm θ : Base → Base)^[n] baseMeasure := by
    intro n hn
    exact rotation_totalErgodic hθ hn
  simpa only [orbitPerm_zpow] using
    orbit_joint_fiber_measure_zero (orbitPerm θ) hm hi he hf hnonconstant z

theorem weight_rotation_joint_fiber_measure_zero
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) (z : ℤ → ℝ) :
    baseMeasure {x | ∀ n : ℤ, weight θ c (rotationIterate θ n x) = z n} = 0 := by
  apply rotation_joint_fiber_measure_zero hadm.2.2 (measurable_weight θ c)
  apply not_ae_constant_of_negInfiniteLogIntegral
  · exact (ae_weight_pos θ c (fun i => (hadm.1 i).1.le)
      (fun i => (hadm.1 i).2.2.le) hadm.2.1).mono fun _ h => h.ne'
  · exact (hasNegInfiniteLogIntegral_iff_tsum θ c
      (fun i => ⟨(hadm.1 i).1.le, (hadm.1 i).2.1⟩)
      (fun i => (hadm.1 i).2.2.le)).mpr hdiv

theorem weight_polar_joint_fiber_measure_zero
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞)
    (k : ℤ) (z : ℤ → ℂ) :
    baseMeasure {x | ∀ n : ℤ,
      (weight θ c (rotationIterate θ (k - n) x) : ℂ) = z n} = 0 := by
  apply measure_mono_null (t := {x | ∀ n : ℤ,
    weight θ c (rotationIterate θ n x) = (z (k - n)).re})
  · intro x hx n
    have he := congrArg Complex.re (hx (k - n))
    have hk : k - (k - n) = n := by omega
    simpa only [hk, Complex.ofReal_re] using he
  · exact weight_rotation_joint_fiber_measure_zero θ c hadm hdiv _

end Invariant233.ProductModel

end

end OAI
