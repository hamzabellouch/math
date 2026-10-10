import OAI.MeasureTheory.Falconer.Shells.PositiveSuffix
import OAI.MeasureTheory.Falconer.Fourier.DistanceSincCollision

namespace OAI

/-! # Fourier control of the actual positive collision state

The tolerance is the manuscript's 100(d+1)2⁻ᵗ. The frequency interval
is enlarged from 2ᵗ/(d+1) to 2ᵗ using positivity, with a fixed dimensional
constant. No regularity of the tested pair measure is required here.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem charFun_testedCellDistance (μ ν : Measure (Space d))
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) (r : ℝ) :
    charFun (testedCellDistance μ ν P Q G) r =
      ∫ z, Complex.exp ((r:ℂ)*(dist z.1 z.2:ℂ)*Complex.I)
        ∂testedCellPair μ ν P Q G := by
  rw [charFun_apply_real,testedCellDistance,integral_map (by fun_prop) (by fun_prop)]

theorem dyadic_distance_collision_fourier (d : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (a t : ℕ), a ≤ t →
      (2:ℝ)^(t-a) * (μ.prod μ).real
        {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t} ≤
      (C/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t), ‖charFun μ r‖^2 := by
  obtain ⟨C,hC,h⟩ := PlanarFalconer.finite_measure_distance_collision_fourier
  refine ⟨((d:ℝ)+1)*C,by positivity,?_⟩
  intro μ _ a t hat
  let A := (2:ℝ)^t/((d:ℝ)+1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hAle : A ≤ (2:ℝ)^t := by
    apply (div_le_iff₀ (by positivity : 0 < (d:ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d,show 0 ≤ (2:ℝ)^t by positivity]
  have htol : 100/A = 100*((d:ℝ)+1)/(2:ℝ)^t := by dsimp [A]; field_simp
  have hh := h μ A hA
  rw [htol] at hh
  have hi : IntegrableOn (fun r => ‖charFun μ r‖^2)
      (Icc (-(2:ℝ)^t) ((2:ℝ)^t)) := by
    simpa only [one_mul,IntegrableOn] using
      PlanarFalconer.charFun_sq_integrable_finite μ
        (volume.restrict (Icc (-(2:ℝ)^t) ((2:ℝ)^t))) 1
  have hsub : Icc (-A) A ⊆ Icc (-(2:ℝ)^t) ((2:ℝ)^t) := by
    intro r hr
    exact ⟨by linarith [hr.1],hr.2.trans hAle⟩
  have hint := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ r‖)) hi
  have hpow : (2:ℝ)^t = (2:ℝ)^a * (2:ℝ)^(t-a) := by
    rw [← pow_add,Nat.add_sub_of_le hat]
  have hscale : (2:ℝ)^(t-a) = (((d:ℝ)+1)/(2:ℝ)^a)*A := by
    dsimp [A]
    rw [hpow]
    field_simp
  calc
    _ = (((d:ℝ)+1)/(2:ℝ)^a) *
        (A*(μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t}) := by
      rw [hscale]; ring
    _ ≤ (((d:ℝ)+1)/(2:ℝ)^a) *
        (C*∫ r in Icc (-A) A, ‖charFun μ r‖^2) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ (((d:ℝ)+1)/(2:ℝ)^a) *
        (C*∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t), ‖charFun μ r‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hint hC.le) (by positivity)
    _ = _ := by ring

theorem positiveCollisionCount_fourier : ∃ C : ℝ, 0 < C ∧
    ∀ (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
      (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ) (J i q a t : ℕ), a ≤ t →
    ∀ (X Y : List (Fin d → Bool)),
      (positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y).toReal ≤
      (C/(2:ℝ)^a)*((2:ℝ)^N)^(4*m a) *
        ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t),
          ‖charFun (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
            (policyTestPairs w₀ Q ρ m A N σ J i q a t)) r‖^2 := by
  obtain ⟨C,hC,h⟩ := dyadic_distance_collision_fourier d
  refine ⟨C,hC,?_⟩
  intro w₀ Q ρ _ m A N σ J i q a t hat X Y
  have hh := mul_le_mul_of_nonneg_right
    (h (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
      (policyTestPairs w₀ Q ρ m A N σ J i q a t)) a t hat)
    (show 0 ≤ ((2:ℝ)^N)^(4*m a) by positivity)
  unfold positiveCollisionCount
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
  simpa only [measureReal_def,mul_assoc,mul_left_comm,mul_comm] using hh

end Falconer

end OAI
