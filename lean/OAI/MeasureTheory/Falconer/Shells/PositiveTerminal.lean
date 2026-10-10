import OAI.MeasureTheory.Falconer.Shells.PositiveSuffix
import OAI.MeasureTheory.Falconer.Estimates.RegularClasses

namespace OAI

/-! # Terminal bounds for the actual positive distance states

The profile is evaluated at integer depths in the recursive state.  The
regularized class stores its profile on [0,1], so the final theorem explicitly
uses `u ↦ m (u / N)` when passing to that state.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem testedCellDistance_mass_le (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) :
    testedCellDistance ρ ρ P Q G univ ≤ ρ P.carrier * ρ Q.carrier := by
  exact (testedCellDistance_le ρ ρ P Q G univ).trans_eq (cellDistance_mass ρ ρ P Q)

theorem positiveCollisionCount_mass_bound (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q a t : ℕ) (X Y : List (Fin d → Bool))
    (ℓ : ℝ)
    (hX : ρ (Q.descendant X).carrier ≤ ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a)))
    (hY : ρ (Q.descendant Y).carrier ≤ ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a))) :
    positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y ≤
      ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*ℓ)) := by
  let θ := testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
    (policyTestPairs w₀ Q ρ m A N σ J i q a t)
  have ht : θ univ ≤ (ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a)))^2 := by
    exact (testedCellDistance_mass_le ρ _ _ _).trans
      (by simpa only [pow_two] using mul_le_mul' hX hY)
  have hc : (θ.prod θ) {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t} ≤
      (ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a)))^4 := by
    calc
      _ ≤ (θ.prod θ) univ := measure_mono (subset_univ _)
      _ = θ univ * θ univ := by rw [← univ_prod_univ,Measure.prod_prod]
      _ ≤ _ := by convert mul_le_mul' ht ht using 1; ring
  change ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) * (θ.prod θ) _ ≤ _
  apply (mul_le_mul' le_rfl hc).trans_eq
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hp : ((((2:ℝ)^N)^(ℓ-m a))^4) = ((2:ℝ)^N)^(4*(ℓ-m a)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
    congr 1
    ring
  rw [hp,mul_assoc,← Real.rpow_add (by positivity)]
  congr 2
  ring

theorem positiveCollisionCount_regularized (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m)
    (A : ℕ → ℝ) (σ : ℝ) (J i q : ℕ) {a t : ℕ}
    (ha : a ≤ N) (X Y : List (Fin d → Bool))
    (hX : X.length = a) (hY : Y.length = a) :
    positiveCollisionCount w₀ Q ρ (fun u => m (u/N)) A N σ J i q a t X Y ≤
      ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*((d:ℝ)+1)*lam)) := by
  let := hreg.probability
  have hcell (P : List (Fin d → Bool)) (hP : P.length = a) :
      ρ (Q.descendant P).carrier ≤
        ENNReal.ofReal (((2:ℝ)^N)^(((d:ℝ)+1)*lam-m ((a:ℝ)/N))) := by
    by_cases hp : 0 < ρ (Q.descendant P).carrier
    · rw [← ENNReal.ofReal_toReal (measure_ne_top ρ _)]
      apply ENNReal.ofReal_le_ofReal
      exact (hreg.cells a ha P hP hp).2.trans_eq
        (Real.rpow_add (by positivity) _ _).symm
    · simp only [not_lt,le_zero_iff] at hp
      rw [hp]
      exact zero_le
  simpa only [mul_assoc] using positiveCollisionCount_mass_bound w₀ Q ρ
    (fun u => m (u/N)) A N σ J i q a t X Y (((d:ℝ)+1)*lam)
    (hcell X hX) (hcell Y hY)

theorem positiveCollisionCount_terminal (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m)
    (hN : 0 < N) (A : ℕ → ℝ) (σ : ℝ) (J i q : ℕ) {a t : ℕ}
    (ha : a ≤ N) (hat : a ≤ t) (ht : t ≤ a+100*q)
    (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a) :
    positiveCollisionCount w₀ Q ρ (fun u => m (u/N)) A N σ J i q a t X Y ≤
      ENNReal.ofReal (((2:ℝ)^N)^(100*(q:ℝ)/N+4*((d:ℝ)+1)*lam)) := by
  let := hreg.probability
  apply (positiveCollisionCount_regularized w₀ Q ρ hreg A σ J i q ha X Y hX hY).trans
  apply ENNReal.ofReal_le_ofReal
  have hwidth : (2:ℝ)^(t-a) ≤ ((2:ℝ)^N)^(100*(q:ℝ)/N) := by
    calc
      _ ≤ (2:ℝ)^(100*q) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by
        rw [dyadic_rpow_change_base hN]
        have he : (100*(q:ℝ)) = ((100*q:ℕ):ℝ) := by push_cast; ring
        rw [he,Real.rpow_natCast]
  calc
    _ ≤ ((2:ℝ)^N)^(100*(q:ℝ)/N)*((2:ℝ)^N)^(4*((d:ℝ)+1)*lam) :=
      mul_le_mul_of_nonneg_right hwidth (by positivity)
    _ = _ := (Real.rpow_add (by positivity) _ _).symm

end Falconer

end OAI
