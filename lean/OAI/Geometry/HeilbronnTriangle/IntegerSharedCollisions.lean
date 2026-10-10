import OAI.Geometry.HeilbronnTriangle.IntegerSamplingPairs
import OAI.Geometry.HeilbronnTriangle.SharedGeometricAlteration

namespace OAI


noncomputable section

namespace Problem355.IntegerSamplingPairs

theorem pairMass_eq_average {Θ X : Type*} [Fintype Θ] [Fintype X]
    (rho : Θ → ℝ) (mu : Θ → X → ℝ) (point : Θ → X → Point) :
    SharedGeometricAlteration.pairMass rho mu point =
      ∑ θ, rho θ * ∑ x : Fin 2 → X, (∏ i, mu θ (x i)) *
        (if point θ (x 0) = point θ (x 1) then 1 else 0) := by
  classical
  simp only [SharedGeometricAlteration.pairMass, Fintype.sum_prod_type,
    ConditionalSamples.sharedWeight, ConditionalSamples.productWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ hθ
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

theorem shared_box_pairMass_le {Θ : Type*} [Fintype Θ]
    (N Q L : ℕ) (hQ : 0 < Q) (hL : 0 < L) (hN : N = Q * L)
    (rho : Θ → ℝ)
    (mu : Θ → IntegerSampling.Box N 3 (IntegerSampling.samplingShift N) → ℝ)
    (hrho0 : ∀ θ, 0 ≤ rho θ) (hrho : ∑ θ, rho θ = 1)
    (hmu0 : ∀ θ x, 0 ≤ mu θ x)
    (hmu : ∀ θ x, mu θ x ≤ 1 / (L : ℝ) ^ 3) :
    SharedGeometricAlteration.pairMass rho mu (fun _ => IntegerSampling.project) ≤
      8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
  rw [pairMass_eq_average]
  calc
    _ ≤ ∑ θ, rho θ * (8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3) := by
      apply Finset.sum_le_sum
      intro θ hθ
      apply mul_le_mul_of_nonneg_left _ (hrho0 θ)
      exact box_finTwo_collision_le N Q L hQ hL hN (mu θ) (hmu0 θ) (hmu θ)
    _ = _ := by rw [← Finset.sum_mul, hrho, one_mul]

theorem shared_mixture_columnLaw_pairMass_le {Θ I : Type*}
    [Fintype Θ] [Fintype I]
    (h q L : ℕ) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L)
    (rho : Θ → ℝ) (hrho0 : ∀ θ, 0 ≤ rho θ) (hrho : ∑ θ, rho θ = 1)
    (w : Θ → I → ℝ) (hw0 : ∀ θ i, 0 ≤ w θ i) (hw : ∀ θ, ∑ i, w θ i = 1)
    (a : Θ → I → Fin 3 → ZMod h)
    (V : Θ → I → Finset (Fin 3 → ZMod q))
    (s : Θ → I → ℕ) (hs : ∀ θ i, 0 < s θ i) :
    SharedGeometricAlteration.pairMass rho
      (fun θ x => ∑ i, w θ i * IntegerSampling.columnLaw h q L
        (IntegerSampling.samplingShift (L * (h * q))) (a θ i) (V θ i) (s θ i) x)
      (fun _ => IntegerSampling.project) ≤
      8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  apply shared_box_pairMass_le _ (h * q) L (Nat.mul_pos hh hq) hL
    (Nat.mul_comm _ _) rho _ hrho0 hrho
  · intro θ x
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 θ i)
      (IntegerSampling.columnLaw_nonneg h q L _ (a θ i) (V θ i) (s θ i) x))
  · intro θ
    apply mixture_mass_le (w θ) _ _ (hw0 θ) (hw θ)
    intro i x
    exact conditionalColumnMass_le _ _ (a θ i) (V θ i) (s θ i) L (hs θ i) x

end Problem355.IntegerSamplingPairs

end

end OAI
