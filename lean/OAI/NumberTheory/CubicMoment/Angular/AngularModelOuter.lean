import OAI.NumberTheory.CubicMoment.Angular.AngularLatticeModel
import OAI.NumberTheory.CubicMoment.Estimates.TypeIFinal

namespace OAI

/-! Summation of the actual angular lattice model over the level dyad.
This is the model term in the low-height Type-I estimate. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma angularSmoothModel_zero_of_not_squarefree {r : Eisenstein}
    (hr : ¬Squarefree r) (ℓ : ℤ) (W : ℝ → ℂ) (U : ℝ) :
    angularSmoothModel r ℓ W U = 0 := by
  have hs (u : Eisenstein) : ¬Squarefree (r*u) := fun h =>
    hr (Squarefree.squarefree_of_dvd (dvd_mul_right r u) h)
  simp [angularSmoothModel,idealMoebius_sq_complex,hs]

lemma angular_model_outer_power {R U δ : ℝ} (hR : 0 < R) (_hU : 0 < U) :
    R*(R^(δ-1/6)*U^(1/3:ℝ)) = R^δ*R^(5/6:ℝ)*U^(1/3:ℝ) := by
  calc
    _ = (R^(1:ℝ)*R^(δ-1/6))*U^(1/3:ℝ) := by rw [Real.rpow_one]; ring
    _ = R^(1+(δ-1/6))*U^(1/3:ℝ) := by rw [←Real.rpow_add hR]
    _ = R^(δ+5/6)*U^(1/3:ℝ) := by rw [show (1:ℝ)+(δ-1/6) = δ+5/6 by ring]
    _ = _ := by rw [Real.rpow_add hR]

theorem LogarithmicWeightFamily.angular_model_outer_bound
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (h : LogarithmicWeightFamily Y W)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) {η : ℝ} (hη : 0 < η)
    (d : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : Finset ι) (α : ι → ℂ) (r : ι → Eisenstein)
      (R U : ℝ), 1 ≤ R → 1 ≤ U →
      (∀ i ∈ S, primary (r i) ∧ R ≤ norm (r i) ∧ norm (r i) ≤ 2*R) →
      (∀ i ∈ S, Y i ≤ R*U) →
      (∑ i ∈ S, ‖α i‖) ≤ A*R*(Real.log (R*U))^d →
      ‖∑ i ∈ S, α i*angularSmoothModel (r i) ℓ (W i) U‖ ≤
        K*(R*U)^η*R^(5/6:ℝ)*U^(1/3:ℝ) := by
  let δ := min (η/4) (1/12)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδsmall : δ-1/6 ≤ 0 := by have := min_le_right (η/4) (1/12:ℝ); dsimp [δ]; linarith
  have hδη : 3*δ ≤ η := by have := min_le_left (η/4) (1/12:ℝ); dsimp [δ]; linarith
  obtain ⟨C,hC,hbound⟩ := h.angularSmoothModel_bound hℓ hδ hδ
  obtain ⟨D,hD,hlog⟩ := typeI_log_power_bound d hδ
  refine ⟨C*A*D,by positivity,?_⟩
  intro S α r R U hR hU hr hY hα
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hX : 1 ≤ R*U := by nlinarith
  have hXp : 0 < R*U := by positivity
  have hRX : R ≤ R*U := le_mul_of_one_le_right hRp.le hU
  let B := C*(R*U)^δ*R^(δ-1/6)*U^(1/3:ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (i : ι) (hi : i ∈ S) : ‖angularSmoothModel (r i) ℓ (W i) U‖ ≤ B := by
    by_cases hs : Squarefree (r i)
    · apply (hbound i (r i) (hr i hi).1 hs U hU).trans
      dsimp [B]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (zero_lt_one.trans_le (h.length_one i)).le (hY i hi) hδ.le) hC.le)
          (Real.rpow_le_rpow_of_nonpos hRp (hr i hi).2.1 hδsmall)
          (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)) (by positivity)
    · rw [angularSmoothModel_zero_of_not_squarefree hs,norm_zero]
      exact hB
  calc
    _ ≤ ∑ i ∈ S, ‖α i‖*‖angularSmoothModel (r i) ℓ (W i) U‖ := by
      simpa only [norm_mul] using norm_sum_le S (fun i => α i*angularSmoothModel (r i) ℓ (W i) U)
    _ ≤ ∑ i ∈ S, ‖α i‖*B := Finset.sum_le_sum
      (fun i hi => mul_le_mul_of_nonneg_left (hb i hi) (_root_.norm_nonneg _))
    _ = (∑ i ∈ S, ‖α i‖)*B := (Finset.sum_mul S _ B).symm
    _ ≤ (A*R*(Real.log (R*U))^d)*B := mul_le_mul_of_nonneg_right hα hB
    _ = (C*A)*(R*U)^δ*(Real.log (R*U))^d*
        (R^δ*R^(5/6:ℝ)*U^(1/3:ℝ)) := by
      rw [←angular_model_outer_power hRp hUp]
      dsimp [B]
      ring
    _ ≤ (C*A)*(R*U)^δ*(D*(R*U)^δ)*
        ((R*U)^δ*R^(5/6:ℝ)*U^(1/3:ℝ)) := by
      gcongr
      · exact hlog _ hX
    _ = (C*A*D)*(R*U)^(3*δ)*R^(5/6:ℝ)*U^(1/3:ℝ) := by
      rw [show 3*δ = δ+δ+δ by ring,Real.rpow_add hXp,Real.rpow_add hXp]
      ring
    _ ≤ _ := by gcongr

lemma angular_model_level_power {R U : ℝ} (hR : 1 ≤ R) (hU : 1 ≤ U)
    (hRX : R ≤ (R*U)^(51/100:ℝ)) :
    R^(5/6:ℝ)*U^(1/3:ℝ) ≤ (R*U)^(589/1000:ℝ) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hX : 1 ≤ R*U := by nlinarith
  calc
    _ = (R*U)^(1/3:ℝ)*R^(1/2:ℝ) := by
      rw [Real.mul_rpow hRp.le hUp.le,
        show (5/6:ℝ) = 1/3+1/2 by norm_num,Real.rpow_add hRp]
      ring
    _ ≤ (R*U)^(1/3:ℝ)*((R*U)^(51/100:ℝ))^(1/2:ℝ) := by gcongr
    _ = (R*U)^(353/600:ℝ) := by
      rw [←Real.rpow_mul (mul_nonneg hRp.le hUp.le),←Real.rpow_add (mul_pos hRp hUp)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

end CubicFirstMoment

end

end OAI
