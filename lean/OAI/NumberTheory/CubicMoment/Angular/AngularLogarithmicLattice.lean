import OAI.NumberTheory.CubicMoment.Angular.AngularUniformLattice
import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily

namespace OAI

/-! The literal low angular model for weights with logarithmic derivative
growth. Every fixed positive power absorbs those derivative costs. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefreeCoprimeAngularLattice_const_mul (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (U : ℝ) (c : ℂ) :
    squarefreeCoprimeAngularLattice r ℓ (fun x => c*W x) U =
      c*squarefreeCoprimeAngularLattice r ℓ W U := by
  unfold squarefreeCoprimeAngularLattice
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hu : primary u ∧ IsCoprime r u
  · simp only [hu.1,hu.2,and_self,ite_true]
    ring
  · simp only [hu,ite_false,mul_zero]

theorem LogarithmicWeightFamily.squarefreeCoprimeAngularLattice_bound
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (h : LogarithmicWeightFamily Y W)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ U, 1 ≤ U →
      ‖squarefreeCoprimeAngularLattice r ℓ (W i) U‖ ≤
        K*(Y i)^s*norm r^ε*Real.sqrt U := by
  obtain ⟨K,hK,hbound⟩ := (h.normalize hs).squarefreeCoprimeAngularLattice_bound hℓ hε
  refine ⟨K,hK,?_⟩
  intro i r hr hsr U hU
  have hY : 0 < Y i := zero_lt_one.trans_le (h.length_one i)
  have he : squarefreeCoprimeAngularLattice r ℓ (normalizedLogWeight Y W s i) U =
      (((Y i)^(-s):ℝ):ℂ)*squarefreeCoprimeAngularLattice r ℓ (W i) U := by
    change squarefreeCoprimeAngularLattice r ℓ (fun x => ((Y i)^(-s):ℝ) • W i x) U = _
    simp_rw [Complex.real_smul]
    exact squarefreeCoprimeAngularLattice_const_mul r ℓ (W i) U (((Y i)^(-s):ℝ):ℂ)
  have hb := hbound i r hr hsr U hU
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hY.le _)] at hb
  have hp : (Y i)^s*(Y i)^(-s) = 1 := by
    rw [←Real.rpow_add hY,add_neg_cancel,Real.rpow_zero]
  calc
    _ = (Y i)^s*((Y i)^(-s)*‖squarefreeCoprimeAngularLattice r ℓ (W i) U‖) := by
      rw [←mul_assoc,hp,one_mul]
    _ ≤ (Y i)^s*(K*norm r^ε*Real.sqrt U) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
