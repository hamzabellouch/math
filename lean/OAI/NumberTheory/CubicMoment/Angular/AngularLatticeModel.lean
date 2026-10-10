import OAI.NumberTheory.CubicMoment.Angular.AngularPowerWeights

namespace OAI

/-! The actual squarefree angular model in the low Type-I argument.
Its norm factor is absorbed into the test function, and its cancellation
is obtained from the proved primary-lattice estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def angularSmoothModel (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (U : ℝ) : ℂ :=
  ∑' u : Eisenstein, if primary u then theta ℓ (r*u)*(idealMoebius (r*u):ℂ)^2*
    (cStar*norm (r*u)^(-1/6:ℝ):ℝ)*W (norm u/U) else 0

lemma idealMoebius_sq_complex (u : Eisenstein) :
    (idealMoebius u:ℂ)^2 = if Squarefree u then 1 else 0 := by
  exact_mod_cast idealMoebius_sq u

lemma idealMoebius_sq_mul_of_squarefree {r : Eisenstein} (hr : Squarefree r)
    (u : Eisenstein) :
    (idealMoebius (r*u):ℂ)^2 = if IsCoprime r u then (idealMoebius u:ℂ)^2 else 0 := by
  simp only [idealMoebius_sq_complex,squarefree_mul_iff,isRelPrime_iff_isCoprime,hr]
  split_ifs <;> simp_all

lemma angularSmoothModel_eq {r : Eisenstein} (hr : Squarefree r)
    (ℓ : ℤ) (W : ℝ → ℂ) {U : ℝ} (hU : 0 < U) :
    angularSmoothModel r ℓ W U =
      (cStar*(norm r*U)^(-1/6:ℝ):ℝ)*theta ℓ r*
        squarefreeCoprimeAngularLattice r ℓ (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W x) U := by
  unfold angularSmoothModel squarefreeCoprimeAngularLattice
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  rw [idealMoebius_sq_mul_of_squarefree hr]
  by_cases hp : primary u
  · by_cases hc : IsCoprime r u
    · simp only [hp,hc,true_and,ite_true,theta_mul]
      have he : norm (r*u)^(-1/6:ℝ) =
          (norm r*U)^(-1/6:ℝ)*(norm u/U)^(-1/6:ℝ) := by
        rw [norm_mul_eq,Real.mul_rpow (norm_nonneg r) (norm_nonneg u),
          Real.mul_rpow (norm_nonneg r) hU.le,Real.div_rpow (norm_nonneg u) hU.le]
        have hn : U^(-1/6:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hU _)
        field_simp
      rw [he]
      push_cast
      ring
    · simp only [hp,hc,true_and,ite_true,ite_false,mul_zero,zero_mul]
  · simp only [hp,false_and,ite_false,mul_zero]

theorem LogarithmicWeightFamily.angularSmoothModel_bound
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (h : LogarithmicWeightFamily Y W)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ U, 1 ≤ U →
      ‖angularSmoothModel r ℓ (W i) U‖ ≤
        K*(Y i)^s*norm r^(ε-1/6)*U^(1/3:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := h.power_lattice_bound hℓ (-1/6) hε hs
  refine ⟨|cStar| * K,by have := cStar_pos; positivity,?_⟩
  intro i r hr hsr U hU
  have hnr := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hUp : 0 < U := zero_lt_one.trans_le hU
  rw [angularSmoothModel_eq hsr ℓ (W i) hUp,norm_mul,norm_mul,norm_theta (primary_ne_zero hr),mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (mul_pos hnr hUp) _)]
  calc
    _ ≤ (|cStar| * (norm r*U)^(-1/6:ℝ))*(K*(Y i)^s*norm r^ε*Real.sqrt U) :=
      mul_le_mul_of_nonneg_left (hbound i r hr hsr U hU) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hnr.le hUp.le,Real.sqrt_eq_rpow,
        show ε-1/6 = (-1/6:ℝ)+ε by ring,Real.rpow_add hnr,
        show (1/3:ℝ) = (-1/6:ℝ)+1/2 by norm_num,Real.rpow_add hUp]
      ring

end CubicFirstMoment

end

end OAI
