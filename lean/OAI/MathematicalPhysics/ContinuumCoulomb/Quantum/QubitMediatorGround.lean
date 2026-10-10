import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorTrial
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorGraph

namespace OAI

/-! A full-space ground-energy estimate for the explicit parallel gadget. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaPhysical_thirdOrder_ground (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hg : 0 < g) (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) {d m η : ℝ}
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hsmall : 2*d+4*m ≤ g)
    (hPert : ‖qmaPerturbationOperator C D V‖ ≤ d)
    (hCouple : ∑ e, ‖spinMatrixOperator (V e)‖ ≤ g*η)
    (hbound : ∀ p : EuclideanSpace ℂ σ, ‖p‖ = 1 →
      |qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => p i)| ≤ m)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix g C D V)-
      Perturbation.thirdOrderBottom ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedInverse g) (qmaComplementOperator C D V) (qmaCouplingOperator V)| ≤
      (2*d^2/g+2*m)*η^2 := by
  obtain ⟨p,hp,hmin⟩ := Perturbation.thirdOrderForm_minimizer
    ((qmaMatrixOperator C).restrictScalars ℝ) (qmaPaddedInverse g)
    (qmaComplementOperator C D V) (qmaCouplingOperator V) u hu
  rw [Perturbation.thirdOrderBottom_eq _ _ _ _ p hp hmin,qmaActual_thirdOrderForm]
  let μ := qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => p i)
  let ε := (2*d^2/g+2*m)*η^2
  have hμ : |μ| ≤ m := hbound p hp
  have hmin' (v : EuclideanSpace ℂ σ) :
      μ*‖v‖^2 ≤ qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => v i) := by
    simpa only [qmaActual_thirdOrderForm] using hmin v
  have hl (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      (μ-ε)*‖x‖^2 ≤ ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ :=
    qmaPhysical_thirdOrder_lower g C D V hg hC hD hV hd hm hsmall hPert hCouple
      (abs_le.mp hμ).2 hmin' x
  have hu0 : ‖qmaMediatorInclusion (κ := κ) u‖ = 1 :=
    (Perturbation.orthogonalInclusion_norm
      (qmaMediatorInclusion (σ := σ) (κ := κ)) (qmaMediatorRestriction (σ := σ) (κ := κ))
      qmaMediator_restrict_include qmaMediator_inclusion_adjoint u).trans hu
  have hnon : {e | ∃ x : EuclideanSpace ℂ (σ × (κ → Fin 2)), ‖x‖ = 1 ∧
      e = ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ}.Nonempty := ⟨_,_,hu0,rfl⟩
  have hlow : μ-ε ≤ MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix g C D V) := by
    apply le_csInf hnon
    rintro e ⟨x,hx,rfl⟩
    simpa only [hx,one_pow,mul_one] using hl x
  obtain ⟨ht,htrial⟩ := qmaPhysical_thirdOrder_trial g C D V hg hC hD hV hm hCouple
    (abs_le.mp hμ).1 p hp rfl
  have hb : BddBelow {e | ∃ x : EuclideanSpace ℂ (σ × (κ → Fin 2)), 0 < ‖x‖^2 ∧
      e = ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ/‖x‖^2} := by
    refine ⟨μ-ε,?_⟩
    rintro e ⟨x,hx,rfl⟩
    exact (le_div_iff₀ hx).mpr (hl x)
  have hup : MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix g C D V) ≤ μ+m*η^2 := by
    rw [MediatorGraph.normalizedBottom_eq_rayleigh]
    exact (csInf_le hb ⟨qmaThirdTrial g V p,ht,rfl⟩).trans htrial
  have heps : m*η^2 ≤ ε := by
    have hz : 0 ≤ 2*d^2/g := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg η)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end ContinuumCoulomb

end

end OAI
