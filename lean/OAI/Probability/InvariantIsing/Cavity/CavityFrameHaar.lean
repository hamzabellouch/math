import OAI.Probability.InvariantIsing.Cavity.CavityFrameOrbit

namespace OAI

/-! Uniqueness of the invariant frame law, proved by averaging bounded
continuous tests over the compact orthogonal group. -/

noncomputable section
open MeasureTheory
open scoped Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityFrame_eq_haar_orbit {n q : ℕ}
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Matrix (Fin n) (Fin q) ℝ)) [IsProbabilityMeasure ν]
    (hinv : ∀ U : Orthogonal n,
      ν.map (fun A => (U : Matrix (Fin n) (Fin n) ℝ) * A) = ν)
    (hframe : ∀ᵐ A ∂ν, A.transpose * A = 1)
    (A₀ : Matrix (Fin n) (Fin q) ℝ) (hA₀ : A₀.transpose * A₀ = 1) :
    ν = μ.map (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) := by
  let : HasOuterApproxClosed (Matrix (Fin n) (Fin q) ℝ) :=
    inferInstanceAs (HasOuterApproxClosed (Fin n → Fin q → ℝ))
  let : SecondCountableTopology (Matrix (Fin n) (Fin q) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin q → ℝ))
  have hact := continuous_cavityFrameAction n q
  have hfix (U : Orthogonal n) :
      Continuous (fun A : Matrix (Fin n) (Fin q) ℝ => (U : Matrix (Fin n) (Fin n) ℝ) * A) :=
    hact.comp (continuous_const.prodMk continuous_id)
  have horbit : Continuous (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) :=
    hact.comp (continuous_id.prodMk continuous_const)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  have hi : Integrable (fun p : Orthogonal n × Matrix (Fin n) (Fin q) ℝ =>
      F ((p.1 : Matrix (Fin n) (Fin n) ℝ) * p.2)) (μ.prod ν) :=
    Integrable.of_bound (F.continuous.comp hact).aestronglyMeasurable ‖F‖
      (ae_of_all _ (fun p => F.norm_coe_le_norm _))
  have hrow (U : Orthogonal n) :
      (∫ A, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂ν) = ∫ A, F A ∂ν := by
    rw [← integral_map (hfix U).aemeasurable F.continuous.aestronglyMeasurable, hinv U]
  have hcol : ∀ᵐ A ∂ν,
      (∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂μ) =
        ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ := by
    filter_upwards [hframe] with A hA
    obtain ⟨V, hV⟩ := cavityFrame_transitive A₀ A hA₀ hA
    rw [← hV]
    simp only [← Matrix.mul_assoc]
    change (∫ U, F (((U * V : Orthogonal n) : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ) = _
    exact integral_mul_right_eq_self (μ := μ)
      (fun U : Orthogonal n => F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀)) V
  calc
    (∫ A, F A ∂ν) = ∫ U, ∫ A, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂ν ∂μ := by
      simp only [hrow]
      simp
    _ = ∫ A, ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A) ∂μ ∂ν :=
      integral_integral_swap hi
    _ = ∫ U, F ((U : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ := by
      rw [integral_congr_ae hcol]
      simp
    _ = ∫ A, F A ∂μ.map (fun U : Orthogonal n => (U : Matrix (Fin n) (Fin n) ℝ) * A₀) :=
      (integral_map horbit.aemeasurable F.continuous.aestronglyMeasurable).symm

end InvariantIsing

end

end OAI
