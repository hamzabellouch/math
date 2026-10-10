import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCorrectionLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAnalyticCorrection

namespace OAI

/-! The converging inverse defines actual ODE corrections. Only invertibility
is needed, so the equation persists under the operator-norm limit argument. -/

open Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem spectralCorrectionInverse_equation (T B : E →L[ℂ] E)
    (hu : IsUnit (1-T*B)) (r : E) :
    let v := Ring.inverse (1-T*B) (T r)
    v=T (B v+r) := by
  intro v
  have he := congrArg (fun A : E →L[ℂ] E => A (T r)) (Ring.mul_inverse_cancel _ hu)
  change v-T (B v)=T r at he
  rw [map_add]
  simpa only [add_comm] using sub_eq_iff_eq_add.mp he

theorem spectralCorrectionInverse_eventually_unit (T : E →L[ℂ] E)
    (B : ℕ → E →L[ℂ] E) (B₀ : E →L[ℂ] E)
    (hB : Tendsto B atTop (𝓝 B₀)) (hu : IsUnit (1-T*B₀)) :
    ∀ᶠ n in atTop, IsUnit (1-T*B n) := by
  have hD : Tendsto (fun n => 1-T*B n) atTop (𝓝 (1-T*B₀)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hB)
  exact hD.eventually (Units.isOpen.mem_nhds hu)

end

local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularInverseCorrection_hasDerivAt (κ : ℝ) (hκ : 0 < κ)
    (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℝ →ᵇ ℂ) (r : CircularTailSpace)
    (hu : IsUnit (1-circularTailCLM κ hκ*circularFieldOperator νp νm η m hm q)) (t : ℝ) :
    let v := Ring.inverse (1-circularTailCLM κ hκ*circularFieldOperator νp νm η m hm q)
      (circularTailCLM κ hκ r)
    HasDerivAt (circularTailEvaluation v)
      (κ • circularTailEvaluation v t+circularLeadingField t (circularTailEvaluation v t)+
        circularBoundedField νp νm η m (q t) (circularTailEvaluation v t)+
        circularTailEvaluation r t) t := by
  let : NormedAddCommGroup CircularTailSpace := inferInstance
  let : NormedSpace ℂ CircularTailSpace := inferInstance
  let : CompleteSpace CircularTailSpace := inferInstance
  intro v
  let B := circularFieldOperator νp νm η m hm q
  have hv : circularTail κ hκ (B v+r)=v :=
    (spectralCorrectionInverse_equation (circularTailCLM κ hκ) B hu r).symm
  have hd := circularTail_hasDerivAt κ hκ (B v+r) t
  dsimp only at hd
  rw [hv] at hd
  apply hd.congr_deriv
  have he := circularFieldOperator_evaluation νp νm η m hm q v t
  change circularTailEvaluation (B v) t=_ at he
  rw [← he]
  apply Prod.ext <;> apply Prod.ext
  all_goals
    simp only [circularTailEvaluation,circularLeadingField,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,BoundedContinuousFunction.add_apply]
    abel

end DefocusingNLS

end OAI
