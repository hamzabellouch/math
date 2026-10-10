import OAI.Analysis.AncientFlat.Evolution.AncientMild

namespace OAI
noncomputable section
open Set
open scoped Topology BoundedContinuousFunction
namespace AncientMild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
lemma fixed_of_fixed_source (T : ℝ → E →L[ℂ] E)
    (hc : ∀ v : E, ContinuousOn (fun t => T t v) (Ici (0:ℝ)))
    (hcircle : ∀ z : ℂ, ‖z‖=1 → z ∈ resolventSet ℂ (T 1))
    (D : (ℝ →ᵇ E) →L[ℂ] (ℝ →ᵇ E))
    (hD : ∀ f : ℝ →ᵇ E, ∀ τ t : ℝ, 0 ≤ t → t≤1 →
      D f (τ+t)=T t (D f τ)+duhamel T f t τ)
    (A : E →L[ℝ] E)
    (hA : ∀ t ∈ Icc (0:ℝ) 1, ∀ v : E, A (T t v)=T t (A v))
    (f : ℝ →ᵇ E) (hf : ∀ τ, A (f τ)=f τ) :
    ∀ τ, A (D f τ)=D f τ := by
  have hi (τ : ℝ) : A (duhamel T f 1 τ)=duhamel T f 1 τ := by
    rw [duhamel,← A.intervalIntegral_comp_comm (integrand_integrable T hc f zero_le_one τ)]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    dsimp only
    rw [hA (1-s) ⟨by linarith [hs.2],by linarith [hs.1]⟩,hf]
  let R : ℝ →ᵇ E := A.compLeftContinuousBounded ℝ (D f)-D f
  have hR : ∀ τ : ℝ, R (τ+1)=T 1 (R τ) := by
    intro τ
    change A (D f (τ+1))-D f (τ+1)=T 1 (A (D f τ)-D f τ)
    rw [hD f τ 1 zero_le_one le_rfl,A.map_add,hA 1 ⟨zero_le_one,le_rfl⟩,hi,(T 1).map_sub]
    abel
  have hz := homogeneous_time_eq_zero (T 1) hcircle R hR
  intro τ
  have he := congrArg (fun g : ℝ →ᵇ E => g τ) hz
  change A (D f τ)-D f τ=0 at he
  exact sub_eq_zero.mp he
end AncientMild

end

end OAI
