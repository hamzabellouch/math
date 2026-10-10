import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionPattern

namespace OAI

namespace ProjectionComparison

open Set MeasureTheory

variable {V E : Type*} [Fintype V] [Fintype E]

theorem projection_mixture (S : System V E) (b v₀ v₁ h₀ h₁ : V → ℝ)
    (hp₀ : IsProjection S b v₀ h₀) (hp₁ : IsProjection S b v₁ h₁) :
    ∃ w : Finset E → ℝ,(∀ F,0≤w F) ∧ (∑ F,w F)=1 ∧
      ∀ x,h₁ x-h₀ x=∑ F,w F*faceAverage S F (fun y => v₁ y-v₀ y) x := by
  classical
  let hne : (feasible S b).Nonempty := ⟨h₀,hp₀.1⟩
  let H : ℝ → V → ℝ := fun t => project S b hne (fun y => v₀ y+t*(v₁ y-v₀ y))
  have hlip (x : V) : LipschitzWith ‖v₁-v₀‖₊ (fun t => H t x) := project_path_lipschitz S b v₀ v₁ hne x
  have hc (x : V) : Continuous (fun t => H t x) := (hlip x).continuous
  have hH₀ : H 0=h₀ := by
    apply projection_unique S b v₀ _ h₀ _ hp₀
    simpa only [H,zero_mul,add_zero] using project_spec S b hne v₀
  have hH₁ : H 1=h₁ := by
    apply projection_unique S b v₁ _ h₁ _ hp₁
    simpa only [H,one_mul,add_sub_cancel] using project_spec S b hne v₁
  have hder : ∀ᵐ t : ℝ,∀ x,deriv (fun s => H s x) t=faceAverage S (activePattern S (H t)) (fun y => v₁ y-v₀ y) x := by
    filter_upwards [project_path_ae_derivative S b v₀ v₁ hne] with t ht
    have hd := projection_derivative S (fun _ => b) (fun s y => v₀ y+s*(v₁ y-v₀ y)) H
      (fun _ => 0) (fun y => v₁ y-v₀ y) (fun y => deriv (fun s => H s y) t) t
      (Filter.Eventually.of_forall fun s => project_spec S b hne _)
      (fun y => hasDerivAt_const t (b y))
      (fun y => by simpa using (((hasDerivAt_id t).mul_const (v₁ y-v₀ y)).const_add (v₀ y)))
      (fun y => (ht y).hasDerivAt)
    intro x
    unfold faceAverage
    rw [faceGraph_pattern,faceComponent_pattern]
    split_ifs with hf
    · exact hd.2 x hf
    · push Not at hf
      obtain ⟨p,hp,hxp⟩ := hf
      exact hd.1 x p hp hxp
  let w : Finset E → ℝ := fun F => ∫ t in (0:ℝ)..1,patternWeight S H F t
  refine ⟨w,?_,?_,?_⟩
  · intro F
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    unfold patternWeight
    split_ifs <;> norm_num
  · dsimp only [w]
    rw [← intervalIntegral.integral_finsetSum (fun F _ => intervalIntegrable_patternWeight S H hc F)]
    simp only [sum_patternWeight]
    norm_num
  · intro x
    have ha : AbsolutelyContinuousOnInterval (fun t => H t x) 0 1 := (hlip x).lipschitzOnWith.absolutelyContinuousOnInterval
    calc
      h₁ x-h₀ x=H 1 x-H 0 x := by rw [hH₀,hH₁]
      _ = ∫ t in (0:ℝ)..1,deriv (fun s => H s x) t := ha.integral_deriv_eq_sub.symm
      _ = ∫ t in (0:ℝ)..1,∑ F,patternWeight S H F t*faceAverage S F (fun y => v₁ y-v₀ y) x := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hder] with t ht
        intro _
        rw [sum_patternWeight_mul]
        exact ht x
      _ = ∑ F,w F*faceAverage S F (fun y => v₁ y-v₀ y) x := by
        rw [intervalIntegral.integral_finsetSum (fun F _ => (intervalIntegrable_patternWeight S H hc F).mul_const _)]
        simp only [intervalIntegral.integral_mul_const,w]

end ProjectionComparison

end OAI
