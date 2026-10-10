import OAI.Probability.ClassicalON.PlanarGinibre

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
namespace ClassicalON

theorem planar_antipode_exists : ∃ t : PlanarAngle,planarCharacter t= -1 := by
  let h := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  refine ⟨h.symm (-1),?_⟩
  change (AddCircle.toCircle (h.symm (-1)) : ℂ)= -1
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  change (h (h.symm (-1)) : ℂ)= -1
  simp

theorem planarCos_add_antipode {s : PlanarAngle} (hs : planarCharacter s= -1) (t : PlanarAngle) :
    planarCos (s+t)= -planarCos t := by
  simp [planarCos,planarCharacter_add,hs]

variable {V : Type uV} {E : Type uE} [Fintype V]

theorem planar_reference_mean_nonneg (left right : E → V) (e : E) :
    0≤∫ θ : V → PlanarAngle,planarEnergy left right e θ ∂planarReference := by
  classical
  by_cases h : left e=right e
  · simp [planarEnergy,h,planarCos,planarCharacter]
  obtain ⟨t,ht⟩ := planar_antipode_exists
  let v : V → PlanarAngle := Function.update (fun _ => 0) (left e) t
  have he (θ : V → PlanarAngle) :
      planarEnergy left right e (v+θ)= -planarEnergy left right e θ := by
    unfold planarEnergy
    have hv : (v+θ) (left e)-(v+θ) (right e)=t+(θ (left e)-θ (right e)) := by
      simp only [Pi.add_apply,v,Function.update_self,Function.update_of_ne (Ne.symm h),zero_add]
      abel
    rw [hv,planarCos_add_antipode ht]
  have hh := integral_add_left_eq_self (μ := planarReference) (planarEnergy left right e) v
  simp_rw [he] at hh
  rw [integral_neg] at hh
  linarith

variable [Fintype E]

theorem planar_edge_mean_nonneg (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e) (e : E) :
    0≤planarMean left right b (planarEnergy left right e) := by
  apply edgeMean_nonneg planarReference (planarEnergy left right)
    (continuous_planarEnergy left right)
  · exact planar_edge_covariance_nonneg left right
  · exact planar_reference_mean_nonneg left right
  · exact hb

end ClassicalON

end

end OAI
