import OAI.Analysis.AncientFlat.Evolution.DuhamelCocycle
import OAI.Analysis.AncientFlat.Evolution.TimeGreen

namespace OAI
noncomputable section
open Set
open scoped Topology BoundedContinuousFunction
namespace AncientMild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
theorem exists_bounded_mild_inverse
    (T : ℝ → E →L[ℂ] E) (K : ℝ)
    (_h0 : T 0=ContinuousLinearMap.id ℂ E)
    (_hK : ∀ t ∈ Icc (0:ℝ) 1, ‖T t‖≤K)
    (hc : ∀ v : E, ContinuousOn (fun t => T t v) (Ici (0:ℝ)))
    (ha : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s+t)=(T s).comp (T t))
    (hcircle : ∀ z : ℂ, ‖z‖=1 → z ∈ resolventSet ℂ (T 1)) :
    ∃ D : (ℝ →ᵇ E) →L[ℂ] (ℝ →ᵇ E),
      ∀ f : ℝ →ᵇ E, ∀ τ h : ℝ, 0≤h → h≤1 →
        D f (τ+h)=T h (D f τ)+∫ s in (0:ℝ)..h, T (h-s) (f (τ+s)) := by
  let G := PeriodicResolvent.coeff (PeriodicResolvent.resolventLoop (T 1) 1)
  have hG : Summable (fun n => ‖G n‖) := PeriodicResolvent.green_summable (T 1) zero_lt_one hcircle
  have hrec : ∀ n : ℤ, G (n+1)-T 1*G n=if n=0 then 1 else 0 := by
    simpa only [Complex.ofReal_one,one_smul] using PeriodicResolvent.green_identity (T 1) zero_lt_one hcircle
  let D := (timeGreen G).comp (sourceStep T hc 1 zero_le_one)
  refine ⟨D,fun f τ h hh _ => ?_⟩
  let w : ℝ →ᵇ E := D f
  have hw (t : ℝ) : w (t+1)=T 1 (w t)+duhamel T f 1 t :=
    timeGreen_solves (T 1) G hG hrec (sourceStep T hc 1 zero_le_one f) t
  let R := translate h w-(T h).compLeftContinuousBounded ℝ w-sourceStep T hc h hh f
  have hR : ∀ t : ℝ, R (t+1)=T 1 (R t) := by
    intro t
    have hcomm (v : E) : T 1 (T h v)=T h (T 1 v) := by
      rw [←ContinuousLinearMap.comp_apply,←ha 1 h zero_le_one hh,
        add_comm 1 h,ha h 1 hh zero_le_one,ContinuousLinearMap.comp_apply]
    have hduh := duhamel_commutator T hc ha f hh t
    simp only [R,BoundedContinuousFunction.sub_apply,translate_apply,
      ContinuousLinearMap.compLeftContinuousBounded_apply] 
    change w (t+1+h)-T h (w (t+1))-duhamel T f h (t+1)=
      T 1 (w (t+h)-T h (w t)-duhamel T f h t)
    rw [show t+1+h=t+h+1 by ring,hw (t+h),hw t,(T h).map_add,(T 1).map_sub,(T 1).map_sub,hcomm]
    calc
      _=T 1 (w (t+h))-T h (T 1 (w t))+
          (duhamel T f 1 (t+h)-T h (duhamel T f 1 t)-duhamel T f h (t+1)) := by abel
      _=T 1 (w (t+h))-T h (T 1 (w t))+
          ((duhamel T f h (t+1)-T 1 (duhamel T f h t))-duhamel T f h (t+1)) := by rw [hduh]
      _=_ := by abel
  have hz := homogeneous_time_eq_zero (T 1) hcircle R hR
  have he := congrArg (fun b : ℝ →ᵇ E => b τ) hz
  simp only [R,BoundedContinuousFunction.sub_apply,translate_apply,
    ContinuousLinearMap.compLeftContinuousBounded_apply,
    BoundedContinuousFunction.coe_zero,Pi.zero_apply] at he
  change w (τ+h)-T h (w τ)-duhamel T f h τ=0 at he
  have hes := sub_eq_zero.mp he
  simpa only [w,duhamel,add_comm] using sub_eq_iff_eq_add.mp hes
end AncientMild

end

end OAI
