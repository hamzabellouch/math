import OAI.Analysis.CircleDomains.Reflection.SmoothReflectedApproximation
import OAI.Analysis.CircleDomains.Reflection.ReflectedApproximationLimit
import OAI.Analysis.CircleDomains.Uniformization.ComplexRectangleLocalLimit
import OAI.Analysis.CircleDomains.Sobolev.RectangularL2

namespace OAI

/-! The actual principal map conjugates every generating circular reflection
to an antiholomorphic map away from its one pole. Vanishing smooth
coefficient defects give the local Morera identity. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma reflectedLimit_holomorphic (D : AnalyticReflectionData C) (i : I) :
    DifferentiableOn ℂ (D.reflectedLimit i) ({D.principal (D.center i)}ᶜ) := by
  intro z hz
  obtain ⟨V,hV,hzV,hVU,hK⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton : IsCompact ({z} : Set ℂ)) isOpen_compl_singleton
    (singleton_subset_iff.mpr hz)
  have hpole : D.principal (D.center i)∉closure V := fun h => hVU h rfl
  obtain ⟨q,hq,he⟩ := D.reflection_target_error i hK hpole
  have hs := (D.eventually_reflectedApproximation_contDiffOn i hK hpole).mono
    (fun n hn => hn.mono subset_closure)
  have hl := (D.reflectedApproximation_tendsto i).mono (subset_closure.trans hVU)
  have hh : DifferentiableOn ℂ (D.reflectedLimit i) V := by
    apply differentiableOn_of_local_rectangle_errors hV hs hl
    intro a b hab
    apply (tendsto_doubleIntervalIntegral_L2 hq a.re b.re a.im b.im).congr'
    filter_upwards [he] with n hn
    apply (doubleIntervalIntegral_congr_ae a b ?_).symm
    filter_upwards [hn] with w hw hwR
    exact hw (subset_closure (hab hwR))
  exact (hh.differentiableAt (hV.mem_nhds (hzV (mem_singleton z)))).differentiableWithinAt

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
