import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryTwist
import OAI.NumberTheory.PiExponent.Ampleness.FiniteAffineFrames
import OAI.NumberTheory.PiExponent.Approximation.PushforwardSectionComparison

namespace OAI

namespace PiExponent.GeometrySupport.ExceptionalRecoveryMap
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque
open CechHigher
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)

private theorem intersection_one {J : Type} (U : J → X.Opens) (t : Fin 1 → J) :
    intersection U t = U (t 0) := by
  apply le_antisymm (iInf_le _ 0)
  apply le_iInf
  intro i
  exact le_of_eq (congrArg (fun j => U (t j)) (Subsingleton.elim 0 i))

private theorem intersection_two {J : Type} (U : J → X.Opens) (t : Fin 2 → J) :
    intersection U t = U (t 0) ⊓ U (t 1) := by
  apply le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1))
  apply le_iInf
  intro i
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right

theorem eventual_comparison_of_affine_recovery [CompactSpace X] [X.IsSeparated]
    (A : LineBundle X)
    (hrecover : ∀ U : X.affineOpens, ∃ N, ∀ n, N ≤ n →
      Function.Bijective ((ordinaryMap f I E ι hE n).app U.1)) :
    ∃ k : ℕ, ∃ U : Fin k → X.affineOpens, (⨆ i, (U i).1) = ⊤ ∧
      ∃ N, ∀ n, N ≤ n → Nonempty
        (CechH1Transfer.SectionComparison (fun i => (U i).1)
          (fun i => f ⁻¹ᵁ (U i).1)
          ((moduleTwistFunctor A n).obj (closedModule (I^n)))
          ((E.tensor (A.pullback f)).pow n).sheaf) := by
  classical
  obtain ⟨k,U,hcover,hframe⟩ := A.finite_affine_frame_cover
  let V : Fin k → X.Opens := fun i => (U i).1
  have ha1 (t : Fin 1 → Fin k) : IsAffineOpen (intersection V t) :=
    (intersection_one V t).symm ▸ (U (t 0)).2
  have ha2 (t : Fin 2 → Fin k) : IsAffineOpen (intersection V t) :=
    (intersection_two V t).symm ▸ (U (t 0)).2.inf (U (t 1)).2
  choose Nv hv using fun t : Fin 1 → Fin k => hrecover ⟨intersection V t, ha1 t⟩
  choose Np hp using fun t : Fin 2 → Fin k => hrecover ⟨intersection V t, ha2 t⟩
  let Bv := Finset.univ.sup Nv
  let Bp := Finset.univ.sup Np
  refine ⟨k,U,hcover,Bv ⊔ Bp,?_⟩
  intro n hn
  let β := twistedMap f I E ι hE A n
  have hvn (t : Fin 1 → Fin k) : Function.Bijective (β.app (intersection V t)) := by
    exact twistedMap_app_bijective f I E ι hE A n (intersection V t)
      (restrictOpenFrame (iInf_le _ 0) (Classical.choice (hframe (t 0))))
      (hv t n ((Finset.le_sup (Finset.mem_univ t)).trans (le_sup_left.trans hn)))
  have hpn (t : Fin 2 → Fin k) : Function.Injective (β.app (intersection V t)) := by
    exact (twistedMap_app_bijective f I E ι hE A n (intersection V t)
      (restrictOpenFrame (iInf_le _ 0) (Classical.choice (hframe (t 0))))
      (hp t n ((Finset.le_sup (Finset.mem_univ t)).trans (le_sup_right.trans hn)))).injective
  exact ⟨PushforwardOpenSections.comparison f β V hvn hpn⟩

end
end PiExponent.GeometrySupport.ExceptionalRecoveryMap

end OAI
