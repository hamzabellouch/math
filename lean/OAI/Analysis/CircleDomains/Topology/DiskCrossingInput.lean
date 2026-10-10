import OAI.Analysis.CircleDomains.Topology.CircleQuantileArcs
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace OAI

/-!
Pascoletti and Zanolin, *A Crossing Lemma for Annular Regions and Invariant
Sets with an Application to Planar Dynamical Systems*, Journal of Mathematics
(2013), Article 267393, DOI 10.1155/2013/267393, Lemma 7 and Remark 6, p. 3.
In the closed unit disk, two compact connected sets containing four cyclically
alternating boundary points intersect. The rational cut coordinate records
that cyclic order.
-/

open Set Function Metric

noncomputable section
namespace CircleDomainRigidity

def standardCirclePoint (θ : UnitAddCircle) : ℂ :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero θ : Circle)

theorem standardCirclePoint_injective : Injective standardCirclePoint :=
  Subtype.val_injective.comp (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).injective

def UnitDiskAlternatingContinua : Prop :=
  ∀ (A B : Set ℂ), IsCompact A → IsConnected A →
    IsCompact B → IsConnected B →
    A ⊆ closedBall 0 1 → B ⊆ closedBall 0 1 →
    ∀ θ : Fin 4 → UnitAddCircle, StrictMono (unitCircleCut ∘ θ) →
      standardCirclePoint (θ 0) ∈ A → standardCirclePoint (θ 2) ∈ A →
      standardCirclePoint (θ 1) ∈ B → standardCirclePoint (θ 3) ∈ B →
      (A ∩ B).Nonempty

end CircleDomainRigidity

end

end OAI
