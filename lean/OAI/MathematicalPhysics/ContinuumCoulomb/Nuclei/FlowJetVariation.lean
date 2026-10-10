import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowJetCoordinates

namespace OAI

/-! The closed-interval variational equation through order four, obtained
by differentiating the path-space integral equation. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb
open WeakMTWTransport

theorem flow_model_jet_derivative (H K : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (hK : ContDiff ℝ 4 K)
    (O : Set Position) (hO : IsOpen O) (x : Position) (hx : x ∈ O)
    (hODE : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => H (s,y)) (K (t,y)) t)
    (n : ℕ) (hn : n ≤ 4) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun s => iteratedFDeriv ℝ n (fun y => H (s,y)) x)
      (iteratedFDeriv ℝ n (fun y => K (t,y)) x) (Icc (0:ℝ) 1) t := by
  apply spatialJet_hasDerivWithinAt n _ _ _ t ht
  intro e
  let q : SpatialPath := iteratedFDeriv ℝ n (modelPath K hK.continuous) x e
  let c : Position := iteratedFDeriv ℝ n (fun y => H (0,y)) x e
  have heq (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      iteratedFDeriv ℝ n (fun y => H (s,y)) x e =
        c + ∫ r in (0:ℝ)..s, extendUnitPath q r := by
    rw [←modelPath_iterated_apply H hH n hn x e ⟨s,hs⟩]
    have hi := congrArg (fun p : SpatialPath => p ⟨s,hs⟩)
      (flow_model_jet_integral H K hH hK O hO x hx hODE n hn e)
    exact hi
  have hd := (hasDerivAt_unitPathPrimitive q t).const_add c
  have hdval : extendUnitPath q t = iteratedFDeriv ℝ n (fun y => K (t,y)) x e := by
    rw [show extendUnitPath q t = q ⟨t,ht⟩ from extendUnitPath_coe q ⟨t,ht⟩]
    exact modelPath_iterated_apply K hK n hn x e ⟨t,ht⟩
  rw [hdval] at hd
  exact hd.hasDerivWithinAt.congr_of_mem heq ht

end ContinuumCoulomb

end

end OAI
