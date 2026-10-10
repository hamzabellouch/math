import OAI.Analysis.CircleDomains.Rigidity.ModelSourceTracePairs
import OAI.Analysis.CircleDomains.Rigidity.PriorityTracePairs

namespace OAI

/-! Every new pair in the actual two-coordinate append operation is null.
The support constancy is precisely the common flattened neighborhood
property used when choosing the cutoffs. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem flattened_priority_trace_pairs (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0)
    (O : Fin m → Set ℝ) (hO : ∀ i, MeasurableSet (O i))
    (V : Set ℝ) (hV : MeasurableSet V) (χ : ℕ → ℂ → ℝ) (c : ℕ → ℝ)
    (hOld : ∀ i n, ∃ a : ℝ, ∀ q ∈ {q : ℂ | (q : Sphere) ∉ G} ∩ support (χ n),
      flattenValues (O i) (sphereFromPlaneFunction (u i) (q : Sphere)) = a)
    (hHeight : ∀ n, ∃ a : ℝ, ∀ q ∈ {q : ℂ | (q : Sphere) ∉ G} ∩ support (χ n),
      flattenValues V (M.heightSection H (q : Sphere)) = a) :
    let B := {q : ℂ | (q : Sphere) ∉ G}
    let U := fun (i : Fin m) (q : ℂ) => flattenValues (O i) (sphereFromPlaneFunction (u i) (q : Sphere))
    let Q := fun q : ℂ => flattenValues V (M.heightSection H (q : Sphere))
    let P := fun q : ℂ => priorityInfiniteValue (fun n => χ n q) c (M.horizontalSection (q : Sphere))
    (∀ i, volume ((fun q => (U i q, Q q)) '' B) = 0 ∧
      volume ((fun q => (U i q, P q)) '' B) = 0) ∧
      volume ((fun q => (Q q, P q)) '' B) = 0 := by
  constructor
  · intro i
    obtain ⟨hh, hx⟩ := M.source_height_trace_pairs hsard hsch hcoarea
      hG hconn hinf hTD hu hs H hHz i
    constructor
    · exact coordinate_lipschitz_pair_null hh
        (flattenValues_lipschitz (hO i)) (flattenValues_lipschitz hV)
    · apply priority_trace_pair_null χ c _ _
        (coordinate_lipschitz_pair_null hx (flattenValues_lipschitz (hO i)) LipschitzWith.id)
      exact hOld i
  · apply priority_trace_pair_null χ c _ _
      (coordinate_lipschitz_pair_null
        (M.source_height_horizontal_pair hsard hsch hcoarea hG hconn hinf hTD H hHz)
        (flattenValues_lipschitz hV) LipschitzWith.id)
    exact hHeight

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
