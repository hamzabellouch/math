import OAI.Analysis.CircleDomains.Transfer.ModelPriorityPairs
import OAI.Analysis.CircleDomains.Rigidity.ModelCompactHeightTrace
import OAI.Analysis.CircleDomains.Selection.AppendedScalarPairs
import OAI.Analysis.CircleDomains.Rigidity.SphereTracePairNull

namespace OAI

/-! The actual compact source priority and height coordinates preserve
every trace-pair condition when appended to the flattened old list. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def compactHeightSource (M : CompactScalarModel G u) {R d : ℝ}
    (H : ControlledHeight R d) (T : ℝ → ℝ) (η : EuclideanPlane → ℝ) : EuclideanPlane → ℝ :=
  fun x => sphereFromPlaneFunction (fun y => η y*T (H.height (complexPlaneCoordinates y)))
    (invFun M.projection (planeSphere x))

 def compactPrioritySource (M : CompactScalarModel G u)
    (χ : ℕ → ℂ → ℝ) (c : ℕ → ℝ) (η : ℂ → ℝ) : EuclideanPlane → ℝ :=
  fun x => η (complexPlaneCoordinates x)*priorityInfiniteValue
    (fun n => χ n (complexPlaneCoordinates x)) c
    (M.horizontalSection (complexPlaneCoordinates x : Sphere))

 theorem compact_appended_trace_pairs (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hpairs : ∀ i j, i ≠ j → volume ((fun p =>
      (sphereFromPlaneFunction (u i) p,sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0)
    (O : Fin m → Set ℝ) (hO : ∀ i, MeasurableSet (O i))
    (V : Set ℝ) (hV : MeasurableSet V) (χ : ℕ → ℂ → ℝ) (c : ℕ → ℝ)
    (hOld : ∀ i n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (χ n),
      flattenValues (O i) (sphereFromPlaneFunction (u i) (z : Sphere)) = a)
    (hHeight : ∀ n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (χ n),
      flattenValues V (M.heightSection H (z : Sphere)) = a)
    (η : ℂ → ℝ) (hη : ∀ z : ℂ, (z : Sphere) ∉ G → η z = 1)
    (θ : EuclideanPlane → ℝ)
    (hθ : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1) :
    let t := appendScalarPair (fun i => flattenValues (O i) ∘ u i)
      (M.compactPrioritySource χ c η) (M.compactHeightSource H (flattenValues V) θ)
    ∀ i j, i ≠ j → volume ((fun p =>
      (sphereFromPlaneFunction (t i) p,sphereFromPlaneFunction (t j) p)) '' Gᶜ) = 0 := by
  dsimp only
  let uf := fun i => flattenValues (O i) ∘ u i
  let p := M.compactPrioritySource χ c η
  let q := M.compactHeightSource H (flattenValues V) θ
  have heq (z : ℂ) (hz : (z : Sphere) ∉ G) :
      sphereFromPlaneFunction q (z : Sphere) = flattenValues V (M.heightSection H (z : Sphere)) := by
    simpa only [q, compactHeightSource, sphereFromPlaneFunction_coe, planeSphere,
      complexPlaneCoordinates.apply_symm_apply] using
      M.compact_height_trace hsard hsch hG hconn hinf hTD H (flattenValues V) θ hθ hz
  have hep (z : ℂ) (hz : (z : Sphere) ∉ G) :
      sphereFromPlaneFunction p (z : Sphere) = priorityInfiniteValue (fun n => χ n z) c
        (M.horizontalSection (z : Sphere)) := by
    simp only [p, compactPrioritySource, sphereFromPlaneFunction_coe,
      complexPlaneCoordinates.apply_symm_apply, hη z hz, one_mul]
  obtain ⟨hnew, hqp⟩ := M.flattened_priority_trace_pairs hsard hsch hcoarea
    hG hconn hinf hTD hu hs H hHz O hO V hV χ c hOld hHeight
  have hold (i j : Fin m) (hij : i ≠ j) : volume ((fun z =>
      (sphereFromPlaneFunction (uf i) z,sphereFromPlaneFunction (uf j) z)) '' Gᶜ) = 0 := by
    simpa only [uf, sphereFromPlaneFunction_flatten] using
      flattened_pair_null (hpairs i j hij) (hO i) (hO j)
  have hq (i : Fin m) : volume ((fun z =>
      (sphereFromPlaneFunction (uf i) z,sphereFromPlaneFunction q z)) '' Gᶜ) = 0 := by
    apply sphere_trace_pair_null_of_plane hinf
    convert (hnew i).1 using 1
    congr 1
    apply image_congr
    intro z hz
    simp only [uf, sphereFromPlaneFunction_flatten, heq z hz]
  have hp (i : Fin m) : volume ((fun z =>
      (sphereFromPlaneFunction (uf i) z,sphereFromPlaneFunction p z)) '' Gᶜ) = 0 := by
    apply sphere_trace_pair_null_of_plane hinf
    convert (hnew i).2 using 1
    congr 1
    apply image_congr
    intro z hz
    simp only [uf, sphereFromPlaneFunction_flatten, hep z hz]
  have hqp' : volume ((fun z => (sphereFromPlaneFunction q z,sphereFromPlaneFunction p z)) '' Gᶜ) = 0 := by
    apply sphere_trace_pair_null_of_plane hinf
    convert hqp using 1
    congr 1
    apply image_congr
    intro z hz
    simp only [heq z hz, hep z hz]
  have ha := appendScalarPair_pair_null (fun i => sphereFromPlaneFunction (uf i))
    (sphereFromPlaneFunction p) (sphereFromPlaneFunction q) hold hp hq hqp'
  intro i j hij
  convert ha i j hij using 1
  congr 1
  apply image_congr
  intro z _
  have hc (k : Fin (m+2)) : sphereFromPlaneFunction (appendScalarPair uf p q k) z =
      appendScalarPair (fun i => sphereFromPlaneFunction (uf i))
        (sphereFromPlaneFunction p) (sphereFromPlaneFunction q) k z := by
    refine Fin.cases rfl (fun l => ?_) k
    exact Fin.cases rfl (fun _ => rfl) l
  exact congrArg₂ Prod.mk (hc i) (hc j)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
