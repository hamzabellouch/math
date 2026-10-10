import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildPointwise

namespace OAI

/-! Compatibility and spatial regularity of the effective heat source. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Set ShearFlows
open scoped Topology ContDiff BigOperators

theorem directionalPath_truncate {T : ℝ} (k n : ℕ) (hkn : k ≤ n) (v : Plane)
    (u : WeaklySingular.Path (Jet (n+1)) T) :
    truncatePath k n hkn T (directionalPath n v T u) =
      directionalPath k v T (truncatePath (k+1) (n+1) (Nat.add_le_add_right hkn 1) T u) := by
  apply (WeaklySingular.pathEquiv (Jet k) T).injective
  apply ContinuousMap.ext
  intro t
  exact BoundedSpatialJets.directionalDerivativeCLM_truncate Plane ℝ k n hkn v (u t)

private theorem map_add_add_sum {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (P : E →L[ℝ] F)
    (a b : E) (v : Fin 2 → E) :
    P (a+b+∑ j, v j) = P a+P b+∑ j, P (v j) := by
  rw [map_add, map_add, map_sum]

namespace CompatibleData

private theorem product_solution_truncate {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k n : ℕ) (hkn : k ≤ n) (i : Fin 3) :
    truncatePath k n hkn T (productPath n (D.coefficient n i) (D.solutionJet hT hν n)) =
      productPath k (D.coefficient k i) (D.solutionJet hT hν k) :=
  (productPath_truncate k n hkn _ _ (D.coefficient_truncate k n hkn i) _).trans
    (congrArg (productPath k (D.coefficient k i)) (D.solutionJet_truncate hT hν k n hkn))

private theorem directional_product_truncate {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k n : ℕ) (hkn : k ≤ n) (j : Fin 2) :
    truncatePath k n hkn T (directionalPath n (Pi.single j 1) T
      (productPath (n+1) (D.coefficient (n+1) j.succ) (D.solutionJet hT hν (n+1)))) =
      directionalPath k (Pi.single j 1) T
        (productPath (k+1) (D.coefficient (k+1) j.succ) (D.solutionJet hT hν (k+1))) :=
  (directionalPath_truncate k n hkn (Pi.single j 1) _).trans
    (congrArg (directionalPath k (Pi.single j 1) T)
      (D.product_solution_truncate hT hν (k+1) (n+1) (Nat.add_le_add_right hkn 1) j.succ))

/-- The effective source represents the same function at every jet order. -/
theorem effectiveSource_truncate {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k n : ℕ) (hkn : k ≤ n) :
    truncatePath k n hkn T (D.effectiveSource hT hν n) = D.effectiveSource hT hν k := by
  let P := truncatePath k n hkn T
  exact (map_add_add_sum P (D.source n)
    (productPath n (D.coefficient n 0) (D.solutionJet hT hν n))
    (fun j => directionalPath n (Pi.single j 1) T
      (productPath (n+1) (D.coefficient (n+1) j.succ) (D.solutionJet hT hν (n+1))))).trans
    (congrArg₂ (fun u v : WeaklySingular.Path (Jet k) T => u+v)
      (congrArg₂ (fun u v : WeaklySingular.Path (Jet k) T => u+v)
        (D.source_truncate k n hkn) (D.product_solution_truncate hT hν k n hkn 0))
      (Finset.sum_congr rfl (fun j _ => D.directional_product_truncate hT hν k n hkn j)))

/-- The common scalar effective source. -/
def effectiveSourceValue {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (t : Icc (0 : ℝ) T) (x : Plane) : ℝ :=
  BoundedSpatialJets.function Plane ℝ 0 (D.effectiveSource hT hν 0 t) x

theorem effectiveSourceValue_eq {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) (t : Icc (0 : ℝ) T) (x : Plane) :
    D.effectiveSourceValue hT hν t x =
      BoundedSpatialJets.function Plane ℝ k (D.effectiveSource hT hν k t) x := by
  have he := congrArg (fun u : WeaklySingular.Path (Jet 0) T =>
    BoundedSpatialJets.function Plane ℝ 0 (u t) x)
    (D.effectiveSource_truncate hT hν 0 k (Nat.zero_le k))
  change BoundedSpatialJets.function Plane ℝ 0
    (BoundedSpatialJets.truncate Plane ℝ 0 k (Nat.zero_le k) (D.effectiveSource hT hν k t)) x =
      D.effectiveSourceValue hT hν t x at he
  rw [BoundedSpatialJets.function_truncate] at he
  exact he.symm

/-- The effective source has smooth spatial slices, obtained from the compatible finite jets. -/
theorem effectiveSource_smooth {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (D.effectiveSourceValue hT hν t) := by
  apply contDiff_infty.mpr
  intro k
  have he : D.effectiveSourceValue hT hν t =
      BoundedSpatialJets.function Plane ℝ k (D.effectiveSource hT hν k t) := by
    funext x
    exact D.effectiveSourceValue_eq hT hν k t x
  rw [he]
  exact BoundedSpatialJets.function_contDiff Plane ℝ k _

/-- Every spatial derivative of the effective source varies jointly continuously. -/
theorem effectiveSource_spatial_continuous {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) T × Plane =>
      iteratedFDeriv ℝ k (D.effectiveSourceValue hT hν p.1) p.2) := by
  let u := D.effectiveSource hT hν k
  let i : Fin (k+1) := ⟨k, Nat.lt_succ_self k⟩
  have hc : Continuous (fun t : Icc (0 : ℝ) T => (u t).val i) :=
    (BoundedSpatialJets.projection Plane ℝ k i).continuous.comp
      (WeaklySingular.pathEquiv (Jet k) T u).continuous
  have he (t : Icc (0 : ℝ) T) : D.effectiveSourceValue hT hν t =
      BoundedSpatialJets.function Plane ℝ k (u t) := by
    funext x
    exact D.effectiveSourceValue_eq hT hν k t x
  have hj : (fun p : Icc (0 : ℝ) T × Plane =>
      iteratedFDeriv ℝ k (D.effectiveSourceValue hT hν p.1) p.2) =
      (fun p => (u p.1).val i p.2) := by
    funext p
    rw [he p.1]
    exact congrFun (BoundedSpatialJets.iteratedFDeriv_function Plane ℝ k (u p.1) k le_rfl) p.2
  rw [hj]
  exact (hc.comp continuous_fst).eval continuous_snd

end CompatibleData
end ForcedComputation.PlaneScalarMild

end

end OAI
