import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixStabilizer
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixCommutator
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantSubspaceDeterminant
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Algebra.Polynomial.Roots

namespace OAI

/-! # Scalar commutators of a connected matrix group are trivial

On an invariant subspace a scalar commutator is a root of unity by its
determinant. For each vector its orbit under these commutators is therefore
finite. Polynomial continuity and connectedness make this orbit constant.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {K : Type*} [Field K] {n : ℕ}

def vectorPolynomial (v : Fin n → K) (i : Fin n) : MvPolynomial (Coord n) K :=
  ∑ j, MvPolynomial.X (false, i, j) * MvPolynomial.C (v j)

theorem continuous_vectorAction (v : Fin n → K) :
    Continuous (fun g : PolynomialMatrixGroup K n =>
      (⟨linearAction g v⟩ : AffinePolynomialPoint (Fin n) K)) := by
  have he : (fun g : PolynomialMatrixGroup K n =>
      (⟨linearAction g v⟩ : AffinePolynomialPoint (Fin n) K)) =
      AffinePolynomialPoint.polynomialMap (vectorPolynomial v) ∘ coordinates := by
    funext g
    apply AffinePolynomialPoint.ext
    funext i
    simp [vectorPolynomial, AffinePolynomialPoint.polynomialMap, coordinates,
      linearAction_apply, Matrix.mulVec, dotProduct]
  rw [he]
  exact (AffinePolynomialPoint.continuous_polynomialMap _).comp inducing_coordinates.continuous

theorem finite_power_eq_one (d : ℕ) (hd : 0 < d) : {c : K | c ^ d = 1}.Finite := by
  have hp := Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero hd (1 : K))
  simpa only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using hp

theorem connected_scalar_commutators_trivial
    {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (W : Submodule K (Fin n → K))
    (hW : ∀ g : G, ∀ v ∈ W, linearAction (ι g) v ∈ W)
    (hs : ∀ g h : G, ∃ c : K, ∀ v ∈ W,
      linearAction (ι ⁅g, h⁆) v = c • v) :
    ∀ g h : G, ∀ v ∈ W, linearAction (ι ⁅g, h⁆) v = v := by
  by_cases hWzero : W = ⊥
  · intro g h v hv
    have hv0 : v = 0 := by simpa only [hWzero, Submodule.mem_bot] using hv
    rw [hv0, map_zero]
  let : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).mpr hWzero
  let ρ := linearAction.toMonoidHom.comp ι
  let d := Module.finrank K W
  let Z := {c : K | c ^ d = 1}
  have hZfinite : Z.Finite := finite_power_eq_one d (Module.finrank_pos (R := K) (M := W))
  intro g h v hv
  let f : G → AffinePolynomialPoint (Fin n) K := fun a => ⟨ρ ⁅a, h⁆ v⟩
  have hf : Continuous f := by
    have he : f = fun a : G =>
        (⟨linearAction ⁅ι a, ι h⁆ v⟩ : AffinePolynomialPoint (Fin n) K) := by
      funext a
      dsimp [f, ρ]
      rw [map_commutatorElement]
    rw [he]
    have hc := (continuous_commutator_right (ι h)).comp hι
    exact (continuous_vectorAction v).comp hc
  let T : Set (AffinePolynomialPoint (Fin n) K) :=
    (fun c : K => (⟨c • v⟩ : AffinePolynomialPoint (Fin n) K)) '' Z
  have hTfinite : T.Finite := hZfinite.image _
  have hmap : Set.MapsTo f Set.univ T := by
    intro a _
    obtain ⟨c, hc⟩ := hs a h
    have hroot : c ^ d = 1 := scalar_commutator_root_of_unity ρ W hW a h c hc
    exact ⟨c, hroot, congrArg AffinePolynomialPoint.mk (hc v hv).symm⟩
  have hfg : f g = f 1 := isPreconnected_univ.constant_of_mapsTo
    hTfinite.isDiscrete hf.continuousOn hmap (Set.mem_univ g) (Set.mem_univ 1)
  have he := congrArg AffinePolynomialPoint.coord hfg
  simp only [f, commutatorElement_one_left, map_one] at he
  exact he

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
