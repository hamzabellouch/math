import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixStabilizer
import OAI.GroupTheory.PolycyclicRecognition.Algebra.QuotientLinearAction

namespace OAI

/-! # Polynomial coordinates for induced quotient actions

Choose lifts of a quotient basis. Every forward and inverse matrix entry
of the induced action is then one linear functional of an ambient translate.
This gives continuity for the concrete polynomial matrix topology.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {K G U : Type*} [Field K] [Group G] [AddCommGroup U] [Module K U]
    {m n : ℕ}

def coordinateLinearAction (ρ : G →* (U ≃ₗ[K] U)) (e : U ≃ₗ[K] (Fin m → K)) :
    G →* PolynomialMatrixGroup K m where
  toFun g := linearAction.symm ((e.symm.trans (ρ g)).trans e)
  map_one' := by
    apply linearAction.injective
    apply LinearEquiv.ext
    intro v
    simp
  map_mul' g h := by
    apply linearAction.injective
    apply LinearEquiv.ext
    intro v
    simp [LinearEquiv.mul_apply]

@[simp] theorem coordinateLinearAction_apply (ρ : G →* (U ≃ₗ[K] U))
    (e : U ≃ₗ[K] (Fin m → K)) (g : G) (v : Fin m → K) :
    linearAction (coordinateLinearAction ρ e g) v = e (ρ g (e.symm v)) := by
  simp [coordinateLinearAction]

theorem coordinateLinearAction_entries (ρ : G →* (U ≃ₗ[K] U))
    (e : U ≃ₗ[K] (Fin m → K)) (g : G) (i j : Fin m) :
    entries (coordinateLinearAction ρ e g) i j =
      e (ρ g (e.symm (Pi.single j 1))) i := by
  rw [← coordinateLinearAction_apply, linearAction_apply, Matrix.mulVec_single_one]
  rfl

def functionalPolynomialAt (b : Bool) (φ : Module.Dual K (Fin n → K))
    (v : Fin n → K) : MvPolynomial (Coord n) K :=
  ∑ i, ∑ j, MvPolynomial.C (φ (fun k => if i = k then 1 else 0)) *
    MvPolynomial.X (b, i, j) * MvPolynomial.C (v j)

theorem eval_functionalPolynomialAt (b : Bool) (φ : Module.Dual K (Fin n → K))
    (v : Fin n → K) (g : PolynomialMatrixGroup K n) :
    MvPolynomial.eval (coordinates g).coord (functionalPolynomialAt b φ v) =
      φ (linearAction (if b then g⁻¹ else g) v) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    rw [linearAction_apply, LinearMap.pi_apply_eq_sum_univ] <;>
    simp [functionalPolynomialAt, coordinates, Matrix.mulVec,
      dotProduct, Finset.sum_mul,
      mul_assoc, mul_comm, mul_left_comm]

theorem continuous_quotientLinearAction
    [TopologicalSpace G] (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (W : Submodule K (Fin n → K))
    (hW : ∀ g : G, ∀ v ∈ W, linearAction (ι g) v ∈ W)
    (e : ((Fin n → K) ⧸ W) ≃ₗ[K] (Fin m → K)) :
    Continuous (coordinateLinearAction
      (quotientLinearAction (linearAction.toMonoidHom.comp ι) W hW) e) := by
  let ρ := quotientLinearAction (linearAction.toMonoidHom.comp ι) W hW
  let v (j : Fin m) : Fin n → K :=
    Function.surjInv W.mkQ_surjective (e.symm (Pi.single j 1))
  have hv (j : Fin m) : W.mkQ (v j) = e.symm (Pi.single j 1) :=
    Function.rightInverse_surjInv W.mkQ_surjective _
  let φ (i : Fin m) : Module.Dual K (Fin n → K) :=
    (LinearMap.proj i).comp (e.toLinearMap.comp W.mkQ)
  let p (s : Coord m) : MvPolynomial (Coord n) K :=
    functionalPolynomialAt s.1 (φ s.2.1) (v s.2.2)
  apply inducing_coordinates.continuous_iff.mpr
  have he : coordinates ∘ coordinateLinearAction ρ e =
      AffinePolynomialPoint.polynomialMap p ∘ coordinates ∘ ι := by
    funext g
    apply AffinePolynomialPoint.ext
    funext ⟨b, i, j⟩
    change (if b then entries ((coordinateLinearAction ρ e g)⁻¹) i j
      else entries (coordinateLinearAction ρ e g) i j) =
      MvPolynomial.eval (coordinates (ι g)).coord
        (functionalPolynomialAt b (φ i) (v j))
    rw [eval_functionalPolynomialAt]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, ← map_inv,
      coordinateLinearAction_entries]
    · rw [← hv j]
      rfl
    · rw [← hv j]
      rfl
  rw [he]
  exact ((AffinePolynomialPoint.continuous_polynomialMap p).comp
    inducing_coordinates.continuous).comp hι

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
