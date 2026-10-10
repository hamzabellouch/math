import OAI.Analysis.BoundedHochschild.TypeIMatrixColumns
import OAI.Analysis.BoundedHochschild.CentralSupportCuts
import OAI.Analysis.BoundedHochschild.FiniteProjectionExtension

namespace OAI

/-! Concrete finite homogeneous central corners and their matrix columns. -/

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners HochschildComparison HochschildMatrixSystems FinitePathMain

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def HomogeneousTypeICorner (z : M) : Prop :=
  ∃ (hz : IsStarProjection z) (n : ℕ) (E : MatrixSystem (Corner z hz) n) (i : Fin n),
    AbelianProjection (E.entry i i)

def partialIsoInCorner {z : M} (hz : IsStarProjection z) (v : PartialIso M)
    (hi : v.initial ≤ z) (hf : v.final ≤ z) : PartialIso (Corner z hz) where
  val := ⟨(v : M), partialIso_left_support hz v hf, partialIso_right_support hz v hi⟩
  mul_star_mul := Subtype.ext v.mul_star_mul

@[simp] lemma partialIsoInCorner_initial {z : M} (hz : IsStarProjection z)
    (v : PartialIso M) (hi : v.initial ≤ z) (hf : v.final ≤ z) :
    ((partialIsoInCorner hz v hi hf).initial : M) = v.initial := rfl

@[simp] lemma partialIsoInCorner_final {z : M} (hz : IsStarProjection z)
    (v : PartialIso M) (hi : v.initial ≤ z) (hf : v.final ≤ z) :
    ((partialIsoInCorner hz v hi hf).final : M) = v.final := rfl

theorem homogeneousCorner_of_columns {z p : M} (hz : IsStarProjection z)
    (hp : AbelianProjection p) (hpz : p ≤ z) {n : ℕ} (i : Fin n)
    (v : Fin n → PartialIso M) (hi : ∀ j, (v j).initial = p)
    (hf : ∀ j, (v j).final ≤ z)
    (ho : ∀ j k, j ≠ k → (v j).final * (v k).final = 0)
    (hs : ∑ j, (v j).final = z) : HomogeneousTypeICorner z := by
  let pC : Corner z hz := ⟨p, (hp.1.le_iff_mul_eq_right hz).mp hpz,
    (hp.1.le_iff_mul_eq_left hz).mp hpz⟩
  have hpC : IsStarProjection pC :=
    ⟨Subtype.ext hp.1.isIdempotentElem.eq, Subtype.ext hp.1.isSelfAdjoint.star_eq⟩
  let w (j : Fin n) := partialIsoInCorner hz (v j) (by rw [hi]; exact hpz) (hf j)
  have hwi (j : Fin n) : (w j).initial = pC := Subtype.ext (hi j)
  have hwo (j k : Fin n) (hjk : j ≠ k) : (w j).final * (w k).final = 0 :=
    Subtype.ext (ho j k hjk)
  have hws : ∑ j, (w j).final = 1 := by
    apply Subtype.ext
    change CentralCorner.includeMap z hz (∑ j, (w j).final) = z
    rw [map_sum]
    exact hs
  let E := matrixSystemOfColumns w hwi hwo hws
  refine ⟨hz, n, E, i, matrixSystemOfColumns_abelian w hwi hwo hws hpC ?_ i⟩
  intro a b
  apply Subtype.ext
  apply Subtype.ext
  have hcut (c : PopaCorner.algebra hpC) : p * ((c : Corner z hz) : M) * p =
      ((c : Corner z hz) : M) := by
    have hl := congrArg (fun a : Corner z hz => (a : M)) c.property.1
    have hr := congrArg (fun a : Corner z hz => (a : M)) c.property.2
    change p * ((c : Corner z hz) : M) = ((c : Corner z hz) : M) at hl
    change ((c : Corner z hz) : M) * p = ((c : Corner z hz) : M) at hr
    rw [hl, hr]
  change ((a : Corner z hz) : M) * ((b : Corner z hz) : M) =
    ((b : Corner z hz) : M) * ((a : Corner z hz) : M)
  simpa only [hcut] using (hp.2 ((a : Corner z hz) : M) ((b : Corner z hz) : M)).eq

end KadisonRingrose
end BoundedHochschild

end

end OAI
