import OAI.Analysis.BoundedHochschild.TracialTypeIHomogeneousPiece
import OAI.Analysis.BoundedHochschild.CentralTypeIIInheritance

namespace OAI

/-! Transport of the homogeneous pieces used in the finite type I partition. -/

noncomputable section

namespace HochschildMatrixSystems.MatrixSystem

variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N] {n : ℕ}

def mapEquiv (E : HochschildMatrixSystems.MatrixSystem M n) (φ : M ≃⋆ₐ[ℂ] N) :
    HochschildMatrixSystems.MatrixSystem N n where
  entry i j := φ (E.entry i j)
  star_entry i j := by rw [← map_star, E.star_entry]
  entry_mul i j k l := by rw [← map_mul, E.entry_mul]; split_ifs <;> simp
  sum_diagonal := by rw [← map_sum, E.sum_diagonal, map_one]

end HochschildMatrixSystems.MatrixSystem

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners HochschildMatrixSystems FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma abelian_map_equiv {N : Type*} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
    (φ : M ≃⋆ₐ[ℂ] N) {p : M} (hp : AbelianProjection p) : AbelianProjection (φ p) :=
  finitePath_abelian_of_popa (hp.1.map φ)
    (abelianProjection_map_equiv φ hp.1 (popa_abelian_of_finitePath hp))

def projectionInCorner {z p : M} (hz : IsStarProjection z) (hp : IsStarProjection p)
    (hpz : p ≤ z) : Corner z hz := ⟨p, projection_mem_corner hz hp hpz⟩

lemma projectionInCorner_abelian {z p : M} (hz : IsStarProjection z)
    (hp : AbelianProjection p) (hpz : p ≤ z) :
    AbelianProjection (projectionInCorner hz hp.1 hpz) := by
  refine ⟨⟨Subtype.ext hp.1.isIdempotentElem.eq, Subtype.ext hp.1.isSelfAdjoint.star_eq⟩, ?_⟩
  intro a b
  exact Subtype.ext (hp.2 (a : M) (b : M)).eq

lemma centralSupport_in_corner {z p : M} (hz : IsStarProjection z)
    (hzc : ∀ a : M, z * a = a * z) (hp : IsStarProjection p) (h : IsCentralSupport p z) :
    IsCentralSupport (projectionInCorner hz hp h.2.1) (1 : Corner z hz) := by
  refine ⟨⟨IsStarProjection.one _, fun _ => Commute.one_left _⟩, ?_, ?_⟩
  · exact (show IsStarProjection (projectionInCorner hz hp h.2.1) from
      ⟨Subtype.ext hp.isIdempotentElem.eq, Subtype.ext hp.isSelfAdjoint.star_eq⟩).le_one
  · intro c hc hcp
    have hcM : CentralProjection (c : M) :=
      ⟨corner_projection_coe z hz hc.1,
        fun a => centralCorner_central hz hzc c (fun b => (hc.2 b).eq) a⟩
    have hcpM : (c : M) * p = 0 := congrArg Subtype.val hcp
    have hcz := h.2.2 (c : M) hcM hcpM
    have hc0 : c = 0 := by
      apply Subtype.ext
      change (c : M) = 0
      simpa only [c.property.2] using hcz
    simp only [hc0, zero_mul]

lemma homogeneousCorner_to_ambient {z : M} (hz : IsStarProjection z)
    (q : Corner z hz) (hq : HomogeneousTypeICorner q) :
    HomogeneousTypeICorner (q : M) := by
  obtain ⟨hqp, n, E, i, hi⟩ := hq
  let φ := nestedCornerEquiv hz q hqp
  exact ⟨corner_projection_coe z hz hqp, n, E.mapEquiv φ, i, abelian_map_equiv φ hi⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
