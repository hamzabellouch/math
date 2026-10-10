import OAI.Analysis.BoundedHochschild.FiniteTypeIVanishing

namespace OAI

/-!
# The remaining properly infinite input

The finite case is proved. The maximal finite central cut reduces the
classical vanishing input to algebras with no nonzero finite central summand,
the properly infinite case of Christensen--Effros--Sinclair (1987), as
recorded in Christensen--Pop--Sinclair--Smith (2003), p. 636, equation (1.1).
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners

universe u

def NoFiniteCentralSummand (M : Type u) [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] : Prop :=
  ∀ (p : M) (hp : IsStarProjection p), (∀ a : M, p * a = a * p) →
    FiniteAlgebra (Corner p hp) → p = 0

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma noTypeII1_centralCorner (hM : NoTypeII1Summand M) {p : M}
    (hp : IsStarProjection p) (hc : ∀ a : M, p * a = a * p) :
    NoTypeII1Summand (Corner p hp) := by
  intro z hz hzc hfin hII
  have hzM := corner_projection_coe p hp hz
  have hzcM := centralCorner_central hp hc z hzc
  have hfinM : FiniteAlgebra (Corner (z : M) hzM) :=
    (finiteCorner_iff (z : M) hzM).mp
      (finiteCorner_trans hp z ((finiteCorner_iff z hz).mpr hfin))
  have hIIM := noTypeICentralPart_map_equiv (nestedCornerEquiv hp z hz) hII
  exact Subtype.ext (hM (z : M) hzM hzcM hfinM hIIM)

theorem exists_finite_central_cut_noFiniteSummand (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ (p : M) (hp : IsStarProjection p), (∀ a : M, p * a = a * p) ∧
      FiniteAlgebra (Corner p hp) ∧ NoFiniteCentralSummand (Corner (1 - p) hp.one_sub) := by
  obtain ⟨p, hp, hc, hfin, hmax⟩ := exists_maximal_finite_central_cut e
  refine ⟨p, hp, hc, (finiteCorner_iff p hp).mp hfin, ?_⟩
  intro q hq hqc hqfin
  have hcc (a : M) : (1 - p) * a = a * (1 - p) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc]
  have hqM := corner_projection_coe (1 - p) hp.one_sub hq
  have hqcM := centralCorner_central hp.one_sub hcc q hqc
  have hqfinM := finiteCorner_trans hp.one_sub q ((finiteCorner_iff q hq).mpr hqfin)
  exact Subtype.ext (hmax (q : M) hqM hqcM hqfinM (corner_projection_le _ _ hq))

end BoundedHochschild.KadisonRingrose

end

end OAI
