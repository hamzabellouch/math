import OAI.Analysis.KadisonKastler.FiniteFactorCommutantNear
import OAI.Analysis.KadisonKastler.NearbyProjectionRounding
import OAI.Analysis.KadisonKastler.CloseProjectionConjugacy
import OAI.Analysis.KadisonKastler.SelfAdjointApproximation
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism

namespace OAI

/-! # Aligning a reducing projection while fixing the common algebra -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]

local instance commonReducingProjectionOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance commonReducingProjectionStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem exists_commutant_projection_of_finite_gap
    (M N : VonNeumannAlgebra H) (hN : Generator.IsII1Factor N.toStarSubalgebra)
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 1 / 128000000)
    (hgap : kkDistance M N < γ)
    (p : H →L[ℂ] H) (hp : IsStarProjection p) (hpM : p ∈ M.commutant) :
    ∃ q : Algebra N.commutant, IsStarProjection q ∧ ‖q.val - p‖ ≤ 50000000 * γ := by
  let : Nontrivial (Algebra N.commutant) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg Subtype.val h)⟩⟩
  obtain ⟨D, hD, hDp⟩ := finiteFactor_commutant_approx_of_gap N M hN hγ
    (by rwa [kkDistance_comm]) p hpM hp.norm_le
  let a : Algebra N.commutant := ⟨realPart D, realPart_mem_vonNeumann N.commutant hD⟩
  have ha : IsSelfAdjoint a := by
    change star a = a
    apply Subtype.ext
    exact (realPart D).property
  have hap : ‖a.val - p‖ ≤ 2000000 * γ := by
    have he : a.val - p = (realPart (D - p) : H →L[ℂ] H) := by
      rw [map_sub]
      change (realPart D : H →L[ℂ] H) - p =
        (realPart D : H →L[ℂ] H) - (realPart p : H →L[ℂ] H)
      rw [hp.isSelfAdjoint.coe_realPart]
    rw [he]
    exact (realPart.norm_le (D - p)).trans hDp.le
  obtain ⟨q, hq, hqp⟩ := exists_projection_near_selfAdjoint_approximant N.commutant
    p hp a ha (by positivity : 0 ≤ 2000000 * γ) (by nlinarith) hap
  exact ⟨q, hq, by nlinarith⟩

theorem exists_unitary_aligning_common_reducing_projection
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M) (hRN : R ≤ N)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 1 / 128000000)
    (hgap : kkDistance M N < γ)
    (p : H →L[ℂ] H) (hp : IsStarProjection p) (hpM : p ∈ M.commutant) :
    ∃ u : unitary (H →L[ℂ] H),
      (u : H →L[ℂ] H) ∈ R.commutant ∧
      unitaryConj u p ∈ N.commutant ∧ ‖(u : H →L[ℂ] H) - 1‖ ≤ 100000000 * γ := by
  obtain ⟨q, hq, hqp⟩ := exists_commutant_projection_of_finite_gap M N hN hγ hsmall hgap p hp hpM
  let P : Algebra R.commutant := ⟨p, VonNeumannAlgebra.mem_commutant_iff.mpr
    (fun r hr => VonNeumannAlgebra.mem_commutant_iff.mp hpM r (hRM hr))⟩
  let Q : Algebra R.commutant := ⟨q.val, VonNeumannAlgebra.mem_commutant_iff.mpr
    (fun r hr => VonNeumannAlgebra.mem_commutant_iff.mp q.property r (hRN hr))⟩
  have hP : IsStarProjection P := by
    constructor
    · exact Subtype.ext hp.isIdempotentElem.eq
    · exact Subtype.ext hp.isSelfAdjoint.star_eq
  have hQ : IsStarProjection Q := by
    constructor
    · exact Subtype.ext (congrArg (fun b : Algebra N.commutant => b.val) hq.isIdempotentElem.eq)
    · exact Subtype.ext (congrArg (fun b : Algebra N.commutant => b.val) hq.isSelfAdjoint.star_eq)
  have hclose : ‖Q - P‖ < 1 := by
    change ‖q.val - p‖ < 1
    exact hqp.trans_lt (by nlinarith)
  obtain ⟨v, hv, hvn⟩ := exists_unitary_conjugating_close_projections P Q hP hQ hclose
  refine ⟨ambientAlgebraUnitary v, (v : Algebra R.commutant).property, ?_, ?_⟩
  · have he : unitaryConj (ambientAlgebraUnitary v) p = q.val := congrArg Subtype.val hv
    rw [he]
    exact q.property
  · change ‖(v : Algebra R.commutant).val - 1‖ ≤ _
    have hn : ‖(v : Algebra R.commutant).val - 1‖ ≤ 2 * ‖q.val - p‖ := hvn
    nlinarith

end

end KadisonKastler

end OAI
