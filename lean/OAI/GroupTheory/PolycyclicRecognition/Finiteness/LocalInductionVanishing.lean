import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InductionExhaustionVanishing
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupInductionDimension
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerProjectiveCoefficientDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CountableUnionDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPolyZ
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FinitelyGeneratedLift

namespace OAI

/-! # Vanishing for locally controlled height-kernel coefficients

Only finite projective dimension at each finitely generated subgroup is used;
there is no uniform bound on those dimensions. In particular this applies to
locally finite kernels, and to torsion-free locally nilpotent kernels.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] [Countable G]

theorem TypeFPInfinity.induction_locally_finite_dimension_vanishing
    (hG : TypeFPInfinity G) (A : Rep.{0} ℤ G) (K : Subgroup G) (p : ℕ)
    (hlocal : ∀ J : Subgroup G, J ≤ K → J.FG →
      ∃ d : ℕ, HasProjectiveDimensionLE (Rep.res J.subtype A) d) :
    Subsingleton (ShiftedCompletedCohomology p (Rep.ind K.subtype (Rep.res K.subtype A))) := by
  obtain ⟨S, hS, hfg, hcov⟩ := exists_fg_subgroup_exhaustion (G := K)
  let H : ℕ → Subgroup G := fun n => (S n).map K.subtype
  have hmono : Monotone H := fun _ _ h => Subgroup.map_mono (hS h)
  have hHK (n : ℕ) : H n ≤ K := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hcover : ∀ g ∈ K, ∃ n, g ∈ H n := by
    intro g hg
    obtain ⟨n, hn⟩ := hcov ⟨g, hg⟩
    exact ⟨n, ⟨⟨g, hg⟩, hn, rfl⟩⟩
  apply TypeFPInfinity.induction_exhaustion_complete_vanishing
    A H K hmono hHK hcover hG p
  intro n
  obtain ⟨d, hd⟩ := hlocal (H n) (hHK n) (fg_subgroup_map (hfg n) K.subtype)
  let := subgroupInduction_projectiveDimension_le (H n) (Rep.res (H n).subtype A) d hd
  exact shiftedCompleteCohomology_subsingleton_of_finite_projectiveDimension p _ d

theorem TypeFPInfinity.locallyFinite_smallCoefficient_induction_vanishing
    (hG : TypeFPInfinity G) (K : Subgroup G) (p : ℕ)
    (hlocal : ∀ J : Subgroup G, J ≤ K → J.FG → Finite J) :
    Subsingleton (ShiftedCompletedCohomology p
      (Rep.ind K.subtype (Rep.res K.subtype (smallCoefficientRepresentation G)))) := by
  apply hG.induction_locally_finite_dimension_vanishing (smallCoefficientRepresentation G) K p
  intro J hJK hfg
  let := hlocal J hJK hfg
  exact ⟨0, (projective_iff_hasProjectiveDimensionLE_zero _).mp
    (smallCoefficient_finite_subgroup_projective G J)⟩

theorem TypeFPInfinity.locallyNilpotent_smallCoefficient_induction_vanishing
    (hG : TypeFPInfinity G) (K : Subgroup G) (p : ℕ)
    (htf : HasNoNontrivialTorsion K)
    (hlocal : ∀ J : Subgroup G, J ≤ K → J.FG → Group.IsNilpotent J) :
    Subsingleton (ShiftedCompletedCohomology p
      (Rep.ind K.subtype (Rep.res K.subtype (smallCoefficientRepresentation G)))) := by
  apply hG.induction_locally_finite_dimension_vanishing (smallCoefficientRepresentation G) K p
  intro J hJK hfg
  let : Group.FG J := (Group.fg_iff_subgroup_fg J).mpr hfg
  let := hlocal J hJK hfg
  obtain ⟨n, hPD⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (htf.of_injective (Subgroup.inclusion hJK) (Subgroup.inclusion_injective hJK))
  obtain ⟨d, hd⟩ := hPD.finiteCohomologicalDimension J
  exact ⟨d, smallCoefficient_dimension_le_of_integral_dimension G J d hd⟩

end PolycyclicRecognition

end

end OAI
