import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteNormalConjugationCover
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalFiniteQuotient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalLocallyNilpotentDimension

namespace OAI

/-! # Finite torsion removal from the locally nilpotent rational-dimension step -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G] [Countable G]

theorem locallyNilpotent_mod_finite_torsion (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H) :
    let T := locallyNilpotentTorsionSubgroup hlocal
    Finite T ∧ Group.IsNilpotent (G ⧸ T) ∧
      HasProjectiveDimensionLE (trivialIntegral (G ⧸ T)) (d + 1) := by
  let T := locallyNilpotentTorsionSubgroup hlocal
  let : Finite T := locallyNilpotentTorsionSubgroup_finite hlocal hb
  let : Countable (G ⧸ T) := Function.Surjective.countable (QuotientGroup.mk'_surjective T)
  have hQ := RationalQuotient.rational_dimension_quotient T d hd
  have hr := rationalHomologyDimension_of_rational_representation d hQ
  have ht := locallyNilpotentTorsionQuotient_torsionFree hlocal
  have hl : ∀ K : Subgroup (G ⧸ T), K.FG → Group.IsNilpotent K :=
    locallyNilpotent_quotient hlocal (QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T)
  exact ⟨inferInstance, hr.locallyNilpotent_isNilpotent ht hl,
    hr.locallyNilpotent_integralDimension ht hl⟩


theorem rationallyFinite_locallyNilpotent_isNilpotent (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H) :
    Group.IsNilpotent G := by
  obtain ⟨hT, hQ, _⟩ := locallyNilpotent_mod_finite_torsion d hd hb hlocal
  let := hT
  let := hQ
  exact nilpotent_of_locallyNilpotent_finite_kernel (locallyNilpotentTorsionSubgroup hlocal) hlocal

end PolycyclicRecognition

end

end OAI
