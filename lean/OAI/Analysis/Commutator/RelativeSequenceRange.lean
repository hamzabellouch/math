import Mathlib
import OAI.Analysis.Commutator.TracialSmallCorners

namespace OAI

noncomputable section

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open HilbertSequence

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (j : B →⋆ₐ[ℂ] A)

def relativeVectorCLM : B →L[ℂ] τ.GNS :=
  (vectorCLM τ).comp (j.toLinearMap.mkContinuous 1 (fun b => by
    change ‖j b‖≤1*‖b‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le j b))

lemma relative_vector_unitball_isClosed (hω : (ω : Filter ℕ)≤atTop) :
    IsClosed {x : boundedSubspace τ ω | ∃ a : ℕ →ᵇ B, ‖a‖≤1 ∧
      vectorIn τ ω (mapSequence j a)=x} := by
  have hc := (bounded_image_isClosed ω (relativeVectorCLM τ j) hω {b : B | ‖b‖≤1} 1
    (fun _ h => h)).preimage (continuous_subtype_val (p := fun x => x∈boundedSubspace τ ω))
  convert hc using 1
  ext x
  constructor
  · rintro ⟨a,ha,hax⟩
    refine ⟨a,fun i => (a.norm_coe_le_norm i).trans ha,?_⟩
    exact congrArg Subtype.val hax
  · rintro ⟨a,ha,hax⟩
    refine ⟨a,(BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ)≤1)).mpr ha,?_⟩
    exact Subtype.ext hax

lemma relative_bicommutant_natural {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp (mapSequence j))))) :
    T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))) := by
  intro c hc
  apply hT c
  rintro _ ⟨a,rfl⟩
  exact hc _ ⟨mapSequence j a,rfl⟩

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma relative_bicommutant_contraction (hω : (ω : Filter ℕ)≤atTop)
    {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp (mapSequence j)))))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) :
    ∃ a : ℕ →ᵇ B, ‖a‖≤1 ∧ leftRestricted τ ω (mapSequence j a)=T := by
  let φ := (leftRestricted τ ω).comp (mapSequence j)
  have hx : T (sequenceVacuum τ ω)∈closure
      {x : boundedSubspace τ ω | ∃ a : ℕ →ᵇ B, ‖a‖≤1 ∧ vectorIn τ ω (mapSequence j a)=x} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,_,hna,ha⟩ := Kaplansky.range_selfAdjoint_contraction_finite_approx
      Unit φ hT hsT hnT (fun _ => sequenceVacuum τ ω) ε hε
    refine ⟨vectorIn τ ω (mapSequence j a),⟨a,hna,rfl⟩,?_⟩
    simpa only [dist_eq_norm,norm_sub_rev,φ,StarAlgHom.comp_apply,leftRestricted_vacuum] using ha ()
  rw [(relative_vector_unitball_isClosed τ ω j hω).closure_eq] at hx
  obtain ⟨a,hna,ha⟩ := hx
  refine ⟨a,hna,bicommutant_eq_of_vacuum τ ω hτ _ _ ?_
    (relative_bicommutant_natural τ ω j hT) ?_⟩
  · exact Set.subset_centralizer_centralizer (Set.mem_range_self (mapSequence j a))
  · simpa only [leftRestricted_vacuum] using ha

include hτ in
lemma relative_range_bicommutant (hω : (ω : Filter ℕ)≤atTop) :
    Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp (mapSequence j))))=
      Set.range ((leftRestricted τ ω).comp (mapSequence j)) := by
  exact BicommutantRange.operatorHom_range
    ((leftRestricted τ ω).comp (mapSequence j)) fun T hT hsT hnT =>
      let h := relative_bicommutant_contraction τ ω j hτ hω hT hsT hnT
      ⟨h.choose, h.choose_spec.2⟩

def relativeUltrapower (hω : (ω : Filter ℕ)≤atTop) : VonNeumannAlgebra (boundedSubspace τ ω) :=
  BicommutantRange.ofStarHom ((leftRestricted τ ω).comp (mapSequence j))
    (relative_range_bicommutant τ ω j hτ hω)

end Kadison.TracialSequence

end

end OAI
