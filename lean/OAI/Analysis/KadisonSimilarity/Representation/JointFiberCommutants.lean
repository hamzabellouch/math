import OAI.Analysis.KadisonSimilarity.Tracial.JointCStarSource
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixVonNeumannRange

namespace OAI

/-! # Central elements of a joint fiber representation

For commuting sources `B,C`, a central element of the represented
bicommutant of `B` commutes with the full joint bicommutant. The proof uses
norm generation of the joint source, with no normality assertion for a
pointwise fiber representation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

variable {A K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A representation of the joint norm closure lands in any closed star
algebra containing the represented copies of both sources. -/
theorem joint_source_representation_mem
    (B C : StarSubalgebra ℂ A)
    (σ : jointCStarSource B C →⋆ₐ[ℂ] (K →L[ℂ] K))
    (N : StarSubalgebra ℂ (K →L[ℂ] K)) (hN : IsClosed (N : Set (K →L[ℂ] K)))
    (hB : ∀ b : B, σ (StarSubalgebra.inclusion (le_jointCStarSource_left B C) b) ∈ N)
    (hC : ∀ c : C, σ (StarSubalgebra.inclusion (le_jointCStarSource_right B C) c) ∈ N)
    (s : jointCStarSource B C) : σ s ∈ N := by
  let D := N.comap σ
  have hD : IsClosed (D : Set (jointCStarSource B C)) :=
    hN.preimage (map_continuous σ)
  have hImage : IsClosed ((D.map (jointCStarSource B C).subtype) : Set A) := by
    rw [StarSubalgebra.coe_map]
    exact (jointCStarSource_isClosed B C).isClosedMap_subtype_val _ hD
  have hb : B ≤ D.map (jointCStarSource B C).subtype := by
    intro b hb
    exact ⟨StarSubalgebra.inclusion (le_jointCStarSource_left B C) ⟨b, hb⟩,
      hB ⟨b, hb⟩, rfl⟩
  have hc : C ≤ D.map (jointCStarSource B C).subtype := by
    intro c hc
    exact ⟨StarSubalgebra.inclusion (le_jointCStarSource_right B C) ⟨c, hc⟩,
      hC ⟨c, hc⟩, rfl⟩
  obtain ⟨t, ht, hts⟩ := jointCStarSource_minimal B C _ hb hc hImage s.property
  have heq : t = s := Subtype.ext hts
  change σ t ∈ N at ht
  simpa only [heq] using ht

/-- The represented second source commutes with the bicommutant of the
first source, since the two original sources commute. -/
theorem joint_second_mem_first_commutant
    (B C : StarSubalgebra ℂ A)
    [IsClosed (B : Set A)] [IsClosed (C : Set A)]
    (hBC : ∀ b : B, ∀ c : C, (b : A) * (c : A) = (c : A) * (b : A))
    (σ : jointCStarSource B C →⋆ₐ[ℂ] (K →L[ℂ] K)) (c : C) :
    σ (StarSubalgebra.inclusion (le_jointCStarSource_right B C) c) ∈
      (representationVonNeumannAlgebra
        (σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C)))).commutant := by
  apply (mem_representation_commutant_iff _ _).mpr
  rintro _ ⟨b, rfl⟩
  change σ (StarSubalgebra.inclusion (le_jointCStarSource_left B C) b) *
      σ (StarSubalgebra.inclusion (le_jointCStarSource_right B C) c) =
    σ (StarSubalgebra.inclusion (le_jointCStarSource_right B C) c) *
      σ (StarSubalgebra.inclusion (le_jointCStarSource_left B C) b)
  rw [← map_mul, ← map_mul]
  apply congrArg σ
  apply Subtype.ext
  exact hBC b c

/-- Centrality in the first represented bicommutant gives commutation with
the entire joint representation. -/
theorem joint_center_mem_joint_commutant
    (B C : StarSubalgebra ℂ A)
    [IsClosed (B : Set A)] [IsClosed (C : Set A)]
    (hBC : ∀ b : B, ∀ c : C, (b : A) * (c : A) = (c : A) * (b : A))
    (σ : jointCStarSource B C →⋆ₐ[ℂ] (K →L[ℂ] K)) (T : K →L[ℂ] K)
    (hT : T ∈ vonNeumannCenter (representationVonNeumannAlgebra
      (σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C))))) :
    T ∈ (representationVonNeumannAlgebra σ).commutant := by
  let σB := σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C))
  let P := representationVonNeumannAlgebra σB
  have ht : T ∈ P := hT.1
  have htc : T ∈ P.commutant := hT.2
  have hst : star T ∈ P := star_mem ht
  have hstc : star T ∈ P.commutant := star_mem htc
  let N := StarSubalgebra.centralizer ℂ ({T} : Set (K →L[ℂ] K))
  have hN : IsClosed (N : Set (K →L[ℂ] K)) := by
    rw [StarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _
  have hb : ∀ b : B, σ (StarSubalgebra.inclusion (le_jointCStarSource_left B C) b) ∈ N := by
    intro b
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro g hg
    have hg' : g = T := Set.mem_singleton_iff.mp hg
    subst g
    have hmem : σB b ∈ P := mem_representationVonNeumannAlgebra σB b
    exact ⟨((VonNeumannAlgebra.mem_commutant_iff.mp htc) _ hmem).symm,
      ((VonNeumannAlgebra.mem_commutant_iff.mp hstc) _ hmem).symm⟩
  have hc : ∀ c : C, σ (StarSubalgebra.inclusion (le_jointCStarSource_right B C) c) ∈ N := by
    intro c
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro g hg
    have hg' : g = T := Set.mem_singleton_iff.mp hg
    subst g
    have hmem := joint_second_mem_first_commutant B C hBC σ c
    exact ⟨(VonNeumannAlgebra.mem_commutant_iff.mp hmem) _ ht,
      (VonNeumannAlgebra.mem_commutant_iff.mp hmem) _ hst⟩
  apply (mem_representation_commutant_iff σ T).mpr
  rintro _ ⟨s, rfl⟩
  have hmem := joint_source_representation_mem B C σ N hN hb hc s
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hmem) T (Set.mem_singleton T)).1.symm

/-- In particular a central first-source operator commutes with every
operator in the represented joint bicommutant, including rank-one tests. -/
theorem joint_center_commutes_joint_bicommutant
    (B C : StarSubalgebra ℂ A)
    [IsClosed (B : Set A)] [IsClosed (C : Set A)]
    (hBC : ∀ b : B, ∀ c : C, (b : A) * (c : A) = (c : A) * (b : A))
    (σ : jointCStarSource B C →⋆ₐ[ℂ] (K →L[ℂ] K)) (T Q : K →L[ℂ] K)
    (hT : T ∈ vonNeumannCenter (representationVonNeumannAlgebra
      (σ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left B C)))))
    (hQ : Q ∈ representationVonNeumannAlgebra σ) : T * Q = Q * T :=
  ((VonNeumannAlgebra.mem_commutant_iff.mp
    (joint_center_mem_joint_commutant B C hBC σ T hT)) Q hQ).symm

end KadisonSimilarity

end

end OAI
