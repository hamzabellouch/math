import OAI.Analysis.KadisonSimilarity.Representation.CountablyGeneratedCStarAlgebra
import OAI.Analysis.KadisonSimilarity.Representation.CentralDecomposition

namespace OAI

/-! # A common separable source for an algebra and its commutant

Taking the norm closure of the joint star algebra preserves norm separability.
When the two sources generate `P` and `P'`, the common source generates the
commutant of the center. This puts both sources in one fiber representation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology

variable {A : Type*} [CStarAlgebra A]

/-- The norm-closed star algebra containing the two given sources. -/
abbrev jointCStarSource (B C : StarSubalgebra ℂ A) : StarSubalgebra ℂ A :=
  (B ⊔ C).topologicalClosure

instance jointCStarSource_isClosed (B C : StarSubalgebra ℂ A) :
    IsClosed (jointCStarSource B C : Set A) :=
  StarSubalgebra.isClosed_topologicalClosure _

theorem le_jointCStarSource_left (B C : StarSubalgebra ℂ A) :
    B ≤ jointCStarSource B C :=
  le_sup_left.trans (StarSubalgebra.le_topologicalClosure _)

theorem le_jointCStarSource_right (B C : StarSubalgebra ℂ A) :
    C ≤ jointCStarSource B C :=
  le_sup_right.trans (StarSubalgebra.le_topologicalClosure _)

theorem jointCStarSource_minimal (B C S : StarSubalgebra ℂ A)
    (hB : B ≤ S) (hC : C ≤ S) (hS : IsClosed (S : Set A)) :
    jointCStarSource B C ≤ S :=
  StarSubalgebra.topologicalClosure_minimal (sup_le hB hC) hS

/-- Countable dense subsets of the two algebras already generate their
joint norm closure. -/
theorem jointCStarSource_eq_dense_generators
    (B C : StarSubalgebra ℂ A)
    (b : ℕ → B) (hb : DenseRange b) (c : ℕ → C) (hc : DenseRange c) :
    jointCStarSource B C =
      (StarAlgebra.adjoin ℂ
        (Set.range (fun n => (b n : A)) ∪ Set.range (fun n => (c n : A)))).topologicalClosure := by
  let S := (StarAlgebra.adjoin ℂ
    (Set.range (fun n => (b n : A)) ∪ Set.range (fun n => (c n : A)))).topologicalClosure
  have hS : IsClosed (S : Set A) := StarSubalgebra.isClosed_topologicalClosure _
  have hbS : B ≤ S := by
    intro x hx
    exact hb.induction_on (p := fun y : B => (y : A) ∈ S)
      (⟨x, hx⟩ : B) (hS.preimage continuous_subtype_val) (fun n =>
      StarSubalgebra.le_topologicalClosure _
        (StarAlgebra.subset_adjoin ℂ _ (Or.inl (Set.mem_range_self n))))
  have hcS : C ≤ S := by
    intro x hx
    exact hc.induction_on (p := fun y : C => (y : A) ∈ S)
      (⟨x, hx⟩ : C) (hS.preimage continuous_subtype_val) (fun n =>
      StarSubalgebra.le_topologicalClosure _
        (StarAlgebra.subset_adjoin ℂ _ (Or.inr (Set.mem_range_self n))))
  apply le_antisymm (jointCStarSource_minimal B C S hbS hcS hS)
  apply StarSubalgebra.topologicalClosure_minimal _
    (StarSubalgebra.isClosed_topologicalClosure _)
  apply StarAlgebra.adjoin_le
  rintro x (⟨n, rfl⟩ | ⟨n, rfl⟩)
  · exact le_jointCStarSource_left B C (b n).property
  · exact le_jointCStarSource_right B C (c n).property

instance jointCStarSource_separable (B C : StarSubalgebra ℂ A)
    [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] :
    TopologicalSpace.SeparableSpace (jointCStarSource B C) := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_dense_seq B
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq C
  rw [jointCStarSource_eq_dense_generators B C b hb c hc]
  apply TopologicalSpace.IsSeparable.separableSpace
  exact (isSeparable_starAlgebra_adjoin
    ((Set.countable_range _).union (Set.countable_range _))).closure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem source_commutant_eq
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) (P : VonNeumannAlgebra H)
    (hB : (starSubalgebraCommutant B).commutant = P) :
    starSubalgebraCommutant B = P.commutant := by
  have h := congrArg VonNeumannAlgebra.commutant hB
  simpa only [VonNeumannAlgebra.commutant_commutant] using h

/-- The joint source has exactly the original center as commutant. -/
theorem jointCStarSource_commutant
    (P : VonNeumannAlgebra H) (B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hB : B ≤ P.toStarSubalgebra) (hC : C ≤ P.commutant.toStarSubalgebra)
    (hBgen : (starSubalgebraCommutant B).commutant = P)
    (hCgen : (starSubalgebraCommutant C).commutant = P.commutant) :
    starSubalgebraCommutant (jointCStarSource B C) = vonNeumannCenter P := by
  have hB' := source_commutant_eq B P hBgen
  have hC' : starSubalgebraCommutant C = P := by
    simpa only [VonNeumannAlgebra.commutant_commutant] using
      source_commutant_eq C P.commutant hCgen
  have hclosed : IsClosed ((vonNeumannCenter P).commutant.toStarSubalgebra :
      Set (H →L[ℂ] H)) := by
    change IsClosed ((vonNeumannCenter P).commutant : Set (H →L[ℂ] H))
    rw [VonNeumannAlgebra.coe_commutant]
    exact Set.isClosed_centralizer _
  have hBcentral : B ≤ (vonNeumannCenter P).commutant.toStarSubalgebra :=
    hB.trans (le_center_commutant P)
  have hCcentral : C ≤ (vonNeumannCenter P).commutant.toStarSubalgebra := by
    intro x hx
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro z hz
    exact (VonNeumannAlgebra.mem_commutant_iff.mp (hC hx)) z hz.1
  have hS := jointCStarSource_minimal B C _ hBcentral hCcentral hclosed
  apply VonNeumannAlgebra.ext
  intro T
  constructor
  · intro hT
    have hcomm : ∀ x ∈ jointCStarSource B C, x * T = T * x := by
      simpa only [← SetLike.mem_coe, coe_starSubalgebraCommutant,
        Set.mem_centralizer_iff] using hT
    have hTB : T ∈ starSubalgebraCommutant B := by
      simpa only [← SetLike.mem_coe, coe_starSubalgebraCommutant,
        Set.mem_centralizer_iff] using
        (show ∀ x ∈ B, x * T = T * x from fun x hx =>
          hcomm x (le_jointCStarSource_left B C hx))
    have hTC : T ∈ starSubalgebraCommutant C := by
      simpa only [← SetLike.mem_coe, coe_starSubalgebraCommutant,
        Set.mem_centralizer_iff] using
        (show ∀ x ∈ C, x * T = T * x from fun x hx =>
          hcomm x (le_jointCStarSource_right B C hx))
    rw [hB'] at hTB
    rw [hC'] at hTC
    exact ⟨hTC, hTB⟩
  · intro hT
    rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
    intro x hx
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp (hS hx)) T hT).symm

theorem jointCStarSource_bicommutant
    (P : VonNeumannAlgebra H) (B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hB : B ≤ P.toStarSubalgebra) (hC : C ≤ P.commutant.toStarSubalgebra)
    (hBgen : (starSubalgebraCommutant B).commutant = P)
    (hCgen : (starSubalgebraCommutant C).commutant = P.commutant) :
    (starSubalgebraCommutant (jointCStarSource B C)).commutant =
      (vonNeumannCenter P).commutant :=
  congrArg VonNeumannAlgebra.commutant (jointCStarSource_commutant P B C hB hC hBgen hCgen)

/-- Simultaneously choose weak generators for the algebra and commutant,
with a norm-separable common source generating the central commutant. -/
theorem exists_separable_joint_cstar_source [TopologicalSpace.SeparableSpace H]
    (P : VonNeumannAlgebra H) :
    ∃ B C : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (B : Set (H →L[ℂ] H)) ∧ IsClosed (C : Set (H →L[ℂ] H)) ∧
      TopologicalSpace.SeparableSpace B ∧ TopologicalSpace.SeparableSpace C ∧
      B ≤ P.toStarSubalgebra ∧ C ≤ P.commutant.toStarSubalgebra ∧
      (starSubalgebraCommutant B).commutant = P ∧
      (starSubalgebraCommutant C).commutant = P.commutant ∧
      (starSubalgebraCommutant (jointCStarSource B C)).commutant =
        (vonNeumannCenter P).commutant := by
  obtain ⟨B, hBclosed, hBsep, hB, hBgen⟩ := exists_separable_generating_cstar_subalgebra P
  obtain ⟨C, hCclosed, hCsep, hC, hCgen⟩ :=
    exists_separable_generating_cstar_subalgebra P.commutant
  exact ⟨B, C, hBclosed, hCclosed, hBsep, hCsep, hB, hC, hBgen, hCgen,
    jointCStarSource_bicommutant P B C hB hC hBgen hCgen⟩

end KadisonSimilarity

end

end OAI
