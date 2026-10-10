import Mathlib
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.FieldBicommutant
import OAI.Analysis.Commutator.FieldUniqueness
import OAI.Analysis.Commutator.ProjectionCommutant
import OAI.Analysis.Commutator.RankOneFactor

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
lemma fieldMember_mono {Q R : Ω → VonNeumannAlgebra H}
    (hQR : ∀ᵐ a ∂μ,Q a≤R a) {A : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hA : FieldMember μ Q A) : FieldMember μ R A := by
  obtain ⟨T,hm,b,hb,hb0,he,hmem⟩ := hA
  refine ⟨T,hm,b,hb,hb0,he,?_⟩
  filter_upwards [hQR,hmem] with a ha hm
  exact ha hm

def fiberJoin (Q R : VonNeumannAlgebra H) : VonNeumannAlgebra H :=
  (vonNeumannIntersection Q.commutant R.commutant).commutant

omit [TopologicalSpace.SeparableSpace H] in
lemma le_fiberJoin_left (Q R : VonNeumannAlgebra H) : Q≤fiberJoin Q R := by
  intro A hA
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro Z hZ
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hZ.1 A hA).symm

omit [TopologicalSpace.SeparableSpace H] in
lemma le_fiberJoin_right (Q R : VonNeumannAlgebra H) : R≤fiberJoin Q R := by
  intro A hA
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro Z hZ
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hZ.2 A hA).symm

omit [TopologicalSpace.SeparableSpace H] in
lemma factor_of_rankOne_mem_join (Q R : VonNeumannAlgebra H)
    (hRQ : R≤Q.commutant) (v : ℕ → H) (hv : DenseRange v)
    (hmem : ∀ i j,InnerProductSpace.rankOne ℂ (v i) (v j)∈fiberJoin Q R) :
    FactorCorner.IsFactor Q := by
  intro Z hZ hZc
  apply scalar_of_dense_rankOne_tests v hv Z
  intro i j
  apply VonNeumannAlgebra.mem_commutant_iff.mp (hmem i j) Z
  exact ⟨VonNeumannAlgebra.mem_commutant_iff.mpr hZc,
    VonNeumannAlgebra.mem_commutant_iff.mpr (fun B hB =>
      (VonNeumannAlgebra.mem_commutant_iff.mp (hRQ hB) Z hZ).symm)⟩

theorem factors_ae_of_central_geometry
    (P : VonNeumannAlgebra (Lp H 2 μ)) (Q R : Ω → VonNeumannAlgebra H)
    (hP : ∀ A,A∈P → FieldMember μ Q A)
    (hPc : ∀ A,A∈P.commutant → FieldMember μ R A)
    (hRQ : ∀ᵐ a ∂μ,R a≤(Q a).commutant)
    (hcenter : ∀ (Z : Lp H 2 μ →L[ℂ] Lp H 2 μ),Z∈P → Z∈P.commutant →
      ∀ B : H →L[ℂ] H,Commute
        (operator μ (fun _ => B) (fun _ => aestronglyMeasurable_const)
          (Eventually.of_forall (fun _ => le_rfl))) Z) :
    ∀ᵐ a ∂μ,FactorCorner.IsFactor (Q a) := by
  let J : Ω → VonNeumannAlgebra H := fun a => fiberJoin (Q a) (R a)
  let N := fieldVonNeumann μ J
  have hPN : P≤N := fun A hA => fieldMember_mono μ
    (Eventually.of_forall (fun a => le_fiberJoin_left (Q a) (R a))) (hP A hA)
  have hPcN : P.commutant≤N := fun A hA => fieldMember_mono μ
    (Eventually.of_forall (fun a => le_fiberJoin_right (Q a) (R a))) (hPc A hA)
  have hconstant (B : H →L[ℂ] H) : ∀ᵐ a ∂μ,B∈J a := by
    let C := operator μ (fun _ => B) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl))
    have hCN : C∈N := by
      change C∈N.carrier
      rw [←N.centralizer_centralizer']
      intro Z hZ
      have hZc : Z∈P.commutant :=
        VonNeumannAlgebra.mem_commutant_iff.mpr (fun A hA => hZ A (hPN hA))
      have hZP : Z∈P := by
        change Z∈P.carrier
        rw [←P.centralizer_centralizer']
        intro A hA
        exact hZ A (hPcN (VonNeumannAlgebra.mem_commutant_iff.mpr hA))
      exact (hcenter Z hZP hZc B).eq.symm
    obtain ⟨T,hm,b,hb,_,he,hmem⟩ := hCN
    have heae := field_eq_ae_of_operator_eq μ T (fun _ => B) hm
      (fun _ => aestronglyMeasurable_const) hb
      (Eventually.of_forall (fun _ => le_rfl)) he.symm
    filter_upwards [heae,hmem] with a ha hm
    rwa [ha] at hm
  let v : ℕ → H := TopologicalSpace.denseSeq H
  filter_upwards [hRQ,ae_all_iff.mpr (fun i => ae_all_iff.mpr
    (fun j => hconstant (InnerProductSpace.rankOne ℂ (v i) (v j))))] with a ha hm
  exact factor_of_rankOne_mem_join (Q a) (R a) ha v
    (TopologicalSpace.denseRange_denseSeq H) hm

end Kadison.Decomposable

end

end
end

end OAI
