import Mathlib
import OAI.Analysis.Commutator.CommutatorBicommutant
import OAI.Analysis.Commutator.ReducingMatrix
import OAI.Analysis.Commutator.SeparableReducingHull

namespace OAI

noncomputable section

noncomputable section

open scoped InnerProductSpace BigOperators

open ContinuousLinearMap

universe u

namespace Kadison

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma image_mem_bicommutant {A : Type*} [CStarAlgebra A]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    σ a∈NormalGNS.bicommutant σ.range :=
  NormalGNS.subset_bicommutant σ.range ⟨a,rfl⟩

lemma reducing_commutator_bound (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]
    (hSP : S≤P.toStarSubalgebra) (K : Submodule ℂ H) [CompleteSpace K]
    (hinv : ∀ (a : S) (x : H),x∈K → S.subtype a x∈K)
    (hY : ∀ x∈K,Y x∈K) :
    commutatorSeminorm (NormalGNS.bicommutant (ReducingRepresentation.restrict S.subtype K hinv).range)
      (Y.restrict hY)≤commutatorSeminorm P Y := by
  apply commutatorSeminorm_image_bicommutant_le _ _ _ (commutatorSeminorm_nonneg P Y)
  intro a
  rw [←ReducingRepresentation.compression_eq_restrict K Y hY]
  exact (ReducingRepresentation.norm_commutator_compression_le S.subtype K hinv Y a).trans
    (commutator_bound P Y (hSP a.property))

lemma reducing_matrix_vector_bound
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]
    (Y : H →L[ℂ] H) (K : Submodule ℂ H) [CompleteSpace K]
    (hinv : ∀ (a : S) (x : H),x∈K → S.subtype a x∈K)
    (hY : ∀ x∈K,Y x∈K) (h : ℕ) (X : Matrix (Fin h) (Fin h) S)
    (v : PiLp 2 (fun _ : Fin h => H)) (hv : ∀ i,v i∈K) (b : ℝ)
    (hb : ‖diagonalAmplification h (Y.restrict hY)*
      matrixOperator h (fun i j => ReducingRepresentation.restrict S.subtype K hinv (X i j))-
      matrixOperator h (fun i j => ReducingRepresentation.restrict S.subtype K hinv (X i j))*
      diagonalAmplification h (Y.restrict hY)‖≤b) :
    ‖(diagonalAmplification h Y*matrixOperator h (fun i j => (X i j:H →L[ℂ] H))-
      matrixOperator h (fun i j => (X i j:H →L[ℂ] H))*diagonalAmplification h Y) v‖≤b*‖v‖ := by
  let v₀ : PiLp 2 (fun _ : Fin h => K) := WithLp.toLp 2 (fun i => ⟨v i,hv i⟩)
  have heq : ReducingRepresentation.matrixInclusion K h v₀=v := by ext i; rfl
  have hvnorm : ‖v₀‖=‖v‖ := by rw [←heq,LinearIsometry.norm_map]
  have he := congrArg (fun A => A v₀)
    (ReducingRepresentation.matrix_commutator_intertwines S.subtype K hinv Y hY h X)
  change (diagonalAmplification h Y*matrixOperator h (fun i j => (X i j:H →L[ℂ] H))-
      matrixOperator h (fun i j => (X i j:H →L[ℂ] H))*diagonalAmplification h Y)
      (ReducingRepresentation.matrixInclusion K h v₀)=
    ReducingRepresentation.matrixInclusion K h
      ((diagonalAmplification h (Y.restrict hY)*
      matrixOperator h (fun i j => ReducingRepresentation.restrict S.subtype K hinv (X i j))-
      matrixOperator h (fun i j => ReducingRepresentation.restrict S.subtype K hinv (X i j))*
      diagonalAmplification h (Y.restrict hY)) v₀) at he
  rw [heq] at he
  rw [he,LinearIsometry.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ v₀).trans
    (by simpa only [hvnorm] using mul_le_mul_of_nonneg_right hb (norm_nonneg v₀))

lemma separable_reducing_bound {C : ℝ} (hC : 0≤C)
    (hsep : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
      (h : ℕ), 1≤h → ∀ X : Matrix (Fin h) (Fin h) (H →L[ℂ] H),
      (∀ i j,X i j∈P) →
      ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
        C*commutatorSeminorm P Y*‖matrixOperator h X‖)
    (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]
    (hSP : S≤P.toStarSubalgebra) (K : Submodule ℂ H) [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K]
    (hinv : ∀ (a : S) (x : H),x∈K → S.subtype a x∈K)
    (hY : ∀ x∈K,Y x∈K) (h : ℕ) (hh : 1≤h) (X : Matrix (Fin h) (Fin h) S)
    (v : PiLp 2 (fun _ : Fin h => H)) (hv : ∀ i,v i∈K) :
    ‖(diagonalAmplification h Y*matrixOperator h (fun i j => (X i j:H →L[ℂ] H))-
      matrixOperator h (fun i j => (X i j:H →L[ℂ] H))*diagonalAmplification h Y) v‖≤
      C*commutatorSeminorm P Y*‖matrixOperator h (fun i j => (X i j:H →L[ℂ] H))‖*‖v‖ := by
  let σ := ReducingRepresentation.restrict S.subtype K hinv
  let P₀ := NormalGNS.bicommutant σ.range
  have hcomm := reducing_commutator_bound P Y S hSP K hinv hY
  have hn := ReducingRepresentation.restricted_matrix_norm_le S.subtype K hinv h X
  apply reducing_matrix_vector_bound S Y K hinv hY h X v hv
  have hm (i j : Fin h) : σ (X i j)∈P₀ :=
    image_mem_bicommutant σ (X i j)
  have hb := hsep K P₀ (Y.restrict hY) h hh (fun i j => σ (X i j)) hm
  exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hcomm hC) hn (norm_nonneg (matrixOperator h (fun i j => σ (X i j))))
    (mul_nonneg hC (commutatorSeminorm_nonneg P Y)))

theorem remove_separability {C : ℝ} (hC : 0≤C)
    (hsep : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
      (h : ℕ), 1≤h → ∀ X : Matrix (Fin h) (Fin h) (H →L[ℂ] H),
      (∀ i j,X i j∈P) →
      ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
        C*commutatorSeminorm P Y*‖matrixOperator h X‖)
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      C*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hC (commutatorSeminorm_nonneg P Y)) (norm_nonneg _))
  intro v
  let T : Option (Fin h × Fin h) → H →L[ℂ] H := fun i =>
    match i with | none => Y | some p => X p.1 p.2
  let K := SeparableReducingHull.hull T (fun i => v i)
  let S := (StarAlgebra.adjoin ℂ (Set.range (fun p : Fin h × Fin h => X p.1 p.2))).topologicalClosure
  let : IsClosed (S : Set (H →L[ℂ] H)) := StarSubalgebra.isClosed_topologicalClosure _
  have hSP : S≤P.toStarSubalgebra := by
    apply StarSubalgebra.topologicalClosure_minimal
    · apply StarAlgebra.adjoin_le
      rintro _ ⟨⟨i,j⟩,rfl⟩
      exact hX i j
    · exact VonNeumannCStar.isClosed P
  have hSK : S≤SeparableReducingHull.reducingAlgebra K := by
    apply StarSubalgebra.topologicalClosure_minimal
    · apply StarAlgebra.adjoin_le
      rintro _ ⟨⟨i,j⟩,rfl⟩
      exact SeparableReducingHull.generator_mem_reducingAlgebra T (fun i => v i) (some (i,j))
    · exact SeparableReducingHull.reducingAlgebra_closed K (SeparableReducingHull.hull_closed T _)
  have hY : ∀ x∈K,Y x∈K := SeparableReducingHull.invariant T (fun i => v i) none
  have hinv : ∀ (a : S) (x : H),x∈K → S.subtype a x∈K := fun a => (hSK a.property).1
  have hXS (i j : Fin h) : X i j∈S :=
    StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ ⟨(i,j),rfl⟩)
  exact separable_reducing_bound hC hsep P Y S hSP K hinv hY h hh
    (fun i j => ⟨X i j,hXS i j⟩) v (SeparableReducingHull.vector_mem T (fun i => v i))

end Kadison
end
end

end OAI
