import Mathlib
import OAI.Analysis.FreeWords.MatrixUnitHom
import OAI.Analysis.FreeWords.ProjectionPartition
import OAI.Analysis.FreeWords.ProjectionRound

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance partitionRefinePartialOrder (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance partitionRefinePreorder (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance partitionRefineLE (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance partitionRefineStarOrderedRing (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem refine_projection_partition {ι : Type*} [Fintype ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (hD : IsDiffuse M)
    (p : ι → ConcreteAlgebra M) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i≠j → p i*p j=0) (h1 : ∑ i, p i=1)
    (k : ι → ℕ) (t : ℝ) (ht : 0 ≤ t) (hτ : ∀ i, τ.map (p i)=(k i:ℂ)*(t:ℂ)) :
    ∃ e : (Σ i, Fin (k i)) → ConcreteAlgebra M,
      (∀ i, IsStarProjection (e i)) ∧
      (∀ i j, i≠j → e i*e j=0) ∧ (∑ i, e i)=1 ∧
      (∀ i, τ.map (e i)=(t:ℂ)) ∧ (∀ i, ∑ a, e ⟨i,a⟩=p i) := by
  classical
  choose f hf hfp hfo hfs hfτ using fun i => projection_partition M τ hD
    (k i) (p i) (hp i) t ht (hτ i)
  let e : (Σ i, Fin (k i)) → ConcreteAlgebra M := fun i => f i.1 i.2
  refine ⟨e,fun i => hf i.1 i.2,?_,?_,fun i => hfτ i.1 i.2,hfs⟩
  · rintro ⟨i,a⟩ ⟨j,b⟩ hij
    by_cases he : i=j
    · subst j
      exact hfo i a b (fun hab => hij (by cases hab; rfl))
    · exact subprojections_orthogonal (hp i) (hp j) (hf i a) (hf j b)
        (hfp i a) (hfp j b) (ho i j he)
  · simpa only [Fintype.sum_sigma,e,hfs] using h1

theorem unitary_of_equal_partition {ι : Type*} [Fintype ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (hF : IsFactor M)
    (p : ι → ConcreteAlgebra M) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i≠j → p i*p j=0) (h1 : ∑ i, p i=1)
    (hτ : ∀ i j, τ.map (p i)=τ.map (p j))
    (c : ι → ℂ) (hc : ∀ i, ‖c i‖=1) :
    ∃ (n : ℕ) (_hn : 0 < n)
      (ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M)
      (v : unitary (Matrix (Fin n) (Fin n) ℂ)),
      Function.Injective ρ ∧ ρ v.val=∑ i, c i • p i := by
  classical
  let : Nontrivial (ConcreteAlgebra M) := ⟨⟨0,1,fun h => by
    have ht := congrArg τ.map h
    rw [map_zero,τ.normalized] at ht
    exact zero_ne_one ht⟩⟩
  have hn : 0 < Fintype.card ι := by
    by_contra h
    have h0 : Fintype.card ι=0 := Nat.eq_zero_of_not_pos h
    let : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
    simp at h1
  let f := (Fintype.equivFin ι).symm
  let q : Fin (Fintype.card ι) → ConcreteAlgebra M := p ∘ f
  have hq (i) : IsStarProjection (q i) := hp (f i)
  have hqo (i j) (hij : i≠j) : q i*q j=0 := ho (f i) (f j) (fun h => hij (f.injective h))
  have hq1 : ∑ i, q i=1 := by rw [show (∑ i, q i)=∑ i, p i from f.sum_comp p]; exact h1
  let i₀ : Fin (Fintype.card ι) := ⟨0,hn⟩
  let : Nonempty (Fin (Fintype.card ι)) := ⟨i₀⟩
  obtain ⟨e,hm,he1,hes,hed⟩ := partial_matrix_system_diagonal M τ hF q hq hqo hq1 i₀
    (fun i => hτ (f i) (f i₀))
  let ρ := matrixUnitHom e hm he1 hes
  let b : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
    Matrix.diagonal (fun i => c (f i))
  have hb : b ∈ unitary _ := by
    rw [Unitary.mem_iff]
    constructor
    · simp only [b,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose]
      change (Matrix.diagonal (fun i => star (c (f i)))) *
        Matrix.diagonal (fun i => c (f i))=1
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      simp only [Matrix.diagonal_apply,Matrix.one_apply]
      split_ifs
      · rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hc]
        norm_num
      · rfl
    · simp only [b,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose]
      change Matrix.diagonal (fun i => c (f i)) *
        (Matrix.diagonal (fun i => star (c (f i))))=1
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      simp only [Matrix.diagonal_apply,Matrix.one_apply]
      split_ifs
      · rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hc]
        norm_num
      · rfl
  refine ⟨Fintype.card ι,hn,ρ,⟨b,hb⟩,ρ.toAlgHom.toRingHom.injective,?_⟩
  change (∑ i, ∑ j, b i j • e i j)=∑ i, c i • p i
  simp only [b,Matrix.diagonal_apply,ite_smul,zero_smul,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true,hed]
  exact f.sum_comp (fun i => c i • p i)

end

end KKProjectionSupport
end

end OAI
