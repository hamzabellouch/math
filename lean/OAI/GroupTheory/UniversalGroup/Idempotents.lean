import OAI.GroupTheory.UniversalGroup.MatrixDiagrams

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity
namespace IdempotentSystems

open PrefixAlgebra MatrixCorners

variable (K : Type) [CommRing K]

noncomputable instance algebraRing : Ring (algebra K) :=
  @Subalgebra.toRing K (Operators K) _ _ _ (algebra K)

noncomputable def corner (a : Fin 3) : Matrix (Fin 3) (Fin 3) K →ₙₐ[K] algebra K :=
  MatrixCorners.hom (fun i => leftWord K (words a i))
    (fun i => rightWord K (words a i)) (word_orthogonality K a)

def carrier : Set (algebra K) :=
  {E | E = 1 ∨ ∃ a M, IsIdempotentElem M ∧ E = corner K a M}

lemma carrier_finite [Finite K] : (carrier K).Finite := by
  classical
  apply ((Set.finite_singleton (1 : algebra K)).union
    (Set.finite_range (fun x : Fin 3 × Matrix (Fin 3) (Fin 3) K => corner K x.1 x.2))).subset
  rintro E (rfl | ⟨a, M, _, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨(a,M), rfl⟩

lemma one_mem : (1 : algebra K) ∈ carrier K := Or.inl rfl

lemma corner_mem (a : Fin 3) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : IsIdempotentElem M) : corner K a M ∈ carrier K :=
  Or.inr ⟨a, M, hM, rfl⟩

lemma carrier_idempotent (E : algebra K) (hE : E ∈ carrier K) : IsIdempotentElem E := by
  rcases hE with rfl | ⟨a, M, hM, rfl⟩
  · exact IsIdempotentElem.one
  · change corner K a M * corner K a M = corner K a M
    rw [← map_mul, hM.eq]

lemma sum_idempotent {D : Type*} [Ring D] {E P : D}
    (hE : IsIdempotentElem E) (hP : IsIdempotentElem P)
    (hEP : E * P = 0) (hPE : P * E = 0) : IsIdempotentElem (E + P) := by
  change (E + P) * (E + P) = E + P
  rw [add_mul, mul_add, mul_add, hE.eq, hP.eq, hEP, hPE]
  simp

lemma diagonalUnit_eq_diagonal (i : Fin 3) :
    (MatrixDiagram.diagonalUnit i : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (Pi.single i 1) := by
  classical
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [MatrixDiagram.diagonalUnit, MatrixDiagram.basisVector,
      Matrix.vecMulVec, Matrix.diagonal, Pi.single_apply]

lemma corner_diagonal (a i : Fin 3) :
    corner K a (MatrixDiagram.diagonalUnit i) = projection K (words a i) := by
  rw [diagonalUnit_eq_diagonal]
  exact MatrixCorners.map_diagonal (K := K)
    (fun i => leftWord K (words a i)) (fun i => rightWord K (words a i))
    (word_orthogonality K a) i

lemma projection_mem (a i : Fin 3) : projection K (words a i) ∈ carrier K := by
  rw [← corner_diagonal]
  exact corner_mem K a _ (MatrixDiagram.diagonalUnit_idempotent i)

lemma projection_first_sum :
    projection K (words 0 0) + projection K (words 0 1) + projection K (words 0 2) = 1 := by
  change projection K [false,false] + projection K [false,true] + projection K [true] = 1
  have h := projection_split K [false]
  have h' := projection_split K []
  simp only [List.cons_append, List.nil_append] at h h'
  rw [← h, ← h']
  simp [projection]

lemma projection_mul_zero (v w : List Bool)
    (h : rightWord K v * leftWord K w = 0) : projection K v * projection K w = 0 := by
  simp only [projection]
  rw [mul_assoc, ← mul_assoc (rightWord K v), h, zero_mul, mul_zero]

lemma projection_orthogonal (a : Fin 3) {i j : Fin 3} (hij : i ≠ j) :
    projection K (words a i) * projection K (words a j) = 0 :=
  projection_mul_zero K _ _ (by rw [word_orthogonality, ite_eq_right hij])

variable {T : Type*} [AddCommGroup T]

def AdditiveOnDiagram (z : algebra K → T) : Prop :=
  ∀ E P, E ∈ carrier K → P ∈ carrier K → E + P ∈ carrier K →
    E * P = 0 → P * E = 0 → z (E + P) = z E + z P

lemma restrict_additive (z : algebra K → T) (hz : AdditiveOnDiagram K z) (a : Fin 3) :
    MatrixDiagram.OrthogonallyAdditive (fun M => z (corner K a M)) := by
  intro E P hE hP hEP hPE
  have hsum := corner_mem K a (E + P) (sum_idempotent hE hP hEP hPE)
  rw [map_add] at hsum
  change z (corner K a (E + P)) = z (corner K a E) + z (corner K a P)
  rw [map_add]
  apply hz _ _ (corner_mem K a E hE) (corner_mem K a P hP) hsum
  · rw [← map_mul, hEP, map_zero]
  · rw [← map_mul, hPE, map_zero]

lemma projection_multiples (z : algebra K → T) (hz : AdditiveOnDiagram K z)
    (p : ℕ) [CharP K p] (a i j : Fin 3) :
    p • z (projection K (words a i)) = p • z (projection K (words a j)) := by
  simpa only [corner_diagonal] using
    MatrixDiagram.diagonal_equality (fun M => z (corner K a M))
      (restrict_additive K z hz a) p i j

lemma first_projection_zero (z : algebra K → T) (hz : AdditiveOnDiagram K z)
    (p : ℕ) [CharP K p] : p • z (projection K [false,false]) = 0 := by
  let A := projection K [false,false]
  let B := projection K [false,true]
  let A₀ := projection K [false,false,false]
  let A₁ := projection K [false,false,true]
  have hA : A ∈ carrier K := projection_mem K 0 0
  have hA₀ : A₀ ∈ carrier K := projection_mem K 1 0
  have hA₁ : A₁ ∈ carrier K := projection_mem K 2 0
  have hAB : p • z A = p • z B := projection_multiples K z hz p 0 0 1
  have hA₀B : p • z A₀ = p • z B := projection_multiples K z hz p 1 0 1
  have hA₁B : p • z A₁ = p • z B := projection_multiples K z hz p 2 0 1
  have hsplit : A = A₀ + A₁ := projection_split K [false,false]
  have horth₀₁ : A₀ * A₁ = 0 := by
    apply projection_mul_zero
    simp only [cancel_initial, Bool.false_eq_true, ite_false, ite_true]
  have horth₁₀ : A₁ * A₀ = 0 := by
    apply projection_mul_zero
    simp only [cancel_initial, Bool.true_eq_false, ite_false, ite_true]
  have hsum := hz A₀ A₁ hA₀ hA₁ (hsplit ▸ hA) horth₀₁ horth₁₀
  rw [← hsplit] at hsum
  have hq : p • z A = p • z A + p • z A := calc
    p • z A = p • z A₀ + p • z A₁ := by rw [hsum, nsmul_add]
    _ = _ := by rw [hA₀B, hA₁B, ← hAB]
  apply add_left_cancel (a := p • z A)
  exact hq.symm.trans (add_zero _).symm

lemma first_two_mem : projection K (words 0 0) + projection K (words 0 1) ∈ carrier K := by
  have hd := corner_mem K 0
    ((MatrixDiagram.diagonalUnit 0 : Matrix (Fin 3) (Fin 3) K) + MatrixDiagram.diagonalUnit 1)
    (sum_idempotent (MatrixDiagram.diagonalUnit_idempotent 0)
      (MatrixDiagram.diagonalUnit_idempotent 1)
      (MatrixDiagram.diagonalUnit_orthogonal (by decide : (0 : Fin 3) ≠ 1))
      (MatrixDiagram.diagonalUnit_orthogonal (by decide : (1 : Fin 3) ≠ 0)))
  simpa only [map_add, corner_diagonal] using hd

lemma identity_additive_decomposition (z : algebra K → T) (hz : AdditiveOnDiagram K z) :
    z 1 = z (projection K (words 0 0)) + z (projection K (words 0 1)) +
      z (projection K (words 0 2)) := by
  let A := projection K (words 0 0)
  let B := projection K (words 0 1)
  let C := projection K (words 0 2)
  have hA : A ∈ carrier K := projection_mem K 0 0
  have hB : B ∈ carrier K := projection_mem K 0 1
  have hC : C ∈ carrier K := projection_mem K 0 2
  have hABorth : A * B = 0 := projection_orthogonal K 0 (by decide : (0 : Fin 3) ≠ 1)
  have hBAorth : B * A = 0 := projection_orthogonal K 0 (by decide : (1 : Fin 3) ≠ 0)
  have hACorth : A * C = 0 := projection_orthogonal K 0 (by decide : (0 : Fin 3) ≠ 2)
  have hBCorth : B * C = 0 := projection_orthogonal K 0 (by decide : (1 : Fin 3) ≠ 2)
  have hCAorth : C * A = 0 := projection_orthogonal K 0 (by decide : (2 : Fin 3) ≠ 0)
  have hCBorth : C * B = 0 := projection_orthogonal K 0 (by decide : (2 : Fin 3) ≠ 1)
  have hABmem : A + B ∈ carrier K := first_two_mem K
  have hone : A + B + C = 1 := projection_first_sum K
  have hzAB := hz A B hA hB hABmem hABorth hBAorth
  have hzI := hz (A + B) C hABmem hC (hone.symm ▸ one_mem K)
    (by rw [add_mul, hACorth, hBCorth, add_zero])
    (by rw [mul_add, hCAorth, hCBorth, add_zero])
  rw [hone, hzAB] at hzI
  exact hzI

theorem annihilates_identity (z : algebra K → T) (hz : AdditiveOnDiagram K z)
    (p : ℕ) [CharP K p] : p • z 1 = 0 := by
  rw [identity_additive_decomposition K z hz, nsmul_add, nsmul_add,
    ← projection_multiples K z hz p 0 0 1, ← projection_multiples K z hz p 0 0 2]
  have h : p • z (projection K (words 0 0)) = 0 := first_projection_zero K z hz p
  rw [h, add_zero, add_zero]

theorem annihilates_identity_subtype (z : carrier K → T)
    (hz : ∀ E P : carrier K, ∀ hsum : E.val + P.val ∈ carrier K,
      E.val * P.val = 0 → P.val * E.val = 0 →
        z ⟨E.val + P.val, hsum⟩ = z E + z P)
    (p : ℕ) [CharP K p] : p • z ⟨1, one_mem K⟩ = 0 := by
  classical
  let z' : algebra K → T := fun E => if h : E ∈ carrier K then z ⟨E,h⟩ else 0
  have hz' : AdditiveOnDiagram K z' := by
    intro E P hE hP hsum hEP hPE
    simpa only [z', dite_eq_left hE, dite_eq_left hP, dite_eq_left hsum] using
      hz ⟨E,hE⟩ ⟨P,hP⟩ hsum hEP hPE
  simpa only [z', dite_eq_left (one_mem K)] using annihilates_identity K z' hz' p

end IdempotentSystems

namespace ConcreteEnvelopes

open PrefixAlgebra IdempotentSystems

noncomputable def system (K : Type) [Field K] [Finite K] :
    FiniteIdempotentSystem (algebra K) where
  carrier := IdempotentSystems.carrier K
  finite := carrier_finite K
  one_mem := one_mem K
  idempotent := fun E h => carrier_idempotent K E h

noncomputable abbrev P₂ := system (ZMod 2)
noncomputable abbrev P₃ := system (ZMod 3)
abbrev Index := TwoEnvelope.Index P₂ P₃
abbrev triples := TwoEnvelope.triples P₂ P₃

structure IsDiagram {V W : Type} [Group V] [Group W] (k : Index → V →* W) : Prop where
  common : k (.inl P₂.identity) = k (.inr P₃.identity)
  commute : ∀ t : triples, ∀ u v, Commute (k t.val.1 u) (k t.val.2.1 v)
  sum : ∀ t : triples, ∀ u, k t.val.2.2 u = k t.val.1 u * k t.val.2.1 u

theorem finite_envelope (V : Type) [Group V] [Group.IsFinitelyPresented V] :
    ∃ (W : Type) (_ : Group W), Group.IsFinitelyPresented W ∧
      ∃ k : Index → V →* W, IsDiagram k ∧
        Function.Injective (k (.inl P₂.identity)) := by
  obtain ⟨W, hW, hfp, k, hc, hi, hcomm, hsum⟩ :=
    TwoEnvelope.finite_envelope (ZMod 2) (ZMod 3) P₂ P₃ V
  exact ⟨W, hW, hfp, k, ⟨hc, hcomm, hsum⟩, hi⟩

def IsUniversal (U : Type) [Group U] : Prop :=
  ∀ (V : Type) [Group V] [Group.IsFinitelyPresented V],
    ∃ φ : V →* U, Function.Injective φ

theorem self_maps (U : Type) [Group U] [Group.IsFinitelyPresented U]
    (hU : IsUniversal U) :
    ∃ k : Index → U →* U, IsDiagram k ∧
      Function.Injective (k (.inl P₂.identity)) := by
  obtain ⟨W, hW, hfp, k, hk, hi⟩ := finite_envelope U
  let := hW
  let := hfp
  obtain ⟨κ, hκ⟩ := hU W
  refine ⟨fun E => κ.comp (k E), ⟨?_, ?_, ?_⟩, hκ.comp hi⟩
  · rw [hk.common]
  · intro E u v
    exact (hk.commute E u v).map κ
  · intro E u
    simp only [MonoidHom.comp_apply, hk.sum E, map_mul]

theorem coprime_annihilation {T : Type*} [AddCommGroup T]
    (z : Index → T)
    (hc : z (.inl P₂.identity) = z (.inr P₃.identity))
    (hs : ∀ t : triples, z t.val.2.2 = z t.val.1 + z t.val.2.1) :
    z (.inl P₂.identity) = 0 := by
  have h₂ : 2 • z (.inl P₂.identity) = 0 := by
    apply annihilates_identity_subtype (ZMod 2)
      (fun E => z (.inl E))
    intro E F hsum hEF hFE
    exact hs ⟨(.inl E, .inl F, .inl ⟨E.val + F.val, hsum⟩),
      ⟨hEF, hFE, rfl⟩⟩
  have h₃ : 3 • z (.inr P₃.identity) = 0 := by
    apply annihilates_identity_subtype (ZMod 3)
      (fun E => z (.inr E))
    intro E F hsum hEF hFE
    exact hs ⟨(.inr E, .inr F, .inr ⟨E.val + F.val, hsum⟩),
      ⟨hEF, hFE, rfl⟩⟩
  rw [← hc] at h₃
  have hx : (3 : ℕ) • z (.inl P₂.identity) = 2 • z (.inl P₂.identity) +
      z (.inl P₂.identity) := by exact succ_nsmul _ 2
  rw [hx, h₂, zero_add] at h₃
  exact h₃

end ConcreteEnvelopes
end UniversalFInfinity

end OAI
