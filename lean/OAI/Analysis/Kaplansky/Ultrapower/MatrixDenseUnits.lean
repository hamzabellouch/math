import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.DenseUnits
import Mathlib.LinearAlgebra.Matrix.Unique

namespace OAI

noncomputable section

namespace KaplanskyConsequences

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
open Matrix Topology
section Algebra
variable {A m n : Type*} [Ring A] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma isUnit_lower (C : Matrix n m A) :
    IsUnit (fromBlocks (1 : Matrix m m A) 0 C (1 : Matrix n n A)) := by
  refine ⟨⟨fromBlocks 1 0 C 1,fromBlocks 1 0 (-C) 1,?_,?_⟩,rfl⟩ <;>
    simp [fromBlocks_multiply,fromBlocks_one]

lemma isUnit_upper (B : Matrix m n A) :
    IsUnit (fromBlocks (1 : Matrix m m A) B 0 (1 : Matrix n n A)) := by
  refine ⟨⟨fromBlocks 1 B 0 1,fromBlocks 1 (-B) 0 1,?_,?_⟩,rfl⟩ <;>
    simp [fromBlocks_multiply,fromBlocks_one]

lemma isUnit_diagonal (u : (Matrix m m A)ˣ) (v : (Matrix n n A)ˣ) :
    IsUnit (fromBlocks (u : Matrix m m A) 0 0 (v : Matrix n n A)) := by
  refine ⟨⟨fromBlocks (↑u) 0 0 (↑v),fromBlocks ((↑(u⁻¹) : Matrix m m A)) 0 0 (↑(v⁻¹)),?_,?_⟩,rfl⟩ <;>
    simp [fromBlocks_multiply,fromBlocks_one]

lemma isUnit_schur (u : (Matrix m m A)ˣ) (v : (Matrix n n A)ˣ)
    (B : Matrix m n A) (C : Matrix n m A) :
    IsUnit (fromBlocks (↑u) B C ((v : Matrix n n A)+C*(↑(u⁻¹) : Matrix m m A)*B)) := by
  have he : fromBlocks (↑u) B C ((v : Matrix n n A)+C*(↑(u⁻¹) : Matrix m m A)*B) =
      fromBlocks 1 0 (C*(↑(u⁻¹) : Matrix m m A)) 1 * fromBlocks (↑u) 0 0 (↑v) *
      fromBlocks 1 ((↑(u⁻¹) : Matrix m m A)*B) 0 1 := by
    simp [fromBlocks_multiply,Matrix.mul_assoc,add_comm]
    simp [← Matrix.mul_assoc]
  rw [he]
  exact ((isUnit_lower _).mul (isUnit_diagonal u v)).mul (isUnit_upper _)
end Algebra

section Topology
variable {A m n : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma denseUnits_blocks (hm : DenseUnits (Matrix m m A)) (hn : DenseUnits (Matrix n n A)) :
    DenseUnits (Matrix (m ⊕ n) (m ⊕ n) A) := by
  let S := closure {x : Matrix (m ⊕ n) (m ⊕ n) A | IsUnit x}
  have hc : IsClosed S := isClosed_closure
  have hunit (u : (Matrix m m A)ˣ) (B : Matrix m n A) (C : Matrix n m A) (D : Matrix n n A) :
      fromBlocks (↑u) B C D ∈ S := by
    have h : ∀ d : Matrix n n A, fromBlocks (↑u) B C (d+C*(↑(u⁻¹) : Matrix m m A)*B) ∈ S := by
      intro d
      refine hn.induction (P:=fun d => fromBlocks (↑u) B C (d+C*(↑(u⁻¹) : Matrix m m A)*B) ∈ S) ?_ ?_ d
      · intro d hd
        obtain ⟨v,rfl⟩ := hd
        exact subset_closure (isUnit_schur u v B C)
      · exact hc.preimage (by fun_prop)
    simpa using h (D-C*(↑(u⁻¹) : Matrix m m A)*B)
  have hall (a : Matrix m m A) (B : Matrix m n A) (C : Matrix n m A) (D : Matrix n n A) :
      fromBlocks a B C D ∈ S := by
    apply hm.induction (P:=fun a => fromBlocks a B C D ∈ S) ?_ ?_ a
    · rintro a ⟨u,rfl⟩
      exact hunit u B C D
    · exact hc.preimage (by fun_prop)
  intro x
  simpa only [Matrix.fromBlocks_toBlocks] using
    hall (Matrix.toBlocks₁₁ x) (Matrix.toBlocks₁₂ x) (Matrix.toBlocks₂₁ x) (Matrix.toBlocks₂₂ x)

lemma denseUnits_ringEquiv {R S : Type*} [Ring R] [Ring S] [TopologicalSpace R]
    [TopologicalSpace S] (e : R ≃+* S) (he : Continuous e) (h : DenseUnits R) : DenseUnits S := by
  have hd : Dense (e '' {a : R | IsUnit a}) := e.surjective.denseRange.dense_image he h
  exact Dense.mono (fun b hb => by obtain ⟨a,ha,rfl⟩ := hb; exact ha.map e.toMonoidHom) hd

lemma denseUnits_matrix (h : DenseUnits A) (n : ℕ) : DenseUnits (Matrix (Fin n) (Fin n) A) := by
  induction n with
  | zero =>
    have : ∀ x : Matrix (Fin 0) (Fin 0) A, IsUnit x := fun x => by
      have hx : x=1 := Subsingleton.elim _ _
      rw [hx]; exact isUnit_one
    change Dense {x : Matrix (Fin 0) (Fin 0) A | IsUnit x}
    exact Dense.mono (fun x _ => this x) dense_univ
  | succ n ih =>
    have h1 : DenseUnits (Matrix (Fin 1) (Fin 1) A) := by
      exact denseUnits_ringEquiv (Matrix.uniqueRingEquiv (m:=Fin 1) (A:=A)).symm (by
        change Continuous (fun a : A => fun (_ _ : Fin 1) => a)
        fun_prop) h
    have hs := denseUnits_blocks ih h1
    exact denseUnits_ringEquiv (Matrix.reindexRingEquiv A (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n+1)))
      (by
        change Continuous (fun a : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) A =>
          fun i j => a (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
        fun_prop) hs
end Topology

variable {A : Type*} [CStarAlgebra A]
lemma DenseUnits.cstarMatrix (h : DenseUnits A) (n : ℕ) :
    DenseUnits (CStarMatrix (Fin n) (Fin n) A) := by
  have hm := denseUnits_matrix h n
  exact denseUnits_ringEquiv (CStarMatrix.ofMatrixRingEquiv (n:=Fin n) (A:=A))
    (CStarMatrix.ofMatrixL (m:=Fin n) (n:=Fin n) (A:=A)).continuous hm

lemma DenseUnits.stablyFinite [Nontrivial A] (h : DenseUnits A) : StablyFinite A := by
  intro n hn v hv
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact DenseUnits.finite (A:=CStarMatrix (Fin n) (Fin n) A) (h.cstarMatrix n) v hv


end KaplanskyConsequences

end

end OAI
