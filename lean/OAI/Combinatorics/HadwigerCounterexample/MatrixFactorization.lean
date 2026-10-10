import OAI.Combinatorics.HadwigerCounterexample.MatrixRanks
import Mathlib.Data.Fintype.EquivFin

namespace OAI

/-! # Matrix Factorization -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module
open scoped BigOperators
variable {I J Q : Type} [Fintype I] [Fintype J] [Fintype Q]

/-- Projecting the columns onto their literal column space keeps the matrix. -/
theorem invariant_cols (M : Mat I J) (Z R) (e : colSp Z = colSp M)
    [DecidableEq Q] (hr : R*Z=(1:Mat Q Q)) :
    Z * (R*M) = M := by
  apply coe_mv_inj
  apply LinearMap.ext
  intro v
  change _ *ᵥ v = M *ᵥ v
  simp only [← Matrix.mulVec_mulVec]
  have h : M*ᵥv ∈ colSp Z := e.symm ▸ (show M*ᵥv ∈ colSp M from ⟨v,rfl⟩)
  obtain ⟨x,hx⟩ := h
  change Z*ᵥx=M*ᵥv at hx
  rw [← hx, Matrix.mulVec_mulVec x R Z,hr, Matrix.one_mulVec]

theorem rank_product (M : Mat I J) :
    ∃ (A : Mat I (Fin M.rank)) (B : Mat (Fin M.rank) J),
      Function.Injective A.mulVec ∧ Function.Surjective B.mulVec ∧ A*B=M := by
  let t := M.rank
  let A := pack (colSp M)
  have ha := pack_inj (colSp M)
  obtain ⟨L,hL⟩ := mat_left_inv ha
  have hh := invariant_cols M A L (colSp_pack _) hL
  refine ⟨A,L*M,ha, mrk_surj.mpr ?_, hh⟩
  refine le_antisymm (Matrix.rank_le_card_height _) ?_
  have hx := Matrix.rank_mul_le_right A (L*M)
  rw [hh] at hx
  rw [Fintype.card_fin]; exact hx

/-- Symmetric nonsingular factor on the rank space. -/
theorem rank_symmetric (M : Mat I I) (hm : Mᵀ=M) :
    ∃ (P : Mat I (Fin M.rank)) (G : Mat (Fin M.rank) (Fin M.rank)),
      Function.Injective P.mulVec ∧ Gᵀ=G ∧ Function.Injective G.mulVec ∧ P*G*Pᵀ=M := by
  let A := pack (colSp M)
  have ha := pack_inj (colSp M)
  obtain ⟨L,hL⟩ := mat_left_inv ha
  let H := L*M*Lᵀ
  have hs := invariant_cols M A L (colSp_pack _) hL
  have hx : A*H*Aᵀ=M := by
    rw [show A*H=A*(L*M)*Lᵀ from (Matrix.mul_assoc ..).symm, hs]
    simpa only [transpose_mul,hm] using congrArg Matrix.transpose hs
  refine ⟨A,H,ha,?_,mrk_inj.mpr ?_,hx⟩
  · change (L*M*Lᵀ)ᵀ = L*M*Lᵀ
    rw [transpose_mul,transpose_mul,transpose_transpose,hm, Matrix.mul_assoc]
  · refine le_antisymm (Matrix.rank_le_card_width _) ?_
    rw [Fintype.card_fin]
    have h := (Matrix.rank_mul_le_left (A*H) Aᵀ).trans (Matrix.rank_mul_le_right _ _)
    rwa [hx] at h

omit [Fintype Q] in
theorem matrix_cancel_left {A : Mat I J} (hA : Function.Injective A.mulVec)
    (C D : Mat J Q) (h : A*C=A*D) : C=D := by
  classical
  obtain ⟨R,hR⟩ := mat_left_inv hA
  have hh := congrArg ((R * ·) : Mat I Q → _) h
  simpa only [← Matrix.mul_assoc,hR,Matrix.one_mul] using hh

theorem eigenbasis_idem {A : Type} [AddCommGroup A] [Module F A] [Fintype A]
    [FiniteDimensional F A] (E : J → A →ₗ[F] A) (h : ∀ i j x, E i (E j x)=E j (E i x))
    (hg : ∀ i x, E i (E i x)=E i x) :
    ∃ B : Basis (Fin (dim A)) F A, ∀ i t, ∃ c : F, E t (B i)=c • B i := by
  classical
  let s (I : Finset J) := {x : A | ∀ i ∈ I, ∃ c : F, E i x=c • x}
  have he (I : Finset J) : Submodule.span F (s I) = ⊤ := by
    induction I using Finset.induction with
    | empty => simp [s]
    | insert t I _ ih =>
      rw [← ih]
      refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.mpr ?_)
      · exact fun x hx i hi => hx i (Finset.mem_insert_of_mem hi)
      intro x hx
      have hi (i) (hi : i ∈ I) :
          ∃ c : F, E i x = c • x ∧ E i (E t x) = c • E t x := by
        obtain ⟨c,hc⟩ := hx i hi
        exact ⟨c,hc,by rw [h,hc,map_smul]⟩
      have ht : E t x ∈ s (insert t I) := by
        intro j hj; rcases Finset.mem_insert.mp hj with rfl|hj
        · exact ⟨1, by rw [hg,one_smul]⟩
        obtain ⟨c,_,he⟩ := hi j hj
        exact ⟨c,he⟩
      have hu : x-E t x ∈ s (insert t I) := by
        intro j hj; rcases Finset.mem_insert.mp hj with rfl|hj
        · exact ⟨0,by rw [map_sub,hg,sub_self,zero_smul]⟩
        obtain ⟨c,hc,hc'⟩ := hi j hj
        exact ⟨c,by rw [map_sub,hc,hc',smul_sub]⟩
      have hw := Submodule.add_mem (Submodule.span F (s (insert t I))) (Submodule.subset_span hu)
        (Submodule.subset_span ht)
      rwa [sub_add_cancel] at hw
  let B := Basis.ofSpan (he Finset.univ).ge
  let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis B).symm
  refine ⟨B.reindex e,fun i t => ?_⟩
  have hb : Set.range B ⊆ s Finset.univ := Basis.extendLe_subset ..
  rw [Basis.reindex_apply]
  exact hb (show B (e.symm i) ∈ Set.range B from ⟨_,rfl⟩) t (Finset.mem_univ _)

theorem diagonalize [DecidableEq I] (M : J → Mat I I)
    (hm : ∀ i j, M i * M j=M j*M i) (hg : ∀ i,M i*M i=M i) :
    ∃ (C D : Mat I I) (f : J → I → F), D*C=1 ∧ C*D=1 ∧ ∀ i, M i*C=C*diagonal (f i) := by
  classical
  let E i := (M i).mulVecLin
  have hh i j x : E i (E j x)=E j (E i x) := by
    simp only [E, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    rw [hm]
  have hb i x : E i (E i x)=E i x := by
    simp only [E, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,hg]
  obtain ⟨B,hB⟩ := eigenbasis_idem E hh hb
  let A : Basis I F (Vec I) :=
    B.reindex (Fintype.equivOfCardEq (by rw [Fintype.card_fin,dim_vec]))
  have h (i j) : ∃ c : F, E i (A j) = c • A j := by
    unfold A; rw [Basis.reindex_apply]; exact hB _ _
  choose f hf using h
  let C : Mat I I := Matrix.of (fun i j => A j i)
  have hi : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.mpr A.linearIndependent
  obtain ⟨D,hD⟩ := mat_left_inv hi
  have he : C*D=1 := mul_eq_one_comm.mp hD
  refine ⟨C,D,f,hD,he,fun i => ?_⟩
  ext j k
  rw [Matrix.mul_diagonal]
  have hk := congr_fun (hf i k) j
  change ∑ l, M i j l * A k l = f i k*A k j at hk
  change ∑ l, M i j l * A k l = A k j * _
  rw [hk,mul_comm]

end HadwigerCounterexample

end

end OAI
