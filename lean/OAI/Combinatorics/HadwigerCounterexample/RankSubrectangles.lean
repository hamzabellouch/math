import OAI.Combinatorics.HadwigerCounterexample.GramCharacterExpansion

namespace OAI

/-! # Rank Subrectangles -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] in
theorem basis_subcolumns (A : Mat I J) :
    ∃ f : Fin A.rank→J, Injective (A.submatrix _root_.id f).mulVec := by
  classical
  let M (S : Finset J) := Submodule.span F (A.col '' (S : Set J))
  have hg (S : Finset J) : ∃ T⊆S,M T=M S ∧ T.card=dim (M T) := by
    induction S using Finset.induction with
    | empty =>
      have he : M ∅ = ⊥ := by
        unfold M
        rw [show (A.col '' ((∅ : Finset J) : Set _))=∅ by ext; simp, Submodule.span_empty]
      refine ⟨∅,by simp,rfl,?_⟩; rw [he]; exact (finrank_bot ..).symm
    | insert x S hx ih =>
      obtain ⟨T,hT,hM,hD⟩ := ih
      have he (S : Finset J) :
          M (insert x S)=M S⊔Submodule.span F ({A.col x}:Set _) := by
        unfold M
        rw [← span_union]
        congr 1
        ext; simp
      rw [he,←hM]
      by_cases h : A.col x∈M T
      · exact ⟨T,hT.trans (Finset.subset_insert _ _),
          (sup_eq_left.mpr (by rwa [Submodule.span_singleton_le_iff_mem])).symm,hD⟩
      refine ⟨insert x T,Finset.insert_subset_insert x hT,he T,?_⟩
      rw [Finset.card_insert_of_notMem (fun v => hx (hT v)), he,hD]
      exact (Submodule.finrank_sup_span_singleton h).symm
  obtain ⟨S,hS,hA,ht⟩ := hg Finset.univ
  have hs : M S=colSp A := by
    rw [hA,colSp, Matrix.range_mulVecLin]; unfold M
    congr 1
    ext x; simp
  have he : S.card=A.rank := by rw [ht,hs,colSp_dim]
  let e := Fintype.equivFinOfCardEq (Fintype.card_coe S |>.trans he)
  let f (x : Fin A.rank) := (e.symm x).val
  have hB : colSp (A.submatrix _root_.id f)=M S := by
    rw [colSp,Matrix.range_mulVecLin]; unfold M
    congr 1
    ext x; constructor
    · rintro ⟨k,rfl⟩; exact ⟨f k,(e.symm k).property,rfl⟩
    · rintro ⟨k,h,rfl⟩
      refine ⟨e ⟨k,h⟩,?_⟩
      have heq : f (e ⟨k,h⟩) = k := by unfold f; rw [Equiv.symm_apply_apply]
      ext; simp [Matrix.col_apply,heq]
  rw [hs] at hB
  refine ⟨f,mrk_inj.mpr ?_⟩
  rw [← colSp_dim,hB,Fintype.card_fin,colSp_dim]

theorem minor_arc (A : Mat I J) :
    ∃ (f : Fin A.rank→ I) (g : Fin A.rank→ J), Injective (A.submatrix f g).mulVec := by
  classical
  let t := A.rank
  obtain ⟨g,hg⟩ := basis_subcolumns A
  let B := A.submatrix _root_.id g
  have he : Bᵀ.rank=t := (Matrix.rank_transpose _).trans ((mrk_inj.mp hg).trans
    (Fintype.card_fin _))
  obtain ⟨f,hf⟩ : ∃ f : Fin t→I,Injective ((Bᵀ.submatrix _root_.id f)).mulVec := by
    have hi := basis_subcolumns Bᵀ
    rwa [he] at hi
  have hh := mrk_inj.mp hf
  refine ⟨f,g,mrk_inj.mpr ?_⟩
  rw [← Matrix.rank_transpose]
  exact hh

private theorem lastCol {t : ℕ} {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Mat I J)
    (f : Fin t→I) (g : Fin t→J) (x : I) (y : J)
    (h : (A.submatrix (Sum.elim f (fun _ : Unit => x))
      (Sum.elim g (fun _ : Unit => y))).rank ≤ t)
    (hb : Injective (A.submatrix f g).mulVec) :
    ∃ z : Vec (Fin t),(A.submatrix f g)*ᵥ z=(fun i => A (f i) y) ∧
      A x y=∑ i,A x (g i)*z i := by
  classical
  let C := A.submatrix (Sum.elim f (fun _ : Unit => x)) (Sum.elim g (fun _ : Unit => y))
  let M := C.submatrix _root_.id (.inl ·)
  have hm : Injective M.mulVec := by
    intro X Y h
    apply hb
    funext i
    exact congr_fun h (.inl i)
  have hM : colSp M≤colSp C := by
    rw [colSp,colSp, Matrix.range_mulVecLin,Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro s ⟨i,rfl⟩; exact ⟨.inl i,rfl⟩
  have he : colSp M=colSp C := Submodule.eq_of_le_of_finrank_le hM (by
    have he : dim (colSp M)=t := (mrk_inj.mp hm).trans (Fintype.card_fin _)
    change dim (colSp C) ≤ dim (colSp M)
    rw [he]; exact h)
  obtain ⟨v,hv⟩ := show C.col (.inr ()) ∈ colSp M from he.symm ▸ colSp_mem _
  exact ⟨v,funext (fun i => congr_fun hv (.inl i)),(congr_fun hv (.inr ())).symm⟩

theorem border_same {t : ℕ} (A B : Mat I J) (f : Fin t→I) (g : Fin t→J)
    (x : I) (y : J)
    (h : Injective (A.submatrix f g).mulVec)
    (hx : ∀ i j,A (f i) j=B (f i) j)
    (hy : ∀ i j,A i (g j)=B i (g j))
    (hA : (A.submatrix (Sum.elim f (fun _ : Unit => x))
      (Sum.elim g (fun _ : Unit => y))).rank ≤ t)
    (hB : (B.submatrix (Sum.elim f (fun _ : Unit => x))
      (Sum.elim g (fun _ : Unit => y))).rank ≤ t) :
    A x y=B x y := by
  classical
  have hh : A.submatrix f g=B.submatrix f g := Matrix.ext fun i j => hx i _
  obtain ⟨s,hs,hL⟩ := lastCol A f g x y hA h
  obtain ⟨s',hs',hR⟩ := lastCol B f g x y hB (hh ▸ h)
  obtain rfl : s=s' := h ((show A.submatrix f g *ᵥ s=(fun i => A (f i) y) from hs).trans
    ((funext (fun i => hx i y)).trans (hh ▸ hs'.symm)))
  rw [hL,hR]; simp_rw [hy]

end HadwigerCounterexample

end

end OAI
