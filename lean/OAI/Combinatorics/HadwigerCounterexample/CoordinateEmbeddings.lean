import OAI.Combinatorics.HadwigerCounterexample.MatrixRanks
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace OAI

/-! # Coordinate Embeddings -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function
open scoped BigOperators
variable {U V I J K T : Type} [Fintype U] [Fintype V] [Fintype I] [Fintype J]
    [Fintype K] [Fintype T]

def embedMat [DecidableEq U] (f : I → U) : Mat U I := Matrix.of (fun i j => if i=f j then 1 else 0)

omit [Fintype I] in
theorem embedMatT [DecidableEq U] (f : I → U) (x : Vec U) :
    (embedMat f)ᵀ *ᵥ x = fun i => x (f i) := by
  classical funext i
            simp [embedMat,Matrix.mulVec,dotProduct]

omit [Fintype V] [Fintype I] in
theorem mul_embedMat [DecidableEq U] (f : I → U) (M : Mat V U) :
    M*embedMat f = M.submatrix _root_.id f := by
  ext i j
  simp [Matrix.mul_apply,embedMat]

omit [Fintype V] [Fintype I] in
theorem embedMat_mul [DecidableEq U] (f : I → U) (M : Mat U V) :
    (embedMat f)ᵀ*M = M.submatrix f _root_.id := by
  ext i j
  simp [Matrix.mul_apply,embedMat]

omit [Fintype I] in
theorem embedMat_self [DecidableEq I] [DecidableEq U] {f : I → U} (h : Injective f) :
    (embedMat f)ᵀ * embedMat f = 1 := by
  ext i j
  rw [embedMat_mul]
  simp only [embedMat,Matrix.submatrix_apply,Matrix.of_apply,id_eq,
    Matrix.one_apply,h.eq_iff]

theorem embedMat_inj [DecidableEq U] {f : I → U} (h : Injective f) :
    Injective (embedMat f).mulVec := by
  classical
  intro x y g
  change embedMat f *ᵥ x = embedMat f *ᵥ y at g
  have he (x : Vec I) : (embedMat f)ᵀ *ᵥ (embedMat f *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec,embedMat_self h,Matrix.one_mulVec]
  rw [← he x,g,he]

omit [Fintype U] in
theorem inj_fromCols {A : Mat U I} {B : Mat U J} (hA : Injective A.mulVec)
    (hB : Injective B.mulVec) (h : Disjoint (colSp A) (colSp B)) :
    Injective (fromCols A B).mulVec := by
  rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  let a := fun i => x (Sum.inl i)
  let b := fun j => x (Sum.inr j)
  rw [fromCols_mulVec] at hx
  have he : A*ᵥa=B*ᵥb := add_right_cancel (hx.trans (char_two (B*ᵥb)).symm)
  have hi : A*ᵥa ∈ colSp A ⊓ colSp B :=
    ⟨⟨a,rfl⟩, he.symm ▸ (show B*ᵥb∈colSp B from ⟨b,rfl⟩)⟩
  rw [h.eq_bot] at hi
  have hg : A*ᵥa=0 := by simpa using hi
  have ha : a=0 := hA (hg.trans (Matrix.mulVec_zero A).symm)
  rw [he] at hg
  have hb : b=0 := hB (hg.trans (Matrix.mulVec_zero B).symm)
  funext i
  cases i
  · exact congr_fun ha _
  · exact congr_fun hb _

/-- Specify an arbitrary cross Gram bilinear form between independent columns. -/
theorem prescribe_between {A : Mat U I} {B : Mat V J}
    (hA : Injective A.mulVec) (hB : Injective B.mulVec) (M : Mat I J) :
    ∃ L : Mat U V, Aᵀ*L*B=M := by
  classical
  obtain ⟨a,ha⟩ := mat_left_inv hA
  obtain ⟨b,hb⟩ := mat_left_inv hB
  refine ⟨aᵀ*(M*b),?_⟩
  rw [← Matrix.mul_assoc Aᵀ,←transpose_mul,ha,transpose_one,Matrix.one_mul,
    Matrix.mul_assoc,hb,Matrix.mul_one]

/-- Two opposite-direction restrictions are specifiable on disjoint bases. -/
theorem prescribe_opposite {A : Mat U I} {B : Mat V J} {C : Mat U K} {D : Mat V T}
    (hc : Injective (fromCols A C).mulVec) (hd : Injective (fromCols B D).mulVec)
    (M : Mat I J) (N : Mat T K) :
    ∃ L : Mat U V, Aᵀ*L*B=M ∧ Dᵀ*Lᵀ*C=N := by
  obtain ⟨L,hL⟩ := prescribe_between hc hd (fromBlocks M 0 0 Nᵀ)
  rw [transpose_fromCols, fromRows_mul, fromRows_mul_fromCols] at hL
  have hi : Cᵀ*L*D=Nᵀ := congrArg Matrix.toBlocks₂₂ hL
  refine ⟨L, congrArg Matrix.toBlocks₁₁ hL, ?_⟩
  have hg := congrArg Matrix.transpose hi
  rwa [transpose_mul,transpose_mul,transpose_transpose,transpose_transpose,← Matrix.mul_assoc] at hg

omit [Fintype I] in
theorem rank_ge_mul (A : Mat I J) (B : Mat J K) :
    A.rank+B.rank ≤ (A*B).rank+Fintype.card J := by
  let f := A.mulVecLin
  let g := f ∘ₗ (colSp B).subtype
  have he : LinearMap.range g = colSp (A*B) := by
    change LinearMap.range g = LinearMap.range ((A*B).mulVecLin)
    rw [mulVecLin_mul]
    unfold g
    rw [LinearMap.range_comp,LinearMap.range_comp]
    simp [f,colSp]
  have hi : dim (LinearMap.ker g) ≤ dim (LinearMap.ker f) := by
    let q := ((colSp B).subtype ∘ₗ (LinearMap.ker g).subtype)
    have hq (x : LinearMap.ker g) : q x ∈ LinearMap.ker f := x.property
    let k := q.codRestrict (LinearMap.ker f) hq
    have hk : Injective k := by
      intro x y h
      have heq := congrArg (fun b : LinearMap.ker f => b.val) h
      exact Subtype.ext (Subtype.ext heq)
    exact LinearMap.finrank_le_finrank_of_injective hk
  have h1 := g.finrank_range_add_finrank_ker
  rw [he] at h1
  have h2 := f.finrank_range_add_finrank_ker
  change (A*B).rank + dim (LinearMap.ker g)=B.rank at h1
  change A.rank + dim (LinearMap.ker f)=dim (Vec J) at h2
  rw [dim_vec] at h2; omega

theorem rank_ge_congr (A : Mat I I) (B : Mat J I) :
    A.rank + 2*B.rank ≤ (liftM B B A).rank + 2*Fintype.card I := by
  have h1 := rank_ge_mul B A
  have h2 := rank_ge_mul (B*A) Bᵀ
  rw [Matrix.rank_transpose] at h2
  rw [liftM_def]; omega

/-- Choose a large space in the domain which becomes disjoint from S in the target. -/
theorem choose_free {A : Mat I J} (hA : Injective A.mulVec) (S : Space (Vec I)) :
    ∃ T : Space (Vec J), Fintype.card J ≤ dim T+dim S ∧
      Disjoint S (colSp (A*pack T)) := by
  let U := S.comap A.mulVecLin
  obtain ⟨T,hT⟩ := U.exists_isCompl
  refine ⟨T,?_,?_⟩
  · have hi : dim U ≤ dim S := by
      let q := A.mulVecLin ∘ₗ U.subtype
      have he (x : U) : q x∈S := x.property
      let B := q.codRestrict S he
      have hb : Injective B := fun x y h => Subtype.ext (hA
        (show q x=q y from congrArg Subtype.val h))
      exact LinearMap.finrank_le_finrank_of_injective hb
    have he := (U.prodEquivOfIsCompl T hT).finrank_eq
    rw [finrank_prod,show finrank F (Vec J)=Fintype.card J from dim_vec _] at he
    change dim U + dim T = Fintype.card J at he
    rw [← he]
    exact (Nat.add_le_add_right hi _).trans_eq (Nat.add_comm _ _)
  rw [colSp,mulVecLin_mul,LinearMap.range_comp,show LinearMap.range (pack T).mulVecLin = T from
    colSp_pack T]
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx,y,hy,rfl⟩
  have hh : y∈U⊓T := ⟨hx,hy⟩
  rw [hT.inf_eq_bot] at hh
  have he : y=0 := by simpa using hh
  rw [he,map_zero]; exact Submodule.zero_mem _

end HadwigerCounterexample

end

end OAI
