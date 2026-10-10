import OAI.Combinatorics.HadwigerCounterexample.RealizationConditions

namespace OAI

/-! # Primal Channel Decomposition -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Submodule
variable {I : Type} [Fintype I]

/-- Onto projection in coordinates, killing a specified disjoint subspace. -/
structure ProjData (S T : Space (Vec I)) (A : Mat I I) : Prop where
  onto (x) : A *ᵥ x ∈ S
  fixes x : x ∈ S → A *ᵥ x=x
  kills x : x∈T → A *ᵥ x=0

theorem proj_exists (S T : Space (Vec I)) (h : Disjoint S T) :
    ∃ A, ProjData S T A := by
  classical
  obtain ⟨A,hA⟩ := mat_left_inv (inj_fromCols (pack_inj S) (pack_inj T)
    (by rw [colSp_pack, colSp_pack]; exact h))
  let B := A.toRows₁
  let C := A.toRows₂
  have he : fromRows B C * fromCols (pack S) (pack T)=1 := by
    rw [show fromRows B C=A from Matrix.fromRows_toRows A,hA]
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one] at he
  have hb : B*pack S=1 := congrArg Matrix.toBlocks₁₁ he
  have hg : B*pack T=0 := congrArg Matrix.toBlocks₁₂ he
  refine ⟨pack S*B,fun x => ?_,fun x hx => ?_,fun x hx => ?_⟩
  · rw [←mulVec_mulVec]
    exact (pack_mem_iff ..).mpr ⟨_,rfl⟩
  · obtain ⟨x,rfl⟩ := (pack_mem_iff ..).mp hx
    rw [←mulVec_mulVec, mulVec_mulVec _ B, hb,one_mulVec]
  · obtain ⟨x,rfl⟩ := (pack_mem_iff ..).mp hx
    rw [←mulVec_mulVec,mulVec_mulVec _ B,hg,zero_mulVec,mulVec_zero]

theorem rank_maps {J : Type} [Fintype J] {A : Mat I J} (S : Space (Vec I))
    (ha : ∀ x,A *ᵥ x∈ S) : A.rank ≤ dim S :=
  Submodule.finrank_mono (show colSp A ≤ S by
    rintro x ⟨x,rfl⟩; exact ha x)

theorem evmat_addM {J : Type} [Fintype J] (A B : Mat I J) (x y) :
    evmat (A+B) x y = evmat A x y+evmat B x y := by rw [←mpair_outer,mpair_add,
      mpair_outer,mpair_outer]

theorem evmat_subM {J : Type} [Fintype J] (A B : Mat I J) (x y) :
    evmat (A-B) x y = evmat A x y-evmat B x y := by
  rw [ZModModule.sub_eq_add, ZModModule.sub_eq_add, evmat_addM]

variable {p : Shape} {n : ℕ}

/-- aggregate primal (resp. channel) directions in a unit. -/
def primal (p : Shape) (n : ℕ) := colSp (IP p n true) ⊔ colSp (IP p n false)
def channels (p : Shape) (n : ℕ) := colSp (IH p n true) ⊔ colSp (IH p n false)

theorem ip_le_primal (b : Bool) : colSp (IP p n b)≤primal p n := by
  cases b; exact le_sup_right; exact le_sup_left

theorem ih_le_channels (b : Bool) : colSp (IH p n b)≤channels p n := by
  cases b; exact le_sup_right; exact le_sup_left

theorem channels_proj (b : Bool) : channels p n ≤ LinearMap.ker (IP p n b)ᵀ.mulVecLin := by
  have hi (i : Bool) : colSp (IH p n i) ≤ LinearMap.ker (IP p n b)ᵀ.mulVecLin := by
    rintro x ⟨y,rfl⟩
    change (IP p n b)ᵀ *ᵥ (IH p n i *ᵥ y) = _
    rw [mulVec_mulVec, IP_IH, Matrix.zero_mulVec]
  exact sup_le (hi _) (hi _)

theorem primal_proj (b : Bool) : primal p n ≤ LinearMap.ker (IH p n b)ᵀ.mulVecLin := by
  have hi (i : Bool) : colSp (IP p n i) ≤ LinearMap.ker (IH p n b)ᵀ.mulVecLin := by
    rintro x ⟨y,rfl⟩
    change (IH p n b)ᵀ *ᵥ (IP p n i *ᵥ y) = _
    rw [mulVec_mulVec, IH_IP, Matrix.zero_mulVec]
  exact sup_le (hi _) (hi _)

theorem channels_disjoint : Disjoint (primal p n) (channels p n) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx,hy⟩
  have he (b : Bool) : (IP p n b)ᵀ *ᵥ x = 0 := channels_proj b hy
  have hf (b : Bool) : (IH p n b)ᵀ *ᵥ x = 0 := primal_proj b hx
  have hh := ip_decomp (show Dir p n from x)
  simp_rw [he,hf,mulVec_zero,add_zero, Finset.sum_const_zero] at hh
  rw [← hh]
  exact Submodule.zero_mem _

/-- prSmall a z consists of the pure-primal coordinates kept by the small
table. -/
def prSmall (a : Plan p n) (z : Place p) :=
  (sPin a z true).map (IP p n true).mulVecLin ⊔
    (sPin a z false).map (IP p n false).mulVecLin

theorem prSmall_le (a : Plan p n) (z : Place p) : prSmall a z≤primal p n := by
  apply sup_le_sup <;> rintro x ⟨x,h,rfl⟩ <;> exact ⟨x,rfl⟩

theorem prSmall_dim (a : Plan p n) (z : Place p) :
    dim (prSmall a z)≤2 * planRank a := by
  rw [two_mul]
  have hh (i : Bool) :
      dim ((sPin a z i).map (IP p n i).mulVecLin) ≤ planRank a :=
    (Submodule.finrank_map_le ..).trans ((sPin_dim ..).trans (dim_le_plan a z))
  exact (Submodule.finrank_add_le_finrank_add_finrank ..).trans (Nat.add_le_add (hh _) (hh _))

theorem prSmall_table (a : Plan p n) (z : Place p) :
    tabSpace a z = prSmall a z ⊔ channels p n := by
  unfold tabSpace halfTable prSmall channels
  ac_rfl

theorem keyPlane (v : Volley p n I) (t : Tagging p I) (z : Place p) :
    v.keyPlan t z≤ primal p n := by
  unfold Volley.keyPlan colSp
  rw [range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro x ⟨j,rfl⟩
  exact (show colSp (IP p n _) ≤ primal p n from ip_le_primal (v.obj j.val))
    (show v.rayLoc j.val∈colSp (IP p n _) from ⟨_,rfl⟩)

end HadwigerCounterexample

end

end OAI
