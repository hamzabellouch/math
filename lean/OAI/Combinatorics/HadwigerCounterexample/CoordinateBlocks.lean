import OAI.Combinatorics.HadwigerCounterexample.BooleanLabels
import OAI.Combinatorics.HadwigerCounterexample.QuadraticTesters
import OAI.Combinatorics.HadwigerCounterexample.CoordinateEmbeddings

namespace OAI

/-! # Coordinate Blocks -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}

def blockA (p : Shape) (n : ℕ) (B : Block p.g) : Mat (AIdx p.g n) (Fin n) :=
  embedMat (fun i => some (B,i))

def blockRay (p : Shape) (n : ℕ) (s : Label p.b) (B : Block p.g) : Mat (Row p n) (Fin n) :=
  labMat p n s * blockA p n B

theorem lab_inj (s : Label p.b) : Function.Injective (labMat p n s).mulVec := by
  intro x y he
  funext i
  rw [labMat_act,labMat_act] at he
  have h := congr_fun he (emptySel,i)
  simpa [putLab,selV,emptySel] using h

theorem joined_lab_inj {s t : Label p.b} (hj : 1≤p.j) (hs : s≠t) :
    Function.Injective (fromCols (labMat p n s) (labMat p n t)).mulVec := by
  apply inj_fromCols (lab_inj _) (lab_inj _)
  classical
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨v,rfl⟩,w,h⟩
  simp only [mulVecLin_apply,labMat_act] at h
  let Z : Label p.b → Vec (AIdx p.g n) := fun i => if i=s then v else -w
  have he : ∑ i ∈ ({s,t} : Finset _), putLab p n i (Z i)=0 := by
    simp [Z,hs,hs.symm,map_neg,h]
  have hi : ({s,t}:Finset _).card ≤ p.j+1 := by
    have hh : ({s,t}:Finset _).card=2 := by simp [hs]
    omega
  have hg := ray_indep _ _ hi he s (by simp)
  have hv : v=0 := by simpa [Z] using hg
  rw [hv,map_zero]; exact Submodule.zero_mem _

theorem block_inj (B : Block p.g) : Function.Injective (blockA p n B).mulVec :=
  embedMat_inj (show Function.Injective (fun i => some (B,i)) from
    fun _ _ h => congrArg Prod.snd (Option.some.inj h))

theorem blockRay_inj (p : Shape) (n) (s) (B) :
    Function.Injective (blockRay p n s B).mulVec :=
  inj_comp_mat _ _ (lab_inj _) (block_inj B)

theorem joined_block_inj {s t : Label p.b} (hj : 1 ≤ p.j) (hs : s ≠ t) (B : Block p.g) :
    Function.Injective (fromCols (blockRay p n s B) (blockRay p n t B)).mulVec := by
  classical
  apply inj_fromCols (blockRay_inj ..) (blockRay_inj ..)
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨v,rfl⟩,w,h⟩
  simp only [Matrix.mulVecLin_apply,blockRay,← Matrix.mulVec_mulVec] at h
  let a := Sum.elim (blockA p n B *ᵥ v) (0 : Vec (AIdx p.g n))
  let b := Sum.elim (0 : Vec (AIdx p.g n)) (blockA p n B *ᵥ w)
  have heq : a=b := joined_lab_inj hj hs (by
    dsimp only [a,b]
    rw [fromCols_mulVec_sumElim,fromCols_mulVec_sumElim,Matrix.mulVec_zero,
      Matrix.mulVec_zero,zero_add,add_zero,h])
  have hg : blockA p n B *ᵥ v = 0 := funext (fun x => congr_fun heq (.inl x))
  change blockRay p n s B *ᵥ v ∈ _
  rw [blockRay,← Matrix.mulVec_mulVec,hg,Matrix.mulVec_zero]
  exact Submodule.zero_mem _

theorem blockRay_eval (p : Shape) (s : Label p.b) (B) (i) (j : Fin n) :
    blockRay p n s B i j = if i.2=some (B,j) then monoBit s i.1.val else 0 := by
  rw [blockRay,blockA,mul_embedMat]; rfl

theorem project_pick {d B : Block p.g} (hd : d ≠ B) (a) (s) (i) :
    (blockRay p n s B)ᵀ *ᵥ pick p n a d i = 0 := by
  classical
  unfold pick
  split
  · rename_i hi
    rw [Matrix.mulVec_single_one]
    ext j
    change blockRay p n s B (a,some (d,⟨i,hi⟩)) j=0
    simp [blockRay_eval,hd]
  rw [Matrix.mulVec_zero]

theorem project_same (B : Block p.g) (a s) (i : Fin n) :
    (blockRay p n s B)ᵀ *ᵥ pick p n a B i.val = Pi.single i (monoBit s a.val) := by
  classical
  rw [pick,dite_eq_left i.isLt,Matrix.mulVec_single_one]
  ext j
  change blockRay p n s B _ j=_
  rw [blockRay_eval]
  simp [Pi.single_apply, eq_comm]

def pullM {I J V U : Type} [Fintype V] [Fintype U] (P : Mat V I) (Q : Mat U J) :
    Mat V U →ₗ[F] Mat I J := liftM Pᵀ Qᵀ
theorem pullM_def {I J V U : Type} [Fintype V] [Fintype U] (P : Mat V I)
    (Q : Mat U J) (M : Mat V U) : pullM P Q M=Pᵀ*M*Q := rfl

theorem pull_test {d B : Block p.g} (h : d≠B) (s s') :
    pullM (blockRay p n s B) (blockRay p n s' B) (testM p n d) = 0 := by
  unfold testM pullM
  simp only [map_sum,liftM_outer,project_pick h]
  simp

theorem pull_self_Z (M) (s s' : Label p.b) :
    pullM (blockRay p n s Block.Z) (blockRay p n s' Block.Z) (selfM p n M)=0 := by
  let L := pullM (blockRay p n s Block.Z) (blockRay p n s' Block.Z)
  have hx (i j : Tag p.g) := pull_test (n:=n) (d:=Block.O i j)
    (B:=Block.Z) (by simp [Block.O,Block.Z]) s s'
  have hs := pull_test (p:=p) (n:=n) (d:=Block.S) (B:=Block.Z) (by simp [Block.S,Block.Z]) s s'
  have h (a : SelIdx p.b p.j) (s : Label p.b) (i) :=
    project_pick (n:=n) (p:=p) (d:=Block.sharp) (B:=Block.Z) (by simp [Block.sharp,Block.Z]) a s i
  rw [selfM]; simp only [map_add,map_sum,hx,hs,Finset.sum_const_zero,zero_add]
  unfold sharpM sharpPick pullM
  by_cases he : 1 ≤ p.j
  · simp only [map_sum,map_smul,map_add, dite_eq_left he,liftM_outer,h]
    simp
  · simp only [dite_eq_right he]; simp

theorem pull_self_sharp (M) (s s' : Label p.b) (hj : 1≤p.j) :
    pullM (blockRay p n s Block.sharp) (blockRay p n s' Block.sharp) (selfM p n M) =
      ∑ i, (s i+s' i) • M i := by
  classical
  have hx (i j : Tag p.g) := pull_test (n:=n) (d:=Block.O i j)
    (B:=Block.sharp) (by simp [Block.O,Block.sharp]) s s'
  have hs := pull_test (p:=p) (n:=n) (d:=Block.S) (B:=Block.sharp) (by simp [Block.S,Block.sharp]) s s'
  rw [selfM]; simp only [map_add,map_sum,hx,hs,Finset.sum_const_zero,zero_add]
  unfold sharpM sharpPick pullM
  simp only [map_sum,map_add,map_smul, dite_eq_left hj,liftM_outer,project_same]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext a b
  simp only [Matrix.sum_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    vecMulVec_apply,monoBit,emptySel,Finset.prod_empty,Finset.prod_singleton,Pi.single_apply]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp; ring
    · intro j _ h; simp [h.symm]
    · simp
  · intro j _ h; simp [h.symm]
  simp
end HadwigerCounterexample

end

end OAI
