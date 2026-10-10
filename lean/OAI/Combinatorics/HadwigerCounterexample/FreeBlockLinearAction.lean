import OAI.Combinatorics.HadwigerCounterexample.UnaryQueryFrequencies

namespace OAI

/-! # Free Block Linear Action -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
abbrev Flit (n : ℕ) := Move (Fin n)

def breeze (p : Shape) (M : Mat (Fin n) (Fin n)) (x : Ray p n) : Ray p n :=
  fun i =>
    match i.2 with
    | none => x i
    | some (B,j) => if B=Block.Z then (M *ᵥ (fun j => x (i.1,some (Block.Z,j)))) j else x i

def blitzL (p : Shape) (M : Mat (Fin n) (Fin n)) : Ray p n →ₗ[F] Ray p n where
  toFun := breeze p M
  map_add' x y := by
    have he (i : SelIdx p.b p.j) :
        (fun j : Fin n => (x+y) (i,some (Block.Z,j)))=
        ((fun j => x (i,some (Block.Z,j)))+ (fun j => y (i,some (Block.Z,j)))) := rfl
    funext i; rcases i with ⟨i, _|⟨B,j⟩⟩
    · rfl
    by_cases h : B=Block.Z
    · simp only [breeze,h,ite_true,he,mulVec_add]
      rfl
    simp [breeze,h]
  map_smul' a x := by
    have he (i : SelIdx p.b p.j) :
        (fun j : Fin n => (a•x) (i,some (Block.Z,j)))=
        a • (fun j => x (i,some (Block.Z,j))) := rfl
    funext i; rcases i with ⟨i, _|⟨B,j⟩⟩
    · rfl
    by_cases h : B=Block.Z
    · simp only [breeze,h,ite_true,he,mulVec_smul]; rfl
    simp [breeze,h]

def blitz (p : Shape) (M : Mat (Fin n) (Fin n)) := LinearMap.toMatrix' (blitzL p M)

theorem blitz_val (p : Shape) (M : Mat (Fin n) (Fin n)) (x) :
    blitz p M *ᵥ x=breeze p M x := by
  change LinearMap.toMatrix' (blitzL p M)*ᵥ x=blitzL p M x
  simp

theorem blitz_mul (p : Shape) (M L : Mat (Fin n) (Fin n)) :
    blitz p (M*L)=blitz p M*blitz p L := by
  classical
  apply coe_mv_inj
  apply LinearMap.ext
  intro x; simp_rw [mulVecLin_apply,← mulVec_mulVec,blitz_val]
  funext i; rcases i with ⟨i, _|⟨B,j⟩⟩
  · rfl
  by_cases h : B=Block.Z
  · simp only [breeze,h,ite_true,←mulVec_mulVec]
  simp [breeze,h]

theorem blitz_one (p : Shape) (n : ℕ) : blitz p (1:Mat (Fin n) (Fin n))=1 := by
  apply coe_mv_inj; apply LinearMap.ext; intro x
  rw [mulVecLin_apply,mulVecLin_apply,Matrix.one_mulVec,blitz_val]
  funext i; rcases i with ⟨i, _|⟨B,j⟩⟩
  · rfl
  by_cases h : B=Block.Z <;> simp [breeze,h]

theorem blitz_pick (p : Shape) (M : Mat (Fin n) (Fin n)) (s : SelIdx p.b p.j)
    (B : Block p.g) (h : B≠Block.Z) (i : ℕ) :
    (blitz p M)ᵀ *ᵥ pick p n s B i=pick p n s B i := by
  classical
  apply sub_eq_zero.mp
  apply dot_ext_zero; intro x
  unfold pick
  split
  next hn =>
    rw [dotProduct_sub,dotProduct_transpose_mulVec,single_one_dotProduct,dotProduct_single,
      blitz_val]; simp [breeze,h]
  next => rw [Matrix.mulVec_zero,sub_zero,dotProduct_zero]

set_option maxHeartbeats 600000 in
theorem blitz_fixes (p : Shape) (M : Mat (Fin n) (Fin n)) (m : Mixer p n) :
    pullM (blitz p M) (blitz p M) (selfM p n m.mixM)=selfM p n m.mixM := by
  classical
  let T := blitz p M
  have h1 (i j : Tag p.g) : Block.O i j ≠ Block.Z := by simp [Block.O,Block.Z]
  have h2 : (@Block.S p.g) ≠ Block.Z := by simp [Block.S,Block.Z]
  have h3 : (@Block.sharp p.g) ≠ Block.Z := by simp [Block.sharp,Block.Z]
  have hh (B : Block p.g) (h : B ≠ Block.Z) :
      pullM T T (testM p n B)=testM p n B := by
    unfold pullM testM
    simp_rw [map_sum, liftM_outer, T,blitz_pick p M _ B h]
  have hr (a i) : Tᵀ*ᵥsharpPick p n a i=sharpPick p n a i := by
    unfold sharpPick
    split
    next h => exact blitz_pick p M _ _ h3 _
    next h => rw [Matrix.mulVec_zero]
  have ht :
      pullM T T (sharpM p n m.mixM)=sharpM p n m.mixM := by
    unfold sharpM pullM
    simp_rw [map_sum,map_smul,map_add,liftM_outer,hr,T,blitz_pick p M _ _ h3]
  unfold selfM
  simp_rw [map_add,map_sum]
  change ((∑ d:Tag p.g,∑ t:Tag p.g,pullM T T (testM p n (Block.O d t)))+
    pullM T T (testM p n Block.S))+pullM T T (sharpM p n m.mixM)=_
  rw [ht,hh _ h2]
  simp_rw [hh _ (h1 _ _)]

/-- knobs player. -/
def doZ (p : Shape) (M : Mat (Fin n) (Fin n)) (x : Knobs p.g n) :=
  Function.update x Block.Z (M *ᵥ (x Block.Z))

theorem sailsZ (p : Shape) (M : Mat (Fin n) (Fin n)) (x : Knobs p.g n)
    (l s f) :
    blitz p M *ᵥ spring p l s f x=spring p l s f (doZ p M x) := by
  classical
  rw [blitz_val]
  funext i; rcases i with ⟨i, _|⟨B,j⟩⟩
  · rfl
  by_cases h : B=Block.Z
  · subst B
    let a := selV p.j s i
    have he (x : Knobs p.g n) (v : Fin n) :
       spring p l s f x (i,some (Block.Z,v))=a*x Block.Z v := by
      simp [spring,point,putLab,baseV,a,lit,Flavor.keepZ]
    unfold breeze
    simp_rw [ite_true,he]
    let K := x Block.Z
    change (M *ᵥ (a • K)) j=a*doZ p M x Block.Z j
    rw [mulVec_smul]; simp [doZ,K]
  simp [breeze,spring,point,baseV,putLab,lit,doZ,h]

end HadwigerCounterexample

end

end OAI
