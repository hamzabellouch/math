import OAI.Combinatorics.HadwigerCounterexample.FreeBlockLinearAction

namespace OAI

/-! # Frame Rotations -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Move

def vault (p : Shape) (c : Flit n) :
    Knobs p.g n ≃ Knobs p.g n where
  toFun x := doZ p c.L x
  invFun x := doZ p c.R x
  left_inv x := by simp only [doZ,update_self,mulVec_mulVec,c.RL,Matrix.one_mulVec]; simp
  right_inv x := by simp only [doZ,update_self,mulVec_mulVec,c.LR,Matrix.one_mulVec]; simp
variable (c : Flit n)

def boom (p : Shape) (c : Flit n) : Move (Full p n) where
  L := Matrix.fromBlocks (blitz p c.L) 0 0 1
  R := Matrix.fromBlocks (blitz p c.R) 0 0 1
  LR := by simp [fromBlocks_multiply,←blitz_mul,c.LR,blitz_one]
  RL := by simp [fromBlocks_multiply,←blitz_mul,c.RL,blitz_one]

def fuse (p : Shape) (c : Flit n) (N : ℕ) :
    Mat (Fin N) (Full p n) ≃ Mat (Fin N) (Full p n) where
  toFun y := y*(boom p c).L
  invFun y := y*(boom p c).R
  left_inv y := by simp only [Matrix.mul_assoc,(boom p c).LR]; exact Matrix.mul_one _
  right_inv y := by simp only [Matrix.mul_assoc,(boom p c).RL]; exact Matrix.mul_one _

theorem boom_primary (y : Mat (Fin N) (Full p n)) :
    primary (fuse p c N y)=primary y*blitz p c.L ∧ channel (fuse p c N y)=channel y := by
  change primary (y*(boom p c).L)=_ ∧ channel (y*_)=_
  have hz : y*(boom p c).L = fromCols (primary y * blitz p c.L) (channel y) := by
    unfold boom
    conv_lhs => arg 1; rw [←fromCols_frame y]
    simp only [fromCols_mul_fromBlocks,Matrix.mul_zero,Matrix.mul_one,zero_add,add_zero]
  rw [hz]; exact ⟨rfl,rfl⟩

theorem fuse_inj (y : Mat (Fin N) (Full p n)) (h : Injective y.mulVec) :
    Injective (fuse p c N y).mulVec :=
  inj_comp_mat _ _ h (boom p c).L_inj

def kite (p : Shape) (c : Flit n) (N) : Orient p n N ≃ Orient p n N :=
  Equiv.piCongrRight (fun _ => (fuse p c N).prodCongr (fuse p c N))

theorem kite_move (m : Mixer p n) {y : Oframe p n N}
    (h : FramesAt (gramCond m) y) :
    FramesAt (gramCond m) (fuse p c N y.1,fuse p c N y.2) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := (valid_iff ..).mpr h
  refine (valid_iff ..).mp ⟨c.fuse_inj _ h1,c.fuse_inj _ h2,?_,?_,?_⟩
  · have ha := (boom_primary c y.1).1; have hb := (boom_primary c y.2).1
    let B := blitz p c.L; let E := selfM p n m.mixM
    change (primary (fuse p c N y.1))ᵀ * primary (fuse p c N y.2)=_
    rw [ha,hb]
    calc _ =pullM B B E := by unfold E; rw [pullM_def,←h3,transpose_mul]; simp only [Matrix.mul_assoc,B]
         _ = E := blitz_fixes ..
  · change (channel (fuse p c N y.1))ᵀ * primary (fuse p c N y.2)=_
    rw [(boom_primary c y.1).2,(boom_primary c y.2).1,←Matrix.mul_assoc,h4,Matrix.zero_mul]
  change (primary (fuse p c N y.1))ᵀ*channel (fuse p c N y.2)=_
  rw [(boom_primary c y.1).1,(boom_primary c y.2).2,transpose_mul,Matrix.mul_assoc,
    h5,Matrix.mul_zero]

theorem kite_weights (m : Mixer p n) (x : Orient p n N) :
    raw m N (kite p c N x)=raw m N x := by
  unfold raw prodW
  refine Finset.prod_congr rfl fun i _ => ?_
  let A := (kite p c N x) i
  have h : FramesAt (gramCond m) A ↔ FramesAt (gramCond m) (x i) := by
    constructor
    · intro h
      have ht := kite_move c.sym m h
      have he : (fuse p c.sym N A.1,fuse p c.sym N A.2)=x i := Prod.ext ((fuse p c N).symm_apply_apply _) ((fuse p c N).symm_apply_apply _)
      rwa [he] at ht
    exact fun h => kite_move c m h
  simp only [unifOn_val]
  change ind (FramesAt _ A)/_=_
  rw [h]
theorem kite_keys (v : Template.Solo p) (x : Orient p n N) (z : Knobs p.g n) :
    v.desc z (kite p c N x)=v.desc (vault p c z) x := by
  let i := x
  let R (e : TagStar (v.t ())) (b : Bool) :
      takeSign (p:=p) ((kite p c N x) e.val) b = fuse p c N (takeSign (p:=p)
        (x e.val) b) := by cases b <;> rfl
  funext e b
  let w (z : Knobs p.g n) := spring p (v.t ()) (v.s ()) (v.f ()) z
  change primary _ *ᵥ w z = primary _ *ᵥ w _
  rw [R,(boom_primary c _).1,←mulVec_mulVec,sailsZ]
  rfl
end Move

def flowZ (p : Shape) (w : Wgt (Knobs p.g n)) :=
  ∀ i j,w (update i Block.Z j) = w i

theorem scannedZ (p : Shape) (l : Tag p.g) (f : Flavor p.g) (w : Knobs p.g n) (v : Vec (Fin n)) :
    scan p l f (update w Block.Z v)=scan p l f w := by
  classical
  funext i
  have h : asBlock i≠Block.Z := by rcases i with (⟨i,j⟩|_) <;> simp [asBlock]
  unfold scan; rw [update_of_ne h]

theorem scanned_flow (p : Shape) (n l f z) : flowZ p (scopedScan p n l f z) := by
  intro i j; simp only [scopedScan,onW_val,spins,← draws_unif,scannedZ,unif_apply]
end HadwigerCounterexample

end

end OAI
