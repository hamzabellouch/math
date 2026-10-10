import OAI.Combinatorics.HadwigerCounterexample.TesterFourierSupport

namespace OAI

/-! # Reindexed Fourier Support -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]

namespace Move
variable (c : Flit n) {j k : Vec (Fin n)}
def jumpV : Vec (Fin n) ≃ Vec (Fin n) where
  toFun := c.L.mulVec
  invFun := c.R.mulVec
  left_inv x := by change c.R*ᵥ(c.L *ᵥ x) = x; rw [mulVec_mulVec,c.RL,Matrix.one_mulVec]
  right_inv x := by change c.L*ᵥ(c.R *ᵥ x) = x; rw [mulVec_mulVec,c.LR,Matrix.one_mulVec]
def zreroute (p : Shape) (c : Flit n) (f : Wgt (Knobs p.g n)) :=
  fun y => f ((vault p c).symm y)

theorem zhat_jump (p : Shape) (c : Flit n) (f : Wgt (Knobs p.g n)) (y : Knobs p.g n)
    (x : Vec (Fin n)) :
    zhat p (zreroute p c f) y (c.dual.jumpV x)=zhat p f y x := by
  classical
  unfold zhat
  rw [← avg_bij c.jumpV]
  have he (z : Vec (Fin n)) : unif (c.jumpV z)=unif z := rfl
  have hh (z) :
      vectorPhase (c.dual.jumpV x) (c.jumpV z)= vectorPhase x z := by
    unfold vectorPhase
    change wsign (dotProduct (c.Rᵀ *ᵥ x) (c.L *ᵥ z))=_
    rw [dotProduct_comm, dotProduct_transpose_mulVec,mulVec_mulVec,c.RL, Matrix.one_mulVec]
  have ht (z) :
      zreroute p c f (update y Block.Z (c.jumpV z))=f (update y Block.Z z) := by
    unfold zreroute vault; simp only [doZ,Equiv.coe_fn_symm_mk,update_self]
    change f (update (update y Block.Z _) _ (c.jumpV.symm (c.jumpV z)))=_
    rw [Equiv.symm_apply_apply]; simp
  simp_rw [he,hh,ht]

theorem jump_in (c : Flit n) (S : Space (Vec (Fin n))) {z} (h : z ∈ S) :
    c.dual.jumpV z∈c.plume S := by
  rw [←colSp_pack S] at h
  obtain ⟨u,h⟩ := h
  refine ⟨u,?_⟩
  change (c.Rᵀ*pack S)*ᵥu=c.dual.jumpV z
  rw [← mulVec_mulVec,show pack S *ᵥ u=z from h]
  rfl
end Move

namespace Template
variable (v : Solo p)

def rotor (v : Solo p) (c : Flit n) (m : Mixer p n) (x : Profile p n) :=
  Move.zreroute p c (v.shanty m x)
theorem rotor_budget (v : Solo p) (c : Flit n) (m : Mixer p n) (x : Profile p n)
    (K s : ℕ) (hg : Odd p.g) (hm : unaryGood m K s) (hK : totalRank x≤K) (hx : 0<totalRank x)
    (u : Knobs p.g n) (i : Vec (Fin n)) :
    |zchar p (v.rotor c m x) i u|≤bp (-((p.J-s:ℕ):ℝ)) ∧
    (i ∉ c.plume (v.scroll m x) → zchar p (v.rotor c m x) i u=0) := by
  classical
  obtain ⟨i,rfl⟩ := c.dual.jumpV.surjective i
  unfold zchar rotor
  rw [Move.zhat_jump,abs_mul,vectorPhase,wsign_abs,mul_one]
  exact ⟨shanty_cap v m x K s hg hm hK hx u i,fun h =>
    mul_eq_zero_of_left (shanty_outer v m x u hg i (fun he => h (Move.jump_in c _ he))) _⟩
end Template
end HadwigerCounterexample

end

end OAI
