import OAI.Combinatorics.HadwigerCounterexample.GramProbabilities

namespace OAI

/-! # Frame Orbit Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Function

variable {U I J R S : Type} [Fintype U] [Fintype I] [Fintype J] [Fintype R] [Fintype S]
    [DecidableEq U]

def FramesAt (C : Mat I J → Prop) (x : Mat U I × Mat U J) :=
  C (x.1ᵀ * x.2) ∧ Injective x.1.mulVec ∧ Injective x.2.mulVec

structure Move (U : Type) [Fintype U] [DecidableEq U] where
  L : Mat U U
  R : Mat U U
  LR : L*R=1
  RL : R*L=1

namespace Move
variable (c : Move U)
def sym : Move U := ⟨c.R,c.L,c.RL,c.LR⟩
def dual : Move U := ⟨c.Rᵀ,c.Lᵀ,by rw [← transpose_mul,c.LR, Matrix.transpose_one],
  by rw [← transpose_mul,c.RL,Matrix.transpose_one]⟩
def permMat (I : Type) : Mat U I ≃ Mat U I where
  toFun A := c.L*A
  invFun A := c.R*A
  left_inv A := by simp only [← Matrix.mul_assoc, c.RL, Matrix.one_mul]
  right_inv A := by simp only [← Matrix.mul_assoc, c.LR, Matrix.one_mul]
def perm (I J : Type) : Mat U I × Mat U J ≃ Mat U I × Mat U J :=
  (c.permMat I).prodCongr (c.dual.permMat J)

omit [Fintype I] [Fintype J] in
theorem gram_invar (A : Mat U I) (B : Mat U J) :
    (c.L*A)ᵀ * (c.Rᵀ*B) = Aᵀ*B := by
  rw [transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc c.Lᵀ c.Rᵀ B,← transpose_mul,c.RL,
    Matrix.transpose_one, Matrix.one_mul]

theorem L_inj : Injective c.L.mulVec := by
  intro x y h
  have hi (x) : c.R *ᵥ (c.L *ᵥ x) = x := by rw [mulVec_mulVec,c.RL, Matrix.one_mulVec]
  change c.L *ᵥ x = c.L *ᵥ y at h
  rw [←hi x,h,hi y]

theorem perm_inj (A : Mat U I) : Injective A.mulVec ↔ Injective (c.L*A).mulVec := by
  refine ⟨inj_comp_mat _ _ c.L_inj, fun h => ?_⟩
  have hh := inj_comp_mat _ _ c.sym.L_inj h
  change Injective (c.R*(c.L*A)).mulVec at hh
  rwa [←Matrix.mul_assoc,c.RL,Matrix.one_mul] at hh

theorem invar (C : Mat I J → Prop) (x : Mat U I × Mat U J) :
    FramesAt C x ↔ FramesAt C (c.perm I J x) := by
  unfold FramesAt
  change _ ↔ C ((c.L*x.1)ᵀ * (c.Rᵀ*x.2)) ∧ _
  rw [gram_invar]
  exact and_congr Iff.rfl (and_congr (c.perm_inj x.1) (c.dual.perm_inj x.2))
end Move

/-- Nonempty matrix family if super-dimension slack. -/
theorem framesAt_exists [DecidableEq I] [DecidableEq J]
    {C : Mat I J → Prop} (h : ∃ G, C G) (hn : num I+num J < num U) :
    ∃ x : Mat U I × Mat U J, FramesAt C x := by
  obtain ⟨G,hG⟩ := h
  let v := (pairW unif unif : Wgt (Mat U I × Mat U J))
  have he (a : ℝ) (h : a < 0) : 0 < 1-bp a := sub_pos.mpr
    ((bp_lt h).trans_eq bp_zero)
  have hpos : 0 < pr v (gramGood G) := by
    refine lt_of_lt_of_le ?_ (gram_norm G hn.le).2
    have hi : num I - num U < 0 := by
      have hh : 0 ≤ num J := by unfold num; positivity
      linarith
    exact mul_pos (mul_pos (bp_pos _) (he _ hi)) (he _ (by linarith only [hn]))
  obtain ⟨x,hx,_⟩ := exists_of_pr_pos (pairW_law unif_law unif_law).nz hpos
  exact ⟨x,hx.1.symm ▸ hG,hx.2⟩

theorem move_exists (G : Mat I J) (x y : Mat U I × Mat U J) (hx : gramGood G x)
    (hy : gramGood G y) : ∃ c : Move U, c.perm I J x = y := by
  obtain ⟨L,R,H,F,E,T⟩ := frame_move hx.2.1 hy.2.1 hx.2.2 hy.2.2 (hx.1.trans hy.1.symm)
  exact ⟨⟨L,R,H,F⟩,Prod.ext E T⟩

theorem move_exists_one {x y : Mat U I} (hx : Injective x.mulVec)
    (hy : Injective y.mulVec) : ∃ c : Move U, c.permMat I x = y := by
  let B := (0:Mat U Empty)
  let G := (0:Mat I Empty)
  have he {x : Mat U I} (hx : Injective x.mulVec) : gramGood G (x,B) :=
    ⟨Subsingleton.elim _ _, hx, fun a b _ => Subsingleton.elim a b⟩
  obtain ⟨c,hc⟩ := move_exists G _ _ (he hx) (he hy)
  exact ⟨c,congrArg Prod.fst hc⟩

variable [DecidableEq I] [DecidableEq J] [DecidableEq R] [DecidableEq S]

def observe (P : Mat I R) (Q : Mat J S) (x : Mat U I × Mat U J) : Mat U R × Mat U S :=
  (x.1 * P, x.2 * Q)

/-- Uniform law of sub-batch with Gram fixed on the batch. -/
theorem framesAt_observe {C : Mat I J → Prop} (hc : ∃ x : Mat U I × Mat U J, FramesAt C x)
    (P : Mat I R) (Q : Mat J S) {G : Mat R S} (hP : Injective P.mulVec)
    (hQ : Injective Q.mulVec) (h : ∀ M, C M → Pᵀ*M*Q=G) :
    mapW (unifOn (FramesAt (U:=U) C)) (observe P Q) = unifOn (gramGood G) := by
  apply uniform_orbit _ hc
  · intro x hx
    refine ⟨?_,inj_comp_mat _ _ hx.2.1 hP,inj_comp_mat _ _ hx.2.2 hQ⟩
    change (x.1 * P)ᵀ * (x.2 * Q) = G
    rw [← h _ hx.1,transpose_mul]
    simp only [Matrix.mul_assoc]
  · intro y z hy hz
    obtain ⟨c,hc'⟩ := move_exists G y z hy hz
    refine ⟨c.perm I J,c.invar C, fun x => ?_⟩
    have hobs : observe P Q (c.perm I J x) = (c.perm R S) (observe P Q x) :=
      Prod.ext (Matrix.mul_assoc _ _ _) (Matrix.mul_assoc _ _ _)
    rw [hobs,←hc']
    exact (c.perm R S).injective.eq_iff.symm

/-- Uniform law of plus-only observation; in particular plus frames are
uniform injective. -/
theorem framesAt_observe_plus {C : Mat I J → Prop} (hc : ∃ x : Mat U I × Mat U J, FramesAt C x)
    {P : Mat I R} (hP : Injective P.mulVec) :
    mapW (unifOn (FramesAt (U:=U) C)) (fun x => x.1*P) =
      unifOn (fun x => Injective x.mulVec) := by
  refine uniform_orbit _ hc ?_ ?_
  · intro x hx; exact inj_comp_mat _ _ hx.2.1 hP
  intro y z hy hz
  obtain ⟨c,hc⟩ := move_exists_one hy hz
  refine ⟨c.perm I J,c.invar C, fun x => ?_⟩
  change x.1*P=y ↔ c.L*x.1*P=z
  rw [Matrix.mul_assoc,←hc]
  exact (c.permMat R).injective.eq_iff.symm

theorem framesAt_observe_minus {C : Mat I J → Prop} (hc : ∃ x : Mat U I × Mat U J, FramesAt C x)
    {Q : Mat J S} (hQ : Injective Q.mulVec) :
    mapW (unifOn (FramesAt (U:=U) C)) (fun x => x.2*Q) =
      unifOn (fun x => Injective x.mulVec) := by
  refine uniform_orbit _ hc ?_ ?_
  · intro x hx; exact inj_comp_mat _ _ hx.2.2 hQ
  intro y z hy hz
  obtain ⟨c,hc⟩ := move_exists_one hy hz
  refine ⟨c.dual.perm I J,c.dual.invar C, fun x => ?_⟩
  change x.2*Q=y ↔ c.L*x.2*Q=z
  rw [Matrix.mul_assoc,←hc]
  exact (c.permMat S).injective.eq_iff.symm

theorem plus_marginal {C : Mat I J → Prop} (hc : ∃ x : Mat U I × Mat U J, FramesAt C x) :
    mapW (unifOn (FramesAt (U:=U) C)) Prod.fst =
      unifOn (fun x => Injective x.mulVec) := by
  have he : Injective (1:Mat I I).mulVec := fun x y h => by simpa using h
  simpa using framesAt_observe_plus hc he

end HadwigerCounterexample

end

end OAI
