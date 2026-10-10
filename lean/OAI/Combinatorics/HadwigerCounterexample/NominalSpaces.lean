import OAI.Combinatorics.HadwigerCounterexample.MatrixQuotients
import OAI.Combinatorics.HadwigerCounterexample.SparseLabelBounds

namespace OAI

/-! # Nominal Spaces -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

def onSide {A : Type} (x : A × A) (b : Bool) := if b then x.1 else x.2
def putFull (p : Shape) (n : ℕ) : Bool → Full p n → JointIdx p n
| true => Sum.inl
| false => Sum.inr

instance jointDecidableEq (p : Shape) (n : ℕ) : DecidableEq (JointIdx p n) := inferInstance

abbrev Chan (p : Shape) := Fin p.h
def IP (p : Shape) (n : ℕ) (b : Bool) : Mat (JointIdx p n) (Row p n) :=
  embedMat (fun i => putFull p n b (.inl i))
def IH (p : Shape) (n : ℕ) (b : Bool) : Mat (JointIdx p n) (Chan p) :=
  embedMat (fun i => putFull p n b (.inr i))

theorem IP_self (b) : (IP p n b)ᵀ*IP p n b=1 := by
  apply embedMat_self
  intro i j; cases b <;> simp [putFull]
theorem IH_self (b) : (IH p n b)ᵀ*IH p n b=1 := by
  apply embedMat_self
  intro i j; cases b <;> simp [putFull]
theorem IP_IH (a b : Bool) : (IP p n a)ᵀ * IH p n b=0 := by
  unfold IP IH; rw [embedMat_mul]
  ext i j; cases a <;> cases b <;> simp [embedMat,putFull]

theorem IP_cross {a b : Bool} (h : a ≠ b) : (IP p n a)ᵀ * IP p n b=0 := by
  unfold IP; rw [embedMat_mul]
  ext i j; cases a <;> cases b <;> first | contradiction | simp [embedMat,putFull]
theorem IH_cross {a b : Bool} (h : a ≠ b) : (IH p n a)ᵀ * IH p n b=0 := by
  unfold IH; rw [embedMat_mul]
  ext i j; cases a <;> cases b <;> first | contradiction | simp [embedMat,putFull]
theorem IH_IP (a b : Bool) : (IH p n a)ᵀ * IP p n b=0 := by
  simpa only [transpose_mul,Matrix.transpose_zero,transpose_transpose] using
    congrArg Matrix.transpose (IP_IH (p:=p) (n:=n) b a)

theorem ip_decomp (x : Dir p n) :
    (∑ b : Bool, ((IP p n b) *ᵥ ((IP p n b)ᵀ*ᵥx)+ (IH p n b)*ᵥ ((IH p n b)ᵀ*ᵥx)))=x := by
  rw [Fintype.sum_bool]
  unfold IP IH
  simp_rw [embedMatT]
  ext i
  rcases i with (i|i)|(i|i) <;>
    simp [embedMat,putFull,Matrix.mulVec,dotProduct,Pi.add_apply]

theorem images_ip (x : UnitType p n N) (z : Place p) (b : Bool) :
    images x z * IP p n b = primary (takeSign (onSide x b z.1) z.2) := by
  unfold IP; rw [mul_embedMat]
  cases b <;> ext <;> rfl
theorem images_ih (x : UnitType p n N) (z : Place p) (b : Bool) :
    images x z * IH p n b = channel (takeSign (onSide x b z.1) z.2) := by
  unfold IH; rw [mul_embedMat]
  cases b <;> ext <;> rfl

def sPin (s : Plan p n) (z : Place p) (i : Bool) : Space (Ray p n) :=
  (s z).map (IP p n i)ᵀ.mulVecLin

def hPin (s : Plan p n) (z : Place p) (i : Bool) : Space (Vec (Chan p)) :=
  (s z).map (IH p n i)ᵀ.mulVecLin

/-- small table-coordinate space J. -/
def halfTable (s : Plan p n) (z : Place p) (i : Bool) :=
  (sPin s z i).map (IP p n i).mulVecLin ⊔ colSp (IH p n i)
def tabSpace (s : Plan p n) : Plan p n :=
  fun z => halfTable s z true ⊔ halfTable s z false

theorem half_le_table (s : Plan p n) (z) (i) : halfTable s z i ≤ tabSpace s z := by
  cases i
  · exact le_sup_right
  exact le_sup_left

theorem channel_le_table (s : Plan p n) (z i) : colSp (IH p n i)≤tabSpace s z :=
  le_trans le_sup_right (half_le_table s z i)

theorem tab_mem (s : Plan p n) (z : Place p) (x : Dir p n) :
    x∈tabSpace s z ↔ ∀ i,(IP p n i)ᵀ *ᵥ x ∈ sPin s z i := by
  constructor
  · intro h i
    let Q := (sPin s z i).comap (IP p n i)ᵀ.mulVecLin
    suffices he : tabSpace s z ≤ Q from he h
    have hg (j : Bool) : halfTable s z j≤Q := by
      refine sup_le ?_ ?_
      · rintro y ⟨x,hx,rfl⟩
        change (IP p n i)ᵀ *ᵥ (IP p n j *ᵥ x) ∈ sPin s z i
        by_cases e : i = j
        · subst j; rwa [mulVec_mulVec,IP_self,Matrix.one_mulVec]
        rw [mulVec_mulVec,IP_cross e,Matrix.zero_mulVec]; exact Submodule.zero_mem _
      rintro y ⟨x,rfl⟩
      change (IP p n i)ᵀ *ᵥ (IH p n j *ᵥ x) ∈ sPin s z i
      rw [mulVec_mulVec,IP_IH,Matrix.zero_mulVec]; exact Submodule.zero_mem _
    exact sup_le (hg _) (hg _)
  intro h
  rw [←ip_decomp x]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  apply (half_le_table s z i)
  exact Submodule.add_mem_sup (show IP p n i *ᵥ _ ∈ (sPin s z i).map (IP p n i).mulVecLin from
    ⟨_,h i,rfl⟩) (show IH p n i *ᵥ _ ∈ colSp (IH p n i) from ⟨_,rfl⟩)

theorem pin_le_table (s : Plan p n) (z : Place p) : s z ≤ tabSpace s z := fun x h =>
  (tab_mem ..).mpr fun _ => ⟨x,h,rfl⟩

/-- effective test space on endpoint i. -/
def effective (s : Plan p n) (i : Bool) : Space (Profile p n) :=
  Xspace p n ⊓ Submodule.pi Set.univ (fun e => box (sPin s (e,true) i) (sPin s (e,false) i))

theorem effective_mem {s : Plan p n} {i} {x : Profile p n} : x∈effective s i ↔
    x∈Xspace p n ∧ ∀ e, x e∈box (sPin s (e,true) i) (sPin s (e,false) i) :=
  and_congr Iff.rfl (by simp)

theorem sPin_dim (s : Plan p n) (z : Place p) (i) : dim (sPin s z i)≤dim (s z) :=
  Submodule.finrank_map_le _ _
theorem hPin_dim (s : Plan p n) (z : Place p) (i) : dim (hPin s z i)≤dim (s z) :=
  Submodule.finrank_map_le _ _

theorem sPin_sum (s : Plan p n) (b i : Bool) :
    ∑ e : Comp p.g, dim (sPin s (e,b) i) ≤ planRank s := by
  unfold planRank
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum (fun e _ => (sPin_dim _ _ _).trans ?_)
  exact Finset.single_le_sum (fun j _ => Nat.zero_le ((fun b => dim (s (e,b))) j))
    (Finset.mem_univ b)

theorem dim_le_plan (s : Plan p n) (e : Place p) :
    dim (s e) ≤ planRank s := Finset.single_le_sum (fun j _ => Nat.zero_le (dim (s j)))
      (Finset.mem_univ _)

theorem effective_rank {s : Plan p n} {x : Profile p n} {i} (hx : x ∈ effective s i) :
    totalRank x ≤ planRank s := by
  apply le_trans (Finset.sum_le_sum ?_) (sPin_sum s true i)
  intro j _
  exact (Submodule.finrank_mono ((box_mem ..).mp ((effective_mem.mp hx).2 j)).1)

private theorem pi_dim_le {V J : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype J] (s : J→ Submodule F V) :
    dim (Submodule.pi Set.univ s) ≤ ∑ i, dim (s i) := by
  let T := Submodule.pi Set.univ s
  have h (i : J) (x : T) : x.val i∈ s i := x.property i (Set.mem_univ i)
  let f : T →ₗ[F] (∀ i,s i) := {
    toFun := fun x i => ⟨_,h i x⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro x y; rfl }
  have hf : Function.Injective f := fun x y e => Subtype.ext (funext (fun i =>
    show x.val i=y.val i from congrArg (fun t:s i => t.val) (congr_fun e i)))
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans_eq
    (Module.finrank_pi_fintype _)

theorem effective_dim (s : Plan p n) (i : Bool) :
    dim (effective s i) ≤ (planRank s)^2 := by
  unfold effective
  let p' (e : Comp p.g) := (sPin s (e,true) i)
  let q (e : Comp p.g) := (sPin s (e,false) i)
  refine ((Submodule.finrank_mono (show _ ⊓ _ ≤ Submodule.pi Set.univ (fun e => box (p' e)
    (q e)) from inf_le_right)).trans (pi_dim_le _)).trans ?_
  simp_rw [box_dim]
  calc ∑ i, dim (p' i) * dim (q i) ≤ ∑ i, dim (p' i)* planRank s := Finset.sum_le_sum (fun j _ =>
         Nat.mul_le_mul_left _ ((sPin_dim s _ i).trans (dim_le_plan s _)))
       _ ≤ _ := by rw [← Finset.sum_mul,pow_two]; exact Nat.mul_le_mul_right _ (sPin_sum s true i)

theorem table_dim (s : Plan p n) (e : Place p) :
    dim (tabSpace s e) ≤ 2*(planRank s + p.h) := by
  have hh i : dim (halfTable s e i)≤ planRank s+p.h := by
    have hg : dim (colSp (IH p n i)) ≤ p.h := (IH p n i).rank_le_card_width.trans_eq
      (Fintype.card_fin _)
    apply le_trans (Submodule.finrank_add_le_finrank_add_finrank ..)
    exact Nat.add_le_add ((Submodule.finrank_map_le _ _).trans
      ((sPin_dim ..).trans (dim_le_plan s e))) hg
  exact ((Submodule.finrank_add_le_finrank_add_finrank ..).trans
    (Nat.add_le_add (hh true) (hh false))).trans_eq (two_mul _).symm

theorem pin_protection (s : Plan p n) (i : Bool) (K q : ℕ)
    (hk : planRank s ≤ K) (hj : (K+1)*q≤p.j+1) :
    ∃ L : Finset (Label p.b),
      L.card ≤ 2*Fintype.card (Comp p.g)*K*q ∧
      ∀ z : Place p, protectedBy p (sPin s z i) q L := by
  classical
  have he z : dim (sPin s z i)≤K := ((sPin_dim s z i).trans (dim_le_plan s z)).trans hk
  choose L hL hP using fun z => protect_labels p (sPin s z i) q
    (le_trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (he z) 1)) hj)
  refine ⟨Finset.univ.biUnion L, ?_,fun z B v h hq x hx hl =>
    hP z B v h hq x hx (fun ht => hl (Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,ht⟩))⟩
  calc (Finset.univ.biUnion L).card
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ z : Place p, K*q := Finset.sum_le_sum
          (fun j _ => (hL j).trans (Nat.mul_le_mul_right _ (he j)))
    _ = _ := by simp [Place]; ring

end HadwigerCounterexample

end

end OAI
