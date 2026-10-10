import OAI.Combinatorics.HadwigerCounterexample.PrimalChannelDecomposition

namespace OAI

/-! # Baseline Extension -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Submodule

variable {p : Shape} {n : ℕ}

theorem project_table (a : Plan p n) (z : Place p) (Q : Space (Dir p n))
    (hq : Q ≤ primal p n) (hd : Disjoint (tabSpace a z) Q) :
    ∃ B, ProjData (tabSpace a z) Q B ∧ ∀ x∈ primal p n, B*ᵥx∈prSmall a z := by
  classical
  let H := channels p n
  let A := primal p n
  let P := prSmall a z
  have hp : P≤ A := prSmall_le _ _
  have he : tabSpace a z=P ⊔ H := prSmall_table a z
  obtain ⟨X,hX⟩ := proj_exists H A channels_disjoint.symm
  have hj : Disjoint P (Q⊔H) := by
    rw [disjoint_iff_inf_le]
    rintro v ⟨hv,hv'⟩
    obtain ⟨y,hy,w,hw,g⟩ := Submodule.mem_sup.mp hv'
    have h := (show w=v-y by rw [←g]; abel) ▸
      A.sub_mem (hp hv) (hq hy)
    have hz : w∈ A ⊓ H := ⟨h,hw⟩
    rw [channels_disjoint.eq_bot] at hz
    have hi : w=0 := by simpa using hz
    rw [hi,add_zero] at g
    have ht : v∈tabSpace a z ⊓ Q :=
      ⟨he.symm ▸ Submodule.mem_sup_left hv,g ▸ hy⟩
    rwa [hd.eq_bot] at ht
  obtain ⟨Y,hY⟩ := proj_exists P (Q⊔H) hj
  refine ⟨X+Y,⟨fun x => ?_,fun x hx => ?_,fun x hx => ?_⟩, fun x hx => ?_⟩
  · rw [add_mulVec,he,add_comm]; exact add_mem_sup (hY.onto _) (hX.onto _)
  · rw [he] at hx
    obtain ⟨v,hv,w,hw,rfl⟩ := Submodule.mem_sup.mp hx
    rw [add_mulVec,mulVec_add,mulVec_add,hX.kills v (hp hv),hX.fixes _ hw,hY.fixes _ hv,
      hY.kills _ (Submodule.mem_sup_right hw),add_zero,zero_add,add_comm]
  · rw [add_mulVec,hX.kills x (hq hx),hY.kills x (Submodule.mem_sup_left hx),zero_add]
  · rw [add_mulVec,hX.kills x hx,zero_add]; exact hY.onto _

abbrev CrossM (p : Shape) (n : ℕ) := Mat (JointIdx p n) (JointIdx p n)

set_option maxHeartbeats 800000 in
theorem base_pair (a b : Plan p n) (u v : Place p)
    (K J : Space (Dir p n)) (hk : K≤primal p n) (hj : J≤primal p n)
    (hK : Disjoint (tabSpace a u) K) (hJ : Disjoint (tabSpace b v) J)
    (A B : CrossM p n)
    (heq : ∀ x∈ tabSpace a u,∀ y∈tabSpace b v,x∈a u ∨ y∈b v → evmat A x y=evmat B x y) :
    ∃ M : CrossM p n,
      (∀ x∈tabSpace a u,∀ y∈tabSpace b v,evmat M x y=evmat B x y) ∧
      (∀ x y, x∈ (a u⊔K) ∨ y∈(b v⊔J) → evmat M x y=evmat A x y) ∧
      (∀ i,(Mᵀ*IP p n i).rank ≤ dim (a u⊔K : Submodule _ _) + dim (b v⊔J : Submodule _ _) +
        2*planRank a) ∧
      (∀ i,(M*IP p n i).rank ≤ dim (a u⊔K : Submodule _ _) + dim (b v⊔J : Submodule _ _) +
        2*planRank b) := by
  let P := a u⊔K
  let Q := b v⊔J
  obtain ⟨X,hX⟩ := proj_exists P ⊥ disjoint_bot_right
  obtain ⟨Y,hY⟩ := proj_exists Q ⊥ disjoint_bot_right
  obtain ⟨L,hL,gL⟩ := project_table a u K hk hK
  obtain ⟨R,hR,gR⟩ := project_table b v J hj hJ
  let C := pullM X (1:CrossM p n) A + pullM (1-X) Y A
  let M := C + pullM L R (B-C)
  have h1 (x y) (hx : x∈P ∨ y∈Q) : evmat C x y=evmat A x y := by
    rw [show C=_ from rfl,evmat_addM,evmat_pull,evmat_pull,sub_mulVec,Matrix.one_mulVec,
      Matrix.one_mulVec]
    rcases hx with h|h
    · rw [hX.fixes _ h,sub_self]; simp [evmat]
    rw [hY.fixes _ h]
    simp [evmat,sub_dotProduct]
  have h2 (x y) : evmat M x y=evmat C x y+
      (evmat B (L *ᵥ x) (R *ᵥ y)-evmat C (L*ᵥ x) (R*ᵥ y)) := by
    rw [show M=_ from rfl,evmat_addM,evmat_pull,evmat_subM]
  have hRank : C.rank≤dim P+dim Q := by
    apply (mrk_add_le ..).trans
    have hx : X.rank≤dim P := rank_maps _ hX.onto
    have hy : Y.rank≤dim Q := rank_maps _ hY.onto
    apply Nat.add_le_add
    · rw [pullM_def]
      refine ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_left ..)).trans ?_
      rwa [Matrix.rank_transpose]
    · rw [pullM_def]; exact (Matrix.rank_mul_le_right ..).trans hy
  have hr (i) {a : Plan p n} (u)
      (R : CrossM p n) (h : ∀ x∈primal p n,R*ᵥ x∈prSmall a u) :
      (R*IP p n i).rank≤ 2*planRank a := by
    apply le_trans (rank_maps (prSmall a u) _)
      (prSmall_dim a u)
    intro x
    rw [← Matrix.mulVec_mulVec]
    exact h _ (ip_le_primal i (show IP p n i*ᵥx∈colSp (IP p n i) from ⟨x,rfl⟩))
  refine ⟨M, fun x hx y hy => ?_, fun x y h => ?_, fun i => ?_, fun i => ?_⟩
  · rw [h2,hL.fixes x hx,hR.fixes y hy,add_sub_cancel]
  · have hi : L*ᵥ x ∈ a u ∨ R *ᵥ y ∈ b v := by
      rcases h with h|h
      · left; obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp h
        rwa [Matrix.mulVec_add,hL.kills _ hy,hL.fixes _ (pin_le_table _ _ hx),add_zero]
      right; obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp h
      rwa [Matrix.mulVec_add,hR.kills _ hy,hR.fixes _ (pin_le_table _ _ hx),add_zero]
    have he : L*ᵥx ∈ P ∨ R*ᵥy∈Q := hi.imp Submodule.mem_sup_left Submodule.mem_sup_left
    rw [h2,h1 _ _ h,h1 _ _ he,heq _ (hL.onto _) _ (hR.onto _) hi,sub_self,add_zero]
  · unfold M
    rw [transpose_add,Matrix.add_mul]
    refine (mrk_add_le ..).trans (Nat.add_le_add ?_ ?_)
    · exact (Matrix.rank_mul_le_left ..).trans ((Matrix.rank_transpose _).trans_le hRank)
    rw [pullM_def,transpose_mul,transpose_mul,transpose_transpose,Matrix.mul_assoc,
      Matrix.mul_assoc]
    exact ((Matrix.rank_mul_le_right ..).trans (Matrix.rank_mul_le_right ..)).trans (hr i u L gL)
  · unfold M
    rw [Matrix.add_mul]
    refine (mrk_add_le ..).trans (Nat.add_le_add ?_ ?_)
    · exact (Matrix.rank_mul_le_left ..).trans hRank
    rw [pullM_def,Matrix.mul_assoc]
    exact (Matrix.rank_mul_le_right ..).trans (hr i v R gR)

end HadwigerCounterexample

end

end OAI
