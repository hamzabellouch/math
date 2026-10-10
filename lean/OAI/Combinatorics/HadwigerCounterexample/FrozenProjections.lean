import OAI.Combinatorics.HadwigerCounterexample.LinearResponse
import OAI.Combinatorics.HadwigerCounterexample.GradientRankBounds

namespace OAI

/-! # Frozen Projections -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}

variable {I : Type} [Fintype I]
namespace Volley
variable (v : Volley p n I)

/-- D + attack directions. -/
def frozen (a : Plan p n) (t : Tagging p I) : Plan p n := a⊔v.keyPlan t

/-- All labels at one endpoint. -/
def marked (i : Bool) := (v.here i).image v.sel

theorem marked_mem (x : I) : v.sel x ∈ v.marked (v.obj x)  := by
  classical exact Finset.mem_image_of_mem _ (by simp [here])

theorem marked_card {w : I → Bool} (hv : v.bounded w) (i : Bool) :
    (v.marked i).card ≤14 := by
  classical exact Finset.card_image_le.trans (v.here_card hv i)

/-- project matrix of active key rays to one endpoint under attack -/
def visitH (t : Tagging p I) (i : Bool) (e : Comp p.g) : Finset (visits p t e) :=
  Finset.univ.filter (fun j => v.obj j.val=i)

theorem visitH_here (t : Tagging p I) (i : Bool) (e : Comp p.g)
    {j : visits p t e} :
    j ∈ v.visitH t i e ↔ j.val ∈ v.here i := by simp [visitH,here]

theorem visitH_card {w : I → Bool} (hv : v.bounded w)
    (t : Tagging p I) (i : Bool) (e : Comp p.g) :
    (v.visitH t i e).card ≤14 := by
  classical
  rw [← Finset.card_image_of_injective _ (@Subtype.val_injective _ _)]
  refine (Finset.card_le_card ?_).trans (v.here_card hv i)
  rintro x hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  exact (v.visitH_here ..).mp hj

theorem key_proj (t : Tagging p I) (i : Bool) (e : Comp p.g) (x : Vec (visits p t e)) :
    (IP p n i)ᵀ *ᵥ (v.keyM t e *ᵥ x)= ∑ j∈v.visitH t i e,x j • v.rayAt j.val := by
  classical
  have he : v.keyM t e *ᵥ x = ∑ j : visits p t e,x j • (v.rayLoc j.val) := by
    rw [mulVec_eq_sum]
    simp_rw [op_smul_eq_smul]
    rfl
  change ((IP p n i)ᵀ.mulVecLin _) = _
  rw [he,map_sum,visitH,Finset.sum_filter]
  refine sum_congr rfl fun j _ => ?_
  rw [map_smul,mulVecLin_apply,rayLoc,mulVec_mulVec]
  by_cases hj : v.obj j.val=i
  · rw [ite_eq_left hj,hj,IP_self,one_mulVec]
  rw [ite_eq_right hj,IP_cross (Ne.symm hj),zero_mulVec,smul_zero]

theorem key_here_dim {w : I→Bool} (hv : v.bounded w) (t : Tagging p I)
    (i : Bool) (z : Place p) :
    dim (sPin (v.keyPlan t) z i) ≤14 := by
  classical
  let S := v.visitH t i z.1
  let M : Mat (Row p n) S := Matrix.of fun i j => v.rayAt j.val.val i
  have hM : M.rank ≤14 := M.rank_le_card_width.trans
    (Fintype.card_coe S ▸ (v.visitH_card hv t i z.1))
  refine (Submodule.finrank_mono (show sPin (v.keyPlan t) z i≤colSp M from ?_)).trans hM
  rintro y ⟨x,⟨a,rfl⟩,rfl⟩
  let b (j:S) := a j.val
  refine ⟨b,?_⟩
  change M *ᵥ b=(IP p n i)ᵀ *ᵥ _
  rw [mulVecLin_apply,v.key_proj,mulVec_eq_sum]
  simp_rw [op_smul_eq_smul]
  change (∑ j:S,b j • v.rayAt j.val.val)=∑ j∈S,a j • v.rayAt j.val
  exact Finset.sum_coe_sort S (fun i => a i • v.rayAt i.val)

theorem key_dim {w : I→Bool} (hv : v.bounded w) (t : Tagging p I) (z : Place p) :
    dim (v.keyPlan t z) ≤28 := by
  classical
  exact (v.keyM t z.1).rank_le_card_width.trans ((Fintype.card_le_of_injective (@Subtype.val _ _) Subtype.val_injective).trans (v.call_count hv))

theorem sPin_frozen (a : Plan p n) (t : Tagging p I) (i : Bool) (z : Place p) :
    sPin (v.frozen a t) z i=sPin a z i⊔sPin (v.keyPlan t) z i :=
  Submodule.map_sup _ _ _

theorem hPin_frozen (a : Plan p n) (t : Tagging p I) (i : Bool) (z : Place p) :
    hPin (v.frozen a t) z i=hPin a z i := by
  have h : hPin (v.keyPlan t) z i≤(⊥ : Space _) := by
    rintro x ⟨y,hy,rfl⟩
    have he := primal_proj i ((keyPlane v t z) hy)
    rw [LinearMap.mem_ker] at he
    rw [he]; exact Submodule.zero_mem _
  change hPin (v.frozen a t) z i=hPin a z i
  rw [show hPin (v.frozen a t) z i=hPin a z i⊔ hPin (v.keyPlan t) z i from
    Submodule.map_sup _ _ _, le_bot_iff.mp h,sup_bot_eq]

theorem frozen_here_dim {w : I→ Bool} (hv : v.bounded w)
    (a : Plan p n) (t : Tagging p I) (i z) :
    dim (sPin (v.frozen a t) z i) ≤ planRank a + 14 := by
  rw [v.sPin_frozen]
  exact (Submodule.finrank_add_le_finrank_add_finrank ..).trans
    (Nat.add_le_add ((sPin_dim ..).trans (dim_le_plan ..)) (v.key_here_dim hv t i z))
end Volley

theorem ip_annih {f : Plan p n} (i : Bool) (z : Place p) (x : Ray p n) :
    IP p n i *ᵥ x∈annih (f z) ↔ x∈ annih (sPin f z i) := by
  rw [annih_mem,annih_mem]
  have hh (y : Dir p n) : dotProduct (IP p n i *ᵥ x) y= dotProduct x ((IP p n i)ᵀ *ᵥ y) := by
    rw [dotProduct_transpose_mulVec,dotProduct_comm]
  constructor
  · rintro he y ⟨y,hy,rfl⟩
    rw [mulVecLin_apply,← hh]
    exact he y hy
  intro h y hy
  rw [hh]
  exact h _ ⟨y,hy,rfl⟩

theorem orth_pair_sym (x : Xpair p n) (e : Comp p.g) (i : Bool) :
    ((x i).val e)ᵀ=(x i).val e := by
  obtain ⟨w,h,hx⟩ := mem_X.mp (x i).property
  rw [←hx]
  exact Wspace_sym ((Wspace p n).add_mem ((Wtag_le _) (h e.val.1)) ((Wtag_le _) (h e.val.2)))

theorem purePair_sym (x : Xpair p n) (e : Comp p.g) :
    (purePair p n x e)ᵀ = purePair p n x e := by
  simp only [purePair,Finset.sum_apply,Fintype.sum_bool,transpose_add,liftM_transpose,
    orth_pair_sym]

theorem pure_ip (x : Xpair p n) (e : Comp p.g) (i : Bool) (v : Ray p n) :
    purePair p n x e *ᵥ (IP p n i *ᵥ v)=IP p n i *ᵥ ((x i).val e *ᵥ v) := by
  classical
  simp only [purePair,Finset.sum_apply,Fintype.sum_bool,Matrix.add_mulVec,liftM_def,
    ← Matrix.mulVec_mulVec]
  cases i <;>
   (simp_rw [Matrix.mulVec_mulVec v (IP p n _)ᵀ]
    simp only [IP_self,IP_cross (show false≠true by decide),IP_cross (show true≠false by decide),
      Matrix.zero_mulVec, Matrix.one_mulVec,Matrix.mulVec_zero,zero_add,add_zero])

theorem vanish_one {f b : Plan p n} {x : Xpair p n} {C : ChanOut p n} {j}
    (h : orth p C f b j x) (i : Bool) (e : Comp p.g) :
    vanish (sPin f (e,true) i) (sPin f (e,false) i) ((x i).val e) := by
  intro u hu v hv
  have he := orth_pure h e (IP p n i *ᵥ u) ((ip_annih i _ u).mpr hu) (IP p n i *ᵥ v)
    ((ip_annih i _ v).mpr hv)
  rw [evmat,pure_ip, ← dotProduct_transpose_mulVec, mulVec_mulVec,
    IP_self, Matrix.one_mulVec,dotProduct_comm] at he
  exact he

/-- For an annihilator cut pair, testing a right or left primal
functional on endpoint i annihilating projected pins-and-keys produces
an entire vector in the opposite frozen space. -/
theorem orth_ip_frozen {f b : Plan p n} {x : Xpair p n} {C : ChanOut p n} {j}
    (h : orth p C f b j x) (i : Bool) (z : Place p) (φ : Ray p n)
    (hh : φ∈annih (sPin f (flipZ p z) i)) :
    IP p n i *ᵥ ((x i).val z.1 *ᵥ φ) ∈ f z := by
  rw [← pure_ip,← annih_annih (f z),annih_mem]
  intro ψ hψ
  have hr := (ip_annih i _ _).mpr hh
  rw [dotProduct_comm]
  rcases z with ⟨e,c|c⟩
  · have he := orth_pure h e _ hr _ hψ
    rw [← evmat_transpose,purePair_sym] at he
    exact he
  exact orth_pure h e _ hψ _ hr

end HadwigerCounterexample

end

end OAI
