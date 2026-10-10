import OAI.Combinatorics.HadwigerCounterexample.AttackCutDecomposition

namespace OAI

/-! # Residual Cut Pairs -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Submodule Module Finset
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]
namespace Volley

def CleanRay (v : Volley p n I) (i : Bool) (R : ℕ) (x : Ray p n) :=
  ∃ (L : Finset (Label p.b)) (u : LabVals p n), x=labcomb p n L u ∧ L.card≤R ∧
    Disjoint L (v.marked i)

variable {v : Volley p n I}
private theorem clean_apply {i : Bool} {R : ℕ} {M : Moment p n} (h : v.clean i R M) (x : Ray p n) :
    v.CleanRay i R (M *ᵥ x) := by
  classical
  obtain ⟨L,Z,rfl,hL,ht⟩ := h
  refine ⟨L,(fun s => Z s *ᵥ ((labMat p n s)ᵀ *ᵥ x)),?_,hL,ht⟩
  rw [labcomb_eval,labelSum,Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mput,liftM_def,←Matrix.mulVec_mulVec]
  rw [labMat_act]

private theorem clean_zero (v : Volley p n I) (i : Bool) (R : ℕ) :
    v.CleanRay i R 0 :=
  ⟨∅,0,(map_zero _).symm,by simp,by simp⟩

/-- Key coefficients cannot contribute to a short nonattack primal
combination even if only the primal projection is specified. -/
private theorem clean_proj {w : I → Bool} {a : Plan p n} (t : Tagging p I) {R q : ℕ}
    (hb : v.bounded w) (hv : v.avoids a q) (hr : R+14 ≤ q)
    (x : Ray p n) (z : Place p) (i : Bool) (hx : v.CleanRay i R x)
    (b : Vec (visits p t z.1)) (he : x-(IP p n i)ᵀ *ᵥ (v.keyM t z.1 *ᵥ b) ∈ sPin a z i) :
    ∀ j∈v.visitH t i z.1,b j = 0 := by
  classical
  let K := v.visitH t i z.1
  obtain ⟨B,hB,hE,hG,hsel⟩ := hv i
  obtain ⟨L,u,hx,hL,hdis⟩ := hx
  let s (j : visits p t z.1) := v.sel j.val
  let T := K.image s
  have hk (i' : visits p t z.1) (h : i'∈K) : i'.val∈v.here i :=
    (v.visitH_here ..).mp h
  have hs : Set.InjOn s (K : Set _) := by
    intro x hx y hy h
    exact Subtype.ext (hsel (hk _ hx) (hk _ hy) h)
  obtain ⟨y,hy,hZ⟩ := point_comb K s (v.par ∘ Subtype.val) b hs
  rw [key_proj] at he
  let r : LabVals p n := withinL p L u - withinL p T y
  have h : labcomb p n (L∪T) r∈sPin a z i := by
    rw [show r =_ - _ from rfl,map_sub,← within_eq subset_union_left u,
      ← within_eq subset_union_right y,← hx, show labcomb p n T y =_ from hZ.symm]
    exact he
  have hh : (L∪T).card≤q :=
     (Finset.card_union_le ..).trans ((Nat.add_le_add hL (Finset.card_image_le.trans
       (v.visitH_card hb t i z.1))).trans hr)
  intro j hj
  have hj' : s j ∈ T := mem_image_of_mem s hj
  have hj'' : s j ∉ L := fun hh => Finset.disjoint_left.mp hdis hh
    (mem_image_of_mem _ (hk j hj))
  have hy' := hB z (L∪T) r h hh _ (mem_union_right _ hj') (hE _ (hk _ hj))
  unfold r withinL at hy'
  simp only [Pi.sub_apply,ite_eq_right hj'',ite_eq_left hj',hy j hj,zero_sub,neg_eq_zero] at hy'
  simpa only [Function.comp_apply,Pi.zero_apply,Pi.smul_apply,smul_eq_mul,baseV,
    Option.elim',mul_one] using congr_fun hy' none

private theorem clean_sPin {w : I → Bool} {a : Plan p n} (t : Tagging p I) {R q : ℕ}
    (hb : v.bounded w) (hv : v.avoids a q) (hr : R+14 ≤ q)
    (x : Ray p n) (z : Place p) (i : Bool) (hx : v.CleanRay i R x)
    (hg : x∈sPin (v.frozen a t) z i) :
    x∈sPin a z i := by
  classical
  rw [sPin_frozen,Submodule.mem_sup] at hg
  obtain ⟨y,hy,q',⟨q',⟨b,rfl⟩,rfl⟩,hX⟩ := hg
  have he : x - ((IP p n i)ᵀ *ᵥ (v.keyM t z.1 *ᵥ b))=y := by
    rw [← hX]; exact add_sub_cancel_right _ _
  have h := clean_proj t hb hv hr x z i hx b (he ▸ hy)
  rw [key_proj,Finset.sum_eq_zero (fun j hj => by rw [h j hj,zero_smul]),sub_zero] at he
  rwa [he]

private theorem clean_Pin {w : I→Bool} {a : Plan p n} (t : Tagging p I)
    {R q : ℕ} (hb : v.bounded w) (hv : v.avoids a q) (hr : R+14 ≤ q)
    (x : Ray p n) (z : Place p) (i : Bool) (hx : v.CleanRay i R x)
    (hg : IP p n i *ᵥ x ∈ v.frozen a t z) :
    IP p n i *ᵥ x∈a z := by
  classical
  obtain ⟨d,hd,q',⟨b,rfl⟩,hX⟩ := Submodule.mem_sup.mp
    (show IP p n i *ᵥ x∈a z ⊔ v.keyPlan t z from hg)
  let f (k : Bool) := (IP p n k)ᵀ
  have hzero : b=0 := by
    funext j
    let k := v.obj j.val
    let x' := f k *ᵥ (IP p n i *ᵥ x)
    have h : x' - ((IP p n k)ᵀ *ᵥ (v.keyM t z.1 *ᵥ b))∈sPin a z k := by
      unfold x'
      rw [← hX,Matrix.mulVec_add]
      change f k *ᵥ d + _ - f k *ᵥ (_ *ᵥ _) ∈ _
      rw [mulVecLin_apply,add_sub_cancel_right]
      exact ⟨d,hd,rfl⟩
    have h' : v.CleanRay k R x' := by
      unfold x' f; rw [Matrix.mulVec_mulVec]
      by_cases h : k=i
      · rw [h,IP_self,Matrix.one_mulVec]
        exact hx
      rw [IP_cross h,Matrix.zero_mulVec]; exact clean_zero v k R
    exact clean_proj t hb hv hr x' z k h' b h j (mem_filter.mpr ⟨mem_univ _,rfl⟩)
  rw [hzero,map_zero,add_zero] at hX
  rwa [← hX]

end Volley

theorem orth_delta_probe {f b : Plan p n} {x : Xpair p n} {C : ChanOut p n} {j}
    (h : orth p C f b j x) (i : Bool) (z : Place p) (φ : Ray p n)
    (hφ : φ∈annih (sPin f (flipZ p z) i)) :
    C z *ᵥ (IP p n i *ᵥ ((x i).val z.1 *ᵥ φ)) ∈ hPin b z j := by
  classical
  rw [← annih_annih (hPin b z j), annih_mem]
  intro y hy
  rw [← pure_ip]
  let Q := IP p n i *ᵥ φ
  have hQ := (ip_annih ..).mpr hφ
  let D : ChanOut p n := Pi.single (flipZ p z) (vecMulVec y Q)
  have hD : D∈deltaSpace p f b j := by
    refine (deltaSpace_mem _).mpr (fun z' => ?_)
    by_cases hz : z'=flipZ p z
    · subst z'
      unfold D; rw [Pi.single_eq_same,flipZ_flip]
      exact outer_in_box y Q hy hQ
    simp [D,hz]
  have hg := h D hD 0 (Submodule.zero_mem _)
  change ∑ i, mpair ((chanDeriv p C D+0) i) (purePair p n x i) = _ at hg
  rw [add_zero,Finset.sum_eq_single z.1] at hg
  · let T := (C z)ᵀ * vecMulVec y Q
    let X := purePair p n x z.1
    have hh : mpair T X = dotProduct (C z *ᵥ (X *ᵥ Q)) y := by
      unfold T; rw [mul_vecMulVec,mpair_comm,mpair_outer,evmat]
      rw [dotProduct_comm, dotProduct_transpose_mulVec,dotProduct_comm]
    change dotProduct (C z *ᵥ (X *ᵥ Q)) y = _
    rw [← hh]
    have hZ : z≠flipZ p z := by cases z with | mk e c => cases c <;> simp [flipZ]
    have h1 : D z=0 := Pi.single_eq_of_ne hZ _
    have h2 : D (flipZ p z)=vecMulVec y Q := Pi.single_eq_same _ _
    rcases z with ⟨e,c|c⟩
    · change mpair ((C (e,true))ᵀ * D (e,false)+(D (e,true))ᵀ * C (e,false)) X=0 at hg
      change D (e,true)=_ at h2
      rw [h1,h2,Matrix.mul_zero,zero_add,transpose_vecMulVec,vecMulVec_mul] at hg
      unfold T; rw [mul_vecMulVec, Matrix.mulVec_transpose,mpair_comm,mpair_outer,
        ←evmat_transpose, show Xᵀ=X from purePair_sym x e]
      rw [mpair_comm,mpair_outer] at hg
      exact hg
    change mpair ((C (e,true))ᵀ * D (e,false)+(D (e,true))ᵀ * C (e,false)) X=0 at hg
    change D (e,false)=_ at h2
    rw [h1,Matrix.transpose_zero,Matrix.zero_mul,add_zero,h2] at hg
    exact hg
  · intro k _ hk
    have h1 (i : Bool) : D (k,i)=0 := Pi.single_eq_of_ne (show (_,_)≠flipZ p z from
      fun hh => hk (congrArg Prod.fst hh)) _
    simp only [chanDeriv,chanInner,Pi.add_apply,h1,Matrix.transpose_zero,Matrix.mul_zero,
      Matrix.zero_mul,zero_add]
    rw [mpair_comm,map_zero]
  simp

namespace Volley
variable {v : Volley p n I}
theorem clean_effective {w : I→Bool} {a b : Plan p n} (t : Tagging p I)
    {q R : ℕ} (hb : v.bounded w) (hv : v.avoids a q) (hr : R+14≤q)
    {j : Bool} (M : Cross p n) (x : Xpair p n)
    (hh : orth p (channelOut p M j) (v.frozen a t) b j x)
    (hg : tableInj a b M) (i : Bool) (hx : ∀ e,v.clean i R ((x i).val e)) :
    (x i).val∈effective a i := by
  classical
  refine effective_mem.mpr ⟨(x i).property,fun e => ?_⟩
  let A := (x i).val e
  let S (z) := sPin (v.frozen a t) (e,z) i
  have hd (c : Bool) (φ : Ray p n) (hφ : φ∈annih (S (!c))) : A *ᵥ φ=0 := by
    have hray := clean_apply (hx e) φ
    have hm := orth_ip_frozen hh i (e,c) φ hφ
    exact hg (e,c) i j (A *ᵥ φ) (clean_Pin t hb hv hr _ _ i hray hm)
      (orth_delta_probe hh i (e,c) φ hφ)
  have hsym : Aᵀ=A := orth_pair_sym x e i
  have h (c : Bool) : colSp A ≤ sPin a (e,c) i := by
    have hh' : colSp A ≤ S c := by
      have hf : colSp A ≤ annih (annih (S c)) := (colSp_kill ..).mpr (fun φ hφ => by
        rw [hsym]
        exact hd (!c) φ (by simpa using hφ))
      rwa [annih_annih] at hf
    rintro x' ⟨y,rfl⟩
    exact clean_sPin t hb hv hr _ _ i (clean_apply (hx e) y) (hh' ⟨y,rfl⟩)
  change A∈box _ _
  rw [box_mem,hsym]
  exact ⟨h _,h _⟩

end Volley
end HadwigerCounterexample

end

end OAI
