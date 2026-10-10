import OAI.Combinatorics.HadwigerCounterexample.ResidualCutPairs

namespace OAI

/-! # Response Solvability -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset Submodule
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

abbrev Individual (p : Shape) (n : ℕ) := Bool → Profile p n
abbrev OnForms (p : Shape) (n : ℕ) := Bool → (Profile p n →ₗ[F] F)
abbrev ReqF (p : Shape) (n : ℕ) := Module.Dual F (Xpair p n)

def combineF (p : Shape) {n} : OnForms p n →ₗ[F] ReqF p n where
  toFun f := ∑ i : Bool, f i ∘ₗ (Xspace p n).subtype ∘ₗ LinearMap.proj i
  map_add' f g := LinearMap.ext fun x => by
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,Pi.add_apply,LinearMap.add_apply,
      Finset.sum_add_distrib]
  map_smul' a f := LinearMap.ext fun x => by
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,Pi.smul_apply,LinearMap.smul_apply,
      RingHom.id_apply,smul_eq_mul,mul_sum]

theorem combineF_val (f : OnForms p n) (x : Xpair p n) :
    combineF p f x= ∑ i, f i (x i).val := by
  simp only [combineF,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.sum_apply]; rfl

theorem combineF_single (f : OnForms p n) (i : Bool) (x : Xspace p n) :
    combineF p f (Pi.single i x)=f i x.val := by
  rw [combineF_val,Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj; simp [hj]
  simp

theorem combineF_same (f g : OnForms p n) : combineF p f=combineF p g ↔
    ∀ i,∀ x ∈ Xspace p n,f i x=g i x := by
  constructor
  · intro h i x hx
    exact (combineF_single f i ⟨x,hx⟩).symm.trans (h ▸ combineF_single g i ⟨x,hx⟩)
  intro h
  apply LinearMap.ext; intro x
  rw [combineF_val,combineF_val]
  exact Finset.sum_congr rfl fun i _ => h i _ (x i).property

def obsPair (p : Shape) {n} : PureForms p n →ₗ[F] ReqF p n :=
  react p 0 ∘ₗ LinearMap.inr F (ChanOut p n) (PureForms p n)

theorem obsPair_val (A : PureForms p n) (x : Xpair p n) :
    obsPair p A x=∑ i,mpair (A i) (purePair p n x i) := by
  change ∑ i : Comp p.g, _ = _
  refine Finset.sum_congr rfl fun i _ => ?_
  change mpair ((chanDeriv p (n:=n) 0 0+A) _) _=_
  simp only [chanDeriv,chanInner,Pi.add_apply,Pi.zero_apply,Matrix.transpose_zero,Matrix.zero_mul,
    zero_add]

/-- Restrict pure form to individual diagonal blocks. -/
def eachF (p : Shape) {n} :
    PureForms p n →ₗ[F] Individual p n where
  toFun P i e := pullM (IP p n i) (IP p n i) (P e)
  map_add' P Q := by ext; simp only [Pi.add_apply,map_add]
  map_smul' a P := by ext; simp only [Pi.smul_apply,map_smul,RingHom.id_apply]

/-- Extend the individual forms by zero outside respective blocks, then add. -/
def sumF (p : Shape) {n} : Individual p n → PureForms p n :=
  fun A e => ∑ i,liftM (IP p n i) (IP p n i) (A i e)
theorem each_sumF (A : Individual p n) : eachF p (sumF p A)=A := by
  classical
  funext i e
  change pullM _ _ (∑ j,_) = _
  rw [map_sum,Finset.sum_eq_single i]
  · unfold pullM; rw [liftM_comp,IP_self]
    simp [liftM_def]
  · intro j _ hj
    unfold pullM
    rw [liftM_comp,IP_cross (Ne.symm hj)]
    simp [liftM_def]
  simp

def repF (p : Shape) {n} (A : Individual p n) : OnForms p n :=
  fun i => ∑ e : Comp p.g, mpair (A i e) ∘ₗ LinearMap.proj e

theorem repF_rep (A : Individual p n) (i) :
    Represents (repF p A i) (A i) := by
  intro x
  simp only [repF,LinearMap.sum_apply]; rfl

theorem obsPair_each (P : PureForms p n) :
    obsPair p P=combineF p (repF p (eachF p P)) := by
  apply LinearMap.ext
  intro x
  rw [obsPair_val,combineF_val]
  simp_rw [purePair,Finset.sum_apply,map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repF_rep]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mpair_liftM]; rfl

theorem obsPair_chan (B : Cross p n) (j : Bool) :
    obsPair p (chanInner p (channelOut p B j) (channelOut p B j))=
    combineF p (fun i => contract p B i j) := by
  apply LinearMap.ext; intro x
  rw [obsPair_val,combineF_val]
  simp_rw [purePair,Finset.sum_apply,map_sum]
  rw [Finset.sum_comm]; rfl

theorem each_chan_val (B C : ChanOut p n) (i) (e : Comp p.g) :
    eachF p (chanInner p B C) i e=(B (e,true) * IP p n i)ᵀ * (C (e,false)*IP p n i) := by
  change pullM _ _ _=_
  simp only [pullM_def,chanInner,transpose_mul,Matrix.mul_assoc]

theorem obsPair_chan_change (B C : ChanOut p n) :
    obsPair p (chanInner p (B+C) (B+C))=
    obsPair p (chanInner p B B)+ obsPair p (chanDeriv p B C) + obsPair p (chanInner p C C) := by
  rw [←map_add,←map_add]
  congr 1
  unfold chanInner chanDeriv
  funext i
  simp only [chanInner,Pi.add_apply,Matrix.transpose_add,Matrix.add_mul,Matrix.mul_add,add_assoc]
  ac_rfl

theorem react_obsPair (B C : ChanOut p n) (D : PureForms p n) :
    react p B (C,D)=obsPair p (chanDeriv p B C) + obsPair p D := by
  rw [←map_add]
  exact LinearMap.ext (fun x => (obsPair_val _ x).symm)

namespace Volley
variable (v w : Volley p n I)

def demand (t : Tagging p I) (m : Mixer p n) (j : Bool) : OnForms p n :=
  fun i => grad m (v.sumAt t w.obj i j)

theorem realize_linear {t : Tagging p I} (m : Mixer p n)
    (x y : UnitType p n N) (a b : Plan p n) (t' B : Cross p n)
    (hb : v.bounded w.obj) (ht : v.legal t)
    (q R : ℕ) (hv : v.avoids a q) (hj : 6*R+4≤p.j)
    (hr : 2*planRank a+28≤R) (hq : R+14≤q)
    (hB : fitsTable a b B t') (hT : tableInj a b t')
    (hf : rowAgree (v.frozen a t) B (actual p x y))
    (hR : v.scalarRecipe w t m x a t') (hk : v.keys t x=w.keys t y)
    (hL : ∀ i, frameLaw m (onSide y i))
    (hS : v.attackGrad w t m y) (j : Bool) :
    ∃ C∈deltaSpace p (v.frozen a t) b j,
    ∃ P∈pureSpace p (v.frozen a t),
      obsPair p (chanInner p (channelOut p B j) (channelOut p B j))+
      obsPair p (chanDeriv p (channelOut p B j) C) + obsPair p P=
        combineF p (v.demand w t m j) := by
  classical
  let G := v.demand w t m j
  let K : OnForms p n := fun i => contract p B i j
  let CC := channelOut p B j
  have h1 (i : I) : G (v.obj i) (v.atomAt t i) = K (v.obj i) (v.atomAt t i) := by
    change grad m (v.sumAt t w.obj (v.obj i) j) _ = contract p B _ _ _
    rw [frozen_contract_key v t hf,contract_actual,LinearMap.comp_apply,hS i j,
      v.atom_share w t x y hk]
    by_cases h : j=w.obj i
    · rw [ite_eq_left h,h,ufun_self (hL _)]
    have hh : (! (w.obj i))=j := by cases j <;> cases e : w.obj i <;> simp_all
    rw [ite_eq_right h, innerP, hh]; rfl
  have hg (z : Xpair p n) (h : orth p CC (v.frozen a t) b j z) :
      combineF p (G-K) z=0 := by
    obtain ⟨c,z,rfl,ho,hy⟩ := split_orth hb ht h hv hj hr hq
    have he (i : Bool) := clean_effective t hb hv hq B z ho (fits_inj hB hT) i (hy i)
    rw [map_add,map_sum]
    have h2 : combineF p (G-K) z = 0 := by
      rw [combineF_val]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Pi.sub_apply,LinearMap.sub_apply]
      exact sub_eq_zero.mpr ((hR.gradient i j _ (he i)).trans (fits_contract hB i j _ (he i)).symm)
    rw [h2,zero_add]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul,strike,combineF_single,Pi.sub_apply,LinearMap.sub_apply,
      h1 i,sub_self,smul_zero]

  obtain ⟨C,hC,P,hP,h⟩ := solve_by_dual _ hg
  rw [react_obsPair,map_sub] at h
  rw [obsPair_chan]
  refine ⟨C,hC,P,hP,?_⟩
  rw [add_assoc,h,add_sub_cancel]
end Volley

end HadwigerCounterexample

end

end OAI
