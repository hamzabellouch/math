import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays11
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays12
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
open ProductExposureLabels SourceExposureSlots
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open scoped BigOperators BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a)
abbrev m (t : Fin D.targets) := Fintype.card {j : Fin a // j∈D.tail t}
abbrev h (t : Fin D.targets) := Fintype.card {j : Fin a // j∉D.tail t}
def perm (t : Fin D.targets) : Fin (m D t+h D t)≃Fin a :=
  finSumFinEquiv.symm.trans
    (((Fintype.equivFin {j : Fin a // j∈D.tail t}).symm.sumCongr
      (Fintype.equivFin {j : Fin a // j∉D.tail t}).symm).trans
        (Equiv.sumCompl (fun j : Fin a=>j∈D.tail t)))
def outer (t : Fin D.targets) (u : Fin a→ℕ) (j : Fin (h D t)) : ℕ :=
  u (perm D t (j.natAdd (m D t)))
def inner (t : Fin D.targets) (u : Fin a→ℕ) (j : Fin (m D t)) : ℕ :=
  u (perm D t (j.castAdd (h D t)))
 

def reconstruct (t : Fin D.targets) (y : Fin (h D t)→ℕ) (b : Label (m D t)) : Fin a→ℤ :=
  fun j=>Fin.append b.residue (fun k=>(y k:ℤ)) ((perm D t).symm j)
abbrev qdim (t : Fin D.targets) := Fintype.card {e : Fin D.pairs // D.owner e=t}
def coord (e : Fin D.pairs) : Fin (qdim D (D.owner e)) :=
  Fintype.equivFin {f : Fin D.pairs // D.owner f=D.owner e} ⟨e,rfl⟩
def ownPair (t : Fin D.targets) (k : Fin (qdim D t)) : {e : Fin D.pairs // D.owner e=t} :=
  (Fintype.equivFin {e : Fin D.pairs // D.owner e=t}).symm k
variable (s r : ℕ) (hs : 1 ≤ s) (Fs : Finset (Scale a)) (q₀ : ℕ) (b₀ : Scale a)
local notation "I" => FiniteModelSlots.Index D s r hs Fs q₀ b₀
variable (G₀ : Fin D.targets→ℚ→Fin r→Type)
variable [∀ t v c,Group (G₀ t v c)] [∀ t v c,TopologicalSpace (G₀ t v c)]
variable (Γ₀ : ∀ t v c,Subgroup (G₀ t v c))
variable (M J R H : ℕ→ℕ) (L : ℕ→ℤ) (C : ℕ→Fin D.pairs→ℤ)
variable (g₀ x₀ : ∀ t,ℕ→(Fin (h D t)→ℕ)→∀ v c,ℤ→ℤ→G₀ t v c)
variable (obs₀ : ∀ t,ℕ→(Fin (h D t)→ℕ)→∀ v c,ℤ→ℤ→((G₀ t v c)⧸Γ₀ t v c) →ᵇ ℝ)
 

def family : ModelFamily D (fun t (i : I)=>G₀ t i.1.val.1 i.2)
    (qdim D) (fun t i=>Γ₀ t i.1.val.1 i.2) a where
  m:=m D
  h:=h D
  perm:=perm D
  M:=M
  J:=J
  R:=R
  L:=L
  H:=H
  slot:=fun t N y b i=>slotValue D (L N) (C N) (reconstruct D t y b) i.1.val.2
  qval:=fun t N y b k=>qValue D (C N) (reconstruct D t y b) (ownPair D t k).val
  g:=fun t N y i=>g₀ t N y i.1.val.1 i.2
  x:=fun t N y i=>x₀ t N y i.1.val.1 i.2
  obs:=fun t N y i=>obs₀ t N y i.1.val.1 i.2

private lemma inside_mem (t : Fin D.targets) (j : Fin (m D t)) :
    perm D t (j.castAdd (h D t))∈D.tail t := by
  unfold perm
  rw [Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,Equiv.trans_apply]
  exact ((Fintype.equivFin {j : Fin a // j∈D.tail t}).symm j).property
private lemma outside_notMem (t : Fin D.targets) (j : Fin (h D t)) :
    perm D t (j.natAdd (m D t))∉D.tail t := by
  unfold perm
  rw [Equiv.trans_apply,finSumFinEquiv_symm_apply_natAdd,Equiv.trans_apply]
  exact ((Fintype.equivFin {j : Fin a // j∉D.tail t}).symm j).property
private lemma reconstruct_inside (t : Fin D.targets) (y : Fin (h D t)→ℕ)
    (b : Label (m D t)) (j : Fin (m D t)) :
    reconstruct D t y b (perm D t (j.castAdd (h D t)))=b.residue j := by
  simp [reconstruct]
private lemma reconstruct_outside (t : Fin D.targets) (y : Fin (h D t)→ℕ)
    (b : Label (m D t)) (j : Fin (h D t)) :
    reconstruct D t y b (perm D t (j.natAdd (m D t)))=(y j:ℤ) := by
  simp [reconstruct]
private def representative (L M : ℤ) (R : ℝ) (t : Fin D.targets) (z : (Fin a→ℕ)×ℕ) : Fin a→ℤ :=
  reconstruct D t (outer D t z.1) (expose L M R (inner D t z.1,z.2))
private lemma representative_data (L M : ℤ) (R : ℝ) (t : Fin D.targets) (z : (Fin a→ℕ)×ℕ) :
    (∀ j∈D.tail t,representative D L M R t z j≡(z.1 j:ℤ) [ZMOD L]) ∧
    (∀ j,j∉D.tail t → representative D L M R t z j=(z.1 j:ℤ)) := by
  constructor
  · intro j hj
    obtain ⟨i,rfl⟩:=(perm D t).surjective j
    revert hj
    refine Fin.addCases ?_ ?_ i
    · intro k hk
      rw [representative,reconstruct_inside]
      exact Int.mod_modEq _ _
    · intro k hk
      exact False.elim ((outside_notMem D t k) hk)
  · intro j hj
    obtain ⟨i,rfl⟩:=(perm D t).surjective j
    revert hj
    refine Fin.addCases ?_ ?_ i
    · intro k hk
      exact False.elim (hk (inside_mem D t k))
    · intro k hk
      rw [representative,reconstruct_outside]
      rfl
private lemma ownPair_coord (e : Fin D.pairs) :
    (ownPair D (D.owner e) (coord D e)).val=e := by
  simp [ownPair,coord]
 

theorem source_frozen_family (N W : ℕ) (z : (Fin a→ℕ)×ℕ)
    (hL : 0<L N) (hWL : (W:ℤ)∣L N) (hc : ∀ e,(W:ℤ)∣C N e)
    (hu : ∀ j,IsCoprime (z.1 j:ℤ) (L N))
    (hd : ∀ e,Disjoint (D.added e) (D.tail (D.owner e))) :
    let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    let l:=(d.atTime N).localModel z
    (∀ t (i : I),
      l.slot t i=slotValue D (L N) (C N) (fun j=>(z.1 j:ℤ)) i.1.val.2 ∧
      (W:ℤ)∣l.slot t i ∧
      |l.slot t i|≤(∑ e,|i.1.val.2 e|)*L N) ∧
    (∀ e,l.qval (D.owner e) (coord D e)=qValue D (C N) (fun j=>(z.1 j:ℤ)) e) ∧
    (∀ t (i : I),l.g t i=g₀ t N (outer D t z.1) i.1.val.1 i.2 ∧
      l.x t i=x₀ t N (outer D t z.1) i.1.val.1 i.2 ∧
      l.obs t i=obs₀ t N (outer D t z.1) i.1.val.1 i.2)
 := by
  dsimp only
  have hf (t : Fin D.targets) := source_exposure_slots D (L N) (W:ℤ) hL hWL (C N) hc
    (fun j=>(z.1 j:ℤ)) (representative D (L N) (M N:ℤ) (R N:ℝ) t z) hu t
    (representative_data D (L N) (M N:ℤ) (R N:ℝ) t z).1
    (representative_data D (L N) (M N:ℤ) (R N:ℝ) t z).2 hd
  refine ⟨?_,?_,?_⟩
  · intro t i
    change slotValue D (L N) (C N) (representative D (L N) (M N:ℤ) (R N:ℝ) t z) i.1.val.2= _ ∧ _
    have hh:=(hf t).2.2 i.1.val.2
    refine ⟨hh.1,?_,?_⟩
    · change (W:ℤ)∣slotValue D (L N) (C N) (representative D (L N) (M N:ℤ) (R N:ℝ) t z) i.1.val.2
      rw [hh.1]
      exact hh.2.1
    · change |slotValue D (L N) (C N) (representative D (L N) (M N:ℤ) (R N:ℝ) t z) i.1.val.2|≤_
      rw [hh.1]
      exact hh.2.2
  · intro e
    change qValue D (C N) (representative D (L N) (M N:ℤ) (R N:ℝ) (D.owner e) z)
      (ownPair D (D.owner e) (coord D e)).val= _
    rw [ownPair_coord]
    exact (hf (D.owner e)).2.1 e rfl
  · intro t i
    exact ⟨rfl,rfl,rfl⟩

end SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
open ProductExposureLabels SourceExposureSlots SourceResidueAlignment
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open scoped BigOperators BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a)
variable (s r : ℕ) (hs : 1 ≤ s) (Fs : Finset (Scale a)) (q₀ : ℕ) (b₀ : Scale a)
local notation "I" => FiniteModelSlots.Index D s r hs Fs q₀ b₀
variable (G₀ : Fin D.targets→ℚ→Fin r→Type)
variable [∀ t v c,Group (G₀ t v c)] [∀ t v c,TopologicalSpace (G₀ t v c)]
variable (Γ₀ : ∀ t v c,Subgroup (G₀ t v c))
variable (M J R H : ℕ→ℕ) (L : ℕ→ℤ) (C : ℕ→Fin D.pairs→ℤ)
variable (g₀ x₀ : ∀ t,ℕ→(Fin (h D t)→ℕ)→∀ v c,ℤ→ℤ→G₀ t v c)
variable (obs₀ : ∀ t,ℕ→(Fin (h D t)→ℕ)→∀ v c,ℤ→ℤ→((G₀ t v c)⧸Γ₀ t v c) →ᵇ ℝ)
private lemma canonical_inner_product (t : Fin D.targets) (u : Fin a→ℕ) :
    (∏ j : Fin (m D t),(inner D t u j:ℤ))=∏ j∈D.tail t,(u j:ℤ) := by
  have hi (j : Fin (m D t)) : perm D t (j.castAdd (h D t))=
      ((Fintype.equivFin {j : Fin a // j∈D.tail t}).symm j).val := by
    unfold perm
    rw [Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,Equiv.trans_apply]
    rfl
  simp only [inner,hi]
  calc
    _ = ∏ j : {j : Fin a // j∈D.tail t},(u j.val:ℤ) :=
      (Fintype.equivFin {j : Fin a // j∈D.tail t}).symm.prod_comp _
    _ = ∏ j∈D.tail t,(u j:ℤ) := Finset.prod_coe_sort (D.tail t) (fun j : Fin a=>(u j:ℤ))
private lemma coprime_of_mod_congr {L t t' : ℤ} (ht : IsCoprime t L) (he : t'≡t [ZMOD L]) :
    IsCoprime t' L := by
  obtain ⟨k,hk⟩:=Int.modEq_iff_dvd.mp he
  obtain ⟨a,b,hab⟩:=ht
  refine ⟨a,b+a*k,?_⟩
  linear_combination hab-a*hk
private lemma source_residue_congr {L t t' q : ℤ} (hL : 0<L) (ht : IsCoprime t L)
    (he : t'≡t [ZMOD L]) :
    SourceResidueAlignment.residue L t' q=SourceResidueAlignment.residue L t q := by
  have hs:=residue_spec L t q hL ht
  have hs':=residue_spec L t' q hL (coprime_of_mod_congr ht he)
  exact IntegerAlignment.residue_unique hL ht hs'.1 hs'.2.1 hs.1 hs.2.1
    ((he.symm.mul_right _).trans hs'.2.2) hs.2.2
 

theorem source_family_numeric (N W : ℕ) (z : (Fin a→ℕ)×ℕ)
    (hL : 0<L N) (hWL : (W:ℤ)∣L N) (hc : ∀ e,(W:ℤ)∣C N e)
    (hu : ∀ j,IsCoprime (z.1 j:ℤ) (L N))
    (hd : ∀ e,Disjoint (D.added e) (D.tail (D.owner e)))
    (hML : (M N:ℤ)∣L N) (k : ℤ) (τ : ℝ) :
    let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    let l:=(d.atTime N).localModel z
    l.modelSuccess (coord D) k s r hs (FiniteModelSlots.formula D s r hs Fs q₀ b₀) Fs q₀ b₀ τ ↔
      FiniteModelSlots.numericSuccess D s r hs Fs q₀ b₀
        (fun t (i : I)=>G₀ t i.1.val.1 i.2) (qdim D)
        (fun t i=>Γ₀ t i.1.val.1 i.2) (coord D) l k τ
 := by
  let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
  let l:=(d.atTime N).localModel z
  let G:=fun t (i : I)=>G₀ t i.1.val.1 i.2
  let Γ:=fun t (i : I)=>Γ₀ t i.1.val.1 i.2
  change l.modelSuccess (coord D) k s r hs (FiniteModelSlots.formula D s r hs Fs q₀ b₀) Fs q₀ b₀ τ ↔
    FiniteModelSlots.numericSuccess D s r hs Fs q₀ b₀ G (qdim D) Γ (coord D) l k τ
  have hf:=source_frozen_family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    N W z hL hWL hc hu hd
  have hmod (t : Fin D.targets) :
      (∏ j,(l.label t).residue j)≡(∏ j∈D.tail t,(z.1 j:ℤ)) [ZMOD L N] := by
    rw [←canonical_inner_product D t z.1]
    apply Int.ModEq.prod
    intro j hj
    exact Int.mod_modEq _ _
  have hcop (t : Fin D.targets) : IsCoprime (∏ j,(l.label t).residue j) (L N) :=
    coprime_of_mod_congr (IsCoprime.prod_left (fun j _=>hu j)) (hmod t)
  have hr (e : Fin D.pairs) : FiniteModelSlots.residue D s r hs Fs q₀ b₀ G (qdim D) Γ (coord D) l e=
      rValue D (L N) (C N) (fun j=>(z.1 j:ℤ)) e := by
    unfold FiniteModelSlots.residue FiniteModelSlots.coefficient
    rw [hf.2.1 e]
    apply source_residue_congr hL
    · exact IsCoprime.prod_left (fun j _=>hu j)
    · exact hmod (D.owner e)
  have hslot (v : Slots D) : FiniteModelSlots.slotSum D s r hs Fs q₀ b₀ G (qdim D) Γ (coord D) l v=
      slotValue D (L N) (C N) (fun j=>(z.1 j:ℤ)) v := by
    unfold FiniteModelSlots.slotSum slotValue
    simp_rw [hr]
  have hslots : (fun t (i : I)=>FiniteModelSlots.slotSum D s r hs Fs q₀ b₀ G (qdim D) Γ (coord D) l i.1.val.2)=l.slot := by
    funext t i
    exact (hslot i.1.val.2).trans (hf.1 t i).1.symm
  have he : FiniteModelSlots.compile D s r hs Fs q₀ b₀ G (qdim D) Γ (coord D) l=l := by
    unfold FiniteModelSlots.compile
    rw [hslots]
  have hn:=FiniteModelSlots.source_numeric_success D s r hs Fs q₀ b₀ G (qdim D) Γ (coord D) l k τ
    hL hML hcop
  rw [he] at hn
  exact hn

end SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
end

end

end OAI
