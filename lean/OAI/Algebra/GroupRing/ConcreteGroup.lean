import Mathlib
import OAI.Algebra.GroupRing.CycleLists
import OAI.Algebra.GroupRing.Path

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ConcreteGroup
open scoped Classical
open SampleGraph
variable {rep : ℕ} (r : ActualPatternEvent.Match rep)
/-- Equal values at distinct endpoints within one graph component have an
actual reduced lifted disk picture. This is the precise obstruction needed
for the nonvanishing of the authors' factors, with no graph embedding assumed. -/
theorem equal_value_picture {z w : VA rep⊕VB rep}
    (hp : (ShortClosure.simpleGraph (Γ rep r)).Reachable z w) (hzw : z≠w)
    (hv : value rep r z=value rep r w) :
    ∃n,∃a : FinitePicture.Data (O:=Fin n) (Γ rep r) (SampleGraph.label rep) Types.inverse z w,
      a.Reduced := by
  let p := GraphPresentation.Path.ofWalk (Γ:=Γ rep r) (Classical.choice hp)
  apply reduced_picture r p hzw
  rw [path_value,hv,inv_mul_cancel]

end TorsionFreeZeroDivisors.ConcreteGroup
namespace TorsionFreeZeroDivisors.SampleGraph.Picture
open scoped Classical
open BlockAlignment ComparedBlocks
variable {rep : ℕ} (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
/-- The exact remaining sharp-separator obligation for the literal prepared
interaction graphs of disk pictures. This is NOT proved or inserted as a
hypothesis into the main target: it records the unclosed dependency. -/
def SeparatorObligation : Prop :=
  ∀(z w : VA rep⊕VB rep) (n : ℕ)
    (a : FinitePicture.Data (O:=Fin n) (graph rep r) (label rep) Types.inverse z w)
    (hzw : z≠w) (hr : a.Reduced) (hz : z=Sum.inl x ∨ z=Sum.inr y),
  ∀ S : Finset ((pairing a hzw hr hz).prepared hL hd).P,
    PlanarParameters.K PathSystem.ε ClosedWords.D<S.card →
    Nonempty (RecursiveSeparator.Split
      (PairingClusters.Rel (fun p : Position (fun t=>(((pairing a hzw hr hz).prepared hL hd).paths t).length)=>p.1)
        ((pairing a hzw hr hz).prepared hL hd).comparisons.pairing.partner) S)
/-- The actual disk/path endpoint, conditional on exactly the
still-missing sharp-separator dependency, not a replacement main theorem. -/
theorem root_path_nontrivial (hsample : r∈ActualPatternEvent.samples rep)
    (hsep : SeparatorObligation r x y hL hd)
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
    {z w : VA rep⊕VB rep} (p : GraphPresentation.Path (graph rep r) z w)
    (hzw : z≠w) (hz : z=Sum.inl x ∨ z=Sum.inr y) :
    p.eval (ConcreteGroup.letter rep r ∘ label rep)≠1 := by
  intro hp
  obtain ⟨n,a,hr⟩ := ConcreteGroup.reduced_picture r p hzw hp
  exact excluded a hzw hr hz hL hd hsample (hsep z w n a hzw hr hz) havoid

end TorsionFreeZeroDivisors.SampleGraph.Picture

namespace TorsionFreeZeroDivisors.BoundaryRefinement

section
open scoped Classical
variable {I : Type} {O : I→Type} [∀i,Fintype (O i)]
/-- Performing literal vertex cuts in one boundary fiber performs the same
cuts in the whole occurrence set, leaving every other fiber unchanged. -/
lemma fiber {i : I} {σ τ : Equiv.Perm (O i)} (h : Cuts σ τ)
    (ρ : ∀j,Equiv.Perm (O j)) :
    Cuts (Equiv.sigmaCongrRight (Function.update ρ i σ))
      (Equiv.sigmaCongrRight (Function.update ρ i τ)) := by
  induction h with
  | refl=>exact .refl _
  | step σ p q hn hc=>
    have he : Equiv.sigmaCongrRight (Function.update ρ i (Equiv.swap p q*σ))=
        Equiv.swap (Sigma.mk i p) (Sigma.mk i q)*
          Equiv.sigmaCongrRight (Function.update ρ i σ) := by
      apply Equiv.ext
      rintro ⟨j,x⟩
      by_cases hj : j=i
      · subst j
        simp only [Equiv.sigmaCongrRight_apply,Function.update_self,Equiv.Perm.mul_apply]
        by_cases hp : σ x=p
        · rw [hp];simp
        · by_cases hq : σ x=q
          · rw [hq];simp
          · simp [Equiv.swap_apply_def,hp,hq]
      · have h₁ : (⟨j,ρ j x⟩ : Sigma O)≠⟨i,p⟩ := fun he=>hj (congrArg Sigma.fst he)
        have h₂ : (⟨j,ρ j x⟩ : Sigma O)≠⟨i,q⟩ := fun he=>hj (congrArg Sigma.fst he)
        simp only [Equiv.sigmaCongrRight_apply,Function.update_of_ne hj,
          Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne h₁ h₂]
    rw [he]
    have hh := Cuts.step (Equiv.sigmaCongrRight (Function.update ρ i σ))
      (Sigma.mk i p) (Sigma.mk i q)
      (fun he=>hn (eq_of_heq (Sigma.mk.inj_iff.mp he).2))
      (mapped_sameCycle (Sigma.mk i) σ (Equiv.sigmaCongrRight (Function.update ρ i σ))
        (fun x=>by simp) hc)
    convert hh using 1
    apply Equiv.ext
    intro x
    simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_def]
    split_ifs <;> rfl
  | trans h h' ih ih'=>exact ih.trans ih'
variable [Fintype I]
/-- All of a finite family's contiguous boundary refinements may be carried
out simultaneously, with the matching on the whole occurrence set retained. -/
lemma sigma {σ τ : ∀i,Equiv.Perm (O i)} (h : ∀i,Cuts (σ i) (τ i)) :
    Cuts (Equiv.sigmaCongrRight σ) (Equiv.sigmaCongrRight τ) := by
  let mix (s : Finset I) (i : I) := if i∈s then τ i else σ i
  have hm : ∀s : Finset I,Cuts (Equiv.sigmaCongrRight σ) (Equiv.sigmaCongrRight (mix s)) := by
    intro s
    induction s using Finset.induction_on with
    | empty=>simpa only [mix,Finset.notMem_empty,ite_false] using (Cuts.refl (Equiv.sigmaCongrRight σ))
    | @insert i s hi ih=>
      have h₁ : Function.update (mix s) i (σ i)=mix s := by
        apply funext
        intro j
        by_cases hj : j=i
        · subst j;simp [mix,hi]
        · simp [Function.update_of_ne hj]
      have h₂ : Function.update (mix s) i (τ i)=mix (insert i s) := by
        apply funext
        intro j
        by_cases hj : j=i
        · subst j;simp [mix]
        · simp [mix,hj]
      have hh := fiber (h i) (mix s)
      rw [h₁,h₂] at hh
      exact ih.trans hh
  simpa only [mix,Finset.mem_univ,ite_true] using hm Finset.univ

end

open scoped Classical BigOperators
lemma finCongr_rotate {n m : ℕ} (h : n=m) :
    (finCongr h).permCongr (finRotate n)=finRotate m := by
  subst m
  rfl
lemma sigmaCongrLeft_rotation {I J : Type} {O : J→Type} (e : I≃J)
    (σ : ∀j,Equiv.Perm (O j)) :
    (e.sigmaCongrLeft).permCongr (Equiv.sigmaCongrRight fun i=>σ (e i))=
      Equiv.sigmaCongrRight σ := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,j⟩,rfl⟩ := e.sigmaCongrLeft.surjective x
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  rfl
lemma sumSigma_rotation {I J : Type} {O : I⊕J→Type}
    (σ : ∀j,Equiv.Perm (O j)) :
    (Equiv.sumSigmaDistrib O).permCongr (Equiv.sigmaCongrRight σ)=
      Equiv.sumCongr (Equiv.sigmaCongrRight fun i=>σ (Sum.inl i))
        (Equiv.sigmaCongrRight fun j=>σ (Sum.inr j)) := by
  apply Equiv.ext
  rintro (⟨i,x⟩|⟨j,x⟩) <;> rfl
lemma uniqueSigma_rotation {I : Type} [Unique I] {O : I→Type}
    (σ : ∀i,Equiv.Perm (O i)) :
    (Equiv.uniqueSigma O).permCongr (Equiv.sigmaCongrRight σ)=σ default := by
  apply Equiv.ext
  intro x
  rfl
/-- The pinned `finSigmaFinEquiv` is the literal consecutive sum indexing;
cutting exactly at its fiber boundaries preserves the entire matching. -/
lemma fin_refinement {m : ℕ} (n : Fin m→ℕ) :
    Cuts (finSigmaFinEquiv.symm.permCongr (finRotate (∑i,n i)))
      (Equiv.sigmaCongrRight fun i=>finRotate (n i)) := by
  induction m with
  | zero=>
    have he : finSigmaFinEquiv.symm.permCongr (finRotate (∑i,n i))=
        Equiv.sigmaCongrRight (fun i=>finRotate (n i)) := by
      apply Equiv.ext
      rintro ⟨i,j⟩
      exact i.elim0
    rw [he]
    exact .refl _
  | succ m ih=>
    let L : Fin m→ℕ := fun i=>n i.castSucc
    let R : Fin 1→ℕ := fun i=>n (Fin.natAdd m i)
    let e₁ : ((i : Fin m⊕Fin 1) × Fin (n (finSumFinEquiv i)))≃((i : Fin (m+1)) × Fin (n i)) :=
      Equiv.sigmaCongrLeft (β:=fun i=>Fin (n i)) (@finSumFinEquiv m 1)
    let e₂ := Equiv.sumSigmaDistrib (fun i : Fin m⊕Fin 1=>Fin (n (finSumFinEquiv i)))
    let e₃ : (((i : Fin m) × Fin (L i))⊕((i : Fin 1) × Fin (R i)))≃
      (Fin (∑i,L i)⊕Fin (n (Fin.last m))) :=
      Equiv.sumCongr finSigmaFinEquiv (Equiv.uniqueSigma _)
    let e : (((i : Fin m) × Fin (L i))⊕((i : Fin 1) × Fin (R i)))≃
      ((i : Fin (m+1)) × Fin (n i)) := e₂.symm.trans e₁
    have hh := conjugate (BlockBoundary.fin_cut (∑i,L i) (n (Fin.last m))) e₃.symm
    have he₁ : e₃.symm.permCongr
        (finSumFinEquiv.symm.permCongr (finRotate ((∑i,L i)+n (Fin.last m))))=
        e.symm.permCongr (finSigmaFinEquiv.symm.permCongr (finRotate (∑i,n i))) := by
      have hf : (finSigmaFinEquiv : ((i : Fin (m+1)) × Fin (n i))≃Fin (∑i,n i))=
          e.symm.trans (e₃.trans (finSumFinEquiv.trans (finCongr (Fin.sum_univ_castSucc n).symm))) := rfl
      rw [hf]
      have hc := finCongr_rotate (Fin.sum_univ_castSucc n)
      apply Equiv.ext
      intro x
      have hc' := congrArg (fun f=>f (finSumFinEquiv (e₃ x))) hc
      simp only [Equiv.permCongr_apply] at hc'
      simp only [Equiv.permCongr_apply,Equiv.trans_apply,Equiv.symm_trans_apply,
        Equiv.symm_symm,Equiv.symm_apply_apply]
      congr 2
      exact hc'.symm
    have he₂ : e₃.symm.permCongr (Equiv.sumCongr (finRotate (∑i,L i)) (finRotate (n (Fin.last m))))=
        Equiv.sumCongr (finSigmaFinEquiv.symm.permCongr (finRotate (∑i,L i)))
          (Equiv.sigmaCongrRight fun i=>finRotate (R i)) := by
      apply Equiv.ext
      rintro (x|x)
      · rfl
      · rcases x with ⟨i,j⟩
        have hi : i=default := Subsingleton.elim _ _
        subst i
        rfl
    rw [he₁,he₂] at hh
    have hl := hh.trans (left (ih L) (Equiv.sigmaCongrRight fun i=>finRotate (R i)))
    have ht := conjugate hl e
    have he₃ : e.permCongr (Equiv.sumCongr (Equiv.sigmaCongrRight fun i=>finRotate (L i))
        (Equiv.sigmaCongrRight fun i=>finRotate (R i)))=
        Equiv.sigmaCongrRight fun i=>finRotate (n i) := by
      have hd := sumSigma_rotation (fun i : Fin m⊕Fin 1=>finRotate (n (finSumFinEquiv i)))
      change e₂.permCongr (Equiv.sigmaCongrRight fun i=>finRotate (n (finSumFinEquiv i)))=
        Equiv.sumCongr (Equiv.sigmaCongrRight fun i=>finRotate (L i))
          (Equiv.sigmaCongrRight fun i=>finRotate (R i)) at hd
      rw [←hd]
      change e₁.permCongr (e₂.symm.permCongr (e₂.permCongr _))=_
      rw [←Equiv.permCongr_symm,Equiv.symm_apply_apply]
      exact sigmaCongrLeft_rotation (O:=fun i=>Fin (n i)) (@finSumFinEquiv m 1) (fun i=>finRotate (n i))
    simpa only [←Equiv.permCongr_symm,Equiv.apply_symm_apply,he₃] using ht

lemma fin_index_refinement {m h : ℕ} (n : Fin m→ℕ) (hs : (∑i,n i)=h) :
    Cuts ((finSigmaFinEquiv.trans (finCongr hs)).symm.permCongr (finRotate h))
      (Equiv.sigmaCongrRight fun i=>finRotate (n i)) := by
  have hc := finCongr_rotate hs.symm
  have he : (finSigmaFinEquiv.trans (finCongr hs)).symm.permCongr (finRotate h)=
      finSigmaFinEquiv.symm.permCongr (finRotate (∑i,n i)) := by
    change finSigmaFinEquiv.symm.permCongr ((finCongr hs).symm.permCongr (finRotate h))=_
    rw [show (finCongr hs).symm=finCongr hs.symm from rfl,hc]
  rw [he]
  exact fin_refinement n
end TorsionFreeZeroDivisors.BoundaryRefinement
namespace TorsionFreeZeroDivisors.BalancedGenus
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions BoundaryRefinement
variable {T A : Type} [Fintype T] (w : T→List A) (cap : ℕ) (hc : 0<cap)
lemma join_refinement : Cuts
    ((WordPositions.join w cap hc).symm.permCongr (BoundaryRotation.perm fun t=>(w t).length))
    (BoundaryRotation.perm (BalancedWords.old w cap)) := by
  let N (t : T) := BalancedPieces.number (w t).length cap
  let n (t : T) : Fin (N t)→ℕ := BalancedPieces.sizes (w t).length cap
  let idx (t : T) := ConsecutivePieces.index (w t) (n t) (BalancedPieces.sizes_sum hc)
  have hh : ∀ t,Cuts ((idx t).symm.permCongr (finRotate (w t).length))
      (Equiv.sigmaCongrRight fun i=>finRotate (n t i)) :=
    fun t=>fin_index_refinement (n t) (BalancedPieces.sizes_sum hc)
  let e : ((t : T) × (i : Fin (N t)) × Fin (n t i))≃Position (BalancedWords.old w cap) :=
    (Equiv.sigmaAssoc fun t i=>Fin (n t i)).symm.trans (fin _).symm
  have ht := conjugate (sigma hh) e
  have he₁ : e.permCongr (Equiv.sigmaCongrRight fun t=>(idx t).symm.permCongr (finRotate (w t).length))=
      (WordPositions.join w cap hc).symm.permCongr (BoundaryRotation.perm fun t=>(w t).length) := by
    apply Equiv.ext
    intro p
    simp only [e,WordPositions.join,WordPositions.joinFin,BoundaryRotation.perm,
      Equiv.permCongr_apply,Equiv.trans_apply,Equiv.symm_trans_apply,
      Equiv.symm_symm]
    rfl
  have he₂ : e.permCongr (Equiv.sigmaCongrRight fun t=>Equiv.sigmaCongrRight fun i=>finRotate (n t i))=
      BoundaryRotation.perm (BalancedWords.old w cap) := by
    apply Equiv.ext
    intro p
    simp only [e,BoundaryRotation.perm,Equiv.permCongr_apply,Equiv.symm_symm]
    rfl
  rwa [he₁,he₂] at ht
lemma position_refinement {T : Type} {l k : T→ℕ} (h : ∀t,l t=k t) :
    (ComparisonGeometry.position (Equiv.refl T) h).permCongr (BoundaryRotation.perm l)=
      BoundaryRotation.perm k := by
  have he : l=k := funext h
  subst k
  rfl
lemma refinement : Cuts (BalancedRotation.perm w cap hc)
    (BoundaryRotation.perm (BalancedRotation.len w cap hc)) := by
  let g := ComparisonGeometry.position (Equiv.refl _) (BalancedWords.segment_length w cap hc)
  have ht := conjugate (join_refinement w cap hc) g.symm
  have hr := position_refinement (BalancedWords.segment_length w cap hc)
  change g.permCongr (BoundaryRotation.perm (BalancedRotation.len w cap hc))=
    BoundaryRotation.perm (BalancedWords.old w cap) at hr
  rw [←hr,←Equiv.permCongr_symm,Equiv.symm_apply_apply] at ht
  exact ht
lemma genusZero (α : Equiv.Perm (Position fun t=>(w t).length))
    (hi : Function.Involutive α) (hz : MapEuler.GenusZero
      (BoundaryRotation.perm fun t=>(w t).length) α) :
    MapEuler.GenusZero (BoundaryRotation.perm (BalancedRotation.len w cap hc))
      ((BalancedRotation.e w cap hc).symm.permCongr α) :=
  preserves (refinement w cap hc) _ (PermutationTransport.involutive _ _ hi)
    (MapConjugation.genusZero (BalancedRotation.e w cap hc).symm _ _ hz)

end TorsionFreeZeroDivisors.BalancedGenus
namespace TorsionFreeZeroDivisors.ExtendComparisons
open scoped Classical
open BlockAlignment ComparedBlocks
variable {T E : Type} {len more : T→ℕ} (C : Comparisons (E:=E) len)
  (hle : ∀t,len t ≤ more t)
/-- Added closure letters are fixed; they introduce no interaction between
DIFFERENT boundary pieces. This statement does not discard self-loops silently. -/
lemma rel_iff {p q : T} (hpq : p≠q) :
    PairingClusters.Rel (fun x : Position more=>x.1) (partner C hle) p q ↔
      PairingClusters.Rel (fun x : Position len=>x.1) C.pairing.partner p q := by
  constructor
  · rintro ⟨x,hx,hy⟩
    by_cases ho : Old (len:=len) x
    · refine ⟨project x ho,hx,?_⟩
      simpa only [partner,dite_eq_left ho,embed] using hy
    · rw [partner_new C hle x ho] at hy
      exact False.elim (hpq (hx.symm.trans hy))
  · rintro ⟨x,hx,hy⟩
    refine ⟨embed hle x,hx,?_⟩
    rw [partner_embed]
    exact hy

end TorsionFreeZeroDivisors.ExtendComparisons
namespace TorsionFreeZeroDivisors.RecursiveSeparator.Split
open scoped Classical
def changeDecidableEq {V : Type} {d d' : DecidableEq V} {R : V→V→Prop} {S : Finset V}
    (P : @RecursiveSeparator.Split V d R S) : @RecursiveSeparator.Split V d' R S := by
  cases Subsingleton.elim d d'
  exact P
variable {V : Type} [DecidableEq V] {R Q : V→V→Prop} {S : Finset V}
/-- Loops have no effect on separator closure. -/
def of_off_diagonal (h : ∀p q,p≠q→(R p q↔Q p q)) (P : RecursiveSeparator.Split R S) :
    RecursiveSeparator.Split Q S where
  remove := P.remove
  parts := P.parts
  remove_subset := P.remove_subset
  cover := P.cover
  disjoint := P.disjoint
  closed := by
    intro b hb x hx y hy hq
    by_cases he : x=y
    · simpa only [←he] using hx
    · exact P.closed b hb x hx y hy ((h x y he).mpr hq)
  size := P.size
  cost := P.cost

end TorsionFreeZeroDivisors.RecursiveSeparator.Split
namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing
open scoped Classical
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
  {s : PathSystem rep r x y} (a : FullPairing s) (cap : ℕ) (hc : 0<cap)
  (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
lemma closed_rel {p q : ClosedWords.Piece s cap} (hpq : p≠q) :
    PairingClusters.Rel (fun z : Position (fun t=>((a.closed cap hc hL hd).paths t).length)=>z.1)
      (a.closed cap hc hL hd).comparisons.pairing.partner p q ↔
    PairingClusters.Rel (fun z : Position (BalancedRotation.len s.paths cap hc)=>z.1)
      (a.α cap hc) p q := by
  exact ExtendComparisons.rel_iff (a.comparisons cap hc)
    (ClosedWords.grow s cap hc hL hd) hpq

end TorsionFreeZeroDivisors.SampleGraph.FullPairing

end

end OAI
