import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.AlignedCovariance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section InitialCoverSystem

private theorem alternating_hom_ext_small {I H : Type*} [Fintype I] [DecidableEq I]
    [Group H] (f g : alternatingGroup I →* H)
    (h : ∀ s : alternatingGroup I, s.val.support.card ≤ 5 → f s = g s) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense alternatingGroup.closure_isThreeCycles_eq_top
  intro s hs
  exact h s (by rw [hs.card_support]; omega)

structure InitialCoverSystem (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m) (M : ℕ) where
  t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm)
  c : alternatingGroup (Fin (m+1)) →*
    BoundedRelationCover M (alternatingGenerator a r m hm)
  t_base : ∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
    PresentedGroup.of (Sum.inr i)
  t_projection : (coverMap M (alternatingGenerator a r m hm)).comp t =
    sourceLatticeMap a r m hm
  t_stabilizers : ∀ s k, Commute (sourceLatticeMap a r m hm k)
    (alternatingGenerator a r m hm s) → Commute (t k) (PresentedGroup.of s)
  c_projection : (coverMap M (alternatingGenerator a r m hm)).comp c =
    conditionalAlternatingHom (wholePolygon a)
  c_base : ∀ b : {σ : Equiv.Perm (Fin (m+1)) // σ ∈ alternatingGroup (Fin (m+1)) ∧
    σ.support.card ≤ 5}, c ⟨b.val,b.property.1⟩ =
      PresentedGroup.of (sourceConditionalLabel m (0,b))
  constant_aligned : ∀ (s : alternatingGroup (Fin (m+1))) (I : Finset (Fin (m+1))),
    ∀ y ∈ sourceAlignedGroup a r m hm M t I,
      c s*y*(c s)⁻¹ ∈ sourceAlignedGroup a r m hm M t (I.map s.val.toEmbedding)
  disjoint_aligned : ∀ (I J : Finset (Fin (m+1))), Disjoint I J →
    ∀ x ∈ sourceAlignedGroup a r m hm M t I,
    ∀ y ∈ sourceAlignedGroup a r m hm M t J, Commute x y
  initialTable : (Set.range (polygonAssignment (initialTest a r)) →
    alternatingGroup (Fin (m+1))) →*
    BoundedRelationCover M (alternatingGenerator a r m hm)
  initialTable_projection : (coverMap M (alternatingGenerator a r m hm)).comp initialTable =
    actualPolygonTableHom (initialTest a r)
  initialTable_injective : Function.Injective initialTable
  initialTable_input : ∀ b, initialTable (polygonTableInput (initialTest a r) b.1
    (⟨b.2.val,b.2.property.1⟩ : alternatingGroup (Fin (m+1)))) =
      PresentedGroup.of (sourceConditionalLabel m b)
  perfect : Group.IsPerfect (BoundedRelationCover M (alternatingGenerator a r m hm))

theorem initialCoverSystem_eventually (a : ℕ) (r : CutRing) (m : ℕ)
    (hm : 2 ≤ m) (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → Nonempty (InitialCoverSystem a r m hm M) := by
  obtain ⟨L₁,hL₁⟩ := source_centralizing_translation_lifts_eventually a r m hm
  obtain ⟨L₂,hL₂⟩ := source_aligned_disjoint_eventually a r m hm (by omega)
  obtain ⟨L₃,hL₃⟩ := source_constant_covariance_eventually a r m hm hr hm'
  obtain ⟨L₄,hL₄⟩ := source_initial_table_lifts_eventually a r m hr hm' hm
  obtain ⟨L₅,hL₅⟩ := sourceCover_eventually_perfect a r m hr hm' hm
  refine ⟨L₁+L₂+L₃+L₄+L₅,fun M hM => ?_⟩
  obtain ⟨t,ht,htp,hts⟩ := hL₁ M (by omega)
  obtain ⟨t',ht',_,hd⟩ := hL₂ M (by omega)
  have he : t' = t := freeAbelianHom_ext t' t (fun i => (ht' i).trans (ht i).symm)
  subst t'
  obtain ⟨c,hcp,hcb,R,hc⟩ := hL₃ M (by omega)
  obtain ⟨hct,hcx⟩ := hc t ht
  obtain ⟨ρ,hρ,hinj,hinput⟩ := hL₄ M (by omega)
  refine ⟨{
    t := t
    c := c
    t_base := ht
    t_projection := htp
    t_stabilizers := hts
    c_projection := hcp
    c_base := hcb
    constant_aligned := ?_
    disjoint_aligned := hd
    initialTable := ρ
    initialTable_projection := hρ
    initialTable_injective := hinj
    initialTable_input := hinput
    perfect := hL₅ M (by omega) }⟩
  intro s I y hy
  exact source_aligned_constant_conjugation a r m hm M t c R hct hcx s I hy

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem initialTable_constant :
    B.initialTable.comp (polygonTableInput (initialTest a r) 0) = B.c := by
  apply alternating_hom_ext_small
  intro s hs
  change B.initialTable (polygonTableInput (initialTest a r) 0 s) = B.c s
  exact (B.initialTable_input (0,⟨s.val,s.property,hs⟩)).trans
    (B.c_base ⟨s.val,s.property,hs⟩).symm

end InitialCoverSystem
end InitialCoverSystem

end SimpleAmenable
end
end

end OAI
