import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeEdgeInjective
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LitEdgesSubsetTree

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.ForestTraversal OrdinaryCorrelations.Rerooting
open Finset Classical SimpleGraph
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

structure DisconnectedWitness (w : ClosedLine h ℓ) (hh : 0<h)
    (a : S.FixedResidues w) (p : S.FixedIndex w) where
  left : ℤ
  right : ℤ
  left_mem : left ∈ treeVertices w
  right_mem : right ∈ treeVertices w
  left_active : a p+(left:ZMod (p.val:ℕ))=0
  right_active : a p+(right:ZMod (p.val:ℕ))=0
  separate : ¬(edgeGraph w hh (litEdges w p.val (a p))).Reachable left right

lemma DisconnectedWitness.left_cast {w : ClosedLine h ℓ} {hh : 0<h} {a : S.FixedResidues w}
    {p q : S.FixedIndex w} (he : p=q) (d : DisconnectedWitness w hh a p) :
    (he ▸ d).left=d.left := by subst q; rfl
lemma DisconnectedWitness.right_cast {w : ClosedLine h ℓ} {hh : 0<h} {a : S.FixedResidues w}
    {p q : S.FixedIndex w} (he : p=q) (d : DisconnectedWitness w hh a p) :
    (he ▸ d).right=d.right := by subst q; rfl

lemma disconnected_witness_exists (w : ClosedLine h ℓ) (hh : 0<h) (a : S.FixedResidues w)
    (p : S.FixedIndex w) (hn : ¬ActiveConnected w hh p.val (a p)) :
    Nonempty (DisconnectedWitness w hh a p) := by
  unfold ActiveConnected at hn
  push Not at hn
  obtain ⟨u,hu,v,hv,hua,hva,hn⟩ := hn
  exact ⟨⟨u,v,hu,hv,hua,hva,hn⟩⟩

structure DisconnectedBlockPair (w : NumericalLine D h ℓ) (hh : 0<h)
    (a : S.FixedResidues w.line) (H : Finset (Fin ℓ)) (L : ℕ) where
  selected : Finset (S.FixedIndex w.line)
  tree : ∀ p ∈ selected,(treeOccurrences w.line p.val).Nonempty
  first : Block (edgeGraph w.line hh (w.line.treeSteps\H))
  second : Block (edgeGraph w.line hh (w.line.treeSteps\H))
  first_small : first.walk.length ≤ L
  second_small : second.walk.length ≤ L
  witness : ∀ p ∈ selected,DisconnectedWitness w.line hh a p
  left_in : ∀ p hp,(witness p hp).left ∈ first.walk.support
  right_in : ∀ p hp,(witness p hp).right ∈ second.walk.support

theorem disconnected_block_pair_exists (w : NumericalLine D h ℓ) (hh : 0<h)
    (a : S.FixedResidues w.line) (H : Finset (Fin ℓ)) (hL : 0<L)
    (hd : 0<disconnectedCount w.line hh a) :
    ∃ F : DisconnectedBlockPair w hh a H L,
      disconnectedCount w.line hh a ≤ ((2*ℓ)/L+2*H.card+1)^2*F.selected.card := by
  obtain ⟨bs,hbs,hsmall,hvertices⟩ := tree_blocks w.line hh H L hL
  let A := univ.filter (fixedDisconnected w.line hh a)
  let p : A↪S.FixedIndex w.line := ⟨fun q => ⟨q.val,(mem_filter.mp q.property).2.2.choose⟩,
    by
      intro q r he
      apply Subtype.ext
      exact congrArg (fun x : S.FixedIndex w.line => x.val) he⟩
  have hp (q : A) : ¬ActiveConnected w.line hh (p q).val (a (p q)) :=
    (mem_filter.mp q.property).2.2.choose_spec
  let W : ∀ q : A,DisconnectedWitness w.line hh a (p q) := fun q =>
    Classical.choice (disconnected_witness_exists w.line hh a (p q) (hp q))
  have h1 (q : A) : ∃ i : Fin bs.length,(W q).left ∈ (bs.get i).walk.support := by
    obtain ⟨b,hb,he⟩ := hvertices _ (W q).left_mem
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hb
    exact ⟨i,he⟩
  have h2 (q : A) : ∃ i : Fin bs.length,(W q).right ∈ (bs.get i).walk.support := by
    obtain ⟨b,hb,he⟩ := hvertices _ (W q).right_mem
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hb
    exact ⟨i,he⟩
  choose c₁ hc₁ using h1
  choose c₂ hc₂ using h2
  let c (q : A) := (c₁ q,c₂ q)
  let I := (univ : Finset A).image c
  have hI : I.Nonempty := by
    obtain ⟨q,hq⟩ := card_pos.mp hd
    exact ⟨c ⟨q,hq⟩,mem_image.mpr ⟨⟨q,hq⟩,mem_univ _,rfl⟩⟩
  obtain ⟨z,hz,hmax⟩ := exists_max_image I (fun k => ((univ : Finset A).filter (fun q => c q=k)).card) hI
  let C := (univ : Finset A).filter (fun q => c q=z)
  have hcount : A.card ≤ bs.length^2*C.card := by
    have he := card_eq_sum_card_image c (univ : Finset A)
    simp only [card_univ,Fintype.card_coe] at he
    calc
      _ = ∑ k ∈ I,((univ : Finset A).filter (fun q => c q=k)).card := he
      _ ≤ ∑ _k ∈ I,C.card := sum_le_sum hmax
      _ = I.card*C.card := by simp
      _ ≤ bs.length^2*C.card := by
        apply Nat.mul_le_mul_right
        have hi := card_le_univ I
        simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using hi
  let A' := C.image p
  have hin (q : S.FixedIndex w.line) (hq : q ∈ A') : ∃ r ∈ C,p r=q := mem_image.mp hq
  choose r hr he using hin
  let F : DisconnectedBlockPair w hh a H L := {
    selected := A'
    tree q hq := by
      rw [←he q hq]
      exact (mem_filter.mp (r q hq).property).2.1
    first := bs.get z.1
    second := bs.get z.2
    first_small := hsmall _ (List.get_mem ..)
    second_small := hsmall _ (List.get_mem ..)
    witness q hq := (he q hq) ▸ W (r q hq)
    left_in q hq := by
      have hc := congrArg Prod.fst (mem_filter.mp (hr q hq)).2
      dsimp [c] at hc
      rw [DisconnectedWitness.left_cast,←hc]
      exact hc₁ (r q hq)
    right_in q hq := by
      have hc := congrArg Prod.snd (mem_filter.mp (hr q hq)).2
      dsimp [c] at hc
      rw [DisconnectedWitness.right_cast,←hc]
      exact hc₂ (r q hq) }
  refine ⟨F,?_⟩
  change A.card ≤ _*A'.card
  rw [card_image_of_injective _ p.injective]
  exact hcount.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbs 2))

namespace DisconnectedBlockPair
variable {w : NumericalLine D h ℓ} {hh : 0<h} {a : S.FixedResidues w.line}
    {H : Finset (Fin ℓ)} (F : DisconnectedBlockPair w hh a H L)

lemma first_nonempty (p : F.selected) : (blockActiveSet w.line hh a F.first p.val).Nonempty :=
  ⟨(F.witness p.val p.property).left,mem_filter.mpr ⟨(F.witness p.val p.property).left_mem,
    F.left_in p.val p.property,(F.witness p.val p.property).left_active⟩⟩
lemma second_nonempty (p : F.selected) : (blockActiveSet w.line hh a F.second p.val).Nonempty :=
  ⟨(F.witness p.val p.property).right,mem_filter.mpr ⟨(F.witness p.val p.property).right_mem,
    F.right_in p.val p.property,(F.witness p.val p.property).right_active⟩⟩

lemma active_separate
    (hcut : ∀ (P : TreePath w L) (p : S.FixedIndex w.line),P.IsGap a p → ∃ i,P.edge i ∈ H)
    (p : F.selected) (hph : ¬(p.val.val:ℕ) ∣ h)
    {x y : ℤ} (hx : x ∈ blockActiveSet w.line hh a F.first p.val)
    (hy : y ∈ blockActiveSet w.line hh a F.second p.val) :
    ¬(edgeGraph w.line hh (litEdges w.line p.val.val (a p.val))).Reachable x y := by
  obtain ⟨hxt,hxb,hxa⟩ := mem_filter.mp hx
  obtain ⟨hyt,hyb,hya⟩ := mem_filter.mp hy
  have h1 := block_active_connected w hh a H hcut F.first F.first_small p.val hph
    (F.witness p.val p.property).left_mem (F.left_in p.val p.property) hxb
    (F.witness p.val p.property).left_active hxa
  have h2 := block_active_connected w hh a H hcut F.second F.second_small p.val hph
    hyt hyb (F.right_in p.val p.property) hya (F.witness p.val p.property).right_active
  intro hn
  exact (F.witness p.val p.property).separate (h1.trans (hn.trans h2))

end DisconnectedBlockPair
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
