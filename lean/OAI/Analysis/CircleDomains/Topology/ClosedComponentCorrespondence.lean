import OAI.Analysis.CircleDomains.Rigidity.MatchedConformalEnds

namespace OAI

/-! A closed correspondence on the full spheres. On the domain it is
the conformal map; over a complementary component its fiber is the
whole matching component. This includes disk-to-point and point-to-disk
matches, where a continuous single-valued extension need not exist. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def relationStage (n : ℕ) : Set (Sphere × Sphere) :=
  (fun q => (q,f q)) '' (D.cores n).carrier ∪
    ⋃ i, closedTerminalCap ((D.cores n).disk i) ×ˢ closedTerminalCap (D.disks n i)

 def componentRelation (q p : Sphere) : Prop := (q,p) ∈ ⋂ n, D.relationStage n

 theorem relationStage_iff (n : ℕ) (q p : Sphere) : (q,p) ∈ D.relationStage n ↔
    (q ∈ (D.cores n).carrier ∧ p = f q) ∨
      ∃ i, q ∈ closedTerminalCap ((D.cores n).disk i) ∧ p ∈ closedTerminalCap (D.disks n i) := by
  constructor
  · rintro (⟨x,hx,hpair⟩ | h)
    · have he : x = q := congrArg Prod.fst hpair
      subst x
      exact Or.inl ⟨hx,(congrArg Prod.snd hpair).symm⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp h
      exact Or.inr ⟨i,hi.1,hi.2⟩
  · rintro (⟨hq,rfl⟩ | ⟨i,hq,hp⟩)
    · exact Or.inl ⟨q,hq,rfl⟩
    · exact Or.inr (mem_iUnion.mpr ⟨i,hq,hp⟩)

 theorem componentRelation_closed (hf : IsConformalEquivalence f G (f '' G)) :
    IsClosed {z : Sphere × Sphere | D.componentRelation z.1 z.2} := by
  change IsClosed (⋂ n, D.relationStage n)
  apply isClosed_iInter
  intro n
  apply IsClosed.union
  · apply IsCompact.isClosed
    apply (D.cores n).isCompact.image_of_continuousOn
    exact continuousOn_id.prodMk (fun q hq => (hf.1 q ((D.cores n).subset hq)).1.continuousWithinAt.mono
      (D.cores n).subset)
  · apply isClosed_iUnion_of_finite
    intro i
    exact (isCompact_closedTerminalCap _).isClosed.prod (isCompact_closedTerminalCap _).isClosed

 theorem componentRelation_graph (_hf : IsConformalEquivalence f G (f '' G))
    {q : Sphere} (hq : q ∈ G) : D.componentRelation q (f q) := by
  apply mem_iInter.mpr
  intro n
  apply (D.relationStage_iff n q (f q)).mpr
  by_cases hn : q ∈ (D.cores n).carrier
  · exact Or.inl ⟨hn,rfl⟩
  · have hqU : q ∈ ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior ((D.cores n).disk i) := by
      exact not_not.mp hn
    obtain ⟨i,hi⟩ := mem_iUnion.mp hqU
    have hfi : f q ∈ f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((D.cores n).disk i))) :=
      ⟨q,⟨hq,hi⟩,rfl⟩
    rw [D.side] at hfi
    exact Or.inr ⟨i,(image_mono subset_closure) hi,(image_mono subset_closure) hfi.2⟩

 theorem componentRelation_on_domain {q p : Sphere} (hq : q ∈ G)
    (h : D.componentRelation q p) : p = f q := by
  obtain ⟨n,hn⟩ := mem_iUnion.mp (D.cover.symm ▸ hq)
  rcases (D.relationStage_iff n q p).mp (mem_iInter.mp h n) with hqp | ⟨i,hqi,_⟩
  · exact hqp.2
  · rw [SmoothJordanCore.carrier,interior_closedJordanCore] at hn
    exact (hn (mem_iUnion.mpr ⟨i,hqi⟩)).elim

 theorem componentRelation_source_fiber (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q : Sphere} (hq : q ∈ Gᶜ) :
    ∃ p ∈ (f '' G)ᶜ, {p' | D.componentRelation q p'} = connectedComponentIn (f '' G)ᶜ p := by
  obtain ⟨b,p,hp,hs,ht,_⟩ := corresponding_target_end_of_source hG hf.1 hf.bijOn.injOn
    D.cores D.disks D.strict D.cover D.disjoint D.complement D.boundary D.side hq
  refine ⟨p,hp,?_⟩
  ext p'
  constructor
  · intro h
    rw [ht]
    apply mem_iInter.mpr
    intro n
    rcases (D.relationStage_iff n q p').mp (mem_iInter.mp h n) with hg | ⟨i,hqi,hpi⟩
    · exact (hq ((D.cores n).subset hg.1)).elim
    · have hqb : q ∈ closedTerminalCap ((D.cores n).disk (b n)) :=
        mem_iInter.mp (hs ▸ mem_connectedComponentIn hq) n
      have hi : i = b n := by
        by_contra hne
        exact Set.disjoint_left.mp (disjoint_closedTerminalCaps _ (D.cores n).disjoint hne) hqi hqb
      simpa only [hi] using hpi
  · intro h
    apply mem_iInter.mpr
    intro n
    apply (D.relationStage_iff n q p').mpr
    exact Or.inr ⟨b n,mem_iInter.mp (hs ▸ mem_connectedComponentIn hq) n,
      mem_iInter.mp (ht ▸ h) n⟩

 theorem componentRelation_target_fiber (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    ∃ q ∈ Gᶜ, {q' | D.componentRelation q' p} = connectedComponentIn Gᶜ q := by
  let E := D.endAt hG hf p hp
  refine ⟨E.source,E.outside,?_⟩
  ext q'
  constructor
  · intro h
    rw [E.source_eq]
    apply mem_iInter.mpr
    intro n
    rcases (D.relationStage_iff n q' p).mp (mem_iInter.mp h n) with hg | ⟨i,hqi,hpi⟩
    · exact (hp ⟨q',(D.cores n).subset hg.1,hg.2.symm⟩).elim
    · have hpb : p ∈ closedTerminalCap (D.disks n (E.address n)) :=
        mem_iInter.mp (E.target_eq ▸ mem_connectedComponentIn hp) n
      have hi : i = E.address n := by
        by_contra hne
        exact Set.disjoint_left.mp (disjoint_closedTerminalCaps _ (D.disjoint n) hne) hpi hpb
      simpa only [hi] using hqi
  · intro h
    apply mem_iInter.mpr
    intro n
    apply (D.relationStage_iff n q' p).mpr
    exact Or.inr ⟨E.address n,mem_iInter.mp (E.source_eq ▸ h) n,
      mem_iInter.mp (E.target_eq ▸ mem_connectedComponentIn hp) n⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
