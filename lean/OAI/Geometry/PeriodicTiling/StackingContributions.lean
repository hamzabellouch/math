import OAI.Geometry.PeriodicTiling.TilingBasic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

namespace OAI

universe uH uK uι

namespace PeriodicTilingThree

section FiniteStack

variable {H : Type uH} {K : Type uK} {ι : Type uι} [Fintype ι]

def IsColorPartition (E : ι → Finset K) : Prop :=
  ∀ t : K, ∃! ν : ι, t ∈ E ν

def HasFullDifferences [AddGroup K] (E : ι → Finset K) : Prop :=
  ∀ (ν : ι) (d : K), ∃ e ∈ E ν, ∃ e' ∈ E ν, e - e' = d

noncomputable def stack (F : ι → Finset H) (E : ι → Finset K) :
    Finset (H × K) := by
  classical
  exact Finset.univ.biUnion (fun ν => (F ν).product (E ν))

@[simp] theorem mem_stack {F : ι → Finset H} {E : ι → Finset K} {p : H × K} :
    p ∈ stack F E ↔ ∃ ν, p.1 ∈ F ν ∧ p.2 ∈ E ν := by
  classical
  simp [stack]

theorem stack_nonempty [Nonempty ι] {F : ι → Finset H} {E : ι → Finset K}
    (hF : ∀ ν, (F ν).Nonempty) (hE : ∀ ν, (E ν).Nonempty) :
    (stack F E).Nonempty := by
  obtain ⟨ν⟩ := ‹Nonempty ι›
  obtain ⟨f, hf⟩ := hF ν
  obtain ⟨e, he⟩ := hE ν
  exact ⟨(f, e), mem_stack.mpr ⟨ν, hf, he⟩⟩

theorem IsColorPartition.eq_of_mem
    {K : Type uK} {ι : Type uι} [Fintype ι]
    {E : ι → Finset K} (hpart : IsColorPartition E)
    {ν μ : ι} {e : K} (hν : e ∈ E ν) (hμ : e ∈ E μ) : ν = μ := by
  obtain ⟨i, _, hi⟩ := hpart e
  exact (hi ν hν).trans (hi μ hμ).symm

theorem HasFullDifferences.nonempty
    {K : Type uK} {ι : Type uι} [Fintype ι]
    [AddGroup K] {E : ι → Finset K}
    (hfull : HasFullDifferences E) (ν : ι) : (E ν).Nonempty := by
  obtain ⟨e, he, _, _, _⟩ := hfull ν 0
  exact ⟨e, he⟩

theorem card_stack {F : ι → Finset H} {E : ι → Finset K}
    (hpart : IsColorPartition E) :
    (stack F E).card = ∑ ν, (F ν).card * (E ν).card := by
  classical
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun ν => (F ν).product (E ν)) := by
    intro ν _ μ _ hne
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    exact hne (hpart.eq_of_mem (Finset.mem_product.mp hp).2
      (Finset.mem_product.mp hp').2)
  simpa only [stack, Finset.product_eq_sprod, Finset.card_product] using
    Finset.card_biUnion hdisj

theorem IsColorPartition.sum_card [Fintype K] {E : ι → Finset K}
    (hpart : IsColorPartition E) : ∑ ν, (E ν).card = Fintype.card K := by
  classical
  let f : (Σ ν, ↥(E ν)) → K := fun z => z.2.1
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨ν, e⟩ ⟨μ, e'⟩ heq
      change (e : K) = (e' : K) at heq
      have hνμ : ν = μ := hpart.eq_of_mem e.property (heq.symm ▸ e'.property)
      cases hνμ
      have he : e = e' := Subtype.ext heq
      cases he
      rfl
    · intro e
      obtain ⟨ν, hν, _⟩ := hpart e
      exact ⟨⟨ν, ⟨e, hν⟩⟩, rfl⟩
  simpa only [Fintype.card_sigma, Fintype.card_coe] using
    Fintype.card_congr (Equiv.ofBijective f hf)

end FiniteStack

section Contributions

variable {H : Type uH} {K : Type uK} {ι : Type uι} [AddCommGroup H] [AddCommGroup K]
variable [Fintype K] [Fintype ι]

noncomputable def stackContributions (F : ι → Finset H) (B : Set (H × K))
    (g : H) (ν : ι) : Finset (H × K) := by
  classical
  exact ((F ν).product Finset.univ).filter (fun ft => (g - ft.1, ft.2) ∈ B)

@[simp] theorem mem_stackContributions
    {H : Type uH} {K : Type uK} {ι : Type uι}
    [AddCommGroup H] [AddCommGroup K] [Fintype K] [Fintype ι]
    {F : ι → Finset H} {B : Set (H × K)}
    {g : H} {ν : ι} {c : H × K} :
    c ∈ stackContributions F B g ν ↔ c.1 ∈ F ν ∧ (g - c.1, c.2) ∈ B := by
  classical
  simp [stackContributions]

theorem stackContributions_eq_of_mem {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hfull : HasFullDifferences E) (hB : Tiles (stack F E) B)
    {g : H} {ν : ι} {c c' : H × K}
    (hc : c ∈ stackContributions F B g ν)
    (hc' : c' ∈ stackContributions F B g ν) : c = c' := by
  obtain ⟨hcf, hcB⟩ := mem_stackContributions.mp hc
  obtain ⟨hc'f, hc'B⟩ := mem_stackContributions.mp hc'
  obtain ⟨e, he, e', he', hd⟩ := hfull ν (c'.2 - c.2)
  have hvertical : c.2 + e = c'.2 + e' := by
    calc
      c.2 + e = c.2 + (e - e') + e' := by abel
      _ = c.2 + (c'.2 - c.2) + e' := by rw [hd]
      _ = c'.2 + e' := by abel
  let p : ↥(stack F E) × B :=
    (⟨(c.1, e), mem_stack.mpr ⟨ν, hcf, he⟩⟩, ⟨(g - c.1, c.2), hcB⟩)
  let p' : ↥(stack F E) × B :=
    (⟨(c'.1, e'), mem_stack.mpr ⟨ν, hc'f, he'⟩⟩, ⟨(g - c'.1, c'.2), hc'B⟩)
  have hp : p = p' := by
    apply hB.1
    apply Prod.ext
    · change c.1 + (g - c.1) = c'.1 + (g - c'.1)
      simp
    · change e + c.2 = e' + c'.2
      simpa only [add_comm] using hvertical
  apply Prod.ext
  · exact congrArg (fun z : ↥(stack F E) × B => z.1.1.1) hp
  · exact congrArg (fun z : ↥(stack F E) × B => z.2.1.2) hp

theorem stackContributions_card_le_one {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hfull : HasFullDifferences E) (hB : Tiles (stack F E) B)
    (g : H) (ν : ι) : (stackContributions F B g ν).card ≤ 1 := by
  classical
  exact Finset.card_le_one.mpr fun _ hc _ hc' =>
    stackContributions_eq_of_mem hfull hB hc hc'

theorem stack_projection_injective [Nonempty ι]
    {F : ι → Finset H} {E : ι → Finset K} {B : Set (H × K)}
    (hF : ∀ ν, (F ν).Nonempty) (hfull : HasFullDifferences E)
    (hB : Tiles (stack F E) B) : Set.InjOn Prod.fst B := by
  obtain ⟨ν⟩ := ‹Nonempty ι›
  obtain ⟨f, hf⟩ := hF ν
  intro b hb b' hb' heq
  have hc : (f, b.2) ∈ stackContributions F B (b.1 + f) ν := by
    apply mem_stackContributions.mpr
    exact ⟨hf, by simpa using hb⟩
  have hc' : (f, b'.2) ∈ stackContributions F B (b.1 + f) ν := by
    apply mem_stackContributions.mpr
    refine ⟨hf, ?_⟩
    simpa [heq] using hb'
  have ht := congrArg Prod.snd (stackContributions_eq_of_mem hfull hB hc hc')
  exact Prod.ext heq ht

def StackFiber (F : ι → Finset H) (E : ι → Finset K)
    (B : Set (H × K)) (g : H) :=
  Σ ν : ι, ↥(stackContributions F B g ν) × ↥(E ν)

def stackFiberSum {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} {g : H} (z : StackFiber F E B g) : K :=
  z.2.1.1.2 + z.2.2.1

theorem stackFiberSum_bijective {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hpart : IsColorPartition E) (hB : Tiles (stack F E) B)
    (g : H) : Function.Bijective (stackFiberSum (F := F) (E := E) (B := B) (g := g)) := by
  classical
  constructor
  · rintro ⟨ν, c, e⟩ ⟨μ, c', e'⟩ heq
    obtain ⟨hcf, hcB⟩ := mem_stackContributions.mp c.property
    obtain ⟨hc'f, hc'B⟩ := mem_stackContributions.mp c'.property
    let p : ↥(stack F E) × B :=
      (⟨(c.1.1, e.1), mem_stack.mpr ⟨ν, hcf, e.property⟩⟩,
        ⟨(g - c.1.1, c.1.2), hcB⟩)
    let p' : ↥(stack F E) × B :=
      (⟨(c'.1.1, e'.1), mem_stack.mpr ⟨μ, hc'f, e'.property⟩⟩,
        ⟨(g - c'.1.1, c'.1.2), hc'B⟩)
    have hp : p = p' := by
      apply hB.1
      apply Prod.ext
      · change c.1.1 + (g - c.1.1) = c'.1.1 + (g - c'.1.1)
        simp
      · change e.1 + c.1.2 = e'.1 + c'.1.2
        simpa only [stackFiberSum, add_comm] using heq
    have hf : c.1.1 = c'.1.1 :=
      congrArg (fun z : ↥(stack F E) × B => z.1.1.1) hp
    have ht : c.1.2 = c'.1.2 :=
      congrArg (fun z : ↥(stack F E) × B => z.2.1.2) hp
    have he : (e : K) = (e' : K) :=
      congrArg (fun z : ↥(stack F E) × B => z.1.1.2) hp
    have hνμ : ν = μ := hpart.eq_of_mem e.property (he.symm ▸ e'.property)
    cases hνμ
    have hc : c = c' := Subtype.ext (Prod.ext hf ht)
    have he' : e = e' := Subtype.ext he
    cases hc
    cases he'
    rfl
  · intro u
    obtain ⟨p, hp⟩ := hB.2 (g, u)
    obtain ⟨ν, hf, he⟩ := mem_stack.mp p.1.property
    have hhorizontal : p.1.1.1 + p.2.1.1 = g := congrArg Prod.fst hp
    have hcenter : g - p.1.1.1 = p.2.1.1 := by
      rw [← hhorizontal]
      simp
    have hc : (p.1.1.1, p.2.1.2) ∈ stackContributions F B g ν := by
      apply mem_stackContributions.mpr
      exact ⟨hf, by simpa only [hcenter] using p.2.property⟩
    refine ⟨⟨ν, ⟨(p.1.1.1, p.2.1.2), hc⟩, ⟨p.1.1.2, he⟩⟩, ?_⟩
    change p.2.1.2 + p.1.1.2 = u
    have hvertical : p.1.1.2 + p.2.1.2 = u := congrArg Prod.snd hp
    simpa only [add_comm] using hvertical

theorem stackContributions_sum_card {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hpart : IsColorPartition E) (hB : Tiles (stack F E) B)
    (g : H) :
    ∑ ν, (stackContributions F B g ν).card * (E ν).card = Fintype.card K := by
  classical
  let e : (Σ ν : ι, ↥(stackContributions F B g ν) × ↥(E ν)) ≃ K :=
    Equiv.ofBijective (stackFiberSum (F := F) (E := E) (B := B) (g := g))
      (stackFiberSum_bijective hpart hB g)
  simpa only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_coe] using
    Fintype.card_congr e

theorem stackContributions_card_eq_one {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty) (hB : Tiles (stack F E) B)
    (g : H) (ν : ι) : (stackContributions F B g ν).card = 1 := by
  classical
  have hle := stackContributions_card_le_one hfull hB g ν
  by_contra hne
  have hz : (stackContributions F B g ν).card = 0 := by omega
  have hstrict :
      (∑ i, (stackContributions F B g i).card * (E i).card) < ∑ i, (E i).card := by
    apply Finset.sum_lt_sum
    · intro i _
      calc
        (stackContributions F B g i).card * (E i).card ≤ 1 * (E i).card :=
          Nat.mul_le_mul_right _ (stackContributions_card_le_one hfull hB g i)
        _ = (E i).card := one_mul _
    · exact ⟨ν, Finset.mem_univ ν, by simpa only [hz, zero_mul] using (hE ν).card_pos⟩
  rw [stackContributions_sum_card hpart hB g, hpart.sum_card] at hstrict
  exact (lt_irrefl _) hstrict

theorem tiles_of_tiles_stack {F : ι → Finset H} {E : ι → Finset K}
    {B : Set (H × K)} (hpart : IsColorPartition E) (hfull : HasFullDifferences E)
    (hE : ∀ ν, (E ν).Nonempty) (hB : Tiles (stack F E) B) :
    ∀ ν, Tiles (F ν) (Prod.fst '' B) := by
  classical
  intro ν
  apply tiles_iff_unique_tile.mpr
  intro g
  have hcard := stackContributions_card_eq_one hpart hfull hE hB g ν
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < (stackContributions F B g ν).card)
  obtain ⟨hcf, hcB⟩ := mem_stackContributions.mp hc
  refine ⟨⟨c.1, hcf⟩, ⟨(g - c.1, c.2), hcB, rfl⟩, ?_⟩
  intro f hf
  obtain ⟨b, hb, hbf⟩ := hf
  have hc' : ((f : H), b.2) ∈ stackContributions F B g ν := by
    apply mem_stackContributions.mpr
    exact ⟨f.property, by simpa only [← hbf] using hb⟩
  apply Subtype.ext
  exact congrArg Prod.fst (stackContributions_eq_of_mem hfull hB hc' hc)

end Contributions

end PeriodicTilingThree

end OAI
