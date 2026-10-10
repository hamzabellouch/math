import OAI.Analysis.LipschitzHilbert.Phase.AngularAmplitudeIdentity
import OAI.Analysis.LipschitzHilbert.Phase.AngularGraphMass

namespace OAI

/-! Actual block children are the nonempty eligible-top cells. Their
canonical representatives are slopes of eligible tops, including cells
whose packet amplitude is zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

def sourceBlockCells {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ) : Finset ℤ :=
  ((g.cellTops tops slope precision cutoff lower parent).filter
    (fun t => g.eligible cutoff (precision t) upper)).image (fun t => g.index upper (slope t))

def sourceBlockTop {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) : ι :=
  (Finset.mem_image.mp c.property).choose

theorem sourceBlockTop_spec {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    let t := g.sourceBlockTop tops slope precision cutoff lower upper parent c
    t ∈ tops ∧ g.index lower (slope t) = parent ∧
      g.eligible cutoff (precision t) upper ∧ g.index upper (slope t) = c.val := by
  have h := (Finset.mem_image.mp c.property).choose_spec
  obtain ⟨hc,he⟩ := Finset.mem_filter.mp h.1
  have ht := (g.mem_cellTops tops slope precision cutoff lower parent _).mp hc
  exact ⟨ht.1,ht.2.1,he,h.2⟩

theorem sourceBlockTop_mem_child {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    g.sourceBlockTop tops slope precision cutoff lower upper parent c ∈
      g.cellTops tops slope precision cutoff upper c.val := by
  obtain ⟨ht,_,he,hi⟩ := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent c
  exact (g.mem_cellTops tops slope precision cutoff upper c.val _).mpr ⟨ht,hi,he⟩

theorem sourceBlockCells_nonempty_child {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    (g.cellTops tops slope precision cutoff upper c.val).Nonempty :=
  ⟨_,g.sourceBlockTop_mem_child tops slope precision cutoff lower upper parent c⟩

/-- Every eligible top in the parent selects one of these children. -/
theorem mem_sourceBlockCells_of_top {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hle : lower ≤ upper)
    (top : ι) (htop : top ∈ tops) (hparent : g.index lower (slope top) = parent)
    (he : g.eligible cutoff (precision top) upper) :
    g.index upper (slope top) ∈ g.sourceBlockCells tops slope precision cutoff lower upper parent := by
  apply Finset.mem_image.mpr
  refine ⟨top,Finset.mem_filter.mpr ⟨?_,he⟩,rfl⟩
  exact (g.mem_cellTops tops slope precision cutoff lower parent top).mpr
    ⟨htop,hparent,g.eligible_of_le (hp top htop) hle he⟩

/-- Using the nonempty top children gives the exact packet decomposition.
A child with no surviving packet contributes its actual zero amplitude. -/
theorem sourcePacketAmplitude_block_children {ι σ X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (stop : σ → ℕ) (value : σ → E) (phase : ℕ → ℂ) (a : ℝ) (x : X)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    {lower upper : ℕ} (hle : lower ≤ upper) (parent : ℤ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
      value phase a x lower parent =
    g.packetResidual packets (fun s => slope (assigned s)) stop
      (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x) lower upper parent +
    ∑ c : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
        lower upper (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent c)) •
      g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        value phase a x upper c.val := by
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  let representative := fun c : ℤ =>
    if hc : c ∈ cells then slope (g.sourceBlockTop tops slope precision cutoff lower upper parent ⟨c,hc⟩)
      else 0
  have hrep (c : ℤ) (hc : c ∈ cells) :
      representative c = slope (g.sourceBlockTop tops slope precision cutoff lower upper parent ⟨c,hc⟩) := by
    simp only [representative,dite_eq_left hc]
  have hb := g.packetAmplitude_block packets (fun s => slope (assigned s)) stop
    (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
    (g.sourceTransition tops slope precision cutoff weight K gap phase x) hle parent cells representative
    (fun c hc => by rw [hrep c hc]; exact (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent ⟨c,hc⟩).2.2.2)
    (fun c hc => by rw [hrep c hc]; exact (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent ⟨c,hc⟩).2.1)
    (by
      intro s hs hstop
      obtain ⟨hsp,hi,_⟩ := Finset.mem_filter.mp hs
      exact g.mem_sourceBlockCells_of_top tops slope precision cutoff lower upper parent hp hle
        (assigned s) (hassigned s hsp) hi
        (g.eligible_of_le (hp _ (hassigned s hsp)) hstop (heligible s hsp)))
  change g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
    value phase a x lower parent = _ at hb
  rw [← Finset.sum_coe_sort] at hb
  convert hb using 1
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [hrep c.val c.property]
  rfl

end LipschitzHilbert.AngularGrid

end

end OAI
