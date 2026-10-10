import OAI.Analysis.LipschitzHilbert.Phase.AngularBoundary
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-! Finite packet amplitudes for the actual translated angular grid.
The stopping level belongs to the packet, independently of when its
assigned top loses eligibility. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {σ E : Type*} [AddCommMonoid E] [Module ℂ E]

def packetPathProduct (g : AngularGrid) (transition : ℕ → ℤ → ℂ)
    (lower upper : ℕ) (slope : ℝ) : ℂ :=
  ∏ j ∈ Finset.Ico lower upper, transition j (g.index (j + 1) slope)

theorem packetPathProduct_split (g : AngularGrid) (transition : ℕ → ℤ → ℂ)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (slope : ℝ) :
    g.packetPathProduct transition a c slope =
      g.packetPathProduct transition a b slope * g.packetPathProduct transition b c slope :=
  (Finset.prod_Ico_consecutive (fun j => transition j (g.index (j + 1) slope)) hab hbc).symm

theorem packetPathProduct_eq_of_cell (g : AngularGrid) (transition : ℕ → ℤ → ℂ)
    (a b : ℕ) {s t : ℝ} (hcell : g.index b s = g.index b t) :
    g.packetPathProduct transition a b s = g.packetPathProduct transition a b t := by
  unfold packetPathProduct
  apply Finset.prod_congr rfl
  intro j hj
  rw [g.index_eq_of_le (Nat.succ_le_of_lt (Finset.mem_Ico.mp hj).2) hcell]

def packetSet (g : AngularGrid) (packets : Finset σ) (slope : σ → ℝ) (stop : σ → ℕ)
    (level : ℕ) (cell : ℤ) : Finset σ := by
  classical
  exact packets.filter (fun s => g.index level (slope s) = cell ∧ level ≤ stop s)

def packetAmplitude (g : AngularGrid) (packets : Finset σ) (slope : σ → ℝ) (stop : σ → ℕ)
    (base : σ → E) (transition : ℕ → ℤ → ℂ) (level : ℕ) (cell : ℤ) : E :=
  ∑ s ∈ g.packetSet packets slope stop level cell,
    g.packetPathProduct transition level (stop s) (slope s) • base s

def packetResidual (g : AngularGrid) (packets : Finset σ) (slope : σ → ℝ) (stop : σ → ℕ)
    (base : σ → E) (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ) : E := by
  classical
  exact ∑ s ∈ (g.packetSet packets slope stop lower cell).filter (fun s => stop s < upper),
    g.packetPathProduct transition lower (stop s) (slope s) • base s

theorem packetAmplitude_eq_zero_above (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    (level : ℕ) (cell : ℤ) (hlevel : packets.sup stop < level) :
    g.packetAmplitude packets slope stop base transition level cell = 0 := by
  classical
  have hempty : g.packetSet packets slope stop level cell = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨hsp, _, hstop⟩ := Finset.mem_filter.mp hs
    have hsup := Finset.le_sup (f := stop) hsp
    omega
  simp only [packetAmplitude, hempty, Finset.sum_empty]

/-- Splitting at a block endpoint isolates exactly the packets that stop
inside the block. No eligibility mass is substituted for these packets. -/
theorem packetAmplitude_split (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    {lower upper : ℕ} (hlu : lower ≤ upper) (cell : ℤ) :
    g.packetAmplitude packets slope stop base transition lower cell =
      g.packetResidual packets slope stop base transition lower upper cell +
      ∑ s ∈ (g.packetSet packets slope stop lower cell).filter (fun s => upper ≤ stop s),
        g.packetPathProduct transition lower upper (slope s) •
          (g.packetPathProduct transition upper (stop s) (slope s) • base s) := by
  classical
  unfold packetAmplitude packetResidual
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (g.packetSet packets slope stop lower cell) (fun s => stop s < upper)
    (fun s => g.packetPathProduct transition lower (stop s) (slope s) • base s)
  rw [← hsplit]
  congr 1
  simp only [not_lt]
  apply Finset.sum_congr rfl
  intro s hs
  rw [g.packetPathProduct_split transition hlu (Finset.mem_filter.mp hs).2, mul_smul]

/-- The block decomposition of the finite packet amplitude. The cells
are actual descendants of the parent and cover all packets surviving
the block; empty cells contribute zero. -/
theorem packetAmplitude_block (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    {lower upper : ℕ} (hlu : lower ≤ upper) (parent : ℤ)
    (cells : Finset ℤ) (representative : ℤ → ℝ)
    (hcell : ∀ c ∈ cells, g.index upper (representative c) = c)
    (hparent : ∀ c ∈ cells, g.index lower (representative c) = parent)
    (hcover : ∀ s ∈ g.packetSet packets slope stop lower parent,
      upper ≤ stop s → g.index upper (slope s) ∈ cells) :
    g.packetAmplitude packets slope stop base transition lower parent =
      g.packetResidual packets slope stop base transition lower upper parent +
      ∑ c ∈ cells, g.packetPathProduct transition lower upper (representative c) •
        g.packetAmplitude packets slope stop base transition upper c := by
  classical
  rw [g.packetAmplitude_split packets slope stop base transition hlu parent]
  congr 1
  let long := (g.packetSet packets slope stop lower parent).filter (fun s => upper ≤ stop s)
  have hmaps : ∀ s ∈ long, g.index upper (slope s) ∈ cells := fun s hs =>
    hcover s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro c hc
  have hset : long.filter (fun s => g.index upper (slope s) = c) =
      g.packetSet packets slope stop upper c := by
    ext s
    constructor
    · intro hs
      obtain ⟨hs, heq⟩ := Finset.mem_filter.mp hs
      obtain ⟨hs, hstop⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, heq, hstop⟩
    · intro hs
      obtain ⟨hsp, heq, hstop⟩ := Finset.mem_filter.mp hs
      have hancestor := g.index_eq_of_le hlu (heq.trans (hcell c hc).symm)
      rw [hparent c hc] at hancestor
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hsp, hancestor, hlu.trans hstop⟩, hstop⟩, heq⟩
  rw [hset, packetAmplitude, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have heq : g.index upper (slope s) = g.index upper (representative c) :=
    (Finset.mem_filter.mp hs).2.1.trans (hcell c hc).symm
  rw [g.packetPathProduct_eq_of_cell transition lower upper heq]

def packetBlockCells (g : AngularGrid) (packets : Finset σ) (slope : σ → ℝ)
    (stop : σ → ℕ) (lower upper : ℕ) (parent : ℤ) : Finset ℤ := by
  classical
  exact ((g.packetSet packets slope stop lower parent).filter (fun s => upper ≤ stop s)).image
    (fun s => g.index upper (slope s))

def packetBlockRepresentative (g : AngularGrid) (packets : Finset σ) (slope : σ → ℝ)
    (stop : σ → ℕ) (lower upper : ℕ) (parent c : ℤ) : ℝ := by
  classical
  exact if h : c ∈ g.packetBlockCells packets slope stop lower upper parent then
    slope (Finset.mem_image.mp h).choose else 0

theorem packetBlockRepresentative_spec (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (lower upper : ℕ) (parent c : ℤ)
    (hc : c ∈ g.packetBlockCells packets slope stop lower upper parent) :
    g.index upper (g.packetBlockRepresentative packets slope stop lower upper parent c) = c ∧
      g.index lower (g.packetBlockRepresentative packets slope stop lower upper parent c) = parent := by
  classical
  obtain ⟨hs, heq⟩ := (Finset.mem_image.mp hc).choose_spec
  have hs' := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2.1
  simpa only [packetBlockRepresentative, dite_eq_left hc] using And.intro heq hs'

theorem packetAmplitude_canonical_block (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    {lower upper : ℕ} (hlu : lower ≤ upper) (parent : ℤ) :
    g.packetAmplitude packets slope stop base transition lower parent =
      g.packetResidual packets slope stop base transition lower upper parent +
      ∑ c ∈ g.packetBlockCells packets slope stop lower upper parent,
        g.packetPathProduct transition lower upper
            (g.packetBlockRepresentative packets slope stop lower upper parent c) •
          g.packetAmplitude packets slope stop base transition upper c := by
  classical
  apply g.packetAmplitude_block packets slope stop base transition hlu parent
  · exact fun c hc => (g.packetBlockRepresentative_spec packets slope stop lower upper parent c hc).1
  · exact fun c hc => (g.packetBlockRepresentative_spec packets slope stop lower upper parent c hc).2
  · intro s hs hstop
    exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hstop⟩, rfl⟩

end LipschitzHilbert.AngularGrid

end

end OAI
