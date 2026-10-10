import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftedDrop
import OAI.Analysis.LipschitzHilbert.Phase.AngularStopping

namespace OAI

/-! The actual finite mass stopping index. A terminal ineligible top has
zero path mass, so the source cutoff is attained without a positive lower
bound on any individual top weight. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def firstMassStop (n : ℕ → ℝ) (count : ℕ) (M : ℝ) : ℕ :=
  if h : ∃ j : ℕ, j ≤ count ∧ n j ≤ M then Nat.find h else count

theorem firstMassStop_spec (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) :
    firstMassStop n count M ≤ count ∧ n (firstMassStop n count M) ≤ M ∧
      ∀ j < firstMassStop n count M, M < n j := by
  have hex : ∃ j : ℕ, j ≤ count ∧ n j ≤ M := ⟨count,le_rfl,hlast⟩
  rw [firstMassStop,dite_eq_left hex]
  refine ⟨(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
  intro j hj
  have hn := Nat.find_min hex hj
  have hcount := (Nat.le_of_lt hj).trans (Nat.find_spec hex).1
  exact lt_of_not_ge fun h => hn ⟨hcount,h⟩

theorem firstMassStop_after (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) (hanti : Antitone n) {j : ℕ}
    (hj : firstMassStop n count M ≤ j) : n j ≤ M :=
  (hanti hj).trans (firstMassStop_spec n count M hlast).2.1

theorem firstMassStop_active_iff (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) (hanti : Antitone n) (j : ℕ) :
    j < firstMassStop n count M ↔ M < n j := by
  constructor
  · exact (firstMassStop_spec n count M hlast).2.2 j
  · intro hj
    by_contra hn
    exact (not_lt_of_ge (firstMassStop_after n count M hlast hanti (Nat.le_of_not_gt hn))) hj

/-- Measurability follows from the actual active-mass events, so the
source stopping indicator can be inserted into its packet factors. -/
theorem measurable_firstMassStop {X : Type*} [MeasurableSpace X]
    (n : X → ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hn : ∀ j, Measurable (fun x => n x j))
    (hlast : ∀ x, n x count ≤ M) (hanti : ∀ x, Antitone (n x)) :
    Measurable (fun x => firstMassStop (n x) count M) := by
  apply measurable_of_Ioi
  intro j
  have hs : (fun x => firstMassStop (n x) count M) ⁻¹' Ioi j = {x | M < n x j} := by
    ext x
    exact firstMassStop_active_iff (n x) count M (hlast x) (hanti x) j
  rw [hs]
  exact measurableSet_lt measurable_const (hn j)

namespace AngularGrid

theorem measurable_shiftedPathMass {ι X : Type*} [MeasurableSpace X] {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t, Measurable (weight t))
    (σ : Fin K) (top : ι) (j : ℕ) :
    Measurable (fun x => g.shiftedPathMass tops slope precision cutoff weight σ top x j) := by
  classical
  unfold shiftedPathMass
  split_ifs
  · exact Finset.measurable_sum _ (fun t _ => hw t)
  · exact measurable_const

theorem shiftedPathMass_terminal_zero {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (σ : Fin K) (top : ι) (count : ℕ)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ count))
    (x : X) : g.shiftedPathMass tops slope precision cutoff weight σ top x count = 0 := by
  rw [shiftedPathMass,ite_eq_right hterminal]

/-- One common finite terminal generation works for every point: the
chosen top has become ineligible there, independently of its weight. -/
theorem exists_shifted_terminal {K : ℕ} (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hK : 0 < K) (σ : Fin K) :
    ∃ count : ℕ, ¬g.eligible cutoff precision (ShiftedBlocks.endpoint σ count) := by
  obtain ⟨count,hcount⟩ := g.exists_ineligible cutoff precision hp
  refine ⟨count,fun he => hcount (g.eligible_of_le hp.le ?_ he)⟩
  have h := (ShiftedBlocks.endpoint_strictMono hK σ).id_le count
  exact h

/-- The source stopped mass path is an initial segment of the original
angular path. The final mass may vanish, and all later masses are at most M. -/
theorem shifted_mass_stopping {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 ≤ weight t x) (hK : 0 < K)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (count : ℕ)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ count))
    (M : ℝ) (hM : 0 ≤ M) (x : X) :
    let n := g.shiftedPathMass tops slope precision cutoff weight σ top x
    let stop := firstMassStop n count M
    stop ≤ count ∧ (∀ j < stop, M < n j) ∧ 0 ≤ n stop ∧ n stop ≤ M ∧
      (∀ j, j < stop ↔ M < n j) ∧ ∀ j, stop ≤ j → n j ≤ M := by
  dsimp only
  let n := g.shiftedPathMass tops slope precision cutoff weight σ top x
  have hnlast : n count ≤ M := by
    rw [show n count = 0 from g.shiftedPathMass_terminal_zero tops slope precision cutoff
      weight σ top count hterminal x]
    exact hM
  have hanti : Antitone n :=
    g.shiftedPathMass_antitone tops slope precision cutoff weight hp hw hK σ top htop x
  have hs := firstMassStop_spec n count M hnlast
  exact ⟨hs.1,hs.2.2,
    g.shiftedPathMass_nonneg tops slope precision cutoff weight hw σ top x _,hs.2.1,
    firstMassStop_active_iff n count M hnlast hanti,
    fun j hj => firstMassStop_after n count M hnlast hanti hj⟩

theorem measurable_shiftedMassStop {ι X : Type*} [MeasurableSpace X] {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 ≤ weight t x) (hmeas : ∀ t, Measurable (weight t))
    (hK : 0 < K) (σ : Fin K) (top : ι) (htop : top ∈ tops) (count : ℕ)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ count))
    (M : ℝ) (hM : 0 ≤ M) :
    Measurable (fun x => firstMassStop
      (g.shiftedPathMass tops slope precision cutoff weight σ top x) count M) := by
  apply measurable_firstMassStop _ count M
    (fun j => g.measurable_shiftedPathMass tops slope precision cutoff weight hmeas σ top j)
  · intro x
    rw [g.shiftedPathMass_terminal_zero tops slope precision cutoff weight σ top count hterminal x]
    exact hM
  · intro x
    exact g.shiftedPathMass_antitone tops slope precision cutoff weight hp hw hK σ top htop x

end AngularGrid
end LipschitzHilbert

end

end OAI
