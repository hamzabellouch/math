import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularSupport
import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularScales

namespace OAI

/-! All graph hypotheses for the source predictor are supplied by the actual
angular cells, top masses and common separated-top count. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

/-- Geometric data for a nonempty block, using exactly its eligible tops.
The counting conclusion concerns only the shrunken support and the path. -/
theorem source_angular_prediction_data {ι κ : Type} [DecidableEq ι] [Fintype κ]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox) (d : ι → ℝ)
    (cutoff : ℝ) (weight : ι → (ℝ × ℝ) → ℝ)
    (hd : ∀ i ∈ tops, 0 ≤ d i) (hw : ∀ i z, 0 < weight i z)
    (z : ℝ × ℝ) (base level : ℕ) (hle : base ≤ level) (parent : ℤ)
    (cells : Finset ℤ) (representative : cells → ℝ)
    (hcell : ∀ c, g.index (level+1) (representative c) = c.val)
    (hancestor : ∀ c, g.index base (representative c) = parent)
    (hnonempty : ∀ c : cells,
      (g.cellTops tops (fun i => (T i).slope) d cutoff (level+1) c.val).Nonempty)
    (path : cells) (A : cells → EuclideanSpace ℂ κ)
    {gap B K D ε threshold etaMin sR : ℝ}
    (hgap : 0 < gap) (hD : 2 ≤ D) (hε : 0 ≤ ε)
    (hprecision : cutoff/(g.branching:ℝ)^(level+1) ≤ gap/B^2)
    (hspan : g.width base ≤ B*gap)
    (hsmall : ∀ c : cells,
      (∀ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff (level+1) c.val,
        K < (T i).radius z) →
      ‖A c‖ ≤ 2*ε*g.mass tops (fun i => (T i).slope) d cutoff weight (level+1) c.val z)
    (hcount : ∀ I : Finset ι, I ⊆ tops →
      (∀ i ∈ I, (T i).radius z ≤ K) →
      (∀ i ∈ I, d i ≤ gap/B^2) →
      (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ B*gap) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → gap ≤ |(T i).slope-(T j).slope|) →
      (I.card:ℝ) ≤ D/100)
    (eta : κ → ℝ) (hetaMin : 0 ≤ etaMin) (heta : ∀ k, etaMin ≤ |eta k|)
    (hthreshold : threshold ≤ gap*etaMin) :
    let c := fun j : cells => g.mass tops (fun i => (T i).slope) d cutoff weight (level+1) j.val z
    let n := g.mass tops (fun i => (T i).slope) d cutoff weight base parent z
    let m := fun j : cells => g.boundaryMass tops (fun i => (T i).slope) d cutoff weight
      base level gap (representative j) z
    let G := fun i j : cells => g.neighbors (level+1) gap i.val j.val
    let f := fun j k => (sR-g.center (level+1) j.val)*eta k
    (∀ j, 0 < c j) ∧ 0 < n ∧ (∑ j, c j/n) ≤ 1 ∧
      (∀ j, orderMass c (closedNeighborhood G j) ≤ m j) ∧
      (∀ i j, i ≠ j → ¬G i j → ∀ k, threshold ≤ |f i k-f j k|) ∧
      (∀ S : Finset cells, (∀ j ∈ S, radialShrink (2*ε*c j) (A j) ≠ 0 ∨ j = path) →
        (S:Set cells).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) := by
  classical
  dsimp only
  let c := fun j : cells => g.mass tops (fun i => (T i).slope) d cutoff weight (level+1) j.val z
  let n := g.mass tops (fun i => (T i).slope) d cutoff weight base parent z
  have hsub (j : ℤ) (hj : j ∈ cells) :
      g.cellTops tops (fun i => (T i).slope) d cutoff (level+1) j ⊆
        g.cellTops tops (fun i => (T i).slope) d cutoff base parent := by
    have h := g.cellTops_subset_ancestor tops (fun i => (T i).slope) d cutoff hd
      (hle.trans (Nat.le_succ _)) (representative ⟨j,hj⟩)
    simpa only [hcell,hancestor] using h
  have hc (j : cells) : 0 < c j := by
    obtain ⟨i,hi⟩ := hnonempty j
    exact g.mass_pos_of_member tops (fun i => (T i).slope) d cutoff weight hw
      (level+1) j.val z hi
  have hn : 0 < n := by
    obtain ⟨i,hi⟩ := hnonempty path
    exact g.mass_pos_of_member tops (fun i => (T i).slope) d cutoff weight hw
      base parent z (hsub path.val path.property hi)
  have htotal : (∑ j : cells, c j/n) ≤ 1 := by
    rw [← Finset.sum_div,div_le_one hn]
    have h := g.sum_cell_mass_le_ancestor tops (fun i => (T i).slope) d cutoff weight
      (fun i z => (hw i z).le) base (level+1) parent cells hsub z
    change (∑ j : cells, g.mass tops (fun i => (T i).slope) d cutoff weight
      (level+1) j.val z) ≤ n
    rw [Finset.sum_subtype cells (p := fun j => j ∈ cells) (by simp)] at h
    exact h
  refine ⟨hc,hn,htotal,?_,?_,?_⟩
  · intro j
    exact g.closed_neighborhood_mass_le_boundary tops (fun i => (T i).slope)
      d cutoff weight hd (fun i z => (hw i z).le) hle hgap.le cells representative parent
      hcell hancestor j z
  · intro i j _ hfar k
    exact hthreshold.trans (g.carrier_frequency_separated (level+1) hetaMin (heta k) hfar)
  · let X := fun j => if j = path then A j else radialShrink (2*ε*c j) (A j)
    have hsig := g.supported_shrink_significant tops T d z cutoff (level+1) cells A c path
      hε (fun j => (hc j).le) hsmall
    intro S hsupport hind
    apply g.supported_snapshot_independence tops T d z cutoff base level parent cells
      representative hcell hancestor hd hle X path hD hprecision hspan hsig hcount S _ hind
    intro j hj
    rcases hsupport j hj with ha | he
    · by_cases he : j = path
      · exact Or.inr he
      · exact Or.inl (by simpa only [X,ite_eq_right he] using ha)
    · exact Or.inr he

end LipschitzHilbert.AngularGrid

end

end OAI
