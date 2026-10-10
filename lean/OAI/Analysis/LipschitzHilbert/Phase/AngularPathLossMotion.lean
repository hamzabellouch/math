import OAI.Analysis.LipschitzHilbert.Phase.AngularLossMotion
import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceWeight

namespace OAI

/-! The two logarithmic losses in an actual endpoint increment inherit
relative motion from their concrete child, parent, and boundary top sets. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

/-- Both P_i=log(n_i/n_(i+1)) and R_i=log(m_i/n_(i+1)) have relative
motion at the source averaging scale. The second statement allows the
boundary ancestor to begin before the current block. -/
theorem source_path_loss_motion {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B)
    (hKw : 0 < Kw) (hD : 0 ≤ D) (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ)
    (h i : ℕ) (hhi : h ≤ i) (hgap0 : 0 ≤ gap i) (hgap : gap i ≤ g.width h)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (i+1))
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (a : ℝ) (ha : |a| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ) :
    let weight := fun t x => (T t).weight Kw D x
    let n := fun k x => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight k (g.index k (T top).slope) x
    let m := fun x => g.sourceBoundaryMass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight Kb gap i (g.index (i+1) (T top).slope) x
    let z' := SlopeBox.lineShift sR a z
    let epsilon := Real.exp (2*((5*D/Kw)/Real.sqrt (g.branching:ℝ)))-1
    |Real.log (n i z'/n (i+1) z')-Real.log (n i z/n (i+1) z)| ≤
      epsilon*Real.log (n i z/n (i+1) z) ∧
    |Real.log (m z'/n (i+1) z')-Real.log (m z/n (i+1) z)| ≤
      epsilon*Real.log (m z/n (i+1) z) := by
  classical
  dsimp only
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let weight := fun t x => (T t).weight Kw D x
  let childSet := g.cellTops tops slope precision cutoff (i+1) (g.index (i+1) (T top).slope)
  let parentSet := g.cellTops tops slope precision cutoff i (g.index i (T top).slope)
  let boundarySet := g.boundaryTops tops slope precision cutoff (i+1-Kb) i (gap i) (T top).slope
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hchildSet : childSet.Nonempty := by
    refine ⟨top,?_⟩
    exact (g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩
  have hparent : parentSet ⊆ boundarySet :=
    g.parent_subset_boundary tops slope precision cutoff (i+1-Kb) i (gap i) (T top).slope
  have hchildParent : childSet ⊆ parentSet :=
    g.cellTops_subset_ancestor tops slope precision cutoff hp (Nat.le_succ i) (T top).slope
  have hP := g.source_relative_loss_motion tops T w B Kw D hw hB hKw hD hwidth
    (i+1-Kb) h i hhi (gap i) hgap0 hgap (T top).slope sR hs child hchild hblock
    parentSet childSet hchildParent hchildSet hparent a ha z
  have hR := g.source_relative_loss_motion tops T w B Kw D hw hB hKw hD hwidth
    (i+1-Kb) h i hhi (gap i) hgap0 hgap (T top).slope sR hs child hchild hblock
    boundarySet childSet (hchildParent.trans hparent) hchildSet (Finset.Subset.refl _) a ha z
  constructor
  · simpa only [parentSet, childSet, mass] using hP
  · have hboundary (x : ℝ × ℝ) :
        g.sourceBoundaryMass tops slope precision cutoff weight Kb gap i
          (g.index (i+1) (T top).slope) x = ∑ t ∈ boundarySet, weight t x := by
      rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hKb gap]
      rfl
    dsimp only [slope, precision, cutoff, weight] at hboundary
    simpa only [hboundary, childSet, mass] using hR

end LipschitzHilbert.AngularGrid

end

end OAI
