import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionMotion
import OAI.Analysis.LipschitzHilbert.Trees.PathCoefficient

namespace OAI

/-! The dominant path coefficient from actual complementary top masses.
Empty complementary sets contribute zero and retain the path-drop factor. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

theorem source_submass_relative_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (A : Finset ι) (hA : A ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ) :
    let mass := fun x => ∑ t ∈ A, (T t).weight K D x
    let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
    |mass (SlopeBox.lineShift sR b z)-mass z| ≤ Real.exp δ*δ*mass z := by
  classical
  dsimp only
  by_cases hne : A.Nonempty
  · have hm := g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
      base h i hhi gap hgap0 hgap s sR hs child hchild hblock A hne hA b hb z
    have hp (x : ℝ × ℝ) : 0 < ∑ t ∈ A, (T t).weight K D x :=
      Finset.sum_pos (fun t _ => (T t).weight_pos hK D x) hne
    have hrel := massPowerScale_relative_motion (hp z) (hp (SlopeBox.lineShift sR b z))
      (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
      (show 0 ≤ (5*D/K)/Real.sqrt (g.branching:ℝ) by positivity)
      hm (by simp; positivity) 1 0
    simp only [massPowerScale,Real.rpow_one,Real.rpow_zero,mul_one,one_mul,
      abs_one,abs_zero,add_zero] at hrel
    exact positive_relative_motion_to_sub (hp z) hrel
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.sum_empty,sub_self,abs_zero,mul_zero,le_refl]

/-- The two complements are actual finite top sums. The parent drop
alone controls the coefficient drop and its motion. -/
theorem source_path_coefficient_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (parentSet boundarySet childSet : Finset ι)
    (hchildBoundary : childSet ⊆ boundarySet) (hboundaryParent : boundarySet ⊆ parentSet)
    (hne : childSet.Nonempty)
    (hparent : parentSet ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (a e u : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hsmall : Real.exp ((5*D/K)/Real.sqrt (g.branching:ℝ))*
      ((5*D/K)/Real.sqrt (g.branching:ℝ)) ≤ 1/2) :
    let mass := fun A x => ∑ t ∈ A, (T t).weight K D x
    let C := fun x => pathCoefficient a e
      (mass childSet x/mass parentSet x) (mass childSet x/mass boundarySet x)
    let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
    let q := Real.exp δ*δ
    1-mass childSet z/mass parentSet z ≤ u →
    0 < C z ∧ C z ≤ 1 ∧ 1-C z ≤ 2*u ∧
      0 < C (SlopeBox.lineShift sR b z) ∧ C (SlopeBox.lineShift sR b z) ≤ 1 ∧
      |C (SlopeBox.lineShift sR b z)-C z| ≤ 24*q*u := by
  classical
  dsimp only
  intro hdrop
  let mass := fun (A : Finset ι) x => ∑ t ∈ A, (T t).weight K D x
  let z' := SlopeBox.lineShift sR b z
  let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
  let q := Real.exp δ*δ
  have hq : 0 ≤ q := by dsimp [q,δ]; positivity
  have hchildParent : childSet ⊆ parentSet := hchildBoundary.trans hboundaryParent
  have hpos : 0 < mass childSet z :=
    Finset.sum_pos (fun t _ => (T t).weight_pos hK D z) hne
  have hboundaryPos : 0 < mass boundarySet z :=
    Finset.sum_pos (fun t _ => (T t).weight_pos hK D z) (hne.mono hchildBoundary)
  have hboundaryLe : mass boundarySet z ≤ mass parentSet z := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hboundaryParent
      (fun t _ _ => (T t).weight_pos hK D z |>.le)
  have hsplit (A : Finset ι) (hA : childSet ⊆ A) (x : ℝ × ℝ) :
      mass A x = mass childSet x+mass (A\childSet) x := by
    have hsum := Finset.sum_sdiff (f := fun t => (T t).weight K D x) hA
    dsimp [mass]
    linarith
  have hrelative (A : Finset ι) (hA : A ⊆ parentSet) :
      |mass A z'-mass A z| ≤ q*mass A z :=
    g.source_submass_relative_motion tops T w B K D hw hB hK hD hwidth
      base h i hhi gap hgap0 hgap s sR hs child hchild hblock A (hA.trans hparent) b hb z
  have hdropBoundary : 1-mass childSet z/(mass childSet z+mass (boundarySet\childSet) z) ≤ u := by
    rw [← hsplit boundarySet hchildBoundary]
    exact (sub_le_sub_left
      (div_le_div_of_nonneg_left hpos.le hboundaryPos hboundaryLe) 1).trans hdrop
  have hdropParent : 1-mass childSet z/(mass childSet z+mass (parentSet\childSet) z) ≤ u := by
    rw [← hsplit parentSet hchildParent]
    exact hdrop
  have hresult := pathCoefficient_from_complementary_masses ha0 ha1 he0 he1 hpos
    (show 0 ≤ mass (parentSet\childSet) z from Finset.sum_nonneg
      (fun t _ => (T t).weight_pos hK D z |>.le))
    (show 0 ≤ mass (boundarySet\childSet) z from Finset.sum_nonneg
      (fun t _ => (T t).weight_pos hK D z |>.le)) hq hsmall
    (hrelative childSet hchildParent)
    (hrelative (parentSet\childSet) Finset.sdiff_subset)
    (hrelative (boundarySet\childSet) (Finset.sdiff_subset.trans hboundaryParent))
    hdropParent hdropBoundary
  simpa only [← hsplit parentSet hchildParent z,← hsplit parentSet hchildParent z',
    ← hsplit boundarySet hchildBoundary z,← hsplit boundarySet hchildBoundary z'] using hresult

end LipschitzHilbert.AngularGrid

end

end OAI
