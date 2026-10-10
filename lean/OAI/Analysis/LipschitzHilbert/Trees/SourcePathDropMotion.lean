import OAI.Analysis.LipschitzHilbert.Trees.SourcePathCoefficientMotion

namespace OAI

/-! The path drop in §9 is comparable throughout the reference cell.
The complement may be empty: relative motion then fixes its zero mass. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem complementary_mass_drop_motion {A B A' B' q : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hq : 0 ≤ q) (hqsmall : q ≤ 1/8)
    (hAmove : |A'-A| ≤ q*A) (hBmove : |B'-B| ≤ q*B) :
    let u := 1-A/(A+B)
    let u' := 1-A'/(A'+B')
    0 ≤ u ∧ |u'-u| ≤ 4*q*u ∧ u/2 ≤ u' ∧ u' ≤ 2*u := by
  dsimp only
  have hden : 0 < A+B := by linarith
  have hr1 : A/(A+B) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hu : 0 ≤ 1-A/(A+B) := by linarith
  obtain ⟨_,_,hm⟩ := complementary_mass_fraction_motion hA hB hq
    (show q ≤ 1/2 by linarith) hAmove hBmove
  have herr : |(1-A'/(A'+B'))-(1-A/(A+B))| ≤ 4*q*(1-A/(A+B)) := by
    calc
      _ = |A'/(A'+B')-A/(A+B)| := by
        rw [show (1-A'/(A'+B'))-(1-A/(A+B)) = -(A'/(A'+B')-A/(A+B)) by ring,abs_neg]
      _ ≤ 4*q*(A/(A+B))*(1-A/(A+B)) := hm
      _ ≤ 4*q*1*(1-A/(A+B)) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr1 (by positivity)) hu
      _ = _ := by ring
  have hsmall : 4*q*(1-A/(A+B)) ≤ (1-A/(A+B))/2 := by
    have hm := mul_le_mul_of_nonneg_right hqsmall hu
    nlinarith
  have habs := abs_le.mp (herr.trans hsmall)
  refine ⟨hu,herr,?_,?_⟩ <;> linarith

namespace AngularGrid

/-- Actual child and complementary top sums give the source's
`pred:drop-comparability`, retaining the exact drop in the error. -/
theorem source_path_drop_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (parentSet childSet : Finset ι) (hsub : childSet ⊆ parentSet) (hne : childSet.Nonempty)
    (hparent : parentSet ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (hsmall : Real.exp ((5*D/K)/Real.sqrt (g.branching:ℝ))*
      ((5*D/K)/Real.sqrt (g.branching:ℝ)) ≤ 1/8) :
    let mass := fun A x => ∑ t ∈ A, (T t).weight K D x
    let u := fun x => 1-mass childSet x/mass parentSet x
    let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
    let q := Real.exp δ*δ
    0 ≤ u z ∧ |u (SlopeBox.lineShift sR b z)-u z| ≤ 4*q*u z ∧
      u z/2 ≤ u (SlopeBox.lineShift sR b z) ∧ u (SlopeBox.lineShift sR b z) ≤ 2*u z := by
  classical
  dsimp only
  let mass := fun (A : Finset ι) x => ∑ t ∈ A, (T t).weight K D x
  let z' := SlopeBox.lineShift sR b z
  let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
  let q := Real.exp δ*δ
  have hpos : 0 < mass childSet z :=
    Finset.sum_pos (fun t _ => (T t).weight_pos hK D z) hne
  have hcomp : 0 ≤ mass (parentSet\childSet) z :=
    Finset.sum_nonneg fun t _ => (T t).weight_pos hK D z |>.le
  have hsplit (x : ℝ × ℝ) : mass parentSet x = mass childSet x+mass (parentSet\childSet) x := by
    have hm := Finset.sum_sdiff (f := fun t => (T t).weight K D x) hsub
    dsimp [mass]
    linarith
  have hmove (A : Finset ι) (hA : A ⊆ parentSet) :
      |mass A z'-mass A z| ≤ q*mass A z :=
    g.source_submass_relative_motion tops T w B K D hw hB hK hD hwidth
      base h i hhi gap hgap0 hgap s sR hs child hchild hblock A (hA.trans hparent) b hb z
  have hresult := complementary_mass_drop_motion hpos hcomp
    (show 0 ≤ q by dsimp [q,δ]; positivity) hsmall
    (hmove childSet hsub) (hmove (parentSet\childSet) Finset.sdiff_subset)
  simpa only [← hsplit z,← hsplit z'] using hresult

end AngularGrid
end LipschitzHilbert

end

end OAI
