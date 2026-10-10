import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryGeometry

namespace OAI

/-! One angular boundary loss is controlled by radial eligible masses.
The comparison includes the precision cutoff, including for extra tops. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem boundary_mass_ratio_le_radial (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (base level : ℕ) (gap r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (top : τ) (hrb : r ≤ g.boundaryDistance level (slope top))
    (hR : gap+2*g.width (level+1) < R)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) level) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap (slope top) x /
        g.mass tops slope precision cutoff weight level (g.index level (slope top)) x ≤
      g.nearbyEligibleMass tops slope precision cutoff weight level R (slope top) x /
        g.nearbyEligibleMass tops slope precision cutoff weight level r (slope top) x := by
  let inner := g.nearbyEligibleTops tops slope precision cutoff level r (slope top)
  let outer := g.nearbyEligibleTops tops slope precision cutoff level R (slope top)
  let extra := g.outsideNearTops tops slope precision cutoff base level gap (slope top)
  let n := g.mass tops slope precision cutoff weight level (g.index level (slope top)) x
  let u := ∑ t ∈ inner, weight t x
  let v := ∑ t ∈ outer, weight t x
  let e := ∑ t ∈ extra, weight t x
  have hn : 0 < n := g.path_mass_pos tops slope precision cutoff weight hw level top htop he x
  have htopi : top ∈ inner := Finset.mem_filter.mpr ⟨htop,he,by simpa using hr⟩
  have hu : 0 < u := (hw top x).trans_le (Finset.single_le_sum (fun t _ => (hw t x).le) htopi)
  have hinner := g.nearbyEligibleTops_subset_cell tops slope precision cutoff level r (slope top) hrb
  have hun : u ≤ n := Finset.sum_le_sum_of_subset_of_nonneg hinner (fun t _ _ => (hw t x).le)
  have hextra := g.outsideNearTops_subset_radial tops slope precision cutoff hp base level gap (slope top) R hR
  have hd : Disjoint inner extra := by
    apply Finset.disjoint_left.mpr
    intro t hti hte
    have hsame := ((g.mem_cellTops _ _ _ _ _ _ _).mp (hinner hti)).2.1
    exact (Finset.mem_filter.mp hte).2.2.2 hsame
  have hsum : u+e ≤ v := by
    rw [← Finset.sum_union hd]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.union_subset (g.nearbyEligibleTops_mono tops slope precision cutoff level (slope top) hrR) hextra)
      (fun t _ _ => (hw t x).le)
  have he0 : 0 ≤ e := Finset.sum_nonneg fun t _ => (hw t x).le
  change _/n ≤ v/u
  rw [g.boundary_mass_eq tops slope precision cutoff weight base level gap (slope top) x]
  change (n+e)/n ≤ v/u
  apply (div_le_div_iff₀ hn hu).mpr
  have hm := mul_le_mul_of_nonneg_right hsum hn.le
  have hem := mul_le_mul_of_nonneg_left hun he0
  nlinarith

theorem boundary_log_loss_le_radial (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (base level : ℕ) (gap r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (top : τ) (hrb : r ≤ g.boundaryDistance level (slope top))
    (hR : gap+2*g.width (level+1) < R)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) level) (x : X) :
    Real.log (g.boundaryMass tops slope precision cutoff weight base level gap (slope top) x /
      g.mass tops slope precision cutoff weight level (g.index level (slope top)) x) ≤
    Real.log (g.nearbyEligibleMass tops slope precision cutoff weight level R (slope top) x /
      g.nearbyEligibleMass tops slope precision cutoff weight level r (slope top) x) := by
  have hn := g.path_mass_pos tops slope precision cutoff weight hw level top htop he x
  have hb : 0 < g.boundaryMass tops slope precision cutoff weight base level gap (slope top) x := by
    rw [g.boundary_mass_eq tops slope precision cutoff weight base level gap (slope top) x]
    exact add_pos_of_pos_of_nonneg hn (Finset.sum_nonneg fun t _ => (hw t x).le)
  exact Real.log_le_log (div_pos hb hn)
    (g.boundary_mass_ratio_le_radial tops slope precision cutoff weight hp hw base level gap r R
      hr hrR top hrb hR htop he x)

theorem boundary_mass_eq_parent_of_far (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (base level : ℕ) (gap R s : ℝ)
    (hR : gap+2*g.width (level+1) < R) (hfar : R ≤ g.boundaryDistance level s) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap s x =
      g.mass tops slope precision cutoff weight level (g.index level s) x := by
  have he : g.outsideNearTops tops slope precision cutoff base level gap s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hi := g.outsideNearTops_subset_radial tops slope precision cutoff hp base level gap s R hR ht
    have hs := g.nearbyEligibleTops_subset_cell tops slope precision cutoff level R s hfar hi
    exact (Finset.mem_filter.mp ht).2.2.2 (((g.mem_cellTops _ _ _ _ _ _ _).mp hs).2.1)
  rw [g.boundary_mass_eq tops slope precision cutoff weight base level gap s x,he]
  simp

end LipschitzHilbert.AngularGrid

end

end OAI
