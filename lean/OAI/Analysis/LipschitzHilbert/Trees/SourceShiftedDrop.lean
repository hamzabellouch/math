import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockModulus
import OAI.Analysis.LipschitzHilbert.Trees.SourcePathDropMotion
import OAI.Analysis.LipschitzHilbert.Trees.PathDrops

namespace OAI

/-! The path mass at shifted block endpoints is set to zero as soon as
the distinguished top becomes ineligible, even if other tops continue.
The actual drop has the same factor-two reference-window comparison,
including this terminal block. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

def shiftedPathMass {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (σ : Fin K) (top : ι) (x : X) (j : ℕ) : ℝ :=
  if g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j) then
    g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x else 0

theorem shiftedPathMass_nonneg {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 ≤ weight t x)
    (σ : Fin K) (top : ι) (x : X) (j : ℕ) :
    0 ≤ g.shiftedPathMass tops slope precision cutoff weight σ top x j := by
  unfold shiftedPathMass
  split_ifs
  · exact Finset.sum_nonneg fun t _ => hw t x
  · exact le_rfl

theorem shiftedPathMass_pos {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 < weight t x)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j)) :
    0 < g.shiftedPathMass tops slope precision cutoff weight σ top x j := by
  rw [shiftedPathMass,ite_eq_left he]
  exact g.path_mass_pos tops slope precision cutoff weight hw _ top htop he x

theorem shiftedPathMass_le_total {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 ≤ weight t x)
    (σ : Fin K) (top : ι) (x : X) (j : ℕ) :
    g.shiftedPathMass tops slope precision cutoff weight σ top x j ≤
      ∑ t ∈ tops, weight t x := by
  unfold shiftedPathMass
  split_ifs
  · exact g.mass_le_total tops slope precision cutoff weight hw _ _ x
  · exact Finset.sum_nonneg fun t _ => hw t x

theorem shiftedPathMass_antitone {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 ≤ weight t x) (hK : 0 < K)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (x : X) :
    Antitone (g.shiftedPathMass tops slope precision cutoff weight σ top x) := by
  intro j k hjk
  have hlevel := (ShiftedBlocks.endpoint_strictMono hK σ).monotone hjk
  by_cases hk : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ k)
  · have hj := g.eligible_of_le (hp top htop) hlevel hk
    rw [shiftedPathMass,ite_eq_left hk,shiftedPathMass,ite_eq_left hj]
    exact g.path_mass_antitone tops slope precision cutoff weight hp hw top x hlevel
  · rw [shiftedPathMass,ite_eq_right hk]
    exact g.shiftedPathMass_nonneg tops slope precision cutoff weight hw σ top x j

theorem shiftedPathDrop_terminal {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 < weight t x)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j))
    (hnext : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))) :
    pathDrop (g.shiftedPathMass tops slope precision cutoff weight σ top x) j = 1 := by
  have hpos := g.shiftedPathMass_pos tops slope precision cutoff weight hw σ top htop x j he
  have hzero : g.shiftedPathMass tops slope precision cutoff weight σ top x (j+1) = 0 := by
    rw [shiftedPathMass,ite_eq_right hnext]
  unfold pathDrop
  rw [hzero,sub_zero,div_self hpos.ne']

/-- Exact shifted source blocks satisfy the drop comparison used in the
stopped error budget. A final block with no eligible path child has drop
one at both endpoints and needs no fictitious child top. -/
theorem source_shifted_path_drop_motion {ι : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (ShiftedBlocks.endpoint σ j))
    (h : ℕ) (hbase : h ≤ ShiftedBlocks.endpoint σ j)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (hblock : g.width h ≤ B*g.width (ShiftedBlocks.endpoint σ (j+1)))
    (b : ℝ) (hb : |b| ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)))
    (z : ℝ × ℝ)
    (hsmall : Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*
      ((5*D/Kw)/Real.sqrt (g.branching:ℝ)) ≤ 1/8) :
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) (fun t x => (T t).weight Kw D x) σ top x
    let u := fun x => pathDrop (n x) j
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    let z' := SlopeBox.lineShift sR b z
    0 ≤ u z ∧ |u z'-u z| ≤ 4*(Real.exp δ*δ)*u z ∧
      u z/2 ≤ u z' ∧ u z' ≤ 2*u z := by
  classical
  dsimp only
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff := g.rootWidth/B^2
  let weight := fun t x => (T t).weight Kw D x
  let n := fun x => g.shiftedPathMass tops slope precision cutoff weight σ top x
  let lo := ShiftedBlocks.endpoint σ j
  let hi := ShiftedBlocks.endpoint σ (j+1)
  let u := fun x => pathDrop (n x) j
  let z' := SlopeBox.lineShift sR b z
  let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hwpos (t : ι) (x : ℝ × ℝ) : 0 < weight t x := (T t).weight_pos hKw D x
  by_cases hnext : g.eligible cutoff (precision top) hi
  · let parent := g.cellTops tops slope precision cutoff lo (g.index lo (slope top))
    let child := g.cellTops tops slope precision cutoff hi (g.index hi (slope top))
    have hlevel : lo ≤ hi := (ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_succ j)
    have hsub : child ⊆ parent := g.cellTops_subset_ancestor tops slope precision cutoff hp hlevel _
    have hne : child.Nonempty :=
      ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,hnext⟩⟩
    have hdrop (x : ℝ × ℝ) : u x =
        1-(∑ t ∈ child, weight t x)/(∑ t ∈ parent, weight t x) := by
      have hpos := g.path_mass_pos tops slope precision cutoff weight hwpos lo top htop he x
      have he0 : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j) := he
      have he1 : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1)) := hnext
      change (n x j-n x (j+1))/n x j = _
      simp only [n,shiftedPathMass,he0,he1,ite_true]
      rw [sub_div,div_self hpos.ne']
      rfl
    have hresult := g.source_path_drop_motion tops T w B Kw D hw hB hKw hD hwidth
      0 h lo hbase 0 (by norm_num) (g.width_pos h).le (slope top) sR hs
      (g.width hi) (g.width_pos hi) hblock parent child hsub hne
      (g.parent_subset_boundary tops slope precision cutoff 0 lo 0 (slope top)) b hb z hsmall
    change 0 ≤ u z ∧ |u z'-u z| ≤ 4*(Real.exp δ*δ)*u z ∧ u z/2 ≤ u z' ∧ u z' ≤ 2*u z
    simpa only [hdrop] using hresult
  · have hterminal (x : ℝ × ℝ) : u x = 1 :=
      g.shiftedPathDrop_terminal tops slope precision cutoff weight hwpos σ top htop x j he hnext
    change 0 ≤ u z ∧ |u z'-u z| ≤ 4*(Real.exp δ*δ)*u z ∧ u z/2 ≤ u z' ∧ u z' ≤ 2*u z
    rw [hterminal z,hterminal z']
    have hδ : 0 ≤ δ := by dsimp [δ]; positivity
    have hq : 0 ≤ Real.exp δ*δ := mul_nonneg (Real.exp_pos _).le hδ
    refine ⟨by norm_num,?_,by norm_num,by norm_num⟩
    simpa only [sub_self,abs_zero,mul_one] using
      mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hq

end LipschitzHilbert.AngularGrid

end

end OAI
