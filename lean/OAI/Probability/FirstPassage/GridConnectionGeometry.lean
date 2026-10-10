import OAI.Probability.FirstPassage.GridTrials
import OAI.Probability.FirstPassage.VerticalIntervals

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

noncomputable def transverseIntervalEdges (b : ℝ) (X : ℤ) (lo hi : ℝ) : Finset Edge :=
  verticalIntervalEdges X ⌈lo+b*X⌉ ⌊hi+b*X⌋

lemma transverseIntervalEdges_card_le (b : ℝ) (X : ℤ) (lo hi A : ℝ)
    (hA : 0 ≤ A) (hwidth : hi-lo ≤ A) :
    ((transverseIntervalEdges b X lo hi).card : ℝ) ≤ A := by
  rw [transverseIntervalEdges,verticalIntervalEdges_card]
  by_cases hle : ⌈lo+b*X⌉ ≤ ⌊hi+b*X⌋
  · have he : ((⌊hi+b*X⌋-⌈lo+b*X⌉).toNat : ℝ) = (⌊hi+b*X⌋ : ℝ)-(⌈lo+b*X⌉ : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ ⌊hi+b*X⌋-⌈lo+b*X⌉ by omega)
    rw [he]
    have hl := Int.le_ceil (lo+b*X)
    have hh := Int.floor_le (hi+b*X)
    linarith
  · rw [Int.toNat_eq_zero.mpr (by omega)]
    simpa using hA

lemma transverse_interval_all_pairs (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b : ℝ) (X : ℤ) (lo hi : ℝ) (p q : Vertex)
    (hp : p.1=X ∧ lo ≤ transverse b p ∧ transverse b p ≤ hi)
    (hq : q.1=X ∧ lo ≤ transverse b q ∧ transverse b q ≤ hi) :
    ∃ ds, p+displacement ds=q ∧
      pathCost w p ds ≤ ∑ e ∈ transverseIntervalEdges b X lo hi,w e ∧
      PathIn p ds {z | z.1=X ∧ lo ≤ transverse b z ∧ transverse b z ≤ hi} := by
  have conv (z : Vertex) (hz : z.1=X) :
      (lo ≤ transverse b z ∧ transverse b z ≤ hi) ↔
      (⌈lo+b*X⌉ ≤ z.2 ∧ z.2 ≤ ⌊hi+b*X⌋) := by
    rw [Int.ceil_le,Int.le_floor]
    simp only [transverse,hz]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  obtain ⟨ds,hd,hc,hin⟩ := vertical_interval_all_pairs w hw X ⌈lo+b*X⌉ ⌊hi+b*X⌋ p q
    ⟨hp.1,(conv p hp.1).mp hp.2⟩ ⟨hq.1,(conv q hq.1).mp hq.2⟩
  refine ⟨ds,hd,hc,?_⟩
  intro i hi'
  have hz := hin i hi'
  exact ⟨hz.1,(conv _ hz.1).mpr hz.2⟩

noncomputable def gridIntervalLower (h w : ℤ) : ℝ := (h : ℝ)*w-2
noncomputable def gridIntervalUpper (j : ℕ) (h w : ℤ) : ℝ :=
  (h : ℝ)*w+(30*(j : ℝ)^2+9)*w+2

lemma grid_interval_card (b : ℝ) (X h w : ℤ) (j : ℕ) (hj : 1 ≤ j) (hw : 1 ≤ w) :
    ((transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w)).card : ℝ) ≤
      50*(j : ℝ)^2*w := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hj2 : (1 : ℝ) ≤ (j : ℝ)^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hj2 (show 0 ≤ (w : ℝ) by linarith)
  apply transverseIntervalEdges_card_le _ _ _ _ _ (by positivity)
  unfold gridIntervalLower gridIntervalUpper
  nlinarith

lemma grid_bin_endpoint (j : ℕ) (hj : 1 ≤ j) (h w : ℤ) (hw : 1 ≤ w)
    (r₀ r : ℝ) (hbin : (h : ℝ)*w ≤ r₀ ∧ r₀ ≤ ((h : ℝ)+1)*w)
    (hr : |r-r₀| ≤ 1) : gridIntervalLower h w ≤ r ∧ r ≤ gridIntervalUpper j h w := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hprod : 0 ≤ (30*(j : ℝ)^2+8)*(w : ℝ) := by positivity
  have hh := abs_le.mp hr
  unfold gridIntervalLower gridIntervalUpper
  constructor <;> nlinarith [hbin.1,hbin.2,hh.1,hh.2]

lemma grid_trial_vertex_interval (b : ℝ) (X h w l : ℤ) (j : ℕ) (hw : 1 ≤ w)
    (t : Fin (j^2)) (p : Vertex)
    (hp : p ∈ rareFastRegion b 1 8 w l (gridTrialTranslate b X h w t)) :
    gridIntervalLower h w ≤ transverse b p ∧ transverse b p ≤ gridIntervalUpper j h w := by
  have hf := Int.floor_le (b*X)
  have hf' := Int.lt_floor_add_one (b*X)
  have ht : (t : ℝ)+1 ≤ (j : ℝ)^2 := by exact_mod_cast t.isLt
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hr : |transverse b p-transverse b (gridTrialTranslate b X h w t)| ≤ 8*w := by
    convert hp.2.2 using 1
    simp [transverse]
    congr 1
    ring
  rw [gridTrialTranslate_center] at hr
  have hh := abs_le.mp hr
  have htu := mul_le_mul_of_nonneg_right ht (show 0 ≤ 30*(w : ℝ) by positivity)
  have htl := mul_nonneg ht0 (show 0 ≤ 30*(w : ℝ) by positivity)
  unfold gridIntervalLower gridIntervalUpper
  constructor <;> nlinarith [hh.1,hh.2]

lemma grid_interval_localization (j : ℕ) (hj : 1 ≤ j) (h w : ℤ) (hw : 1 ≤ w)
    (r₀ r : ℝ) (hbin : (h : ℝ)*w ≤ r₀ ∧ r₀ ≤ ((h : ℝ)+1)*w)
    (hr : gridIntervalLower h w ≤ r ∧ r ≤ gridIntervalUpper j h w) :
    |r-r₀| ≤ 50*(j : ℝ)^2*w := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hj2 : (1 : ℝ) ≤ (j : ℝ)^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hj2 (show 0 ≤ (w : ℝ) by linarith)
  unfold gridIntervalLower gridIntervalUpper at hr
  apply abs_le.mpr
  constructor <;> nlinarith [hbin.1,hbin.2,hr.1,hr.2]

theorem grid_bin_connection (weights : Edge → ℝ) (hweights : ∀ e, 0 ≤ weights e)
    (b m K : ℝ) (hK : 0 ≤ K) (X h w l : ℤ) (hl : 0 ≤ l) (j : ℕ)
    (hj : 1 ≤ j) (hw : 1 ≤ w)
    (htrial : ∃ t : Fin (j^2), weights ∈ crossingEvent b m K w l (gridTrialTranslate b X h w t))
    (hleft : (∑ e ∈ transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w),
      weights e) ≤ 100*(j : ℝ)^2*w)
    (hright : (∑ e ∈ transverseIntervalEdges b (X+l) (gridIntervalLower h w) (gridIntervalUpper j h w),
      weights e) ≤ 100*(j : ℝ)^2*w)
    (r₀ : ℝ) (hbin : (h : ℝ)*w ≤ r₀ ∧ r₀ ≤ ((h : ℝ)+1)*w)
    (p q : Vertex) (hp : p.1=X ∧ |transverse b p-r₀| ≤ 1)
    (hq : q.1=X+l ∧ |transverse b q-r₀| ≤ 1) :
    ∃ ds, p+displacement ds=q ∧ pathCost weights p ds ≤ m*l+(K+200)*(j : ℝ)^2*w ∧
      PathIn p ds {z | X-l ≤ z.1 ∧ z.1 ≤ X+2*l ∧
        |transverse b z-r₀| ≤ (K+200)*(j : ℝ)^2*w} := by
  obtain ⟨t,a,ds,hcols,hin,hcost⟩ := htrial
  have ha : a.1=X := hcols.1
  have hz : (a+displacement ds).1=X+l := hcols.2
  have hpath : PathIn a ds (rareFastRegion b 1 8 w l (gridTrialTranslate b X h w t)) := by
    intro i hi
    exact (mem_rareFastVertices ..).mp (hin i hi)
  have hai := grid_trial_vertex_interval b X h w l j hw t a (by simpa using hpath 0 (by omega))
  have hzi := grid_trial_vertex_interval b X h w l j hw t (a+displacement ds)
    (pathIn_endpoint _ _ _ hpath)
  obtain ⟨left,hld,hlcost,hlin⟩ := transverse_interval_all_pairs weights hweights b X
    (gridIntervalLower h w) (gridIntervalUpper j h w) p a
    ⟨hp.1,grid_bin_endpoint j hj h w hw r₀ _ hbin hp.2⟩ ⟨ha,hai⟩
  obtain ⟨right,hrd,hrcost,hrin⟩ := transverse_interval_all_pairs weights hweights b (X+l)
    (gridIntervalLower h w) (gridIntervalUpper j h w) (a+displacement ds) q
    ⟨hz,hzi⟩ ⟨hq.1,grid_bin_endpoint j hj h w hw r₀ _ hbin hq.2⟩
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hj2 : (1 : ℝ) ≤ (j : ℝ)^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hj2 (show 0 ≤ K*(w : ℝ) by positivity)
  have hbound : 50*(j : ℝ)^2*w ≤ (K+200)*(j : ℝ)^2*w := by
    nlinarith [mul_nonneg hK (show 0 ≤ (j : ℝ)^2*(w : ℝ) by positivity)]
  let S : Set Vertex := {z | X-l ≤ z.1 ∧ z.1 ≤ X+2*l ∧
    |transverse b z-r₀| ≤ (K+200)*(j : ℝ)^2*w}
  have hlin' : PathIn p left S := by
    intro i hi
    have hh := hlin i hi
    have hx : (p+displacement (left.take i)).1=X := hh.1
    exact ⟨by omega,by omega,(grid_interval_localization j hj h w hw r₀ _ hbin hh.2).trans hbound⟩
  have hrin' : PathIn (a+displacement ds) right S := by
    intro i hi
    have hh := hrin i hi
    have hx : (a+displacement ds+displacement (right.take i)).1=X+l := hh.1
    exact ⟨by omega,by omega,(grid_interval_localization j hj h w hw r₀ _ hbin hh.2).trans hbound⟩
  have hin' : PathIn a ds S := by
    intro i hi
    have hh := hpath i hi
    have hix := hh.1
    have hix' := hh.2.1
    have hlo : X-l ≤ (a+displacement (ds.take i)).1 := by
      simp only [gridTrialTranslate,Prod.fst_sub,Int.cast_sub] at hix
      exact_mod_cast (show (X : ℝ)-l ≤ ((a+displacement (ds.take i)).1 : ℝ) by linarith)
    have hhi : (a+displacement (ds.take i)).1 ≤ X+2*l := by
      simp only [gridTrialTranslate,Prod.fst_sub,Int.cast_sub] at hix'
      exact_mod_cast (show ((a+displacement (ds.take i)).1 : ℝ) ≤ (X : ℝ)+2*l by linarith)
    exact ⟨hlo,hhi,(grid_interval_localization j hj h w hw r₀ _ hbin
      (grid_trial_vertex_interval b X h w l j hw t _ hh)).trans hbound⟩
  refine ⟨left++ds++right,?_,?_,?_⟩
  · rw [displacement_append,displacement_append,← add_assoc,← add_assoc,hld,hrd]
  · rw [pathCost_append,pathCost_append,hld,displacement_append,← add_assoc,hld]
    linarith
  · apply pathIn_append _ _ _ _ (pathIn_append _ _ _ _ hlin' (by simpa [hld] using hin'))
    simpa [displacement_append,← add_assoc,hld] using hrin'

end PlanarFPP

end OAI
