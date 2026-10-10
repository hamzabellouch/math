import OAI.Analysis.AncientFlat.Geometry.InteriorCutoff
import OAI.Analysis.AncientFlat.Evolution.TraceFour

namespace OAI
noncomputable section
open Set Filter Metric
open scoped ContDiff ZeroAtInfty Laplacian
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [FiniteDimensional ℝ V] in
lemma HolderBound.of_jet_zero {α K : ℝ} {Ω : Set (V × ℝ)} (u : ℝ → V → E)
    (h : HolderBound α Ω (fun p => iteratedFDeriv ℝ 0 (u p.2) p.1) K) :
    HolderBound α Ω (fun p => u p.2 p.1) K := by
  refine ⟨fun p hp => by simpa only [norm_iteratedFDeriv_zero] using h.1 p hp,?_⟩
  intro p hp q hq
  have hh := h.2 p hp q hq
  dsimp only at hh
  simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,LinearIsometryEquiv.norm_map] using hh
lemma cutoff_support (t : ℝ) : tsupport (cutoff t : V → ℝ)⊆closedBall 0 (3/2) := by
  have h := tsupport_smul_subset_right (fun _ : V => baseBump ℝ t) (baseBump V)
  change tsupport (cutoff t : V → ℝ) ⊆ tsupport (baseBump V) at h
  rw [(baseBump V).tsupport_eq] at h
  exact h
lemma cutoff_product_support (t : ℝ) (u : V → E) :
    tsupport (fun x => cutoff t x • u x)⊆closedBall 0 (3/2) :=
  (tsupport_smul_subset_left (cutoff t) u).trans (cutoff_support t)
lemma cutoff_product_jet_zero (n : ℕ) (t : ℝ) (u : V → E) (x : V) (hx : 7/4≤‖x‖) :
    iteratedFDeriv ℝ n (fun y => cutoff t y • u y) x=0 := by
  apply Function.notMem_support.mp
  intro h
  have hh := cutoff_product_support t u (support_iteratedFDeriv_subset n h)
  simp only [mem_closedBall,dist_zero_right] at hh
  linarith
lemma cutoff_product_compact (t : ℝ) (u : V → E) :
    HasCompactSupport (fun x => cutoff t x • u x) :=
  (cutoff_compact t).smul_right
lemma cutoff_time_zero (t : ℝ) (x : V) (hx : 3/2≤‖x‖) : cutoffTime t x=0 := by
  unfold cutoffTime
  rw [(baseBump V).zero_of_le_dist (by simpa only [baseBump,dist_zero_right] using hx),mul_zero]
lemma cutoff_time_compact (t : ℝ) : HasCompactSupport (cutoffTime t : V → ℝ) :=
  (baseBump V).hasCompactSupport.mul_left
def cutoffValue (u : ℝ → V → E) (t : ℝ) (x : V) : E := cutoff t x • u t x
def cutoffDerivative (u ut : ℝ → V → E) (t : ℝ) (x : V) : E :=
  cutoff t x • ut t x+cutoffTime t x • u t x
lemma cutoffDerivative_compact (u ut : ℝ → V → E) (t : ℝ) :
    HasCompactSupport (cutoffDerivative u ut t) := by
  have h1 : HasCompactSupport (fun x => cutoff t x • ut t x) := cutoff_product_compact t _
  have h2 : HasCompactSupport (fun x => cutoffTime t x • u t x) := (cutoff_time_compact t).smul_right
  exact h1.add h2
lemma cutoffDerivative_zero (u ut : ℝ → V → E) (t : ℝ) (x : V) (hx : 3/2≤‖x‖) :
    cutoffDerivative u ut t x=0 := by
  simp only [cutoffDerivative,cutoff_zero_space t hx,cutoff_time_zero t x hx,zero_smul,add_zero]
lemma cutoffValue_contDiff (u : ℝ → V → E) (t : ℝ) (hs : ContDiff ℝ 4 (u t)) :
    ContDiff ℝ 4 (cutoffValue u t) :=
  ((cutoff_contDiff t).of_le (by change ((4:ℕ∞):WithTop ℕ∞)≤((⊤:ℕ∞):WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top)).smul hs
def cutoffC0 (u : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t)) (t : ℝ) : C₀(V,ℂ) :=
  ⟨⟨cutoffValue u t,(cutoffValue_contDiff u t (hs t)).continuous⟩,
    (cutoff_product_compact t (u t)).is_zero_at_infty⟩
@[simp] lemma cutoffC0_apply (u : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t)) (t : ℝ) (x : V) :
    cutoffC0 u hs t x=cutoffValue u t x := rfl
lemma cutoffValue_pointwise_derivative (u ut : ℝ → V → E)
    (hd : ∀ p∈cylinder 2, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2)
    (t : ℝ) (ht : t∈Ioo (-2) 0) (x : V) :
    HasDerivAt (fun s => cutoffValue u s x) (cutoffDerivative u ut t x) t := by
  by_cases hx : ‖x‖<2
  · have hz : (x,t)∈cylinder 2 := by unfold cylinder; dsimp; norm_num; exact ⟨hx,by linarith [ht.1],ht.2.le⟩
    simpa only [cutoffValue,cutoffDerivative] using (cutoff_hasDerivAt t x).fun_smul (hd (x,t) hz)
  · have hx' : 3/2≤‖x‖ := by linarith [le_of_not_gt hx]
    have he : (fun s => cutoffValue u s x)=fun _ => (0:E) := by
      funext s; simp only [cutoffValue,cutoff_zero_space s hx',zero_smul]
    rw [he,cutoffDerivative_zero u ut t x hx']
    exact hasDerivAt_const t 0
end ParabolicLocalization

end

end OAI
