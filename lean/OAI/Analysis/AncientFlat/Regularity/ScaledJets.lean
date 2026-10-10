import OAI.Analysis.AncientFlat.Evolution.GeneralWindows
import OAI.Analysis.AncientFlat.Weighted.WeightedScaling

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace FlatWeighted
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
def scaleU (w r : ℝ) (u : ℝ → V → ℂ) : ℝ → V → ℂ :=
  fun t x => r^(-w) • windowValue 0 r u t x
def scaleUT (w r : ℝ) (ut : ℝ → V → ℂ) : ℝ → V → ℂ :=
  fun t x => r^(-w) • windowTime 0 r ut t x
lemma window_zero_eq_scale (r : ℝ) (p : V × ℝ) : window 0 r p=scale r p := by simp [window,scale]
lemma scaleU_apply (w r : ℝ) (u : ℝ → V → ℂ) (p : V × ℝ) :
    scaleU w r u p.2 p.1=r^(-w) • u (scale r p).2 (scale r p).1 := by simp [scaleU,windowValue,scale]
lemma scaleUT_apply (w r : ℝ) (ut : ℝ → V → ℂ) (p : V × ℝ) :
    scaleUT w r ut p.2 p.1=(r^(-w)*r^4) • ut (scale r p).2 (scale r p).1 := by simp [scaleUT,windowTime,scale,mul_assoc]
lemma scaleU_contDiff (w r : ℝ) (u : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t)) (t : ℝ) :
    ContDiff ℝ 4 (scaleU w r u t) :=
  (windowValue_contDiff 0 r u hs t).const_smul _
lemma scaled_jet_bound {α w M r : ℝ} {Ω S : Set (V × ℝ)}
    (hr : 0<r) (hM : 0≤M) (u ut : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t))
    (hj : JetBound α Ω u ut M) (hm : MapsTo (scale r) S Ω) :
    JetBound α S (scaleU w r u) (scaleUT w r ut) (r^(-w)*((1+r^4)*(1+r^α)*M)) := by
  have hw := window_jet_bound_general hM hr (0:V × ℝ) u ut hs hj (fun p hp => by rw [window_zero_eq_scale]; exact hm hp)
  have hh := hw.const_smul (windowValue_contDiff 0 r u hs) (r^(-w))
  unfold scaleU scaleUT
  rw [abs_of_pos (Real.rpow_pos_of_pos hr _)] at hh
  exact hh
lemma LocallyFiniteJets.scale {α w r : ℝ} {u ut : ℝ → V → ℂ}
    (h : LocallyFiniteJets α u ut) (hr : 0<r) (hs : ∀ t, ContDiff ℝ 4 (u t)) :
    LocallyFiniteJets α (scaleU w r u) (scaleUT w r ut) := by
  intro R hR b hb
  let R' := 1+r*R+r^4*R
  have hR' : 0<R' := by dsimp [R']; positivity
  obtain ⟨N,hN,hj⟩ := h R' hR' (r^4*b) (mul_neg_of_pos_of_neg (pow_pos hr _) hb)
  refine ⟨r^(-w)*((1+r^4)*(1+r^α)*N),by positivity,scaled_jet_bound hr hN u ut hs hj ?_⟩
  intro p hp
  simp only [FlatWeighted.scale,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mem_ofPred_eq]
  refine ⟨?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hp.1 hr.le
    dsimp [R']; nlinarith [mul_nonneg (pow_nonneg hr.le 4) hR.le]
  · have hh := mul_le_mul_of_nonneg_left hp.2.1 (pow_nonneg hr.le 4)
    dsimp [R']; nlinarith [mul_nonneg hr.le hR.le]
  · exact mul_le_mul_of_nonneg_left hp.2.2 (pow_nonneg hr.le 4)
variable [FiniteDimensional ℝ V]
lemma weightedValue_scale (w r : ℝ) (hr : 0<r) (p : V × ℝ) (hp : p.2<0) (u : ℝ → V → ℂ) :
    weightedValue w p (scaleU w r u)=weightedValue w (scale r p) u := by
  funext t x
  change sigma p^(-w) • scaleU w r u (chart p (x,t)).2 (chart p (x,t)).1=_
  rw [scaleU_apply,scale_chart r hr]
  simp only [weightedValue,sigma_scale_general r hr,Real.mul_rpow hr.le (sigma_pos p hp).le,smul_smul]
  rw [mul_comm]
lemma weightedTime_scale (w r : ℝ) (hr : 0<r) (p : V × ℝ) (hp : p.2<0) (ut : ℝ → V → ℂ) :
    weightedTime w p (scaleUT w r ut)=weightedTime w (scale r p) ut := by
  funext t x
  change (sigma p^(-w)*sigma p^4) • scaleUT w r ut (chart p (x,t)).2 (chart p (x,t)).1=_
  rw [scaleUT_apply,scale_chart r hr]
  simp only [weightedTime,sigma_scale_general r hr,Real.mul_rpow hr.le (sigma_pos p hp).le,smul_smul,mul_pow]
  congr 1
  ring
end FlatWeighted

end

end OAI
