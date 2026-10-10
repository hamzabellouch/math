import OAI.Analysis.AncientFlat.Evolution.FiniteSourceBound

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma finite_time_scale (T r : ℝ) (hr : 0<r) (p : V × ℝ) :
    -T/r^4≤p.2 ∧ p.2<0 ↔ -T≤(scale r p).2 ∧ (scale r p).2<0 := by
  rw [scale_time_neg r hr]
  exact and_congr ((div_le_iff₀ (pow_pos hr 4)).trans (by simp only [scale,mul_comm])) Iff.rfl
lemma finiteLocalDomain_scale (a T r : ℝ) (hr : 0<r) (p : V × ℝ) :
    finiteLocalDomain T a (scale r p)=finiteLocalDomain (T/r^4) a p := by
  ext q
  simp only [finiteLocalDomain,mem_ofPred_eq,←scale_chart r hr]
  rw [←finite_time_scale T r hr,neg_div]
lemma FiniteYBound.scale {α w a T M : ℝ} {f : V × ℝ → ℂ}
    (h : FiniteYBound α w a T M f) (r : ℝ) (hr : 0<r) :
    FiniteYBound α w a (T/r^4) M (scaleValue (w-4) r f) := by
  intro p hp
  rw [pullback_scale (w-4) r hr p hp.2]
  simpa only [finiteLocalDomain_scale a T r hr p] using
    h (FlatWeighted.scale r p) ((finite_time_scale T r hr p).mp (by simpa only [neg_div] using hp))
omit [FiniteDimensional ℝ V] in
lemma innerExtension_scale (ψ : ℝ → ℝ) (w T r : ℝ) (hr : 0<r) (f : V × ℝ → ℂ) :
    scaleValue w r (innerExtension ψ T f)=innerExtension ψ (T/r^4) (scaleValue w r f) := by
  ext p
  have hT : -T≤r^4*p.2 ↔ -(T/r^4)≤p.2 := by
    rw [←neg_div,div_le_iff₀ (pow_pos hr 4),mul_comm]
  have h4 : r^4=(r^2)^2 := by ring
  have hroot : Real.sqrt (T/r^4)=Real.sqrt T/r^2 := by
    rw [Real.sqrt_div' _ (pow_nonneg hr.le 4), h4,Real.sqrt_sq (sq_nonneg r)]
  have hg : (-(r^4*p.2)-T)/(‖r • p.1‖^2+Real.sqrt T)^2=
      (-p.2-T/r^4)/(‖p.1‖^2+Real.sqrt (T/r^4))^2 := by
    rw [hroot,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    field_simp
  simp only [scaleValue,innerExtension,scale,hT]
  split_ifs with h
  · rfl
  · rw [hg,smul_comm]
    congr 2
    simp [hr.ne',mul_div_cancel₀]
lemma normalize_sigma (p : V × ℝ) (hp : p.2<0) :
    ∃ r : ℝ, 0<r ∧ ∃ q : V × ℝ, q.2<0 ∧ sigma q=1 ∧ scale r q=p := by
  let r := sigma p
  have hr : 0<r := sigma_pos p hp
  let q : V × ℝ := (r⁻¹ • p.1,p.2/r^4)
  have he : scale r q=p := by
    simp only [scale,q,smul_smul,mul_inv_cancel₀ hr.ne',one_smul,mul_div_cancel₀ _ (pow_ne_zero 4 hr.ne'),Prod.mk.eta]
  have hq : q.2<0 := div_neg_of_neg_of_pos hp (pow_pos hr _)
  refine ⟨r,hr,q,hq,?_,he⟩
  have hs := sigma_scale_general r hr q
  rw [he] at hs
  change r=r*sigma q at hs
  nlinarith
end FlatWeighted

end

end OAI
