import OAI.Analysis.AncientFlat.Weighted.WeightedCharts
import OAI.Analysis.AncientFlat.Weighted.WeightedEstimateCore
import OAI.Analysis.AncientFlat.Geometry.ParabolicWindows

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace FlatWeighted
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
def scale (r : ℝ) (p : V × ℝ) : V × ℝ := (r • p.1,r^4*p.2)
def scaleValue (w r : ℝ) (f : V × ℝ → ℂ) (p : V × ℝ) : ℂ := r^(-w) • f (scale r p)
lemma scale_time_neg [FiniteDimensional ℝ V]
    (r : ℝ) (hr : 0<r) (p : V × ℝ) : (scale r p).2<0 ↔ p.2<0 := by
  change r^4*p.2<0 ↔ p.2<0
  constructor <;> intro h <;> nlinarith [pow_pos hr 4]
lemma sigma_scale_general [FiniteDimensional ℝ V]
    (r : ℝ) (hr : 0<r) (p : V × ℝ) : sigma (scale r p)=r*sigma p := by
  have h4 : r^4=(r^2)^2 := by ring
  simp only [sigma,scale,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  rw [show -(r^4*p.2)=r^4*(-p.2) by ring,Real.sqrt_mul (pow_nonneg hr.le 4),h4,Real.sqrt_sq (sq_nonneg r)]
  rw [show (r*‖p.1‖)^2+r^2*Real.sqrt (-p.2)=r^2*(‖p.1‖^2+Real.sqrt (-p.2)) by ring,
    Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr.le]
variable [FiniteDimensional ℝ V]

lemma scale_chart (r : ℝ) (hr : 0<r) (p q : V × ℝ) :
    scale r (chart p q)=chart (scale r p) q := by
  unfold chart
  rw [sigma_scale_general r hr]
  simp only [scale,smul_add,smul_smul,mul_pow,Prod.mk.injEq]
  constructor
  · trivial
  · ring
lemma localDomain_scale (a r : ℝ) (hr : 0<r) (p : V × ℝ) :
    localDomain a (scale r p)=localDomain a p := by
  ext q
  simp only [localDomain,mem_ofPred_eq,←scale_chart r hr,scale_time_neg r hr]
lemma pullback_scale (w r : ℝ) (hr : 0<r) (p : V × ℝ) (hp : p.2<0) (f : V × ℝ → ℂ) :
    pullback w p (scaleValue w r f)=pullback w (scale r p) f := by
  ext q
  simp only [pullback,scaleValue,scale_chart r hr,sigma_scale_general r hr,
    Real.mul_rpow hr.le (sigma_pos p hp).le,smul_smul]
  rw [mul_comm]
lemma YBound.scale {α w a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α w a M f) (r : ℝ) (hr : 0<r) :
    YBound α w a M (scaleValue (w-4) r f) := by
  intro p hp
  rw [pullback_scale (w-4) r hr p hp]
  simpa only [localDomain_scale a r hr p] using h (FlatWeighted.scale r p) ((scale_time_neg r hr p).mpr hp)
lemma pdist_unchart (p q : V × ℝ) (hp : p.2<0) :
    pdist (0:V × ℝ) (unchart p q)=pdist p q/sigma p := by
  have hs := sigma_pos p hp
  have hw := pdist_window p hs.le (0:V × ℝ) (unchart p q)
  change pdist (chart p 0) (chart p (unchart p q))=_ at hw
  rw [chart_zero,chart_unchart p q hp] at hw
  apply (eq_div_iff hs.ne').mpr
  simpa only [mul_comm] using hw.symm
lemma unchart_mem_of_near {a : ℝ} (ha : 0<a) (p q : V × ℝ) (hp : p.2<0) (hq : q.2<0)
    (hd : pdist p q<a*sigma p) : unchart p q∈localDomain a p := by
  have hs := sigma_pos p hp
  have hd' : pdist (0:V × ℝ) (unchart p q)<a := by rw [pdist_unchart p q hp]; exact (div_lt_iff₀ hs).mpr hd
  have hx : ‖(unchart p q).1‖<a := by
    simpa only [pdist,Prod.fst_zero,zero_sub,norm_neg] using
      lt_of_le_of_lt (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) ((1:ℝ)/4))) hd'
  have ht : |(unchart p q).2|^((1:ℝ)/4)<a := by
    simpa only [Prod.snd_zero,zero_sub,abs_neg] using
      lt_of_le_of_lt (le_add_of_nonneg_left (norm_nonneg ((0:V)-(unchart p q).1))) hd'
  have htime : |(unchart p q).2|<a^4 := by
    have hh := (pow_lt_pow_iff_left₀ (Real.rpow_nonneg (abs_nonneg _) ((1:ℝ)/4)) ha.le
      (by norm_num : (4:ℕ)≠0)).mpr ht
    rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)] at hh
    norm_num at hh
    exact hh
  exact ⟨hx,(abs_lt.mp htime).1,(abs_lt.mp htime).2,by rwa [chart_unchart p q hp]⟩
end FlatWeighted

end

end OAI
