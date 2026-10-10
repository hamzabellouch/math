import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedUnfold
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedCuspGaussian
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedWeightFactor
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedRowMellin

namespace OAI

/-! Gaussian Mellin representation of the actual rows at a translated
inverted cusp, retaining their finite ramified character. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaShiftedRowSeries (b c : Eisenstein) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' a : Eisenstein, cubicThetaShiftedRowWeight b c a*
    ((p.2/(Complex.normSq ((c:ℂ)*p.1+(3*a:Eisenstein))+norm c*p.2^2):ℝ):ℂ)^s

lemma cubicThetaShiftedGrid_row (b : Eisenstein) {c : Eisenstein} (hc : primary c)
    (p : ℂ × ℝ) (s : ℂ) :
    (∑' d : Eisenstein, cubicThetaShiftedGridTerm b (c,d) p s)=cubicThetaShiftedRowSeries b c p s := by
  have hi : Function.Injective (fun a : Eisenstein => 3*a) :=
    fun a b h => mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) h
  have hs : Function.support (fun d => cubicThetaShiftedGridTerm b (c,d) p s) ⊆
      Set.range (fun a : Eisenstein => 3*a) := by
    intro d hd
    by_cases ht : (3:Eisenstein)∣d
    · obtain ⟨a,ha⟩ := ht
      exact ⟨a,ha.symm⟩
    · exact False.elim (hd (by simp [cubicThetaShiftedGridTerm,cubicThetaInvertedAdmissible,ht]))
  rw [←hi.tsum_eq hs]
  unfold cubicThetaShiftedRowSeries
  apply tsum_congr
  intro a
  exact cubicThetaShiftedGridTerm_triple b hc a p s

theorem cubicThetaEisenstein_shifted_rows (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisenstein ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s=
      ∑' c : Eisenstein, if primary c then cubicThetaShiftedRowSeries b c p s else 0 := by
  rw [cubicThetaEisenstein_shifted_grid b hp,(cubicThetaShiftedGrid_summable b hp hs).tsum_prod]
  apply tsum_congr
  intro c
  by_cases hc : primary c
  · rw [ite_eq_left hc,cubicThetaShiftedGrid_row b hc]
  · simp [cubicThetaShiftedGridTerm,cubicThetaInvertedAdmissible,hc]

lemma cubicThetaShiftedRowWeight_norm_eq {c : Eisenstein} (hc : primary c)
    (b u : Eisenstein) :
    ‖cubicThetaShiftedRowWeight b c u‖=‖cubicSymbol c (3*u)‖ := by
  rw [cubicThetaShiftedRowWeight_factor hc,norm_mul,norm_star]
  change ‖cubicThetaKubotaValue (cubicThetaCuspStep b u)‖*_= _
  rw [cubicThetaKubotaValue_norm,one_mul]

lemma cubicThetaShiftedRowRadius_summable {c : Eisenstein} (hc : primary c)
    (b : Eisenstein) {p : ℂ×ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2<s.re) :
    Summable (fun a : Eisenstein => ‖cubicThetaShiftedRowWeight b c a‖*
      (cubicThetaRowRadius c p (3*a))^(-s.re)) := by
  simpa only [cubicThetaShiftedRowWeight_norm_eq hc] using cubicThetaInvertedRowRadius_summable hc hp hs

theorem cubicThetaShiftedRow_mellin (b : Eisenstein) {c : Eisenstein} (hc : primary c)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2<s.re) :
    Complex.Gamma s*cubicThetaShiftedRowSeries b c p s=
      ((p.2/norm c:ℝ):ℂ)^s*
        ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*(Real.exp (-p.2^2*t):ℂ)*
          cubicThetaShiftedCuspGaussianRow b c p.1 t := by
  have hscale : cubicThetaShiftedRowSeries b c p s=
      ((p.2/norm c:ℝ):ℂ)^s*∑' a : Eisenstein,
        cubicThetaShiftedRowWeight b c a*(cubicThetaRowRadius c p (3*a):ℂ)^(-s) := by
    unfold cubicThetaShiftedRowSeries
    rw [←tsum_mul_left]
    apply tsum_congr
    intro a
    rw [cubicThetaRowRadius_complex_power (primary_ne_zero hc) hp]
    ring
  have hM := cubicTheta_laplace_tsum (fun a => cubicThetaShiftedRowWeight b c a)
    (fun a => cubicThetaRowRadius c p (3*a)) (fun a => cubicThetaRowRadius_pos c (3*a) hp)
    (show 0<s.re by linarith) (cubicThetaShiftedRowRadius_summable hc b hp hs)
  rw [hscale,mul_left_comm,hM]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  unfold cubicThetaShiftedCuspGaussianRow
  simp only [←tsum_mul_left]
  apply tsum_congr
  intro a
  have he : Real.exp (-cubicThetaRowRadius c p (3*a)*t)=
      Real.exp (-p.2^2*t)*Real.exp (-t*‖p.1+3*(a:ℂ)/(c:ℂ)‖^2) := by
    rw [←Real.exp_add]
    congr 1
    unfold cubicThetaRowRadius
    rw [Complex.normSq_eq_norm_sq]
    change -(‖p.1+3*(a:ℂ)/(c:ℂ)‖^2+p.2^2)*t=_
    ring
  rw [he,Complex.ofReal_mul]
  ring

end CubicFirstMoment

end

end OAI
