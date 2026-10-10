import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedUnfold
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedGaussian

namespace OAI

/-! The literal inverted Eisenstein rows and their convergent Gaussian
Mellin representation. This connects finite arithmetic to the actual series. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaInvertedRowSeries (c : Eisenstein) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' a : Eisenstein, cubicSymbol c (3*a)*
    ((p.2/(Complex.normSq ((c:ℂ)*p.1+(3*a:Eisenstein))+norm c*p.2^2):ℝ):ℂ)^s

lemma cubicThetaInvertedGrid_row {c : Eisenstein} (hc : primary c)
    (p : ℂ × ℝ) (s : ℂ) :
    (∑' d : Eisenstein, cubicThetaInvertedGridTerm (c,d) p s)=cubicThetaInvertedRowSeries c p s := by
  have hi : Function.Injective (fun a : Eisenstein => 3*a) :=
    fun a b h => mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) h
  have hs : Function.support (fun d => cubicThetaInvertedGridTerm (c,d) p s) ⊆
      Set.range (fun a : Eisenstein => 3*a) := by
    intro d hd
    by_cases ht : (3:Eisenstein)∣d
    · obtain ⟨a,ha⟩ := ht
      exact ⟨a,ha.symm⟩
    · exact False.elim (hd (by simp [cubicThetaInvertedGridTerm,cubicThetaInvertedAdmissible,ht]))
  rw [←hi.tsum_eq hs]
  unfold cubicThetaInvertedRowSeries
  apply tsum_congr
  intro a
  exact cubicThetaInvertedGridTerm_triple hc a p s

theorem cubicThetaEisenstein_inverted_rows {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      ∑' c : Eisenstein, if primary c then cubicThetaInvertedRowSeries c p s else 0 := by
  rw [cubicThetaEisenstein_inverted_grid hp,(cubicThetaInvertedGrid_summable hp hs).tsum_prod]
  apply tsum_congr
  intro c
  by_cases hc : primary c
  · rw [ite_eq_left hc,cubicThetaInvertedGrid_row hc]
  · simp [cubicThetaInvertedGridTerm,cubicThetaInvertedAdmissible,hc]

lemma cubicThetaInvertedRowRadius_summable {c : Eisenstein} (hc : primary c)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2<s.re) :
    Summable (fun a : Eisenstein => ‖cubicSymbol c (3*a)‖*
      (cubicThetaRowRadius c p (3*a))^(-s.re)) := by
  have hi : Function.Injective (fun a : Eisenstein => (c,3*a)) := by
    intro a b h
    exact mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) (Prod.mk.inj h).2
  have hr := (cubicThetaInvertedGrid_summable hp hs).norm.comp_injective hi
  have ht := hr.mul_left ((norm c/p.2)^s.re)
  have hc0 := primary_ne_zero hc
  apply ht.congr
  intro a
  dsimp only [Function.comp_apply]
  have hpos : 0<p.2/(Complex.normSq ((c:ℂ)*p.1+(3*a:Eisenstein))+norm c*p.2^2) := by
    rw [←cubicThetaRowRadius_scale hc0]
    exact div_pos hp (mul_pos (norm_pos_of_ne_zero hc0) (cubicThetaRowRadius_pos c (3*a) hp))
  have he : cubicThetaInvertedGridTerm (c,3*a) p s=
      cubicSymbol c (3*a)*
        ((p.2/(Complex.normSq ((c:ℂ)*p.1+(3*a:Eisenstein))+norm c*p.2^2):ℝ):ℂ)^s := by
    unfold cubicThetaInvertedGridTerm
    by_cases hcop : IsCoprime c (3*a)
    · rw [ite_eq_left ⟨hc,⟨a,rfl⟩,hcop⟩]
    · rw [ite_eq_right (by intro h; exact hcop h.2.2),
        cubicSymbol_eq_zero_of_not_isCoprime hc hcop,zero_mul]
  rw [he,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hpos,
    cubicThetaRowRadius_power hc0 hp]
  ring

theorem cubicThetaInvertedRow_mellin {c : Eisenstein} (hc : primary c)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2<s.re) :
    Complex.Gamma s*cubicThetaInvertedRowSeries c p s=
      ((p.2/norm c:ℝ):ℂ)^s*
        ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*(Real.exp (-p.2^2*t):ℂ)*
          cubicThetaInvertedGaussianRow c p.1 t := by
  have hscale : cubicThetaInvertedRowSeries c p s=
      ((p.2/norm c:ℝ):ℂ)^s*∑' a : Eisenstein,
        cubicSymbol c (3*a)*(cubicThetaRowRadius c p (3*a):ℂ)^(-s) := by
    unfold cubicThetaInvertedRowSeries
    rw [←tsum_mul_left]
    apply tsum_congr
    intro a
    rw [cubicThetaRowRadius_complex_power (primary_ne_zero hc) hp]
    ring
  have hM := cubicTheta_laplace_tsum (fun a => cubicSymbol c (3*a))
    (fun a => cubicThetaRowRadius c p (3*a)) (fun a => cubicThetaRowRadius_pos c (3*a) hp)
    (show 0<s.re by linarith) (cubicThetaInvertedRowRadius_summable hc hp hs)
  rw [hscale,mul_left_comm,hM]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  unfold cubicThetaInvertedGaussianRow
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
