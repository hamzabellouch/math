import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantSummability
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroFourier

namespace OAI

/-! Separation of the actual Eisenstein series into its constant mode
and nonzero Fourier rows on the initial half-plane. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaConstantRow (v : ℝ) (s : ℂ) (c : Eisenstein) : ℂ :=
  if (3:Eisenstein)∣c ∧ c≠0 then
    (((v/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
      cubicThetaEisensteinGaussCoefficient c 0*
        (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s 0 t))/Complex.Gamma s else 0

def cubicThetaNonzeroFourierRow (c : Eisenstein) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  if (3:Eisenstein)∣c ∧ c≠0 then
    (((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
      ∑' h : Eisenstein, if h=0 then 0 else
        cubicThetaRowFourierCoefficient c p.1 h*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)) /
            Complex.Gamma s else 0

lemma cubicThetaRowFourier_summable {v : ℝ} (hv : 0<v) {s : ℂ}
    (hs : 1<s.re) {c : Eisenstein} (hc : c≠0) (z : ℂ) :
    Summable (fun h : Eisenstein => cubicThetaRowFourierCoefficient c z h*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)) := by
  apply (cubicThetaWeightedDualHeat_mass_summable hv hs hc z).of_norm_bounded
  intro h
  rw [←integral_const_mul]
  exact norm_integral_le_integral_norm _

lemma cubicThetaRowFourierCoefficient_zero (c : Eisenstein) (z : ℂ) :
    cubicThetaRowFourierCoefficient c z 0=cubicThetaEisensteinGaussCoefficient c 0 := by
  simp [cubicThetaRowFourierCoefficient,cubicThetaRowFrequency,tracePair]

lemma cubicThetaEisensteinRow_split {c : Eisenstein} (hc0 : c≠0)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisensteinRow c p s=
      cubicThetaConstantRow p.2 s c+cubicThetaNonzeroFourierRow c p s := by
  by_cases hc : (3:Eisenstein)∣c
  · have hG := Complex.Gamma_ne_zero_of_re_pos (show 0<s.re by linarith)
    have hrow := cubicThetaEisensteinRow_fourier hc hc0 hp hs
    have hsum := cubicThetaRowFourier_summable hp (show 1<s.re by linarith) hc0 p.1
    rw [hsum.tsum_eq_add_tsum_ite 0,cubicThetaRowFourierCoefficient_zero,
      cubicThetaRowHeatScale_zero,mul_add] at hrow
    unfold cubicThetaConstantRow cubicThetaNonzeroFourierRow
    rw [ite_eq_left ⟨hc,hc0⟩,ite_eq_left ⟨hc,hc0⟩]
    rw [←add_div]
    apply (eq_div_iff hG).mpr
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hrow
  · simp [cubicThetaEisensteinRow_nondivisible hc,cubicThetaConstantRow,
      cubicThetaNonzeroFourierRow,hc]

lemma cubicThetaConstantRow_eq {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 1<s.re)
    (c : Eisenstein) :
    cubicThetaConstantRow v s c=
      (((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s))*
        cubicThetaConstantTermWeight s c := by
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · simp only [cubicThetaConstantRow,cubicThetaConstantTermWeight,ite_eq_left hc]
    exact cubicTheta_zero_row_factor hv hs hc.2
  · simp [cubicThetaConstantRow,cubicThetaConstantTermWeight,hc]

lemma cubicThetaConstantRow_summable {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 4/3<s.re) :
    Summable (cubicThetaConstantRow v s) := by
  have hsum := ((cubicThetaConstantTermWeight_norm_summable hs).of_norm).mul_left
    (((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s))
  exact hsum.congr (fun c => (cubicThetaConstantRow_eq hv (by linarith) c).symm)

lemma cubicThetaNonzeroFourierRow_eq {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ}
    (hs : 2<s.re) (c : Eisenstein) :
    cubicThetaNonzeroFourierRow c p s=cubicThetaEisensteinRow c p s-
      (if c=0 then (p.2:ℂ)^s else 0)-cubicThetaConstantRow p.2 s c := by
  by_cases hc : c=0
  · subst c
    simp [cubicThetaNonzeroFourierRow,cubicThetaConstantRow,cubicThetaEisensteinRow_zero]
  · rw [ite_eq_right hc,cubicThetaEisensteinRow_split hc hp hs]
    ring

lemma cubicThetaNonzeroFourierRow_summable {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ}
    (hs : 2<s.re) : Summable (fun c => cubicThetaNonzeroFourierRow c p s) := by
  have hrow : Summable (fun c : Eisenstein => cubicThetaEisensteinRow c p s) :=
    (cubicThetaEisensteinGrid_summable hp hs).prod
  have hz : Summable (fun c : Eisenstein => if c=0 then (p.2:ℂ)^s else 0) :=
    (hasSum_ite_eq 0 _).summable
  exact ((hrow.sub hz).sub (cubicThetaConstantRow_summable hp (by linarith))).congr
    (fun c => (cubicThetaNonzeroFourierRow_eq hp hs c).symm)

theorem cubicThetaEisenstein_constant_add_nonzero {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisenstein p s=cubicThetaEisensteinConstantMode p.2 s+
      ∑' c : Eisenstein, cubicThetaNonzeroFourierRow c p s := by
  have hrow : Summable (fun c : Eisenstein => cubicThetaEisensteinRow c p s) :=
    (cubicThetaEisensteinGrid_summable hp hs).prod
  have hz : Summable (fun c : Eisenstein => if c=0 then (p.2:ℂ)^s else 0) :=
    (hasSum_ite_eq 0 _).summable
  have hc := cubicThetaConstantRow_summable hp (show 4/3<s.re by linarith)
  simp_rw [cubicThetaNonzeroFourierRow_eq hp hs]
  rw [(hrow.sub hz).tsum_sub hc,hrow.tsum_sub hz]
  rw [show (∑' c : Eisenstein, if c=0 then (p.2:ℂ)^s else 0)=(p.2:ℂ)^s by simp]
  have he : cubicThetaEisenstein p s=∑' c : Eisenstein, cubicThetaEisensteinRow c p s := by
    rw [cubicThetaEisenstein_eq_grid,(cubicThetaEisensteinGrid_summable hp hs).tsum_prod]
    rfl
  change cubicThetaEisenstein p s=((p.2:ℂ)^s+∑' c, cubicThetaConstantRow p.2 s c)+_
  rw [he]
  ring

end CubicFirstMoment

end

end OAI
