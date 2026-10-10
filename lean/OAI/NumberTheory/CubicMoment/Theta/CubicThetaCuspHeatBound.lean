import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussianLinearTail

namespace OAI

/-! Uniform Gaussian control of rows with nonzero first coordinate in a
fixed-height cusp. This estimate precedes the scalar Rankin domination. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaScalarGaussian_uniform :
    ∃ C : ℝ, 1≤C ∧ ∀ z : ℂ, ∀ t : ℝ, 0<t →
      cubicThetaScalarGaussianReal z t≤C*(t+t⁻¹) := by
  let a := 2*Real.pi/(9*Real.sqrt 3)
  let c := 4*Real.pi^2/27
  let b := a*cubicThetaGaussianPowerConstant/c^2
  have ha : 0≤a := by dsimp [a]; positivity
  have hb : 0≤b := by
    dsimp only [b]
    exact div_nonneg (mul_nonneg ha cubicThetaGaussianPowerConstant_nonneg) (sq_nonneg c)
  refine ⟨1+a+b,by linarith,?_⟩
  intro z t ht
  have h := cubicThetaScalarGaussianReal_le z ht
  have htail := cubicThetaLatticeGaussianTail_div_bound (c:=c) (by dsimp [c]; positivity) ht
  have hpref : 2*Real.pi/(9*Real.sqrt 3*t)=a/t := by dsimp [a]; ring
  have harg : 4*Real.pi^2/(27*t)=c/t := by dsimp [c]; ring
  rw [hpref,harg] at h
  have h' : cubicThetaScalarGaussianReal z t≤a/t+b*t := by
    apply h.trans
    calc
      _ ≤ a/t*(1+(cubicThetaGaussianPowerConstant/c^2)*t^2) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) htail) (div_nonneg ha ht.le)
      _ = _ := by dsimp [b]; field_simp
  apply h'.trans
  have htinv : 0≤t⁻¹ := inv_nonneg.mpr ht.le
  rw [div_eq_mul_inv]
  nlinarith [mul_nonneg ha ht.le,mul_nonneg hb htinv]

def cubicThetaNonzeroFirstHeat (p : ℂ × ℝ) (t : ℝ) : ℝ :=
  ∑' c : {c : Eisenstein // c≠0},Real.exp (-(t*p.2)*norm c.val)*
    cubicThetaScalarGaussianReal (3*(c.val:ℂ)*p.1) (t/(9*p.2))

lemma cubicThetaNonzeroFirstHeat_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    Summable (fun c : {c : Eisenstein // c≠0} => Real.exp (-(t*p.2)*norm c.val)*
      cubicThetaScalarGaussianReal (3*(c.val:ℂ)*p.1) (t/(9*p.2))) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaScalarGaussian_uniform
  have hs := (cubicThetaLatticeGaussianTail_summable (mul_pos ht hp)).mul_right
    (C*(t/(9*p.2)+(t/(9*p.2))⁻¹))
  apply hs.of_nonneg_of_le
  · intro c
    exact mul_nonneg (Real.exp_pos _).le (cubicThetaScalarGaussianReal_nonneg _ _)
  · intro c
    exact mul_le_mul_of_nonneg_left (hbound _ _ (by positivity)) (Real.exp_pos _).le

lemma cubicThetaNonzeroFirstHeat_bound :
    ∃ D : ℝ, 0≤D ∧ ∀ p : ℂ × ℝ, 1/2≤p.2 → ∀ t : ℝ, 0<t →
      cubicThetaNonzeroFirstHeat p t≤D*(1+t⁻¹^2) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaScalarGaussian_uniform
  let L := cubicThetaGaussianLinearConstant
  have hL : 0≤L := cubicThetaGaussianLinearConstant_nonneg
  refine ⟨36*C*L,by positivity,?_⟩
  intro p hp t ht
  have hp0 : 0<p.2 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hp
  have hmajor := (cubicThetaLatticeGaussianTail_summable (mul_pos ht hp0)).mul_right
    (C*(t/(9*p.2)+(t/(9*p.2))⁻¹))
  have hsum := (cubicThetaNonzeroFirstHeat_summable hp0 ht).tsum_le_tsum
    (fun c => mul_le_mul_of_nonneg_left (hbound _ _ (by positivity)) (Real.exp_pos _).le) hmajor
  rw [tsum_mul_right] at hsum
  have htail := cubicThetaLatticeGaussianTail_linear_bound (mul_pos ht hp0)
  have hfac : 0≤C*(t/(9*p.2)+(t/(9*p.2))⁻¹) := by positivity
  have h := hsum.trans (mul_le_mul_of_nonneg_right htail hfac)
  change cubicThetaNonzeroFirstHeat p t≤_ at h
  have he : L/(t*p.2)*(C*(t/(9*p.2)+(t/(9*p.2))⁻¹))=
      C*L*((1/9)/(p.2^2)+9/(t^2)) := by field_simp
  rw [he] at h
  apply h.trans
  have hv : (1/9:ℝ)/(p.2^2)≤4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
    nlinarith
  rw [inv_pow]
  have hn : 0≤(t^2)⁻¹ := inv_nonneg.mpr (sq_nonneg t)
  have hx : (1/9:ℝ)/(p.2^2)+9/(t^2)≤36*(1+(t^2)⁻¹) := by
    rw [div_eq_mul_inv (9:ℝ)]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hx (mul_nonneg (by linarith : 0≤C) hL)
  convert hm using 1
  ring

end CubicFirstMoment

end

end OAI
