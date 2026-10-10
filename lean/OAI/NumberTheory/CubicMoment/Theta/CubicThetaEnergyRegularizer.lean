import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactEnergyCorrection

namespace OAI

/-! At every real spectral parameter below two the energy pencil admits
an explicit compact correction which is invertible. This is the local
Fredholm reduction used for continuation across the real axis. -/
noncomputable section
open scoped MatrixGroups InnerProduct NNReal
namespace CubicFirstMoment

def cubicThetaEnergyRegularizer (S R : Finset SL(2,Eisenstein)) (B ε z : ℝ) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  1-(z:ℂ) • cubicThetaEnergyMass+
    ((z/(2+ε):ℝ):ℂ) • cubicThetaCompactEnergyCorrection S R B

lemma cubicThetaEnergy_real_smul_inner (u v : cubicThetaGlobalEnergySpace) (r : ℝ) :
    (inner ℂ ((r:ℂ) • u) v).re=r*(inner ℂ u v).re := by
  have h : inner ℂ ((r:ℂ) • u) v=star (r:ℂ)*inner ℂ u v :=
    inner_smul_left (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) u v (r:ℂ)
  rw [RCLike.star_def,Complex.conj_ofReal] at h
  have hh := congrArg Complex.re h
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hh

lemma cubicThetaEnergyRegularizer_inner (S R : Finset SL(2,Eisenstein)) (B ε z : ℝ)
    (u : cubicThetaGlobalEnergySpace) :
    (inner ℂ (cubicThetaEnergyRegularizer S R B ε z u) u).re=
      ‖u‖^2-z*(inner ℂ (cubicThetaEnergyMass u) u).re+
        (z/(2+ε))*(inner ℂ (cubicThetaCompactEnergyCorrection S R B u) u).re := by
  let v := cubicThetaEnergyMass u
  let w := cubicThetaCompactEnergyCorrection S R B u
  have ha := inner_add_left (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace)
    (u-(z:ℂ) • v) (((z/(2+ε):ℝ):ℂ) • w) u
  have hs := inner_sub_left (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) u ((z:ℂ) • v) u
  have hh := congrArg Complex.re (ha.trans (congrArg₂ (fun x y : ℂ => x+y) hs rfl))
  have hnorm : (inner ℂ u u).re=‖u‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) u
  rw [Complex.add_re,Complex.sub_re,hnorm,cubicThetaEnergy_real_smul_inner,
    cubicThetaEnergy_real_smul_inner] at hh
  exact hh

lemma cubicThetaEnergyRegularizer_unit {ε z : ℝ} (hε : 0<ε) (hz : 0≤z)
    (hgap : z*(1+ε)<2+ε)
    (S R : Finset SL(2,Eisenstein)) (B : ℝ)
    (hupper : ∀ u : cubicThetaGlobalEnergySpace,
      (2+ε)*(inner ℂ (cubicThetaEnergyMass u) u).re≤
        (1+ε)*‖u‖^2+(inner ℂ (cubicThetaCompactEnergyCorrection S R B u) u).re) :
    IsUnit (cubicThetaEnergyRegularizer S R B ε z) := by
  have hd : 0<2+ε := by linarith
  let c : ℝ := 1-z*(1+ε)/(2+ε)
  have hc : 0<c := sub_pos.mpr ((div_lt_one hd).mpr hgap)
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _ (c:=⟨c,hc.le⟩) hc
  intro u
  have hs := mul_le_mul_of_nonneg_left (hupper u) (div_nonneg hz hd.le)
  have hcancel : z/(2+ε)*((2+ε)*(inner ℂ (cubicThetaEnergyMass u) u).re)=
      z*(inner ℂ (cubicThetaEnergyMass u) u).re := by field_simp
  rw [hcancel] at hs
  calc
    ‖u‖^2*(⟨c,hc.le⟩:ℝ≥0)≤(inner ℂ (cubicThetaEnergyRegularizer S R B ε z u) u).re := by
      rw [cubicThetaEnergyRegularizer_inner]
      change ‖u‖^2*c≤_
      dsimp [c]
      rw [mul_add] at hs
      have he : z/(2+ε)*(1+ε)=z*(1+ε)/(2+ε) := by ring
      rw [← mul_assoc,he] at hs
      have hlin (N M Q r t : ℝ) (h : z*M≤r*N+t*Q) :
          N*(1-r)≤N-z*M+t*Q := by nlinarith only [h]
      exact hlin _ _ _ _ _ hs
    _ ≤ _ := Complex.re_le_norm _

theorem cubicThetaEnergyPencil_compact_regularizer {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    ∃ K : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace,
      IsCompactOperator K ∧ IsUnit (1-(z:ℂ) • cubicThetaEnergyMass+K) := by
  let ε : ℝ := (2-z)/(2*(z+1))
  have hε : 0<ε := div_pos (sub_pos.mpr hz2) (by positivity)
  have hgap : z*(1+ε)<2+ε := by
    have he : ε*(2*(z+1))=2-z := by dsimp [ε]; field_simp
    nlinarith [mul_pos hε (by linarith : 0<z+2)]
  obtain ⟨S,R,B,_,h⟩ := cubicThetaEnergyMass_upper_mod_compact hε
  refine ⟨((z/(2+ε):ℝ):ℂ) • cubicThetaCompactEnergyCorrection S R B,
    (cubicThetaCompactEnergyCorrection_compact S R B).smul (((z/(2+ε):ℝ):ℂ)),?_⟩
  exact cubicThetaEnergyRegularizer_unit hε hz hgap S R B h

end CubicFirstMoment

end

end OAI
