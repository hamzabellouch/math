import OAI.Geometry.NodalSets.Elliptic.ExponentialIntegralSeparation
import OAI.Geometry.NodalSets.Elliptic.RealEllipticLocalityLemmas
import OAI.Geometry.NodalSets.Elliptic.RealLocalCarleman

namespace OAI

namespace Yau.Geometry
open MeasureTheory Metric
open scoped ContDiff
noncomputable section

lemma real_carleman_weighted_mass (gamma potential phi : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hgp : ∀ x, 0 < gamma x) (hphi : ContDiff ℝ ∞ phi)
    (x0 : Yau.Jets.Coord) (r a b T : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hcar : ∀ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ ball x0 r → ∀ t : ℝ, T ≤ t →
      a*t*(∫ x, gamma x*realGradientSquare v x)+(b*t^3/4)*(∫ x, gamma x*v x^2) ≤
      (∫ x, gamma x*(Real.exp (t*phi x)*
        realEllipticResidual gamma potential B (fun y ↦ Real.exp (-t*phi y)*v y) x)^2))
    (f : Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ ball x0 r) (t : ℝ) (ht : max T 1 ≤ t) :
    (∫ x, Real.exp ((2*t)*phi x)*((b/4)*gamma x*f x^2)) ≤
      (∫ x, Real.exp ((2*t)*phi x)*(gamma x*(realEllipticResidual gamma potential B f x)^2)) := by
  let v := fun x ↦ Real.exp (t*phi x)*f x
  have hv : ContDiff ℝ ∞ v := (contDiff_const.mul hphi).exp.mul hf
  have hvc : HasCompactSupport v := hc.mul_left
  have hvs : tsupport v ⊆ ball x0 r := tsupport_mul_subset_right.trans hs
  have hinv : (fun y ↦ Real.exp (-t*phi y)*v y) = f := by
    funext y
    dsimp [v]
    rw [← mul_assoc,← Real.exp_add,show -t*phi y+t*phi y=0 by ring,Real.exp_zero,one_mul]
  have hh := hcar v hv hvc hvs t ((le_max_left _ _).trans ht)
  rw [hinv] at hh
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have hg0 : 0 ≤ a*t*(∫ x, gamma x*realGradientSquare v x) :=
    mul_nonneg (mul_nonneg ha.le ht0) (integral_nonneg (fun x ↦
      mul_nonneg (hgp x).le (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _))))
  have hv0 : 0 ≤ ∫ x, gamma x*v x^2 := integral_nonneg (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _))
  have ht3 : 1 ≤ t^3 := one_le_pow₀ ht1
  have hcub := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht3 (by positivity : 0 ≤ b/4)) hv0
  have he (x : Yau.Jets.Coord) : (Real.exp (t*phi x))^2 = Real.exp ((2*t)*phi x) := by
    rw [pow_two,← Real.exp_add]; congr 1; ring
  have hleft : (∫ x, Real.exp ((2*t)*phi x)*((b/4)*gamma x*f x^2)) =
      (b/4)*(∫ x, gamma x*v x^2) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [v]
    rw [mul_pow,he]; ring
  have hright : (∫ x, Real.exp ((2*t)*phi x)*(gamma x*(realEllipticResidual gamma potential B f x)^2)) =
      (∫ x, gamma x*(Real.exp (t*phi x)*realEllipticResidual gamma potential B f x)^2) := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [mul_pow,he]; ring
  rw [hleft,hright]
  nlinarith only [hh,hg0,hcub]

theorem real_local_carleman_support (gamma potential psi : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hpsi : ContDiff ℝ ∞ psi) (x0 : Yau.Jets.Coord)
    (hzero : psi x0 = 0) (hgrad : realCoordGradient psi x0 ≠ 0) (hpos : (B x0).PosDef) :
    ∃ K > 0, ∃ r > 0, ∀ f : Yau.Jets.Coord → ℝ,
      ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ ball x0 r →
      ∀ c : ℝ, (∀ x, realEllipticResidual gamma potential B f x ≠ 0 →
        realConvexifiedPhase psi K x ≤ c) →
      ∀ y, c < realConvexifiedPhase psi K y → f y = 0 := by
  obtain ⟨K,hK,r,hr,a,ha,b,hb,T,hT,hcar⟩ :=
    real_local_carleman gamma potential psi B hg hgp hpot hB hsym hpsi x0 hzero hgrad hpos
  let phi := realConvexifiedPhase psi K
  have hphi : ContDiff ℝ ∞ phi := realConvexifiedPhase_smooth psi hpsi K
  refine ⟨K,hK,r,hr,?_⟩
  intro f hf hc hs c hgap y hy
  let F := fun x ↦ (b/4)*gamma x*f x^2
  let G := fun x ↦ gamma x*(realEllipticResidual gamma potential B f x)^2
  have hR := realEllipticResidual_smooth gamma potential B f hg (fun x ↦ (hgp x).ne') hpot hB hf
  have hcR := realEllipticResidual_compact gamma potential B f hc
  have hF : Continuous F := ((continuous_const.mul hg.continuous).mul (hf.continuous.pow 2))
  have hG : Continuous G := hg.continuous.mul (hR.continuous.pow 2)
  have hcf2 : HasCompactSupport (fun x ↦ f x^2) := by
    convert hc.mul_right (f' := f) using 1
    first | rfl | (ext point; simp [pow_two])
  have hcr2 : HasCompactSupport (fun x ↦ (realEllipticResidual gamma potential B f x)^2) := by
    convert hcR.mul_right (f' := realEllipticResidual gamma potential B f) using 1
    first | rfl | (ext point; simp [pow_two])
  have hbound (t : ℝ) (ht : max T 1 ≤ t) :
      (∫ x, Real.exp (t*(2*phi x))*F x) ≤ (∫ x, Real.exp (t*(2*phi x))*G x) := by
    have hh := real_carleman_weighted_mass gamma potential phi B hgp hphi x0 r a b T ha hb
      hcar f hf hc hs t ht
    convert hh using 1 <;> congr 1 <;> funext x <;> dsimp [F,G] <;> congr 2 <;> ring
  have hsep := exponential_integral_separation F G (fun x ↦ 2*phi x) hF hG
    (continuous_const.mul hphi.continuous) hcf2.mul_left hcr2.mul_left
    (fun x ↦ mul_nonneg (mul_nonneg (by positivity) (hgp x).le) (sq_nonneg _))
    (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _))
    (2*c) (max T 1) (fun x hx ↦ by
      have hn : realEllipticResidual gamma potential B f x ≠ 0 := by
        intro hz; apply hx; simp [G,hz]
      exact mul_le_mul_of_nonneg_left (hgap x hn) (by norm_num)) hbound y
    (mul_lt_mul_of_pos_left hy (by norm_num))
  dsimp [F] at hsep
  have hbf : (b/4)*gamma y ≠ 0 := mul_ne_zero (div_ne_zero hb.ne' (by norm_num)) (hgp y).ne'
  exact sq_eq_zero_iff.mp (mul_eq_zero.mp hsep |>.resolve_left hbf)

end
end Yau.Geometry

end OAI
