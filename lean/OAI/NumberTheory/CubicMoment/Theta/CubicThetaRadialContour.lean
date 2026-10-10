import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialPolynomialStrip
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticMellinShift

namespace OAI

/-! The radial Mellin contour crosses exactly the actual theta pole.
The weight supplies absolute convergence and vanishing horizontal edges. -/
noncomputable section
open MeasureTheory Set Filter
open scoped MatrixGroups ContDiff Topology
namespace CubicFirstMoment

lemma cubicThetaSelectedRadialDirichlet_continuous_line (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {σ : ℝ} (hσ : σ≠5/6) :
    Continuous (fun t : ℝ => cubicThetaSelectedRadialDirichlet g hc
      ((σ:ℂ)+(t:ℂ)*Complex.I)) := by
  have hne (t : ℝ) : (σ:ℂ)+(t:ℂ)*Complex.I≠(5/6:ℂ) := by
    intro h
    apply hσ
    have hr := congrArg Complex.re h
    simpa using hr
  have hE := (cubicThetaSelectedRadialHolomorphicPart_differentiable g hc).continuous.comp
    (show Continuous (fun t : ℝ => (σ:ℂ)+(t:ℂ)*Complex.I) by fun_prop)
  have hP : Continuous (fun t : ℝ => cubicThetaSelectedRadialResidue g hc/
      ((σ:ℂ)+(t:ℂ)*Complex.I-5/6)) :=
    continuous_const.div (by fun_prop) (fun t => sub_ne_zero.mpr (hne t))
  exact (hE.add hP).congr (fun t =>
    (cubicThetaSelectedRadialDirichlet_pole_decomposition g hc (hne t)).symm)

theorem cubicThetaSelectedRadialDirichlet_contour (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {a b Z : ℝ} (ha : a<5/6) (hb : 5/6<b) (hZ : 0<Z) :
    (∫ t : ℝ,mellin W ((b:ℂ)+(t:ℂ)*Complex.I)*(Z:ℂ)^((b:ℂ)+(t:ℂ)*Complex.I)*
      cubicThetaSelectedRadialDirichlet g hc ((b:ℂ)+(t:ℂ)*Complex.I))=
    (∫ t : ℝ,mellin W ((a:ℂ)+(t:ℂ)*Complex.I)*(Z:ℂ)^((a:ℂ)+(t:ℂ)*Complex.I)*
      cubicThetaSelectedRadialDirichlet g hc ((a:ℂ)+(t:ℂ)*Complex.I))+
      (2*Real.pi:ℝ)*(cubicThetaSelectedRadialResidue g hc*mellin W (5/6)*(Z:ℂ)^(5/6:ℂ)) := by
  let F : ℂ→ℂ := fun s => (Z:ℂ)^s*cubicThetaSelectedRadialDirichlet g hc s
  obtain ⟨C,N,hC,hD⟩ := cubicThetaSelectedRadialDirichlet_large_height g hc a b
  have hF : MetaplecticStripPolynomial F a b := by
    refine ⟨max (Z^a) (Z^b)*C,by positivity,N,?_⟩
    intro σ hσ t ht
    have hz : Z^σ ≤ max (Z^a) (Z^b) := by
      by_cases h : 1 ≤ Z
      · exact (Real.rpow_le_rpow_of_exponent_le h hσ.2).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hZ (le_of_not_ge h) hσ.1).trans
          (le_max_left _ _)
    have hd : ‖cubicThetaSelectedRadialDirichlet g hc ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ C*(1+|t|)^N := by
      simpa using hD ((σ:ℂ)+(t:ℂ)*Complex.I) (by simpa using hσ) (by simpa using ht)
    dsimp only [F]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hZ]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    calc
      _  ≤  max (Z^a) (Z^b)*(C*(1+|t|)^N) :=
        mul_le_mul hz hd (_root_.norm_nonneg _) (by positivity)
      _ = _ := by ring
  obtain ⟨K,hK,hbound⟩ := metaplectic_mellin_large_majorant F hF W hW hpos hsm
    (U:=1) (by norm_num) 0
  let M : ℂ→ℂ := fun s => mellin W s*(Z:ℂ)^s
  have : NeZero (Z:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hZ.ne'⟩
  have hM : Differentiable ℂ M := (smooth_mellin_entire W hW hpos hsm.continuous).mul
    (differentiable_const_cpow_of_neZero _)
  have hlarge (σ : ℝ) (hσ : σ∈Icc a b) (t : ℝ) (ht : 1 ≤ |t|) :
      ‖M ((σ:ℂ)+(t:ℂ)*Complex.I)*cubicThetaSelectedRadialDirichlet g hc
        ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ mellinEdgeMajorant K t := by
    simpa only [F,M,Complex.ofReal_zero,add_zero,Complex.ofReal_one,Complex.one_cpow,mul_one,mul_assoc]
      using hbound σ hσ t ht
  have hInt (σ : ℝ) (hσ : σ∈Icc a b) (hσp : σ≠5/6) :
      Integrable (fun t : ℝ => M ((σ:ℂ)+(t:ℂ)*Complex.I)*
        cubicThetaSelectedRadialDirichlet g hc ((σ:ℂ)+(t:ℂ)*Complex.I)) := by
    apply continuous_integrable_of_large_height_bound _
      ((hM.continuous.comp (by fun_prop)).mul
        (cubicThetaSelectedRadialDirichlet_continuous_line g hc hσp))
      (mellinEdgeMajorant K) (mellinEdgeMajorant_integrable K)
    · intro t
      dsimp [mellinEdgeMajorant]
      positivity
    · exact hlarge σ hσ
  have hLine (σ : ℝ) (hσ : σ≠5/6) (t : ℝ) :
      cubicThetaSelectedRadialDirichlet g hc ((σ:ℂ)+(t:ℂ)*Complex.I)=
        cubicThetaSelectedRadialHolomorphicPart g hc ((σ:ℂ)+(t:ℂ)*Complex.I)+
          cubicThetaSelectedRadialResidue g hc/((σ:ℂ)+(t:ℂ)*Complex.I-(5/6:ℂ)) := by
    apply cubicThetaSelectedRadialDirichlet_pole_decomposition
    intro he
    exact hσ (by simpa using congrArg Complex.re he)
  have hab : a ≤ b := (ha.trans hb).le
  have hshift := mellin_single_pole_shift_of_majorant M
    (cubicThetaSelectedRadialHolomorphicPart g hc) (cubicThetaSelectedRadialResidue g hc)
    ha hb hM (cubicThetaSelectedRadialHolomorphicPart_differentiable g hc).differentiableOn
    (by simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,hLine a ha.ne] using
      hInt a ⟨le_rfl,hab⟩ ha.ne)
    (by simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,hLine b hb.ne'] using
      hInt b ⟨hab,le_rfl⟩ hb.ne')
    (mellinEdgeMajorant K) (mellinEdgeMajorant_tendsto K).1 (mellinEdgeMajorant_tendsto K).2
    (by
      intro σ hσ t ht
      have hn : (σ:ℂ)+(t:ℂ)*Complex.I≠(5/6:ℂ) := by
        intro he
        have hz : t=0 := by simpa using congrArg Complex.im he
        simp only [hz,abs_zero] at ht
        linarith
      simp only [Complex.ofReal_div,Complex.ofReal_ofNat]
      rw [←cubicThetaSelectedRadialDirichlet_pole_decomposition g hc hn]
      exact hlarge σ hσ t ht)
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat,←hLine a ha.ne,←hLine b hb.ne'] at hshift
  simpa only [M,mul_assoc] using hshift

end CubicFirstMoment

end

end OAI
