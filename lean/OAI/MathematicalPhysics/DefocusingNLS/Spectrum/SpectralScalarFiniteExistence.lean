import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFiniteExistence
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreen

namespace OAI

/-! Existence of the scalar comparison solutions on every compact interval,
using the weighted Picard construction. -/

open Set
namespace DefocusingNLS

theorem spectralScalarField_lipschitz (V : ℂ) (u v : ℂ × ℂ) :
    ‖spectralScalarField V u-spectralScalarField V v‖≤(1+‖V‖)*‖u-v‖ := by
  have hfst : ‖u.1-v.1‖≤‖u-v‖ := norm_fst_le (u-v)
  have hsnd : ‖u.2-v.2‖≤‖u-v‖ := norm_snd_le (u-v)
  have he : -V*u.1- -V*v.1= -V*(u.1-v.1) := by ring
  change max ‖u.2-v.2‖ ‖-V*u.1- -V*v.1‖≤_
  rw [he,norm_mul,norm_neg]
  apply max_le
  · nlinarith [mul_nonneg (norm_nonneg V) (norm_nonneg (u-v))]
  · have hh := mul_le_mul_of_nonneg_left hfst (norm_nonneg V)
    nlinarith [norm_nonneg (u-v)]

noncomputable def spectralScalarFiniteField (a T : ℝ) (V : ℝ → ℂ) (hV : Continuous V) :
    C((Icc (0 : ℝ) T) × (ℂ × ℂ),ℂ × ℂ) where
  toFun x := spectralScalarField (V (a+(x.1 : ℝ))) x.2
  continuous_toFun := by
    exact continuous_snd.snd.prodMk
      (((hV.comp (continuous_const.add (continuous_subtype_val.comp continuous_fst))).neg).mul
        continuous_snd.fst)

theorem spectralScalar_finite_exists (a b B : ℝ) (hab : a≤b) (hB : 0≤B)
    (V : ℝ → ℂ) (hV : Continuous V) (hbound : ∀ r ∈ Icc a b, ‖V r‖≤B)
    (x : ℂ × ℂ) :
    ∃ q : ℝ → ℂ × ℂ, Continuous q ∧ q a=x ∧
      ∀ r ∈ Icc a b, HasDerivAt q (spectralScalarField (V r) (q r)) r := by
  have hT : 0≤b-a := sub_nonneg.mpr hab
  have hF (t : Icc (0 : ℝ) (b-a)) (u v : ℂ × ℂ) :
      ‖spectralScalarFiniteField a (b-a) V hV (t,u)-spectralScalarFiniteField a (b-a) V hV (t,v)‖≤
        (1+B)*‖u-v‖ := by
    apply (spectralScalarField_lipschitz (V (a+t)) u v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have ht : a+(t : ℝ) ∈ Icc a b := by constructor <;> linarith [t.2.1,t.2.2]
    linarith [hbound _ ht]
  obtain ⟨z,hz,hz0,hzd⟩ := exists_radial_finite_solution (b-a) hT
    (spectralScalarFiniteField a (b-a) V hV) (1+B) (by positivity) hF x
  refine ⟨fun r => z (r-a),hz.comp (continuous_id.sub continuous_const),?_,?_⟩
  · simpa only [sub_self] using hz0
  · intro r hr
    have ht : r-a ∈ Icc (0 : ℝ) (b-a) := by constructor <;> linarith [hr.1,hr.2]
    have hd := (hzd (r-a) ht).scomp r ((hasDerivAt_id r).sub_const a)
    simp only [Function.comp_def,one_smul,id_eq] at hd
    change HasDerivAt (fun t => z (t-a)) (spectralScalarField (V (a+(r-a))) (z (r-a))) r at hd
    simpa only [show a+(r-a)=r by ring] using hd

end DefocusingNLS

end OAI
