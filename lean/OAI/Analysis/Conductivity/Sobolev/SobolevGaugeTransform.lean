import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevMaximum
import OAI.Analysis.Conductivity.Sobolev.SobolevSmoothTests

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma H1_sub_constant_spec (u : H1) (c : ℝ) :
    (∀ᵐ x ∂ballMeasure, weakValue (u-constantH1 c) x=weakValue u x-c) ∧
    (weakGradient (u-constantH1 c) =ᵐ[ballMeasure] weakGradient u) := by
  constructor
  · filter_upwards [weakValue_sub u (constantH1 c),constantH1_value c] with x hx hy
    simpa only [Pi.sub_apply,hy] using hx
  · filter_upwards [weakGradient_sub u (constantH1 c),constantH1_gradient c] with x hx hy
    simpa only [Pi.sub_apply,hy,Pi.zero_apply,sub_zero] using hx

theorem exists_gauge_transform {u w : H1} {M : ℝ}
    (hu : ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M)
    (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2) (hw0 : w∈H10) (c : ℝ) :
    ∃ v : H1, trace v=trace u ∧
      (∀ᵐ x ∂ballMeasure, weakValue v x=c+(weakValue u x-c)/(1+weakValue w x)) ∧
      (∀ᵐ x ∂ballMeasure, ∀ a : ℝ,
        (a*(1+weakValue w x)^2) • weakGradient v x=
          ((1+weakValue w x)*a) • weakGradient u x-
          ((weakValue u x-c)*a) • weakGradient w x) := by
  let q := inverseOperation.onH1 w
  have hi := inverseOperation_spec hw
  have hs := H1_sub_constant_spec u c
  have huc : ∀ᵐ x ∂ballMeasure, |weakValue (u-constantH1 c) x|≤M+|c| := by
    filter_upwards [hs.1,hu] with x hx hy
    rw [hx]
    exact (abs_sub _ _).trans (add_le_add hy (le_refl _))
  obtain ⟨p,hpv,hpg,hp0⟩ := exists_H1_product huc hi.2.2.1
  have hp : p∈H10 := hp0 (hi.2.2.2 hw0)
  refine ⟨u+p,?_,?_,?_⟩
  · apply (Submodule.Quotient.eq H10).mpr
    simpa only [add_sub_cancel_left] using hp
  · filter_upwards [weakValue_add u p,hpv,hs.1,hi.1,hw] with x hx hp hs hq hw
    rw [hx,Pi.add_apply,hp,hs,hq]
    ring
  · filter_upwards [weakGradient_add u p,hpg,hs.1,hs.2,hi.1,hi.2.1,hw]
      with x hx hp hs hg hq hd hw
    intro a
    rw [hx,Pi.add_apply,hp,hs,hg,hq,hd]
    have hn : (1:ℝ)+weakValue w x≠0 := by have := (abs_le.mp hw).1; linarith
    ext i
    change (a*(1+weakValue w x)^2)*((weakGradient u x) i+
      ((weakValue u x-c)*(-((1+weakValue w x)^2)⁻¹*(weakGradient w x) i)+
      ((1+weakValue w x)⁻¹-1)*(weakGradient u x) i))=_
    change _ = ((1+weakValue w x)*a)*(weakGradient u x) i-
      ((weakValue u x-c)*a)*(weakGradient w x) i
    field_simp [hn]
    ring

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def WeightedAnnihilation (a : R3 → ℝ) (w u : H1) (c : ℝ) : Prop :=
  ∀ (f : R3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) f →
    HasCompactSupport f → tsupport f⊆ball →
      ∫ x, a x*inner ℝ (weakGradient w x)
        ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure=0

def gaugeCoefficient (a : R3 → ℝ) (w : H1) (x : R3) : ℝ := a x*(1+weakValue w x)^2

lemma gaugeCoefficient_aeStronglyMeasurable (a : R3 → ℝ)
    (ha : AEStronglyMeasurable a ballMeasure) (w : H1) :
    AEStronglyMeasurable (gaugeCoefficient a w) ballMeasure :=
  ha.mul ((aestronglyMeasurable_const.add
    (jetValue.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable w.val))).pow 2)

lemma gaugeCoefficient_bounds {a : R3 → ℝ} {w : H1} {c C : ℝ}
    (hc : 0<c) (ha : ∀ᵐ x ∂ballMeasure, c≤a x ∧ a x≤C)
    (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2) :
    ∀ᵐ x ∂ballMeasure, c/4≤gaugeCoefficient a w x ∧ gaugeCoefficient a w x≤9*C/4 := by
  filter_upwards [ha,hw] with x hx hy
  have hlo := (abs_le.mp hy).1
  have hup := (abs_le.mp hy).2
  have hp : 0≤a x := le_trans hc.le hx.1
  have hrlo : (1/4:ℝ)≤(1+weakValue w x)^2 := by nlinarith
  have hrup : (1+weakValue w x)^2≤(9/4:ℝ) := by nlinarith
  constructor
  · change c/4≤a x*(1+weakValue w x)^2
    calc
      _ = c*(1/4:ℝ) := by ring
      _ ≤ a x*(1/4:ℝ) := mul_le_mul_of_nonneg_right hx.1 (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hrlo hp
  · change a x*(1+weakValue w x)^2≤9*C/4
    calc
      _ ≤ a x*(9/4:ℝ) := mul_le_mul_of_nonneg_left hrup hp
      _ ≤ C*(9/4:ℝ) := mul_le_mul_of_nonneg_right hx.2 (by norm_num)
      _ = _ := by ring

lemma gauge_test_integrand (a r U c F : ℝ) (du dw dF : R3) :
    inner ℝ ((r*a) • du-((U-c)*a) • dw) dF =
      a*inner ℝ du (dF+(r-1) • dF+F • dw)-
      a*inner ℝ dw ((U-c) • dF+F • du) := by
  simp only [inner_sub_left,real_inner_smul_left,inner_add_right,real_inner_smul_right]
  rw [real_inner_comm dw du]
  ring

theorem gauge_harmonic_of_weighted (a : R3 → ℝ)
    (ha : AEStronglyMeasurable a ballMeasure) (C : ℝ) (hC : 0≤C)
    (hb : ∀ᵐ x ∂ballMeasure, |a x|≤C)
    {u w v : H1} {M : ℝ} (hu : ∀ᵐ x ∂ballMeasure, |weakValue u x|≤M)
    (hw : ∀ᵐ x ∂ballMeasure, |weakValue w x|≤1/2)
    (huh : Harmonic a u) (c : ℝ) (hweighted : WeightedAnnihilation a w u c)
    (hflux : ∀ᵐ x ∂ballMeasure,
      gaugeCoefficient a w x • weakGradient v x=
      ((1+weakValue w x)*a x) • weakGradient u x-
        ((weakValue u x-c)*a x) • weakGradient w x) :
    Harmonic (gaugeCoefficient a w) v := by
  have hgb : ∀ᵐ x ∂ballMeasure, |gaugeCoefficient a w x|≤C*(9/4:ℝ) := by
    filter_upwards [hb,hw] with x hx hy
    have hsq : (1+weakValue w x)^2≤(9/4:ℝ) := by
      have hl := (abs_le.mp hy).1; have hu := (abs_le.mp hy).2; nlinarith
    rw [gaugeCoefficient,abs_mul,abs_of_nonneg (sq_nonneg (1+weakValue w x))]
    exact mul_le_mul hx hsq (sq_nonneg _) hC
  apply harmonic_of_compact_tests _ (gaugeCoefficient_aeStronglyMeasurable a ha w)
    (C*(9/4:ℝ)) (mul_nonneg hC (by norm_num)) hgb v
  intro f hf hfc hfs
  let φ := smoothH1 f hf
  obtain ⟨N,hN,hφ⟩ := smoothH1_bounded f hf
  have hφ0 : φ∈H10 := smoothH1_mem_H10 f hf hfc hfs
  have hs := H1_sub_constant_spec u c
  have huc : ∀ᵐ x ∂ballMeasure, |weakValue (u-constantH1 c) x|≤M+|c| := by
    filter_upwards [hu,hs.1] with x hx hy
    rw [hy]; exact (abs_sub _ _).trans (add_le_add hx (le_refl _))
  obtain ⟨p₁,_,hp₁,hp₁0⟩ := exists_H1_product hw hφ
  obtain ⟨p₂,_,hp₂,_⟩ := exists_H1_product huc hφ
  have hρφ : φ+p₁∈H10 := H10.add_mem hφ0 (hp₁0 hφ0)
  have he₁ : energy a u (φ+p₁)=0 := huh _ hρφ
  have he₂ : energy a w p₂=0 := by
    calc
      _ = ∫ x, a x*inner ℝ (weakGradient w x)
        ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure := by
          apply integral_congr_ae
          filter_upwards [hp₂,hs.1,hs.2,smoothH1_value f hf,smoothH1_gradient f hf]
            with x hx hy hz hv hg
          rw [hx,hy,hz,hv,hg]
      _ = 0 := hweighted f hf hfc hfs
  have he : energy (gaugeCoefficient a w) v φ=energy a u (φ+p₁)-energy a w p₂ := by
    unfold energy
    rw [←integral_sub (energy_integrable a ha C hC hb u (φ+p₁))
      (energy_integrable a ha C hC hb w p₂)]
    apply integral_congr_ae
    filter_upwards [hflux,hp₁,hp₂,hs.1,hs.2,weakGradient_add φ p₁]
      with x hx h₁ h₂ hv hg ha
    rw [←real_inner_smul_left,hx,ha,Pi.add_apply,h₁,h₂,hv,hg]
    convert gauge_test_integrand (a x) (1+weakValue w x) (weakValue u x) c
      (weakValue φ x) (weakGradient u x) (weakGradient w x) (weakGradient φ x) using 1
    simp only [add_sub_cancel_left,add_assoc,φ]
  rw [he,he₁,he₂,sub_zero]

end ScalarConductivity

end
end

end OAI
