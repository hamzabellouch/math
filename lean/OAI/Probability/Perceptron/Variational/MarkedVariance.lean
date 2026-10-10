import Mathlib
import OAI.Probability.Perceptron.Variational.CompactTripleGG

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory Set ProbabilityTheory
open scoped BoundedContinuousFunction NNReal ContDiff

lemma bounded_continuous_test_extend {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsFiniteMeasure P] (p : Ω→E) (hp : Measurable p)
    (Z : Ω→ℝ) (hZ : Measurable Z) {C : ℝ} (hC : 0≤C) (hb : ∀ x,|Z x|≤C)
    (hz : ∀ F : E→ᵇℝ,(∫ x,F (p x)*Z x ∂P)=0)
    (a : E→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (haB : ∀ r,|a r|≤A) :
    (∫ x,a (p x)*Z x ∂P)=0 := by
  have hmap : MeasurePreserving p P (P.map p) := ⟨hp,rfl⟩
  have hai : Integrable a (P.map p) := Integrable.of_bound ha.aestronglyMeasurable A
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using haB x)
  have hap : Integrable (fun x => a (p x)*Z x) P :=
    Integrable.of_bound ((ha.comp hp).mul hZ).aestronglyMeasurable (A*C)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (haB _) (hb x) (abs_nonneg _) hA)
  have he : |∫ x,a (p x)*Z x ∂P|≤0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := ε/(C+1)
    have hδ : 0<δ := div_pos hε (by linarith)
    obtain ⟨F,hF,hFi⟩ := hai.exists_boundedContinuous_integral_sub_le hδ
    have hiF : Integrable (fun x => F (p x)*Z x) P :=
      Integrable.of_bound ((F.measurable.comp hp).mul hZ).aestronglyMeasurable (‖F‖*C)
        (ae_of_all _ fun x => by
          simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (F.norm_coe_le_norm _) (hb x) (abs_nonneg _) (norm_nonneg F))
    have hdif : Integrable (fun x => a (p x)-F (p x)) P :=
      hmap.integrable_comp_of_integrable (hai.sub hFi)
    have hrep : (∫ x,a (p x)*Z x ∂P)=(∫ x,(a (p x)-F (p x))*Z x ∂P) := by
      simp_rw [sub_mul]
      rw [integral_sub hap hiF,hz F,sub_zero]
    have happrox : (∫ x,|a (p x)-F (p x)| ∂P)≤δ := by
      have hm := integral_map (μ := P) hp.aemeasurable ((ha.sub F.measurable).abs.aestronglyMeasurable)
      change (∫ x, |a x - F x| ∂P.map p) = (∫ x, |a (p x) - F (p x)| ∂P) at hm
      rw [←hm]
      simpa only [Real.norm_eq_abs] using hF
    have hbound : |∫ x,(a (p x)-F (p x))*Z x ∂P|≤(∫ x,|a (p x)-F (p x)| * C ∂P) := by
      rw [←Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hdif.abs.mul_const C)
      exact ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
    rw [hrep]
    refine hbound.trans ?_
    rw [integral_mul_const]
    have hmul := mul_le_mul_of_nonneg_right happrox hC
    have hc : δ*(C+1)=ε := div_mul_cancel₀ ε (by linarith)
    linarith
  exact abs_nonpos_iff.mp he

lemma marked_zero_variance {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsFiniteMeasure P] (p : Ω→E) (hp : Measurable p)
    (b : Ω→ℝ) (hb : Measurable b) (a : E→ℝ) (ha : Measurable a)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B) (haB : ∀ r,|a r|≤A) (hbB : ∀ x,|b x|≤B)
    (hfirst : ∀ F : E→ᵇℝ,(∫ x,F (p x)*b x ∂P)=(∫ x,F (p x)*a (p x) ∂P))
    (hsecond : (∫ x,(b x)^2 ∂P)=(∫ x,(a (p x))^2 ∂P)) :
    ∀ᵐ x ∂P,b x=a (p x) := by
  let Z := fun x => b x-a (p x)
  have hZm : Measurable Z := hb.sub (ha.comp hp)
  have hZb (x) : |Z x|≤B+A := (abs_sub _ _).trans (add_le_add (hbB x) (haB _))
  have hi (F : E→ᵇℝ) : Integrable (fun x => F (p x)*b x) P :=
    Integrable.of_bound ((F.measurable.comp hp).mul hb).aestronglyMeasurable (‖F‖*B)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (F.norm_coe_le_norm _) (hbB x) (abs_nonneg _) (norm_nonneg F))
  have hi' (F : E→ᵇℝ) : Integrable (fun x => F (p x)*a (p x)) P :=
    Integrable.of_bound ((F.measurable.comp hp).mul (ha.comp hp)).aestronglyMeasurable (‖F‖*A)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (F.norm_coe_le_norm _) (haB _) (abs_nonneg _) (norm_nonneg F))
  have hz (F : E→ᵇℝ) : (∫ x,F (p x)*Z x ∂P)=0 := by
    simp only [Z,mul_sub]
    rw [integral_sub (hi F) (hi' F),hfirst F,sub_self]
  have hcross := bounded_continuous_test_extend P p hp Z hZm (add_nonneg hB hA) hZb hz a ha hA haB
  have hi2 : Integrable (fun x => (b x)^2) P :=
    Integrable.of_bound (hb.pow_const 2).aestronglyMeasurable (B^2)
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hbB x) 2)
  have hi2' : Integrable (fun x => (a (p x))^2) P :=
    Integrable.of_bound ((ha.comp hp).pow_const 2).aestronglyMeasurable (A^2)
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (haB _) 2)
  have hiZ : Integrable (fun x => a (p x)*Z x) P :=
    Integrable.of_bound ((ha.comp hp).mul hZm).aestronglyMeasurable (A*(B+A))
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (haB _) (hZb x) (abs_nonneg _) hA)
  have hiZ2 : Integrable (fun x => (Z x)^2) P :=
    Integrable.of_bound (hZm.pow_const 2).aestronglyMeasurable ((B+A)^2)
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hZb x) 2)
  have hzero : (∫ x,(Z x)^2 ∂P)=0 := by
    have he (x) : (Z x)^2=(b x)^2-(a (p x))^2-2*(a (p x)*Z x) := by dsimp [Z]; ring
    simp_rw [he]
    rw [integral_sub (show Integrable (fun x => (b x)^2-(a (p x))^2) P from hi2.sub hi2') (hiZ.const_mul 2),integral_sub hi2 hi2',integral_const_mul,
      hsecond,hcross]
    ring
  have hh := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (Z x)) hiZ2).mp hzero
  filter_upwards [hh] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

lemma tangent_wronskian_test {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure Time) [IsProbabilityMeasure ν]
    (r s t : Ω→Time) (hr : Measurable r) (hs : Measurable s) (ht : Measurable t)
    (hmarg : P.map r=ν)
    (hlaws : P.map (fun x=>(r x,s x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (hlawt : P.map (fun x=>(r x,t x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (htri : ∀ᵐ x ∂P,UltrametricTriangle (r x:ℝ) (s x:ℝ) (t x:ℝ))
    (a : Time→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (hab : ∀ x,|a x|≤A)
    (G : ℝ→ᵇℝ) :
    (∫ x,G (r x)*((r x:ℝ)-a (r x)*(1-(r x:ℝ)^2)+2*a (s x)*((t x:ℝ)-(r x:ℝ)*(s x:ℝ))) ∂P)=
      ∫ x,G x*((x:ℝ)-a x*sphereTail ν x+∫ y,sphereKernel x y*a y ∂ν) ∂ν := by
  let H : Time×Time→ℝ := fun p=>G p.1*sphereKernel p.1 p.2*a p.2
  let J : Time×Time→ℝ := fun p=>G p.1*a p.1*max ((p.2:ℝ)-p.1) 0
  let B : Time→ℝ := fun x=>G x*((x:ℝ)-a x*(1-(x:ℝ)^2))
  have hH : Measurable H := by dsimp [H]; unfold sphereKernel; fun_prop
  have hJ : Measurable J := by dsimp [J]; fun_prop
  have hB : Measurable B := by dsimp [B]; fun_prop
  have hbH (p : Time×Time) : |H p|≤‖G‖*A := by
    dsimp [H]
    rw [abs_mul,abs_mul]
    have h := mul_le_mul (G.norm_coe_le_norm (p.1:ℝ)) (sphereKernel_abs_le_one p.1 p.2) (abs_nonneg _) (norm_nonneg G)
    simp only [mul_one] at h
    exact mul_le_mul h (hab _) (abs_nonneg _) (norm_nonneg G)
  have hbJ (p : Time×Time) : |J p|≤‖G‖*A := by
    dsimp [J]
    rw [abs_mul,abs_mul]
    have h := mul_le_mul (G.norm_coe_le_norm (p.1:ℝ)) (hab p.1) (abs_nonneg _) (norm_nonneg G)
    simpa only [mul_one,Real.norm_eq_abs] using mul_le_mul h (time_pospart_le_one p.1 p.2) (abs_nonneg _) (mul_nonneg (norm_nonneg G) hA)
  have hbB (x : Time) : |B x|≤‖G‖*(1+A) := by
    have hx : |1-(x:ℝ)^2|≤1 := by
      have hx2 : (x:ℝ)^2≤1 := by nlinarith [x.property.1,x.property.2]
      rw [abs_of_nonneg (sub_nonneg.mpr hx2)]
      nlinarith [sq_nonneg (x:ℝ)]
    have habx : |a x*(1-(x:ℝ)^2)|≤A := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul (hab x) hx (abs_nonneg _) hA
    have hb := (abs_sub (x:ℝ) (a x*(1-(x:ℝ)^2))).trans (add_le_add (time_abs_le_one x) habx)
    exact (abs_mul _ _).le.trans (mul_le_mul (G.norm_coe_le_norm _) hb (abs_nonneg _) (norm_nonneg G))
  have hiHp := boundedAbs_integrable P (fun x=>H (r x,s x)) (hH.comp (hr.prodMk hs)) _ (fun x=>hbH _)
  have hiJp := boundedAbs_integrable P (fun x=>J (r x,t x)) (hJ.comp (hr.prodMk ht)) _ (fun x=>hbJ _)
  have hiBp := boundedAbs_integrable P (fun x=>B (r x)) (hB.comp hr) _ (fun x=>hbB _)
  have hiB := boundedAbs_integrable ν B hB _ hbB
  have hiH := boundedAbs_integrable (ν.prod ν) H hH _ hbH
  have hiJ := boundedAbs_integrable (ν.prod ν) J hJ _ hbJ
  have hiHd := boundedAbs_integrable ν (fun x=>H (x,x)) (hH.comp (measurable_id.prodMk measurable_id)) _ (fun x=>hbH _)
  have hiJd := boundedAbs_integrable ν (fun x=>J (x,x)) (hJ.comp (measurable_id.prodMk measurable_id)) _ (fun x=>hbJ _)
  have heH := two_edge_integral P ν r s hr hs hlaws H hH _ hbH
  have heJ := two_edge_integral P ν r t hr ht hlawt J hJ _ hbJ
  have heB : (∫ x,B (r x) ∂P)=∫ x,B x ∂ν := by
    rw [←hmarg,integral_map hr.aemeasurable hB.aestronglyMeasurable]
  have hiBH : Integrable (fun x=>B (r x)+2*H (r x,s x)) P := hiBp.add (hiHp.const_mul 2)
  have hiHC : Integrable (fun x=>(∫ y,H (x,y) ∂ν)+H (x,x)) ν := hiH.integral_prod_left.add hiHd
  have hiJC : Integrable (fun x=>(∫ y,J (x,y) ∂ν)+J (x,x)) ν := hiJ.integral_prod_left.add hiJd
  have hiBC : Integrable (fun x=>B x+((∫ y,H (x,y) ∂ν)+H (x,x))) ν := hiB.add hiHC
  calc
    _ = ∫ x,B (r x)+2*H (r x,s x)+2*J (r x,t x) ∂P := by
      apply integral_congr_ae
      filter_upwards [htri] with x hx
      have he := sphereKernel_tangent_algebra (r x) (s x) (t x) hx a
      dsimp [B,H,J]
      calc
        _ = G (r x)*((r x:ℝ)-a (r x)*(1-(r x:ℝ)^2))+2*G (r x)*(a (s x)*((t x:ℝ)-(r x:ℝ)*(s x:ℝ))) := by ring
        _ = _ := by rw [he]; ring
    _ = (∫ x,B x ∂ν)+(∫ x,(∫ y,H (x,y) ∂ν)+H (x,x) ∂ν)+
        (∫ x,(∫ y,J (x,y) ∂ν)+J (x,x) ∂ν) := by
      rw [integral_add hiBH (hiJp.const_mul 2),
        integral_add hiBp (hiHp.const_mul 2),integral_const_mul,integral_const_mul,
        heB,heH,heJ,integral_add hiH.integral_prod_left hiHd,
        integral_add hiJ.integral_prod_left hiJd]
      ring
    _ = _ := by
      rw [←integral_add hiB hiHC,
        ←integral_add hiBC hiJC]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [B,H,J]
      simp_rw [mul_assoc (G x),integral_const_mul]
      rw [sphereTail_pospart]
      simp only [sphereKernel,min_self,sub_self,max_self,mul_zero,add_zero]
      ring

end SphericalPerceptronFreeEnergy
end

end OAI
