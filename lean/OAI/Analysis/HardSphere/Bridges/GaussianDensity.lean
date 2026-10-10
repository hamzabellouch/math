import Mathlib
import OAI.Analysis.HardSphere.Bridges.GaussianPacking

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

def density (b : ℝ) (x : Point) : ℝ := (Real.sqrt (b/Real.pi))^3*kernel b x
lemma density_nonneg (b : ℝ) (x : Point) : 0 ≤ density b x := by unfold density kernel; positivity
lemma density_continuous (b : ℝ) : Continuous (density b) := by unfold density kernel square; fun_prop
lemma density_integrable {b : ℝ} (hb : 0<b) : Integrable (density b) volume :=
  (kernel_integrable hb).const_mul _
lemma density_integral {b : ℝ} (hb : 0<b) : (∫x,density b x)=1 := by
  unfold density
  rw [integral_const_mul,kernel_integral,←mul_pow,←Real.sqrt_mul (by positivity)]
  rw [show (b/Real.pi)*(Real.pi/b)=1 by field_simp]
  norm_num

lemma sum_density_le {m : ℕ} (q : Fin m → Point) (x : Point)
    {b ε δ : ℝ} (hb : 0<b) (hε : 0<ε) (hδ : 0<δ)
    (hδε : 4*δ≤ε) (hbd : b*δ^2≤1)
    (hsep : ∀i j, i≠j → ε^2 ≤ square (q i-q j)) :
    (∑i,density b (x-q i)) ≤ Real.exp 3*(Real.sqrt 2)^3/(2*δ)^3 := by
  have hs := mul_le_mul_of_nonneg_left (sum_kernel_le q x hb hε hδ hδε hsep)
    (show 0≤(Real.sqrt (b/Real.pi))^3 by positivity)
  have he : (Real.sqrt (b/Real.pi))^3*(Real.sqrt (Real.pi/(b/2)))^3=(Real.sqrt 2)^3 := by
    rw [←mul_pow,←Real.sqrt_mul (by positivity)]
    congr 2
    field_simp
  calc
    _ = (Real.sqrt (b/Real.pi))^3*(∑i,kernel b (x-q i)) := by simp only [density,Finset.mul_sum]
    _ ≤ _ := hs
    _ = Real.exp (3*b*δ^2)*(Real.sqrt 2)^3/(2*δ)^3 := by
      calc
        _ = Real.exp (3*b*δ^2)*((Real.sqrt (b/Real.pi))^3*(Real.sqrt (Real.pi/(b/2)))^3)/(2*δ)^3 := by ring
        _ = _ := by rw [he]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)

def packingConstant : ℝ := 8*Real.exp 3*(Real.sqrt 2)^3
lemma packingConstant_pos : 0<packingConstant := by unfold packingConstant; positivity

theorem density_packing {m : ℕ} (q : Fin m → Point) (x : Point)
    {b ε : ℝ} (hb : 0<b) (hε : 0<ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (q i-q j)) :
    (∑i,density b (x-q i)) ≤ packingConstant*(ε⁻¹^3+(Real.sqrt b)^3) := by
  let δ := min (ε/4) (Real.sqrt b)⁻¹
  have hsb := Real.sqrt_pos.mpr hb
  have hd : 0<δ := lt_min (by positivity) (by positivity)
  have hde : 4*δ≤ε := by have ht:=min_le_left (ε/4) (Real.sqrt b)⁻¹; dsimp only [δ]; linarith
  have hdb : b*δ^2≤1 := by
    have ht := min_le_right (ε/4) (Real.sqrt b)⁻¹
    have hm : Real.sqrt b*δ≤1 := by
      have := mul_le_mul_of_nonneg_left ht hsb.le
      simpa only [mul_inv_cancel₀ hsb.ne'] using this
    have hm2 := (sq_le_sq₀ (by positivity : 0≤Real.sqrt b*δ) zero_le_one).mpr hm
    simpa only [mul_pow,Real.sq_sqrt hb.le,one_pow] using hm2
  have hh := sum_density_le q x hb hε hd hde hdb hsep
  apply hh.trans
  have hs : 0≤Real.exp 3*(Real.sqrt 2)^3 := by positivity
  have hbound : (2*δ)⁻¹^3 ≤ 8*(ε⁻¹^3+(Real.sqrt b)^3) := by
    by_cases ht : ε/4≤(Real.sqrt b)⁻¹
    · have he : δ=ε/4 := min_eq_left ht
      rw [he]
      have he' : (2*(ε/4))⁻¹=2*ε⁻¹ := by field_simp; ring
      rw [he',mul_pow]
      nlinarith [show 0≤(Real.sqrt b)^3 by positivity]
    · have he : δ=(Real.sqrt b)⁻¹ := min_eq_right (le_of_not_ge ht)
      rw [he,mul_inv_rev,inv_inv,mul_pow]
      calc
        _ ≤ (Real.sqrt b)^3*8 := mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
        _ ≤ 8*(ε⁻¹^3+(Real.sqrt b)^3) := by
          rw [mul_comm ((Real.sqrt b)^3)]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by norm_num)

  unfold packingConstant
  rw [div_eq_mul_inv,←inv_pow]
  nlinarith [mul_le_mul_of_nonneg_left hbound hs]

def gaussianDensity (q : Point) (v : ℝ≥0) (x : Point) : ℝ := ∏j,gaussianPDFReal (q j) v (x j)
lemma gaussianDensity_nonneg (q : Point) (v : ℝ≥0) (x : Point) : 0≤gaussianDensity q v x :=
  Finset.prod_nonneg (fun _ _ ↦ gaussianPDFReal_nonneg _ _ _)
lemma gaussianDensity_integrable (q : Point) (v : ℝ≥0) : Integrable (gaussianDensity q v) volume :=
  Integrable.fintype_prod (fun j ↦ integrable_gaussianPDFReal (q j) v)
lemma gaussianDensity_measurable (q : Point) (v : ℝ≥0) : Measurable (gaussianDensity q v) := by
  unfold gaussianDensity
  fun_prop

theorem gaussian_pi_density (q : Point) {v : ℝ≥0} (hv : v≠0) :
    Measure.pi (fun j : Fin 3 ↦ gaussianReal (q j) v)=
      (volume : Measure Point).withDensity (fun x ↦ ENNReal.ofReal (gaussianDensity q v x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply' _ _,←ofReal_integral_eq_lintegral_ofReal
    (gaussianDensity_integrable q v).restrict (Eventually.of_forall (gaussianDensity_nonneg q v))]
  change ENNReal.ofReal (∫x,gaussianDensity q v x ∂(Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ))).restrict (univ.pi s))=_
  rw [Measure.restrict_pi_pi]
  unfold gaussianDensity
  rw [integral_fintype_prod_eq_prod]
  simp_rw [gaussianReal_apply_eq_integral _ hv]
  exact ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ integral_nonneg (gaussianPDFReal_nonneg (q j) v))

lemma gaussianDensity_eq (q x : Point) {v : ℝ≥0} (hv : v≠0) :
    gaussianDensity q v x=density ((2*(v:ℝ))⁻¹) (x-q) := by
  have hvp : 0<(v:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  unfold gaussianDensity gaussianPDFReal density
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have he : (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹=Real.sqrt ((2*(v:ℝ))⁻¹/Real.pi) := by
    rw [←Real.sqrt_inv]
    congr 1
    field_simp
  rw [he]
  congr 1
  rw [kernel_product]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  simp only [Pi.sub_apply]
  ring

lemma gaussian_pi_eq (q : Point) {v : ℝ≥0} (hv : v≠0) :
    Measure.pi (fun j : Fin 3 ↦ gaussianReal (q j) v)=
      (volume : Measure Point).withDensity (fun x ↦ ENNReal.ofReal (density ((2*(v:ℝ))⁻¹) (x-q))) := by
  rw [gaussian_pi_density q hv]
  congr 1
  funext x
  rw [gaussianDensity_eq q x hv]

end HardSphere.GaussianPacking

end

end OAI
