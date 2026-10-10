import Mathlib
import OAI.Geometry.CAT0Fillings.Minimizers.CriticalEnergy

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer

lemma abs_power_derivative_bound {p s a b : ℝ} (hp : 2 < p) (hs : |s| ≤ 1) :
    |(p*|a+s*b|^(p-2)*(a+s*b))*b| ≤ p*(|a|+|b|)^p := by
  have hp0 : 0 ≤ p := by linarith
  have hr : 0 ≤ p-2 := by linarith
  let R := |a|+|b|
  have hR : 0 ≤ R := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb : |b| ≤ R := le_add_of_nonneg_left (abs_nonneg _)
  have ha : |a+s*b| ≤ R := by
    have hh := abs_add_le a (s*b)
    rw [abs_mul] at hh
    have := mul_le_mul_of_nonneg_right hs (abs_nonneg b)
    dsimp [R]
    linarith
  rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hp0,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hh := mul_le_mul (mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) ha hr) hp0)
    ha (abs_nonneg _) (by positivity)) hb (abs_nonneg _) (by positivity)
  apply hh.trans_eq
  change p*R^(p-2)*R*R = p*R^p
  by_cases hR0 : R = 0
  · simp only [hR0,Real.zero_rpow (by linarith : p ≠ 0),mul_zero]
  · have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    rw [mul_assoc,mul_assoc]
    congr 1
    rw [show R*R = R^(2:ℝ) by rw [Real.rpow_two,pow_two],←Real.rpow_add hRp]
    congr 1
    ring

lemma integral_abs_power_variation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : α → ℝ} {p : ℝ} (hp : 2 < p)
    (hu : MemLp u (ENNReal.ofReal p) μ) (hv : MemLp v (ENNReal.ofReal p) μ) :
    Integrable (fun x => (p*|u x|^(p-2)*u x)*v x) μ ∧
      HasDerivAt (fun s : ℝ => ∫ x, |u x+s*v x|^p ∂μ)
        (∫ x, (p*|u x|^(p-2)*u x)*v x ∂μ) 0 := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ p-2 := by linarith
  have huM := hu.aestronglyMeasurable
  have hvM := hv.aestronglyMeasurable
  have hm (s : ℝ) : AEStronglyMeasurable (fun x => |u x+s*v x|^p) μ :=
    (Real.continuous_rpow_const hp0.le).comp_aestronglyMeasurable ((huM.add (hvM.const_mul s)).norm)
  have hi : Integrable (fun x => |u x|^p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le,Real.norm_eq_abs] using
      hu.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
  have hb : Integrable (fun x => p*(|u x|+|v x|)^p) μ := by
    have hh := (hu.norm.add hv.norm).integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
    simp only [ENNReal.toReal_ofReal hp0.le,Real.norm_eq_abs,Pi.add_apply] at hh
    have hab (x : α) : |(|u x|+|v x|)| = |u x|+|v x| := abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
    simp only [hab] at hh
    exact hh.const_mul p
  have hdm : AEStronglyMeasurable (fun x => (p*|u x|^(p-2)*u x)*v x) μ :=
    ((((Real.continuous_rpow_const hr).comp_aestronglyMeasurable huM.norm).const_mul p).mul huM).mul hvM
  have hd (x : α) (s : ℝ) : HasDerivAt (fun t : ℝ => |u x+t*v x|^p)
      ((p*|u x+s*v x|^(p-2)*(u x+s*v x))*v x) s := by
    simpa only [one_mul,Function.comp_def,id_eq] using (hasDerivAt_abs_rpow (u x+s*v x) (by linarith : 1 < p)).comp s
      (((hasDerivAt_id s).mul_const (v x)).const_add (u x))
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => |u x+s*v x|^p)
    (F' := fun s x => (p*|u x+s*v x|^(p-2)*(u x+s*v x))*v x)
    (bound := fun x => p*(|u x|+|v x|)^p)
    (s := Ioo (-1:ℝ) 1) (x₀ := (0:ℝ))
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall hm) (by simpa only [zero_mul,add_zero] using hi)
    (by simpa only [zero_mul,add_zero] using hdm)
    (Eventually.of_forall fun x s hs => by
      rw [Real.norm_eq_abs]
      exact abs_power_derivative_bound hp (abs_le.mpr ⟨hs.1.le,hs.2.le⟩)) hb
    (Eventually.of_forall fun x s _ => hd x s)
  simpa only [zero_mul,add_zero] using hh

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace H] [SeparableSpace H] in
lemma criticalMass_variation (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 2 < p)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ) (u v : H) :
    Integrable (fun x => (p*|(I u) x|^(p-2)*(I u) x)*(I v) x) μ ∧
    HasDerivAt (fun s : ℝ => criticalMass I p (u+s • v))
      (∫ x, (p*|(I u) x|^(p-2)*(I u) x)*(I v) x ∂μ) 0 := by
  obtain ⟨hi,hd⟩ := integral_abs_power_variation hp (hm u) (hm v)
  refine ⟨hi,?_⟩
  have he : (fun s : ℝ => criticalMass I p (u+s • v)) =
      (fun s : ℝ => ∫ x, |(I u) x+s*(I v) x|^p ∂μ) := by
    funext s
    dsimp [criticalMass]
    rw [map_add,map_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (I u) (s • I v),Lp.coeFn_smul s (I v)] with x ha hs
    rw [ha,Pi.add_apply,hs]
    rfl
  rw [he]
  exact hd

omit [CompleteSpace H] [SeparableSpace H] [CompleteSpace F] in
lemma energy_variation (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    (A B : ℝ) (u v : H) :
    HasDerivAt (fun s : ℝ => energy I G A B (u+s • v))
      (2*(A*inner ℝ (G u) (G v)+B*inner ℝ (I u) (I v))) 0 := by
  have hG : HasDerivAt (fun s : ℝ => G u+s • G v) (G v) 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const (G v)).const_add (G u)
  have hI : HasDerivAt (fun s : ℝ => I u+s • I v) (I v) 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const (I v)).const_add (I u)
  have hh := (hG.norm_sq.const_mul A).add (hI.norm_sq.const_mul B)
  simp only [zero_smul,add_zero] at hh
  convert hh using 1 <;> try rfl
  · funext s
    simp only [energy,map_add,map_smul,Pi.add_apply]
  · ring

omit [CompleteSpace H] [SeparableSpace H] [CompleteSpace F] in
lemma critical_euler (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    (A B : ℝ) {p : ℝ} (hp : 2 < p)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ) (u : H)
    (hu : criticalNorm I p u = 1)
    (hmin : ∀ w, energy I G A B u*(criticalNorm I p w)^2 ≤ energy I G A B w)
    (v : H) :
    A*inner ℝ (G u) (G v)+B*inner ℝ (I u) (I v) =
      energy I G A B u * (∫ x, |(I u) x|^(p-2)*(I u) x*(I v) x ∂μ) := by
  have hp0 : 0 < p := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hmass : criticalMass I p u = 1 := by rw [criticalMass_eq I hp0,hu,Real.one_rpow]
  obtain ⟨hi,hD⟩ := criticalMass_variation I hp hm u v
  have heint : (∫ x, (p*|(I u) x|^(p-2)*(I u) x)*(I v) x ∂μ) =
      p*(∫ x, |(I u) x|^(p-2)*(I u) x*(I v) x ∂μ) := by
    rw [←integral_const_mul]
    congr 1
    funext x
    ring
  rw [heint] at hD
  have hDr := hD.rpow_const (p := 2/p) (Or.inl (by simpa only [zero_smul,add_zero,hmass] using (one_ne_zero : (1:ℝ) ≠ 0)))
  simp only [zero_smul,add_zero,hmass,Real.one_rpow] at hDr
  let f := fun s : ℝ => energy I G A B (u+s • v)-energy I G A B u*criticalMass I p (u+s • v)^(2/p)
  have hf0 : f 0 = 0 := by simp only [f,zero_smul,add_zero,hmass,Real.one_rpow,mul_one,sub_self]
  have hminf : IsLocalMin f 0 := by
    apply Eventually.of_forall
    intro s
    rw [hf0]
    exact sub_nonneg.mpr (by simpa only [criticalNorm_sq I hp0] using hmin (u+s • v))
  have hd := (energy_variation I G A B u v).sub (hDr.const_mul (energy I G A B u))
  have he := hminf.hasDerivAt_eq_zero hd
  field_simp at he
  nlinarith

end CAT0Fillings.AnalyticMinimizer
end

end OAI
