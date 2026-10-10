import OAI.Analysis.LiebThirring.PotentialSplit

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology

structure PotentialData (W : ℝ → ℝ) where
  measurable : AEStronglyMeasurable W volume
  nonneg : ∀ᵐ x, 0 ≤ W x
  b : ℝ
  b_nonneg : 0 ≤ b
  V : ℝ → ℝ
  V_nonneg : ∀ x, 0 ≤ V x
  V_integrable : Integrable V
  V_small : (∫ x, V x) ≤ 1/32
  decomp : ∀ x, ‖W x‖ ≤ b+V x

def potentialData {γ : ℝ} {W : ℝ → ℝ} (hγ : 1/2 < γ) (hW : Admissible γ W) :
    PotentialData W := Classical.choice (by
  obtain ⟨b,hb,V,hV,hVI,hVs,hD⟩ := potential_decomposition hγ hW (ε := 1/32) (by norm_num)
  exact ⟨⟨hW.2.aestronglyMeasurable,hW.1,b,hb,V,hV,hVI,hVs,hD⟩⟩)

lemma memLp_integral_norm_sq {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    (∫ x, ‖f x‖^2) = ‖hf.toLp f‖^2 := by
  rw [L2_norm_sq_eq_integral]
  exact integral_congr_ae (hf.coeFn_toLp.symm.mono (fun x hx ↦ by simp only [hx]))

lemma potential_quadratic_bound {W : ℝ → ℝ} (d : PotentialData W) (u : H1) :
    Integrable (fun x ↦ ‖W x‖*‖u.val x‖^2) ∧
    (∫ x, ‖W x‖*‖u.val x‖^2) ≤
      (d.b+1/4)*‖u.val_memLp.toLp u.val‖^2+(1/4)*‖u.grad_memLp.toLp u.grad‖^2 := by
  let C := 8*(‖u.val_memLp.toLp u.val‖^2+‖u.grad_memLp.toLp u.grad‖^2)
  have hC : 0 ≤ C := by positivity
  have hdom : Integrable (fun x ↦ d.b*‖u.val x‖^2+d.V x*C) :=
    ((u.val_memLp.integrable_norm_pow (by norm_num)).const_mul d.b).add
      (d.V_integrable.mul_const C)
  have hle : ∀ᵐ x, ‖W x‖*‖u.val x‖^2 ≤ d.b*‖u.val x‖^2+d.V x*C := by
    filter_upwards [h1_ae_sq_bound u] with x hx
    calc
      _ ≤ (d.b+d.V x)*‖u.val x‖^2 := mul_le_mul_of_nonneg_right (d.decomp x) (sq_nonneg _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hx (d.V_nonneg x)]
  have hi : Integrable (fun x ↦ ‖W x‖*‖u.val x‖^2) := hdom.mono'
    (d.measurable.norm.mul (u.val_memLp.aestronglyMeasurable.norm.pow 2))
    (hle.mono (fun x hx ↦ by simpa only [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))] using hx))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x, (d.b*‖u.val x‖^2+d.V x*C) := integral_mono_ae hi hdom hle
    _ = d.b*‖u.val_memLp.toLp u.val‖^2+(∫ x, d.V x)*C := by
      rw [integral_add ((u.val_memLp.integrable_norm_pow (by norm_num)).const_mul d.b)
        (d.V_integrable.mul_const C),integral_const_mul,integral_mul_const,memLp_integral_norm_sq]
    _ ≤ d.b*‖u.val_memLp.toLp u.val‖^2+(1/32)*C :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right d.V_small hC)
    _ = _ := by dsimp [C]; ring

def weightedVal {W : ℝ → ℝ} (_d : PotentialData W) (u : H1C) (x : ℝ) : ℂ :=
  (Real.sqrt ‖W x‖ : ℂ)*valL u x

lemma weightedVal_norm_sq {W : ℝ → ℝ} (d : PotentialData W) (u : H1C) (x : ℝ) :
    ‖weightedVal d u x‖^2 = ‖W x‖*‖valL u x‖^2 := by
  simp only [weightedVal,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (norm_nonneg _)]

lemma weightedVal_memLp {W : ℝ → ℝ} (d : PotentialData W) (u : H1C) :
    MemLp (weightedVal d u) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Real.continuous_sqrt.comp_aestronglyMeasurable d.measurable.norm)).mul
      (Lp.aestronglyMeasurable (valL u)))).mpr
  have h := (potential_quadratic_bound d (toH1 u)).1
  change Integrable (fun x ↦ ‖W x‖*‖valL u x‖^2) at h
  simpa only [weightedVal_norm_sq] using h

def weightedLM {W : ℝ → ℝ} (d : PotentialData W) : H1C →ₗ[ℂ] L2C where
  toFun u := (weightedVal_memLp d u).toLp (weightedVal d u)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(weightedVal_memLp d (u+v)).coeFn_toLp,
      (weightedVal_memLp d u).coeFn_toLp,(weightedVal_memLp d v).coeFn_toLp,
      Lp.coeFn_add ((weightedVal_memLp d u).toLp (weightedVal d u))
        ((weightedVal_memLp d v).toLp (weightedVal d v)),
      Lp.coeFn_add (valL u) (valL v)] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1,h4,h2,h3]
    simp only [weightedVal,map_add]
    rw [h5,mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(weightedVal_memLp d (c • u)).coeFn_toLp,
      (weightedVal_memLp d u).coeFn_toLp,
      Lp.coeFn_smul c ((weightedVal_memLp d u).toLp (weightedVal d u)),
      Lp.coeFn_smul c (valL u)] with x h1 h2 h3 h4
    simp only [Pi.smul_apply] at h3 h4
    simp only [RingHom.id_apply]
    rw [h1,h3,h2]
    simp only [weightedVal,map_smul]
    rw [h4]
    simp only [smul_eq_mul]
    ring

lemma weightedLM_norm_sq {W : ℝ → ℝ} (d : PotentialData W) (u : H1C) :
    ‖weightedLM d u‖^2 ≤ (d.b+1/4)*‖valL u‖^2+(1/4)*‖gradL u‖^2 := by
  change ‖(weightedVal_memLp d u).toLp (weightedVal d u)‖^2 ≤ _
  rw [← memLp_integral_norm_sq]
  simp only [weightedVal_norm_sq]
  have h := (potential_quadratic_bound d (toH1 u)).2
  simp only [toLp_toH1,grad_toLp_toH1] at h
  exact h

lemma h1_norm_sq (u : H1C) : ‖u‖^2 = ‖valL u‖^2+‖gradL u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

lemma weightedLM_bound {W : ℝ → ℝ} (d : PotentialData W) (u : H1C) :
    ‖weightedLM d u‖ ≤ Real.sqrt (d.b+1)*‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by linarith [d.b_nonneg]),h1_norm_sq]
  have h := weightedLM_norm_sq d u
  nlinarith [mul_nonneg d.b_nonneg (sq_nonneg ‖gradL u‖)]

def weightedL {W : ℝ → ℝ} (d : PotentialData W) : H1C →L[ℂ] L2C :=
  (weightedLM d).mkContinuous (Real.sqrt (d.b+1)) (weightedLM_bound d)

end SharpLiebThirring.OperatorProof

end

end OAI
