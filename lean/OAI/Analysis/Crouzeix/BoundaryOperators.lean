import Mathlib
import OAI.Analysis.Crouzeix.Fourier

namespace OAI

/-! Boundary Operators. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Boundary

local instance boundaryOperatorsFactOnePos : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma norm_integral_weight_sq_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} (w : α → ℝ) (u : α → E)
    (hw0 : ∀ᵐ t ∂μ, 0 ≤ w t) (hw : Integrable w μ)
    (hwu : Integrable (fun t => w t • u t) μ)
    (hwu2 : Integrable (fun t => w t * ‖u t‖ ^ 2) μ)
    (hw1 : ∫ t, w t ∂μ = 1) :
    ‖∫ t, w t • u t ∂μ‖ ^ 2 ≤ ∫ t, w t * ‖u t‖ ^ 2 ∂μ := by
  let v := ∫ t, w t • u t ∂μ
  have hi := integral_mono_ae (((hwu.const_inner v)).const_mul 2)
    ((hw.mul_const (‖v‖ ^ 2)).add hwu2) (hw0.mono fun t ht => by
      simp only [Pi.add_apply, real_inner_smul_right]
      have h := sq_nonneg ‖v - u t‖
      rw [norm_sub_sq_real] at h
      nlinarith [mul_nonneg ht h])
  have hv : ∫ t, ⟪v, w t • u t⟫_ℝ ∂μ = ‖v‖ ^ 2 := by
    rw [integral_inner hwu v]
    exact real_inner_self_eq_norm_sq v
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, hv, integral_add (hw.mul_const _) hwu2,
    integral_mul_const, hw1, one_mul] at hi
  linarith

abbrev CircleKernel := C(CircleSpace × CircleSpace, ℝ)

def kernelApply {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) (x : CircleSpace) : HS k :=
  ∫ y, m (x,y) • u y ∂circleMeasure

lemma boundaryLp_integrable {k : ℕ} (u : BoundaryL2 k) : Integrable u circleMeasure :=
  (Lp.memLp u).integrable (by norm_num)

lemma kernel_integrable {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) (x : CircleSpace) :
    Integrable (fun y => m (x,y) • u y) circleMeasure := by
  have hm : AEStronglyMeasurable (fun y => m (x,y)) circleMeasure :=
    (m.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  change Integrable ((fun y => m (x,y)) • (u : CircleSpace → HS k)) circleMeasure
  exact Integrable.bdd_smul (𝕜 := ℝ) (boundaryLp_integrable u) ‖m‖ hm
    (Filter.Eventually.of_forall fun y => m.norm_coe_le_norm (x,y))

lemma kernel_sq_integrable {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) (x : CircleSpace) :
    Integrable (fun y => m (x,y) * ‖u y‖ ^ 2) circleMeasure := by
  have hm : AEStronglyMeasurable (fun y => m (x,y)) circleMeasure :=
    (m.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact ((Lp.memLp u).norm.integrable_sq).bdd_mul hm
    (Filter.Eventually.of_forall fun y => m.norm_coe_le_norm (x,y))

lemma continuous_kernelApply {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) :
    Continuous (kernelApply m u) := by
  apply continuous_of_dominated (bound := fun y => ‖m‖ * ‖u y‖)
  · intro x
    exact (kernel_integrable m u x).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun y => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm (x,y)) (norm_nonneg _)
  · exact (boundaryLp_integrable u).norm.const_mul _
  · exact Filter.Eventually.of_forall fun y =>
      (m.continuous.comp (continuous_id.prodMk continuous_const)).smul continuous_const

def kernelLp {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) : BoundaryL2 k :=
  ContinuousMap.toLp 2 circleMeasure ℝ ⟨kernelApply m u, continuous_kernelApply m u⟩

lemma kernelLp_apply_ae {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) :
    kernelLp m u =ᵐ[circleMeasure] kernelApply m u := ContinuousMap.coeFn_toLp _ _

lemma norm_kernelApply_sq_le {k : ℕ} (m : CircleKernel)
    (hm : ∀ x, 0 ≤ m x) (hm1 : ∀ x, ∫ y, m (x,y) ∂circleMeasure = 1)
    (u : BoundaryL2 k) (x : CircleSpace) :
    ‖kernelApply m u x‖ ^ 2 ≤ ∫ y, m (x,y) * ‖u y‖ ^ 2 ∂circleMeasure := by
  apply norm_integral_weight_sq_le (μ := circleMeasure) (fun y => m (x,y)) u
    (Filter.Eventually.of_forall fun y => hm (x,y))
  · exact (m.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact kernel_integrable m u x
  · exact kernel_sq_integrable m u x
  · exact hm1 x

lemma kernel_sq_integrable_prod {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) :
    Integrable (fun z : CircleSpace × CircleSpace => m z * ‖u z.2‖ ^ 2)
      (circleMeasure.prod circleMeasure) :=
  (((Lp.memLp u).norm.integrable_sq).comp_snd circleMeasure).bdd_mul
    m.continuous.aestronglyMeasurable (Filter.Eventually.of_forall m.norm_coe_le_norm)

lemma norm_kernelLp_le {k : ℕ} (m : CircleKernel)
    (hm : ∀ x, 0 ≤ m x) (hm1 : ∀ x, ∫ y, m (x,y) ∂circleMeasure = 1)
    (hm2 : ∀ y, ∫ x, m (x,y) ∂circleMeasure = 1) (u : BoundaryL2 k) :
    ‖kernelLp m u‖ ≤ ‖u‖ := by
  have hs : ‖kernelLp m u‖ ^ 2 ≤ ‖u‖ ^ 2 := calc
    _ = ∫ x, ‖kernelLp m u x‖ ^ 2 ∂circleMeasure := lp_norm_sq_eq_integral _
    _ ≤ ∫ x, ∫ y, m (x,y) * ‖u y‖ ^ 2 ∂circleMeasure ∂circleMeasure := by
      apply integral_mono_ae ((Lp.memLp (kernelLp m u)).norm.integrable_sq)
        (kernel_sq_integrable_prod m u).integral_prod_left
      filter_upwards [kernelLp_apply_ae m u] with x hx
      rw [hx]
      exact norm_kernelApply_sq_le m hm hm1 u x
    _ = ∫ y, ∫ x, m (x,y) * ‖u y‖ ^ 2 ∂circleMeasure ∂circleMeasure :=
      integral_integral_swap (kernel_sq_integrable_prod m u)
    _ = ∫ y, ‖u y‖ ^ 2 ∂circleMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change (∫ x, m (x,y) * ‖u y‖ ^ 2 ∂circleMeasure) = ‖u y‖ ^ 2
        rw [integral_mul_const, hm2, one_mul]
    _ = ‖u‖ ^ 2 := (lp_norm_sq_eq_integral _).symm
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

lemma kernelLp_add {k : ℕ} (m : CircleKernel) (u v : BoundaryL2 k) :
    kernelLp m (u + v) = kernelLp m u + kernelLp m v := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae m (u+v), kernelLp_apply_ae m u, kernelLp_apply_ae m v,
    Lp.coeFn_add (kernelLp m u) (kernelLp m v)] with x huv hu hv hsum
  simp only [huv, hsum, Pi.add_apply, hu, hv]
  simp only [kernelApply]
  calc
    _ = ∫ y, m (x,y) • u y + m (x,y) • v y ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add u v] with y hy
      simp only [hy, Pi.add_apply, smul_add]
    _ = _ := integral_add (kernel_integrable m u x) (kernel_integrable m v x)

lemma kernelLp_smul {k : ℕ} (m : CircleKernel) (c : ℝ) (u : BoundaryL2 k) :
    kernelLp m (c • u) = c • kernelLp m u := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae m (c • u), kernelLp_apply_ae m u,
    Lp.coeFn_smul c (kernelLp m u)] with x hcu hu hsmul
  simp only [hcu, hsmul, Pi.smul_apply, hu]
  simp only [kernelApply]
  calc
    _ = ∫ y, c • (m (x,y) • u y) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c u] with y hy
      rw [hy]
      change m (x,y) • (c • u y) = c • (m (x,y) • u y)
      exact smul_comm _ _ _
    _ = _ := integral_smul c _

def kernelOperator {k : ℕ} (m : CircleKernel)
    (hm : ∀ x, 0 ≤ m x) (hm1 : ∀ x, ∫ y, m (x,y) ∂circleMeasure = 1)
    (hm2 : ∀ y, ∫ x, m (x,y) ∂circleMeasure = 1) :
    BoundaryL2 k →L[ℝ] BoundaryL2 k :=
  ({ toFun := kernelLp m
     map_add' := kernelLp_add m
     map_smul' := kernelLp_smul m } : BoundaryL2 k →ₗ[ℝ] BoundaryL2 k).mkContinuous 1
    (fun u => by
      change ‖kernelLp m u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using norm_kernelLp_le m hm hm1 hm2 u)

lemma norm_kernelOperator_le {k : ℕ} (m : CircleKernel)
    (hm : ∀ x, 0 ≤ m x) (hm1 : ∀ x, ∫ y, m (x,y) ∂circleMeasure = 1)
    (hm2 : ∀ y, ∫ x, m (x,y) ∂circleMeasure = 1) :
    ‖kernelOperator (k := k) m hm hm1 hm2‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖kernelLp m u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using norm_kernelLp_le m hm hm1 hm2 u

def transposeKernel (m : CircleKernel) : CircleKernel :=
  ⟨fun z => m z.swap, m.continuous.comp continuous_swap⟩

@[simp] lemma transposeKernel_apply (m : CircleKernel) (x y : CircleSpace) :
    transposeKernel m (x,y) = m (y,x) := rfl

@[simp] lemma transposeKernel_transposeKernel (m : CircleKernel) :
    transposeKernel (transposeKernel m) = m := by
  ext z
  rfl

lemma kernel_inner_integrable {k : ℕ} (m : CircleKernel) (u v : BoundaryL2 k) :
    Integrable (fun z : CircleSpace × CircleSpace => m z * ⟪u z.2, v z.1⟫_ℝ)
      (circleMeasure.prod circleMeasure) := by
  have hints : Integrable (fun z : CircleSpace × CircleSpace =>
      ‖v z.1‖ * ‖u z.2‖) (circleMeasure.prod circleMeasure) :=
    (boundaryLp_integrable v).norm.mul_prod (boundaryLp_integrable u).norm
  have hinner : Integrable (fun z : CircleSpace × CircleSpace => ⟪u z.2, v z.1⟫_ℝ)
      (circleMeasure.prod circleMeasure) := hints.mono'
    (((Lp.aestronglyMeasurable u).comp_snd).inner ((Lp.aestronglyMeasurable v).comp_fst))
    (Filter.Eventually.of_forall fun z => by
      simpa only [mul_comm] using norm_inner_le_norm (𝕜 := ℝ) (u z.2) (v z.1))
  exact hinner.bdd_mul m.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall m.norm_coe_le_norm)

lemma inner_kernelLp {k : ℕ} (m : CircleKernel) (u v : BoundaryL2 k) :
    ⟪kernelLp m u, v⟫_ℝ =
      ∫ x, ∫ y, m (x,y) * ⟪u y,v x⟫_ℝ ∂circleMeasure ∂circleMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernelLp_apply_ae m u] with x hx
  rw [hx]
  change ⟪∫ y, m (x,y) • u y ∂circleMeasure, v x⟫_ℝ = _
  calc
    _ = ⟪v x, ∫ y, m (x,y) • u y ∂circleMeasure⟫_ℝ := real_inner_comm _ _
    _ = ∫ y, ⟪v x, m (x,y) • u y⟫_ℝ ∂circleMeasure :=
      (integral_inner (kernel_integrable m u x) _).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change ⟪v x, m (x,y) • u y⟫_ℝ = m (x,y) * ⟪u y,v x⟫_ℝ
        rw [real_inner_smul_right, real_inner_comm]

lemma inner_kernelLp_swap {k : ℕ} (m : CircleKernel) (u v : BoundaryL2 k) :
    ⟪kernelLp m u, v⟫_ℝ = ⟪u, kernelLp (transposeKernel m) v⟫_ℝ := by
  conv_rhs => rw [real_inner_comm]
  rw [inner_kernelLp, inner_kernelLp]
  calc
    _ = ∫ y, ∫ x, m (x,y) * ⟪u y,v x⟫_ℝ ∂circleMeasure ∂circleMeasure :=
      integral_integral_swap (kernel_inner_integrable m u v)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change m (x,y) * ⟪u y,v x⟫_ℝ = transposeKernel m (y,x) * ⟪v x,u y⟫_ℝ
          rw [transposeKernel_apply, real_inner_comm]

lemma adjoint_kernelOperator {k : ℕ} (m : CircleKernel)
    (hm : ∀ x, 0 ≤ m x) (hm1 : ∀ x, ∫ y, m (x,y) ∂circleMeasure = 1)
    (hm2 : ∀ y, ∫ x, m (x,y) ∂circleMeasure = 1) :
    ContinuousLinearMap.adjoint (kernelOperator (k := k) m hm hm1 hm2) =
      kernelOperator (transposeKernel m) (fun z => hm z.swap) hm2 hm1 := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  change ⟪kernelLp (transposeKernel m) u,v⟫_ℝ = ⟪u,kernelLp m v⟫_ℝ
  simpa only [transposeKernel_transposeKernel] using inner_kernelLp_swap (transposeKernel m) u v

lemma kernelLp_star {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) :
    kernelLp m (lpStar u) = lpStar (kernelLp m u) := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae m (lpStar u), lpStar_apply_ae (kernelLp m u),
    kernelLp_apply_ae m u] with x hmu hstar hu
  rw [hmu, hstar, hu]
  change (∫ y, m (x,y) • lpStar u y ∂circleMeasure) =
    hsStar k (∫ y, m (x,y) • u y ∂circleMeasure)
  calc
    _ = ∫ y, hsStar k (m (x,y) • u y) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [lpStar_apply_ae u] with y hy
      rw [hy, map_smul]
      rfl
    _ = _ := (hsStar k).toContinuousLinearMap.integral_comp_comm (kernel_integrable m u x)

lemma kernel_integrable_prod {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) :
    Integrable (fun z : CircleSpace × CircleSpace => m z • u z.2)
      (circleMeasure.prod circleMeasure) := by
  change Integrable ((m : CircleSpace × CircleSpace → ℝ) • (fun z : CircleSpace × CircleSpace => u z.2))
    (circleMeasure.prod circleMeasure)
  exact Integrable.bdd_smul (𝕜 := ℝ) ((boundaryLp_integrable u).comp_snd circleMeasure)
    ‖m‖ m.continuous.aestronglyMeasurable (Filter.Eventually.of_forall m.norm_coe_le_norm)

lemma integral_kernelLp {k : ℕ} (m : CircleKernel)
    (hm2 : ∀ y, ∫ x, m (x,y) ∂circleMeasure = 1) (u : BoundaryL2 k) :
    (∫ x, kernelLp m u x ∂circleMeasure) = ∫ y, u y ∂circleMeasure := by
  calc
    _ = ∫ x, ∫ y, m (x,y) • u y ∂circleMeasure ∂circleMeasure :=
      integral_congr_ae (kernelLp_apply_ae m u)
    _ = ∫ y, ∫ x, m (x,y) • u y ∂circleMeasure ∂circleMeasure :=
      integral_integral_swap (kernel_integrable_prod m u)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change (∫ x, m (x,y) • u y ∂circleMeasure) = u y
        rw [integral_smul_const, hm2, one_smul]

lemma matrixMean_eq_integral {k : ℕ} (u : BoundaryL2 k) :
    matrixMean u = ofHS (∫ t, u t ∂circleMeasure) := by
  ext i j
  let L : HS k →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin k × Fin k => ℂ) (i,j)
  exact L.integral_comp_comm (boundaryLp_integrable u)

lemma matrixMean_kernelLp {k : ℕ} (m : CircleKernel)
    (hm2 : ∀ y, ∫ x, m (x,y) ∂circleMeasure = 1) (u : BoundaryL2 k) :
    matrixMean (kernelLp m u) = matrixMean u := by
  rw [matrixMean_eq_integral, integral_kernelLp m hm2, matrixMean_eq_integral]

lemma kernelLp_const {k : ℕ} (m : CircleKernel)
    (hm1 : ∀ x, ∫ y, m (x,y) ∂circleMeasure = 1) (u : BoundaryL2 k) (v : HS k)
    (hu : u =ᵐ[circleMeasure] fun _ => v) : kernelLp m u = u := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae m u, hu] with x hmu hx
  rw [hmu, hx]
  change (∫ y, m (x,y) • u y ∂circleMeasure) = v
  calc
    _ = ∫ y, m (x,y) • v ∂circleMeasure :=
      integral_congr_ae (hu.mono fun y hy => by rw [hy])
    _ = v := by rw [integral_smul_const, hm1, one_smul]

end CrouzeixHilbert.Boundary

end

end OAI
