import OAI.MathematicalPhysics.AlternatingFlow.Analytic

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Analytic
noncomputable section

lemma spatial_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) : spatial (fun _ => 0) F = F := by simp [spatial]

lemma spatial_single {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (i : Fin 3) (r : ℕ) :
    spatial (fun j => if j = i then r else 0) F = (dx i)^[r] F := by
  fin_cases i <;> simp [spatial]

lemma h_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) {k : ℕ} {T t : ℝ} (hF : ContinuousInH k F T)
    (ht : t ∈ Set.Icc 0 T) : MemLp (F t) 2 (volume : Measure Space) := by
  obtain ⟨g, _, hg⟩ := hF (fun _ => 0) (by simp)
  have hm := (Lp.memLp (g t)).ae_eq (hg t ht)
  simpa only [spatial_zero] using hm

lemma h_dx_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) {k : ℕ} {T t : ℝ} (hF : ContinuousInH k F T) (hk : 1 ≤ k)
    (ht : t ∈ Set.Icc 0 T) (i : Fin 3) : MemLp (dx i F t) 2 (volume : Measure Space) := by
  obtain ⟨g, _, hg⟩ := hF (fun j => if j = i then 1 else 0) (by simpa using hk)
  have hm := (Lp.memLp (g t)).ae_eq (hg t ht)
  simpa only [spatial_single, Function.iterate_one, Function.comp_apply] using hm

lemma h_dxx_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) {T t : ℝ} (hF : ContinuousInH 2 F T)
    (ht : t ∈ Set.Icc 0 T) (i : Fin 3) : MemLp (dx i (dx i F) t) 2 (volume : Measure Space) := by
  obtain ⟨g, _, hg⟩ := hF (fun j => if j = i then 2 else 0) (by simp)
  have hm := (Lp.memLp (g t)).ae_eq (hg t ht)
  simpa only [spatial_single, Function.iterate_succ_apply, Function.iterate_zero_apply] using hm

lemma L2_inner_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : Space → E} (hf : MemLp f 2 (volume : Measure Space)) (hg : MemLp g 2 volume) :
    Integrable (fun x => inner ℝ (f x) (g x)) volume := by
  apply (hf.norm.integrable_mul hg.norm).mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => norm_inner_le_norm (f x) (g x))

lemma L2_bounded_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} {a : Space → ℝ} (hf : MemLp f 2 (volume : Measure Space))
    (ha : AEStronglyMeasurable a volume) (C : ℝ) (hC : ∀ x, ‖a x‖ ≤ C) :
    MemLp (fun x => a x • f x) 2 volume := by
  apply hf.of_le_mul (ha.smul hf.aestronglyMeasurable) (c := C)
  filter_upwards [] with x
  change ‖a x • f x‖ ≤ C * ‖f x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

lemma L2_coord {f : Space → Space} (hf : MemLp f 2 (volume : Measure Space)) (i : Fin 3) :
    MemLp (fun x => f x i) 2 volume :=
  hf.continuousLinearMap_comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i)

lemma d_coord (f : Space → Space) (hf : Differentiable ℝ f) (i j : Fin 3) (x : Space) :
    Spatial.d i (fun x => f x j) x = Spatial.d i f x j := by
  have hd := (Spatial.coord_hasFDeriv j (f x)).comp x (hf x).hasFDerivAt
  change fderiv ℝ (fun x => f x j) x (e i) = _
  change fderiv ℝ ((fun x : Space => x j) ∘ f) x (e i) = _
  rw [hd.fderiv]
  rfl

lemma sum_basis (x : Space) : ∑ i : Fin 3, x i • e i = x := by
  ext j
  simp [WithLp.ofLp_sum, Spatial.e_apply]

lemma directional_sum (f : Space → Space) (x v : Space) :
    fderiv ℝ f x v = ∑ i : Fin 3, v i • Spatial.d i f x := by
  conv_lhs => rw [← sum_basis v]
  simp [Spatial.d, map_sum]

lemma L2_directional {f v : Space → Space}
    (hd : ∀ i, MemLp (Spatial.d i f) 2 (volume : Measure Space))
    (hv : AEStronglyMeasurable v volume) (C : ℝ) (hC : ∀ x, ‖v x‖ ≤ C) :
    MemLp (fun x => fderiv ℝ f x (v x)) 2 volume := by
  simp_rw [directional_sum]
  apply memLp_finsetSum
  intro i _
  apply L2_bounded_smul (hd i)
    (((Spatial.coord_smooth i).continuous.comp_aestronglyMeasurable hv)) C
  intro x
  exact (PiLp.norm_apply_le (v x) i).trans (hC x)

lemma diffusion_identity (w : Space → Space) (i : Fin 3)
    (hw : Differentiable ℝ w) (hdw : Differentiable ℝ (Spatial.d i w))
    (hm : MemLp w 2 (volume : Measure Space)) (hdm : MemLp (Spatial.d i w) 2 volume)
    (hddm : MemLp (Spatial.d i (Spatial.d i w)) 2 volume) :
    (∫ x : Space, inner ℝ (w x) (Spatial.d i (Spatial.d i w) x)) =
      -(∫ x : Space, ‖Spatial.d i w x‖ ^ 2) := by
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := (volume : Measure Space)) (B := innerSL ℝ) (v := e i)
    (f := w) (g := Spatial.d i w) (L2_inner_integrable hdm hdm)
    (L2_inner_integrable hm hddm) (L2_inner_integrable hm hdm)
    (fun x _ => hw x) (fun x _ => hdw x)
  change (∫ x : Space, inner ℝ (w x) (Spatial.d i (Spatial.d i w) x)) =
    -(∫ x : Space, inner ℝ (Spatial.d i w x) (Spatial.d i w x)) at h
  simpa only [real_inner_self_eq_norm_sq] using h

lemma norm_sq_d (w : Space → Space) (hw : Differentiable ℝ w) (i : Fin 3) (x : Space) :
    Spatial.d i (fun x => ‖w x‖ ^ 2) x = 2 * inner ℝ (w x) (Spatial.d i w x) := by
  unfold Spatial.d
  rw [(hw x).hasFDerivAt.norm_sq.fderiv]
  simp

lemma bounded_L2_sq {w : Space → Space} (hm : MemLp w 2 (volume : Measure Space))
    (W : ℝ) (hW : ∀ x, ‖w x‖ ≤ W) : MemLp (fun x => ‖w x‖ ^ 2) 2 volume := by
  apply hm.of_le_mul (hm.aestronglyMeasurable.norm.pow 2) (c := W)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (hW x) (norm_nonneg _)

lemma pressure_identity (w : Space → Space) (p : Space → ℝ)
    (hw : Differentiable ℝ w) (hp : Differentiable ℝ p)
    (hm : MemLp w 2 (volume : Measure Space)) (hdm : ∀ i, MemLp (Spatial.d i w) 2 volume)
    (pm : MemLp p 2 volume) (pdm : ∀ i, MemLp (Spatial.d i p) 2 volume)
    (hdiv : ∀ x, ∑ i : Fin 3, Spatial.d i w x i = 0) :
    (∫ x : Space, ∑ i : Fin 3, Spatial.d i p x * w x i) = 0 := by
  have hc (i : Fin 3) (x : Space) : fderiv ℝ (fun x => w x i) x (e i) =
      Spatial.d i w x i := d_coord w hw i i x
  have hi (i : Fin 3) : (∫ x : Space, Spatial.d i p x * w x i) =
      -(∫ x : Space, p x * Spatial.d i w x i) := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure Space)) (v := e i) (f := p) (g := fun x => w x i)
      ((pdm i).integrable_mul (L2_coord hm i))
      (by
        simp only [hc]
        exact pm.integrable_mul (L2_coord (hdm i) i))
      (pm.integrable_mul (L2_coord hm i)) (fun x _ => hp x)
      (fun x _ => (Spatial.coord_smooth i).differentiable (by simp) (w x) |>.comp x (hw x))
    have h' : (∫ x : Space, p x * Spatial.d i w x i) =
        -(∫ x : Space, Spatial.d i p x * w x i) := by
      simpa only [hc, Spatial.d, Pi.mul_apply] using h
    linarith
  rw [integral_finsetSum Finset.univ (f := fun i x => Spatial.d i p x * w x i)
    (fun i _ => (pdm i).integrable_mul (L2_coord hm i))]
  simp_rw [hi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (f := fun i x => p x * Spatial.d i w x i)
    (fun i _ => pm.integrable_mul (L2_coord (hdm i) i))]
  simp_rw [← Finset.mul_sum, hdiv, mul_zero]
  simp

lemma transport_identity (w v : Space → Space)
    (hw : Differentiable ℝ w) (hv : Differentiable ℝ v)
    (hm : MemLp w 2 (volume : Measure Space)) (hdm : ∀ i, MemLp (Spatial.d i w) 2 volume)
    (vdm : ∀ i, MemLp (Spatial.d i v) 2 volume)
    (W V : ℝ) (hW : ∀ x, ‖w x‖ ≤ W) (hV : ∀ x, ‖v x‖ ≤ V)
    (hdiv : ∀ x, ∑ i : Fin 3, Spatial.d i v x i = 0) :
    (∫ x : Space, inner ℝ (w x) (fderiv ℝ w x (v x))) = 0 := by
  have hvc (i : Fin 3) : ∀ x, ‖v x i‖ ≤ V :=
    fun x => (PiLp.norm_apply_le (v x) i).trans (hV x)
  have hvm (i : Fin 3) : AEStronglyMeasurable (fun x => v x i) volume :=
    ((Spatial.coord_smooth i).continuous.comp hv.continuous).aestronglyMeasurable
  have hq := bounded_L2_sq hm W hW
  have hA (i : Fin 3) : Integrable
      (fun x : Space => v x i * inner ℝ (w x) (Spatial.d i w x)) volume :=
    (L2_inner_integrable hm (hdm i)).bdd_mul (hvm i) (Filter.Eventually.of_forall (hvc i))
  have hB (i : Fin 3) : Integrable
      (fun x : Space => Spatial.d i v x i * ‖w x‖ ^ 2) volume :=
    (L2_coord (vdm i) i).integrable_mul hq
  have hi (i : Fin 3) :
      2 * (∫ x : Space, v x i * inner ℝ (w x) (Spatial.d i w x)) =
        -(∫ x : Space, Spatial.d i v x i * ‖w x‖ ^ 2) := by
    have hfg' : Integrable
        (fun x : Space => v x i * fderiv ℝ (fun x => ‖w x‖ ^ 2) x (e i)) volume := by
      have he : (fun x : Space => v x i * fderiv ℝ (fun x => ‖w x‖ ^ 2) x (e i)) =
          fun x => 2 * (v x i * inner ℝ (w x) (Spatial.d i w x)) := by
        funext x
        rw [← Spatial.d, norm_sq_d w hw]
        ring
      rw [he]
      exact (hA i).const_mul 2
    have hc (x : Space) : fderiv ℝ (fun x => v x i) x (e i) = Spatial.d i v x i :=
      d_coord v hv i i x
    have hq (x : Space) : fderiv ℝ (fun x => ‖w x‖ ^ 2) x (e i) =
        2 * inner ℝ (w x) (Spatial.d i w x) := norm_sq_d w hw i x
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure Space)) (v := e i) (f := fun x => v x i)
      (g := fun x => ‖w x‖ ^ 2)
      (by simpa only [hc] using hB i) hfg'
      ((hm.integrable_norm_pow (by norm_num)).bdd_mul (hvm i) (Filter.Eventually.of_forall (hvc i)))
      (fun x _ => ((Spatial.coord_smooth i).differentiable (by simp) (v x)).comp x (hv x))
      (fun x _ => (hw x).hasFDerivAt.norm_sq.differentiableAt)
    simp only [hc, hq] at h
    convert h using 1
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hsum : 2 * (∫ x : Space, inner ℝ (w x) (fderiv ℝ w x (v x))) = 0 := by
    simp_rw [directional_sum, inner_sum, real_inner_smul_right]
    rw [integral_finsetSum _ (fun i _ => hA i), Finset.mul_sum]
    simp_rw [hi]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hB i)]
    simp_rw [← Finset.sum_mul, hdiv, zero_mul]
    simp
  linarith

lemma spatial_energy_inequality (ν : ℝ) (hν : 0 ≤ ν) (w v U a : Space → Space)
    (p : Space → ℝ)
    (hw : Differentiable ℝ w) (hdw : ∀ i, Differentiable ℝ (Spatial.d i w))
    (hv : Differentiable ℝ v) (hp : Differentiable ℝ p)
    (hm : MemLp w 2 (volume : Measure Space))
    (hdm : ∀ i, MemLp (Spatial.d i w) 2 volume)
    (hddm : ∀ i, MemLp (Spatial.d i (Spatial.d i w)) 2 volume)
    (vdm : ∀ i, MemLp (Spatial.d i v) 2 volume)
    (Udm : ∀ i, MemLp (Spatial.d i U) 2 volume)
    (pm : MemLp p 2 volume) (pdm : ∀ i, MemLp (Spatial.d i p) 2 volume)
    (W V C : ℝ) (hW : ∀ x, ‖w x‖ ≤ W) (hV : ∀ x, ‖v x‖ ≤ V)
    (hC : ∀ x, ‖fderiv ℝ U x‖ ≤ C)
    (hdivw : ∀ x, ∑ i : Fin 3, Spatial.d i w x i = 0)
    (hdivv : ∀ x, ∑ i : Fin 3, Spatial.d i v x i = 0)
    (heq : ∀ x, a x = ν • (∑ i : Fin 3, Spatial.d i (Spatial.d i w) x) -
      fderiv ℝ w x (v x) - fderiv ℝ U x (w x) -
      (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => Spatial.d i p x)) :
    (∫ x : Space, inner ℝ (w x) (a x)) ≤ C * (∫ x : Space, ‖w x‖ ^ 2) := by
  have hD (i : Fin 3) := L2_inner_integrable hm (hddm i)
  have hDsum : Integrable (fun x => ∑ i : Fin 3,
      inner ℝ (w x) (Spatial.d i (Spatial.d i w) x)) volume :=
    integrable_finsetSum _ (fun i _ => hD i)
  have hT := L2_inner_integrable hm (L2_directional hdm hv.continuous.aestronglyMeasurable V hV)
  have hS := L2_inner_integrable hm (L2_directional Udm hw.continuous.aestronglyMeasurable W hW)
  have hP : Integrable (fun x => ∑ i : Fin 3, Spatial.d i p x * w x i) volume :=
    integrable_finsetSum _ (fun i _ => (pdm i).integrable_mul (L2_coord hm i))
  have hDI : (∫ x : Space, ∑ i : Fin 3, inner ℝ (w x) (Spatial.d i (Spatial.d i w) x)) =
      -(∑ i : Fin 3, ∫ x : Space, ‖Spatial.d i w x‖ ^ 2) := by
    rw [integral_finsetSum _ (fun i _ => hD i)]
    simp_rw [diffusion_identity w _ hw (hdw _) hm (hdm _) (hddm _)]
    rw [Finset.sum_neg_distrib]
  have hDN : 0 ≤ ∑ i : Fin 3, ∫ x : Space, ‖Spatial.d i w x‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact integral_nonneg (fun x => sq_nonneg _)
  have hTI := transport_identity w v hw hv hm hdm vdm W V hW hV hdivv
  have hPI := pressure_identity w p hw hp hm hdm pm pdm hdivw
  have hSI : -(∫ x : Space, inner ℝ (w x) (fderiv ℝ U x (w x))) ≤
      C * (∫ x : Space, ‖w x‖ ^ 2) := by
    rw [← integral_neg, ← integral_const_mul]
    apply integral_mono hS.neg ((hm.integrable_norm_pow (by norm_num)).const_mul C)
    intro x
    calc
      -inner ℝ (w x) (fderiv ℝ U x (w x)) ≤ ‖w x‖ * ‖fderiv ℝ U x (w x)‖ :=
        (neg_le_abs _).trans (by
          simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (w x) (fderiv ℝ U x (w x)))
      _ ≤ ‖w x‖ * (C * ‖w x‖) := by
        gcongr
        exact ((fderiv ℝ U x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
      _ = C * ‖w x‖ ^ 2 := by ring
  have he (x : Space) : inner ℝ (w x) (a x) =
      ν * (∑ i : Fin 3, inner ℝ (w x) (Spatial.d i (Spatial.d i w) x)) -
      inner ℝ (w x) (fderiv ℝ w x (v x)) - inner ℝ (w x) (fderiv ℝ U x (w x)) -
      ∑ i : Fin 3, Spatial.d i p x * w x i := by
    rw [heq]
    simp only [inner_sub_right, real_inner_smul_right, inner_sum]
    congr 1
  have hDT : Integrable (fun x => ν * (∑ i : Fin 3,
      inner ℝ (w x) (Spatial.d i (Spatial.d i w) x)) -
      inner ℝ (w x) (fderiv ℝ w x (v x))) volume := (hDsum.const_mul ν).sub hT
  have hDTS : Integrable (fun x => ν * (∑ i : Fin 3,
      inner ℝ (w x) (Spatial.d i (Spatial.d i w) x)) -
      inner ℝ (w x) (fderiv ℝ w x (v x)) -
      inner ℝ (w x) (fderiv ℝ U x (w x))) volume := hDT.sub hS
  simp_rw [he]
  rw [integral_sub hDTS hP, integral_sub hDT hS,
    integral_sub (hDsum.const_mul ν) hT, integral_const_mul, hDI, hTI, hPI]
  nlinarith [mul_nonneg hν hDN]

lemma d_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : Space → E) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin 3) :
    Spatial.d i (fun x => f x - g x) = fun x => Spatial.d i f x - Spatial.d i g x := by
  funext x
  simp [Spatial.d, fderiv_fun_sub (hf x) (hg x)]

lemma grad_zero (t : ℝ) (x : Space) : grad (fun _ _ => 0) t x = 0 := by
  ext i
  simp [grad, dx, EuclideanSpace.equiv]

lemma navierStokes_energy_inequality (ν : ℝ) (hν : 0 ≤ ν) (f U v : Velocity) (p : Pressure)
    (hU : NavierStokes ν f U (fun _ _ => 0)) (hv : NavierStokes ν f v p)
    {T t : ℝ} (ht : t ∈ Set.Icc 0 T)
    (hUH : ContinuousInH 2 U T) (hvH : ContinuousInH 2 v T) (hpH : ContinuousInH 1 p T)
    (CU Cv C : ℝ) (hCU : ∀ x, ‖U t x‖ ≤ CU) (hCv : ∀ x, ‖v t x‖ ≤ Cv)
    (hC : ∀ x, ‖fderiv ℝ (U t) x‖ ≤ C) :
    (∫ x : Space, inner ℝ (v t x - U t x) (dt v t x - dt U t x)) ≤
      C * (∫ x : Space, ‖v t x - U t x‖ ^ 2) := by
  let w : Space → Space := fun x => v t x - U t x
  have hUD := hU.1.2.1 t ht.1
  have hvD := hv.1.2.1 t ht.1
  have hwD : Differentiable ℝ w := hvD.sub hUD
  have hd (i : Fin 3) : Spatial.d i w = fun x => dx i v t x - dx i U t x :=
    d_sub (v t) (U t) hvD hUD i
  have hdd (i : Fin 3) : Spatial.d i (Spatial.d i w) =
      fun x => dx i (dx i v) t x - dx i (dx i U) t x := by
    rw [hd]
    exact d_sub _ _ (hv.1.2.2.1 t ht.1 i) (hU.1.2.2.1 t ht.1 i) i
  have hdD (i : Fin 3) : Differentiable ℝ (Spatial.d i w) := by
    rw [hd]
    exact (hv.1.2.2.1 t ht.1 i).sub (hU.1.2.2.1 t ht.1 i)
  have hdM (i : Fin 3) : MemLp (Spatial.d i w) 2 (volume : Measure Space) := by
    rw [hd]
    exact (h_dx_memLp v hvH (by norm_num) ht i).sub (h_dx_memLp U hUH (by norm_num) ht i)
  have hddM (i : Fin 3) : MemLp (Spatial.d i (Spatial.d i w)) 2 (volume : Measure Space) := by
    rw [hdd]
    exact (h_dxx_memLp v hvH ht i).sub (h_dxx_memLp U hUH ht i)
  apply spatial_energy_inequality ν hν w (v t) (U t) _ (p t) hwD hdD hvD
    (hv.1.2.2.2.1 t ht.1) ((h_memLp v hvH ht).sub (h_memLp U hUH ht)) hdM hddM
    (h_dx_memLp v hvH (by norm_num) ht) (h_dx_memLp U hUH (by norm_num) ht)
    (h_memLp p hpH ht) (h_dx_memLp p hpH (by norm_num) ht)
    (Cv + CU) Cv C (fun x => (norm_sub_le _ _).trans (add_le_add (hCv x) (hCU x))) hCv hC
  · intro x
    simp only [hd, PiLp.sub_apply, Finset.sum_sub_distrib]
    change div v t x - div U t x = 0
    rw [(hv.2.2 t ht.1 x).1, (hU.2.2 t ht.1 x).1, sub_self]
  · exact fun x => (hv.2.2 t ht.1 x).1
  · intro x
    have h1 := eq_sub_of_add_eq (hv.2.2 t ht.1 x).2
    have h2 := eq_sub_of_add_eq (hU.2.2 t ht.1 x).2
    rw [grad_zero, neg_zero, zero_add] at h2
    simp only [hdd, Finset.sum_sub_distrib, smul_sub]
    rw [h1, h2]
    simp only [w, fderiv_fun_sub (hvD x) (hUD x), sub_apply, map_sub,
      laplacian, advection]
    change (-grad p t x + ν • (∑ i, dx i (dx i v) t x) + f t x -
      fderiv ℝ (v t) x (v t x)) -
      (ν • (∑ i, dx i (dx i U) t x) + f t x - fderiv ℝ (U t) x (U t x)) = _
    unfold grad dx Spatial.d
    abel

lemma l2_inner_representatives (g h : Lp Space 2 (volume : Measure Space))
    (w a : Space → Space) (hw : ∀ᵐ x ∂volume, g x = w x) (ha : ∀ᵐ x ∂volume, h x = a x) :
    inner ℝ g h = ∫ x : Space, inner ℝ (w x) (a x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hw, ha] with x hx hy
  rw [hx, hy]

lemma l2_norm_sq_representative (g : Lp Space 2 (volume : Measure Space))
    (w : Space → Space) (hw : ∀ᵐ x ∂volume, g x = w x) :
    ‖g‖ ^ 2 = ∫ x : Space, ‖w x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, l2_inner_representatives g g w w hw hw]
  simp only [real_inner_self_eq_norm_sq]

theorem energy_velocity_unique (ν : ℝ) (hν : 0 ≤ ν) (f U v : Velocity) (p : Pressure)
    (hU : NavierStokes ν f U (fun _ _ => 0)) (hv : NavierStokes ν f v p)
    (hUE : EnergyClass U (fun _ _ => 0)) (hvE : CompetitorEnergyClass v p) :
    ∀ t, 0 ≤ t → ∀ x, v t x = U t x := by
  intro T hT
  obtain ⟨hUH, hUL, _, CU, hCU⟩ := hUE.1 T hT
  obtain ⟨hvH, hvL, hpH, Cv, hCv⟩ := hvE T hT
  obtain ⟨C, hC⟩ := hUE.2 T hT
  obtain ⟨gU, gU', hgUc, _, hgUd, hgU, hgU'⟩ := hUL
  obtain ⟨gv, gv', hgvc, _, hgvd, hgv, hgv'⟩ := hvL
  let g := fun t => gv t - gU t
  let g' := fun t => gv' t - gU' t
  have hgc : ContinuousOn g (Set.Icc 0 T) := hgvc.sub hgUc
  have hgd : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt g (g' t) (Set.Icc 0 T) t :=
    fun t ht => (hgvd t ht).sub (hgUd t ht)
  have hgw (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      ∀ᵐ x ∂(volume : Measure Space), (g t) x = v t x - U t x := by
    filter_upwards [Lp.coeFn_sub (gv t) (gU t), hgv t ht, hgU t ht] with x hx hvx hUx
    change (gv t - gU t) x = _
    rw [hx]
    change gv t x - gU t x = _
    rw [hvx, hUx]
  have hga (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      ∀ᵐ x ∂(volume : Measure Space), (g' t) x = dt v t x - dt U t x := by
    filter_upwards [Lp.coeFn_sub (gv' t) (gU' t), hgv' t ht, hgU' t ht] with x hx hvx hUx
    change (gv' t - gU' t) x = _
    rw [hx]
    change gv' t x - gU' t x = _
    rw [hvx, hUx]
  have hg0 : g 0 = 0 := by
    apply Lp.ext
    filter_upwards [hgw 0 ⟨le_rfl, hT⟩, Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx h0x
    rw [hx, h0x]
    change v 0 x - U 0 x = 0
    rw [hU.2.1, hv.2.1, sub_self]
  have hgi (t : ℝ) (ht : t ∈ Set.Icc 0 T) : inner ℝ (g t) (g' t) ≤ C * ‖g t‖ ^ 2 := by
    rw [l2_inner_representatives (g t) (g' t) _ _ (hgw t ht) (hga t ht),
      l2_norm_sq_representative (g t) _ (hgw t ht)]
    exact navierStokes_energy_inequality ν hν f U v p hU hv ht hUH hvH hpH CU Cv C
      (hCU t ht) (hCv t ht) (fun x => (le_add_of_nonneg_left (norm_nonneg _)).trans (hC t ht x))
  have hrd (t : ℝ) (ht : t ∈ Set.Ico 0 T) :
      HasDerivWithinAt (fun t => ‖g t‖ ^ 2) (2 * inner ℝ (g t) (g' t)) (Set.Ici t) t := by
    apply (hgd t ⟨ht.1, ht.2.le⟩).norm_sq.mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with s hs hs'
    exact ⟨ht.1.trans hs, hs'.le⟩
  have hbound := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun t => ‖g t‖ ^ 2) (f' := fun t => 2 * inner ℝ (g t) (g' t))
    (δ := 0) (K := 2 * C) (ε := 0) (hgc.norm.pow 2)
    (fun t ht r hr => (hrd t ht).liminf_right_slope_le hr)
    (by simp [hg0]) (fun t ht => by nlinarith [hgi t ⟨ht.1, ht.2.le⟩])
    T ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0_δ0] at hbound
  have hgT : g T = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (g T)]
  have he : v T = U T := by
    apply ((hv.1.2.1 T hT).continuous.ae_eq_iff_eq volume (hU.1.2.1 T hT).continuous).mp
    filter_upwards [hgw T ⟨hT, le_rfl⟩, Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx h0x
    rw [hgT, h0x] at hx
    exact sub_eq_zero.mp hx.symm
  exact congrFun he

lemma pressure_zero_of_gradient_zero (p : Space → ℝ) (hp : Differentiable ℝ p)
    (hm : MemLp p 2 (volume : Measure Space))
    (hd : ∀ x i, Spatial.d i p x = 0) : ∀ x, p x = 0 := by
  have hfd (x : Space) : fderiv ℝ p x = 0 := by
    ext y
    rw [← sum_basis y, map_sum]
    have hde : ∀ i, fderiv ℝ p x (e i) = 0 := hd x
    simp only [map_smul, hde, smul_zero, Finset.sum_const_zero, zero_apply]
  have hc (x : Space) : p x = p 0 := is_const_of_fderiv_eq_zero hp hfd x 0
  have hpc : p = fun _ => p 0 := funext hc
  rw [hpc] at hm
  have hzero : p 0 = 0 := by
    simpa [memLp_const_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)] using hm
  intro x
  rw [hc, hzero]

theorem energy_unique (ν : ℝ) (hν : 0 ≤ ν) (f U v : Velocity) (p : Pressure)
    (hU : NavierStokes ν f U (fun _ _ => 0)) (hv : NavierStokes ν f v p)
    (hUE : EnergyClass U (fun _ _ => 0)) (hvE : CompetitorEnergyClass v p) :
    ∀ t, 0 ≤ t → ∀ x, v t x = U t x ∧ p t x = 0 := by
  have he := energy_velocity_unique ν hν f U v p hU hv hUE hvE
  have hef (t : ℝ) (ht : 0 ≤ t) : v t = U t := funext (he t ht)
  have hdt (t : ℝ) (ht : 0 ≤ t) (x : Space) : dt v t x = dt U t x := by
    unfold dt
    rw [fderivWithin_congr' (fun s (hs : s ∈ Set.Ici 0) => he s hs x) ht]
  intro t ht x
  refine ⟨he t ht x, ?_⟩
  apply pressure_zero_of_gradient_zero (p t) (hv.1.2.2.2.1 t ht)
    (h_memLp p (hvE t ht).2.2.1 ⟨ht, le_rfl⟩)
  intro y i
  have h1 := (hv.2.2 t ht y).2
  have h2 := (hU.2.2 t ht y).2
  rw [grad_zero, neg_zero, zero_add] at h2
  have ha : advection v t y = advection U t y := by simp only [advection, hef t ht]
  have hdx (j : Fin 3) : dx j v t = dx j U t := by
    funext z
    simp only [dx, hef t ht]
  have hl : laplacian v t y = laplacian U t y := by simp only [laplacian, dx, hdx]
  rw [hdt t ht y, ha, hl, h2] at h1
  have hg : grad p t y = 0 := by
    have hn : -grad p t y = 0 := by
      apply add_right_cancel (b := ν • laplacian U t y + f t y)
      simpa only [zero_add, add_assoc] using h1.symm
    exact neg_eq_zero.mp hn
  have hcoord := congrArg (fun z : Space => z i) hg
  exact hcoord

end
end Analytic

namespace Construction

theorem velocity_unique (ν : ℝ) (hν : 0 < ν) (M : Machine) (w : List ℕ)
    (v : Velocity) (p : Pressure) (hv : NavierStokes ν (force ν M w) v p)
    (hvE : CompetitorEnergyClass v p) :
    ∀ t, 0 ≤ t → ∀ x, v t x = velocity M w t x ∧ p t x = 0 := by
  apply Analytic.energy_unique ν hν.le (force ν M w) (velocity M w) v p
    (Analytic.residual_navierStokes ν _ (velocity_smooth M w) (velocity_rest M w) (velocity_div M w))
    hv (velocity_energyClass M w) hvE

end Construction
end AlternatingNS

end OAI
