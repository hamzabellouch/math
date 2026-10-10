import Mathlib

namespace OAI

/-! Local L2 restriction and bounded varying multipliers. -/

namespace BFSSLocalL2
noncomputable section
open MeasureTheory Set Filter Topology
variable {E F : Type*} [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (μ : Measure E) (s : Set E)

def restrictLinear : Lp F 2 μ →ₗ[ℝ] Lp F 2 (μ.restrict s) where
  toFun f := ((Lp.memLp f).restrict s).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f+g)).restrict s),
      MemLp.coeFn_toLp ((Lp.memLp f).restrict s), MemLp.coeFn_toLp ((Lp.memLp g).restrict s),
      Lp.coeFn_add (((Lp.memLp f).restrict s).toLp f) (((Lp.memLp g).restrict s).toLp g),
      ae_restrict_of_ae (Lp.coeFn_add f g)] with x hfg hf hg ha hb
    simp only [Pi.add_apply,hf,hg] at ha hb
    exact hfg.trans (hb.trans ha.symm)
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).restrict s),
      MemLp.coeFn_toLp ((Lp.memLp f).restrict s),
      Lp.coeFn_smul c (((Lp.memLp f).restrict s).toLp f),
      ae_restrict_of_ae (Lp.coeFn_smul c f)] with x hcf hf ha hb
    simp only [Pi.smul_apply,hf] at ha hb
    exact hcf.trans (hb.trans ha.symm)

lemma restrictLinear_norm_le (f : Lp F 2 μ) : ‖restrictLinear μ s f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).restrict s).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure _ (Measure.restrict_le_self))

def restrict : Lp F 2 μ →L[ℝ] Lp F 2 (μ.restrict s) :=
  (restrictLinear μ s).mkContinuous 1 (fun f => by simpa using restrictLinear_norm_le μ s f)

lemma restrict_ae (f : Lp F 2 μ) : (restrict μ s f : E → F) =ᵐ[μ.restrict s] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).restrict s)

variable {μ s}
omit [NormedSpace ℝ F] in
lemma norm_le_of_ae_norm_le (f g : Lp F 2 μ) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) : ‖f‖ ≤ ‖g‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g)
    (eLpNorm_mono_ae (Lp.memLp f).aestronglyMeasurable h)

lemma norm_le_mul_of_ae_norm_le (f g : Lp F 2 μ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c*‖g x‖) : ‖f‖ ≤ c*‖g‖ := by
  rw [←abs_of_nonneg hc,←Real.norm_eq_abs,←norm_smul]
  apply norm_le_of_ae_norm_le
  filter_upwards [h,Lp.coeFn_smul c g] with x hx hg
  rw [hg,Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
  exact hx
end
end BFSSLocalL2
namespace BFSSLocalL2
noncomputable section
open MeasureTheory Set Filter Topology
variable {E F : Type*} [MeasurableSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {μ : Measure E}

lemma boundedMul_mem (w : E → ℝ) (hw : AEStronglyMeasurable w μ)
    (B : ℝ) (hB : ∀ᵐ x ∂μ, |w x| ≤ B) (f : Lp F 2 μ) :
    MemLp (fun x => w x • f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (hw.smul (Lp.memLp f).aestronglyMeasurable)
  filter_upwards [hB] with x hx
  change ‖w x • f x‖ ≤ B*‖f x‖
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

def boundedMul (w : E → ℝ) (hw : AEStronglyMeasurable w μ)
    (B : ℝ) (hB : ∀ᵐ x ∂μ, |w x| ≤ B) (f : Lp F 2 μ) : Lp F 2 μ :=
  (boundedMul_mem w hw B hB f).toLp (fun x => w x • f x)

lemma boundedMul_ae (w : E → ℝ) (hw : AEStronglyMeasurable w μ)
    (B : ℝ) (hB : ∀ᵐ x ∂μ, |w x| ≤ B) (f : Lp F 2 μ) :
    (boundedMul w hw B hB f : E → F) =ᵐ[μ] fun x => w x • f x :=
  MemLp.coeFn_toLp _

attribute [local irreducible] boundedMul

lemma boundedMul_dist_le (w : E → ℝ) (hw : AEStronglyMeasurable w μ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂μ, |w x| ≤ B) (f g : Lp F 2 μ) :
    dist (boundedMul w hw B hB f) (boundedMul w hw B hB g) ≤ B*dist f g := by
  simp only [dist_eq_norm]
  apply norm_le_mul_of_ae_norm_le _ (f-g) B hB0
  filter_upwards [boundedMul_ae w hw B hB f, boundedMul_ae w hw B hB g,
    Lp.coeFn_sub (boundedMul w hw B hB f) (boundedMul w hw B hB g),
    Lp.coeFn_sub f g,hB] with x hf hg hs hfg hx
  rw [hs,Pi.sub_apply,hf,hg,←smul_sub,hfg,Pi.sub_apply,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

lemma lp_norm_sq (f : Lp F 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem boundedMul_fixed_tendsto (w : ℕ → E → ℝ) (hw : ∀ n, AEStronglyMeasurable (w n) μ)
    (B : ℝ) (_hB0 : 0 ≤ B) (hB : ∀ n, ∀ᵐ x ∂μ, |w n x| ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 1)) (u : Lp F 2 μ) :
    Tendsto (fun n => boundedMul (w n) (hw n) B (hB n) u) atTop (𝓝 u) := by
  have ht : Tendsto (fun n => ∫ x, ‖(w n x-1) • u x‖^2 ∂μ) atTop (𝓝 0) := by
    have hu := (Lp.memLp u).integrable_norm_pow (by decide : 2 ≠ 0)
    have hd := tendsto_integral_of_dominated_convergence
      (F := fun n x => ‖(w n x-1) • u x‖^2) (f := fun _ => (0 : ℝ))
      (fun x => (B+1)^2*‖u x‖^2)
      (fun n => (((hw n).sub aestronglyMeasurable_const).smul
        (Lp.memLp u).aestronglyMeasurable).norm.pow 2)
      (hu.const_mul ((B+1)^2)) ?_ ?_
    · simpa only [integral_zero] using hd
    · intro n
      filter_upwards [hB n] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),norm_smul,Real.norm_eq_abs,mul_pow]
      have hh : |w n x-1| ≤ B+1 := by
        calc
          |w n x-1| ≤ |w n x|+1 := by simpa only [abs_one] using abs_sub (w n x) 1
          _ ≤ B+1 := by linarith
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hh 2) (sq_nonneg _)
    · filter_upwards [hlim] with x hx
      have hh := ((hx.sub (tendsto_const_nhds (x := (1 : ℝ)))).smul
        (tendsto_const_nhds (x := u x))).norm.pow 2
      simpa only [sub_self,zero_smul,norm_zero,zero_pow (by decide : 2 ≠ 0)] using hh
  have he (n : ℕ) : dist (boundedMul (w n) (hw n) B (hB n) u) u ^2 =
      ∫ x, ‖(w n x-1) • u x‖^2 ∂μ := by
    rw [dist_eq_norm,lp_norm_sq]
    apply integral_congr_ae
    filter_upwards [boundedMul_ae (w n) (hw n) B (hB n) u,
      Lp.coeFn_sub (boundedMul (w n) (hw n) B (hB n) u) u] with x hx hs
    rw [hs,Pi.sub_apply,hx,sub_smul,one_smul]
  rw [tendsto_iff_dist_tendsto_zero]
  have hsq : Tendsto (fun n => dist (boundedMul (w n) (hw n) B (hB n) u) u ^2)
      atTop (𝓝 0) := by simpa only [he] using ht
  have hr := hsq.sqrt
  simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg dist_nonneg,Real.sqrt_zero] using hr

theorem boundedMul_tendsto (w : ℕ → E → ℝ) (hw : ∀ n, AEStronglyMeasurable (w n) μ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ n, ∀ᵐ x ∂μ, |w n x| ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 1))
    (f : ℕ → Lp F 2 μ) (u : Lp F 2 μ) (hf : Tendsto f atTop (𝓝 u)) :
    Tendsto (fun n => boundedMul (w n) (hw n) B (hB n) (f n)) atTop (𝓝 u) := by
  let g : ℕ → Lp F 2 μ := fun n => boundedMul (w n) (hw n) B (hB n) u
  let k : ℕ → Lp F 2 μ := fun n => boundedMul (w n) (hw n) B (hB n) (f n)
  have hfixed : Tendsto g atTop (𝓝 u) := boundedMul_fixed_tendsto w hw B hB0 hB hlim u
  have hsmall : Tendsto (fun n => B*dist (f n) u) atTop (𝓝 0) := by
    simpa only [dist_self,mul_zero] using (tendsto_const_nhds (x := B)).mul (hf.dist (tendsto_const_nhds (x := u)))
  have hdist (n : ℕ) : dist (k n) u ≤ B*dist (f n) u + dist (g n) u := by
    have hl : dist (k n) (g n) ≤ B*dist (f n) u :=
      boundedMul_dist_le (w n) (hw n) B hB0 (hB n) (f n) u
    exact (dist_triangle (k n) (g n) u).trans (add_le_add hl (le_refl (dist (g n) u)))
  have hsum : Tendsto (fun n => B*dist (f n) u + dist (g n) u) atTop (𝓝 0) := by
    simpa only [dist_self,zero_add] using hsmall.add (hfixed.dist (tendsto_const_nhds (x := u)))
  exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) hdist hsum)
end
end BFSSLocalL2

end OAI
