import Mathlib

namespace OAI

/-! A narrow transverse correction with arbitrarily small values and a fixed first jet. -/
noncomputable section
open Set Metric
open scoped ContDiff

namespace ClosedSurfaceR4.TransverseSmallFunction

def cutoff : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

lemma cutoff_zero : cutoff 0 = 1 :=
  cutoff.one_of_mem_closedBall (mem_closedBall_self cutoff.rIn_pos.le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def correction (f g : E → ℝ) (δ : ℝ) (x : E) : ℝ :=
  f x * g x * cutoff (f x / δ)

lemma correction_smooth {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (δ : ℝ) :
    ContDiff ℝ ∞ (correction f g δ) :=
  (hf.mul hg).mul (cutoff.contDiff.comp (hf.div_const δ))

/-- At the defining curve the cutoff introduces no change in the prescribed first jet. -/
lemma correction_hasFDerivAt {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hf0 : f x = 0) (δ : ℝ) :
    HasFDerivAt (correction f g δ) (g x • fderiv ℝ f x) x := by
  have hcd : Differentiable ℝ (cutoff : ℝ → ℝ) :=
    (cutoff.contDiff : ContDiff ℝ ∞ (cutoff : ℝ → ℝ)).differentiable (by simp)
  have hdiv : DifferentiableAt ℝ (fun y => f y / δ) x := by
    simpa only [div_eq_mul_inv] using hf.mul_const δ⁻¹
  have hc : DifferentiableAt ℝ (fun y => cutoff (f y / δ)) x :=
    DifferentiableAt.comp x (g := (cutoff : ℝ → ℝ)) (f := fun y => f y / δ)
      (hcd (f x / δ)) hdiv
  have hd := (hf.hasFDerivAt.mul hg.hasFDerivAt).mul hc.hasFDerivAt
  convert! hd using 1
  simp only [Pi.mul_apply, hf0, zero_div, cutoff_zero, zero_mul, zero_smul, zero_add, one_smul]

lemma correction_derivative {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hf0 : f x = 0)
    (δ : ℝ) (v : E) :
    fderiv ℝ (correction f g δ) x v = g x * fderiv ℝ f x v := by
  rw [(correction_hasFDerivAt hf hg hf0 δ).fderiv]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma correction_abs_le {f g : E → ℝ} {δ G : ℝ} (hδ : 0 < δ) (hG : 0 ≤ G)
    (hg : ∀ x, |g x| ≤ G) (x : E) : |correction f g δ x| ≤ δ * G := by
  by_cases hz : cutoff (f x / δ) = 0
  · simp only [correction, hz, mul_zero, abs_zero]
    exact mul_nonneg hδ.le hG
  have hmem : f x / δ ∈ ball (0 : ℝ) cutoff.rOut := by
    rw [← cutoff.support_eq]
    exact hz
  have hr : |f x / δ| < 1 := by
    change dist (f x / δ) 0 < 1 at hmem
    simpa only [Real.dist_eq, sub_zero] using hmem
  have hf : |f x| ≤ δ := by
    rw [abs_div, abs_of_pos hδ] at hr
    exact ((div_lt_one hδ).mp hr).le
  have hc : |cutoff (f x / δ)| ≤ 1 := by
    rw [abs_of_nonneg cutoff.nonneg]
    exact cutoff.le_one
  calc
    |correction f g δ x| = |f x| * |g x| * |cutoff (f x / δ)| := by
      simp only [correction, abs_mul]
    _ ≤ δ * G * 1 := mul_le_mul (mul_le_mul hf (hg x) (abs_nonneg _) hδ.le)
      hc (abs_nonneg _) (mul_nonneg hδ.le hG)
    _ = δ * G := mul_one _

omit [NormedSpace ℝ E] in
lemma correction_support (f g : E → ℝ) (δ : ℝ) :
    tsupport (correction f g δ) ⊆ tsupport g := by
  change tsupport ((f * g) * (fun x => cutoff (f x / δ))) ⊆ tsupport g
  exact tsupport_mul_subset_left.trans tsupport_mul_subset_right

omit [NormedSpace ℝ E] in
lemma correction_compactSupport (f : E → ℝ) {g : E → ℝ} (hg : HasCompactSupport g) (δ : ℝ) :
    HasCompactSupport (correction f g δ) := by
  change HasCompactSupport ((f * g) * (fun x => cutoff (f x / δ)))
  exact hg.mul_left.mul_right

/-- Narrowing the support in the defining-function direction makes the value
arbitrarily small without changing any prescribed derivative along its zero set. -/
theorem exists_small_correction {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {G ε : ℝ} (hG : 0 ≤ G) (hgb : ∀ x, |g x| ≤ G) (hε : 0 < ε) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ tsupport H ⊆ tsupport g ∧
      (∀ x, |H x| < ε) ∧
      ∀ x, f x = 0 → fderiv ℝ H x = g x • fderiv ℝ f x := by
  let δ := ε / (G + 1)
  have hden : 0 < G + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδG : δ * G < ε := by
    change ε / (G + 1) * G < ε
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  refine ⟨correction f g δ, correction_smooth hf hg δ, correction_support f g δ,
    (fun x => lt_of_le_of_lt (correction_abs_le hδ hG hgb x) hδG), ?_⟩
  intro x hx
  exact (correction_hasFDerivAt (hf.differentiable (by simp) x)
    (hg.differentiable (by simp) x) hx δ).fderiv

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
