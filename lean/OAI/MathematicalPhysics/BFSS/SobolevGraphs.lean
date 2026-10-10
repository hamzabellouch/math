import Mathlib
import OAI.MathematicalPhysics.BFSS.WeakLimits

namespace OAI

/-! Closed vector-valued gradient graphs and scaled smooth cutoffs. -/

namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Topology Set Filter
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
abbrev Core := TestFunction (⊤ : TopologicalSpace.Opens E) F ⊤

def toL2 : Core (E := E) (F := F) →ₗ[ℝ] Lp F 2 μ where
  toFun f := (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp f
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' scalar _ := MemLp.toLp_const_smul scalar _

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma toL2_ae (f : Core (E := E) (F := F)) : (toL2 μ f : E → F) =ᵐ[μ] f :=
  MemLp.coeFn_toLp (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma toL2_norm_sq (f : Core (E := E) (F := F)) : ‖toL2 μ f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [toL2_ae μ f] with x hx
  rw [hx,real_inner_self_eq_norm_sq]

variable {ι : Type*} [Fintype ι] (e : ι → E)
abbrev Gradient := PiLp 2 (fun _ : ι => Lp F 2 μ)

def gradient : Core (E := E) (F := F) →ₗ[ℝ] Gradient (F := F) μ (ι := ι) :=
  (WithLp.linearEquiv 2 ℝ (ι → Lp F 2 μ)).symm.toLinearMap.comp
    (LinearMap.pi fun j => (toL2 μ).comp (TestFunction.lineDerivCLM ℝ (e j)).toLinearMap)

omit [FiniteDimensional ℝ E] [CompleteSpace F] [Fintype ι] in
lemma gradient_apply (f : Core (E := E) (F := F)) (j : ι) :
    gradient μ e f j = toL2 μ ((TestFunction.lineDerivCLM ℝ (e j)) f) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [InnerProductSpace ℝ F] [CompleteSpace F] in
lemma norm_sq_compact (f : E → F) (h : HasCompactSupport f) :
    HasCompactSupport (fun x => ‖f x‖^2) := by
  rw [hasCompactSupport_iff_eventuallyEq] at h ⊢
  filter_upwards [h] with x hx
  simp only [Pi.zero_apply] at hx ⊢
  rw [hx,norm_zero,zero_pow (by decide : 2 ≠ 0)]

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma derivative_sq_integrable (f : Core (E := E) (F := F)) (v : E) :
    Integrable (fun x => ‖fderiv ℝ (f : E → F) x v‖^2) μ := by
  let g : Core (E := E) (F := F) := TestFunction.lineDerivCLM ℝ v f
  have hg : ∀ x, g x = fderiv ℝ (f : E → F) x v := by
    intro x
    rfl
  have hi : Integrable (fun x => ‖g x‖^2) μ := (g.continuous.norm.pow 2).integrable_of_hasCompactSupport
    (norm_sq_compact g g.hasCompactSupport)
  simpa only [hg] using hi

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma gradient_norm_sq (f : Core (E := E) (F := F)) :
    ‖gradient μ e f‖^2 = ∫ x, ∑ j, ‖fderiv ℝ (f : E → F) x (e j)‖^2 ∂μ := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [gradient_apply,toL2_norm_sq]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [] with x
    congr 2
  · intro j _
    exact derivative_sq_integrable μ f (e j)

def graph : Submodule ℝ (Lp F 2 μ × Gradient (F := F) μ (ι := ι)) :=
  LinearMap.range ((toL2 μ).prod (gradient μ e))

def closedGraph : Submodule ℝ (Lp F 2 μ × Gradient (F := F) μ (ι := ι)) :=
  (graph μ e).topologicalClosure

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma core_mem_closedGraph (f : Core (E := E) (F := F)) :
    (toL2 μ f,gradient μ e f) ∈ closedGraph μ e :=
  Submodule.le_topologicalClosure _ ⟨f,rfl⟩
end
end BFSSSliceSobolev
namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Topology Set Filter
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [IsSeparable μ]
variable {ι : Type*} [Fintype ι] (e : ι → E)

omit [FiniteDimensional ℝ E] in
theorem closedGraph_extract (f : ℕ → Core (E := E) (F := F))
    (u : Lp F 2 μ) (B : ℝ) (hf : Tendsto (fun n => toL2 μ (f n)) atTop (𝓝 u))
    (hB : ∀ n, ‖gradient μ e (f n)‖ ≤ B) :
    ∃ (v : Gradient (F := F) μ (ι := ι)) (σ : ℕ → ℕ), StrictMono σ ∧
      (u,v) ∈ closedGraph μ e ∧ ‖v‖ ≤ B ∧
      ∀ w : Gradient (F := F) μ (ι := ι),
        Tendsto (fun n => inner ℝ (gradient μ e (f (σ n))) w) atTop (𝓝 (inner ℝ v w)) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp F 2 μ) := Lp.SecondCountableTopology
  let : SecondCountableTopology (Gradient (F := F) μ (ι := ι)) :=
    PiLp.secondCountableTopology 2 (fun _ : ι => Lp F 2 μ)
  let : TopologicalSpace.SeparableSpace (Gradient (F := F) μ (ι := ι)) := inferInstance
  obtain ⟨v,σ,hσ,hv,hw⟩ := BFSSNormalAnalysis.bounded_weak_subsequence
    (F := Gradient (F := F) μ (ι := ι))
    (fun n => gradient μ e (f n)) B hB
  refine ⟨v,σ,hσ,?_,hv,hw⟩
  let C : Set (Lp F 2 μ × Gradient (F := F) μ (ι := ι)) :=
    (closedGraph (F := F) μ e : Set _)
  have hCc : Convex ℝ C := (closedGraph (F := F) μ e).convex
  have hCcl : IsClosed C := (graph (F := F) μ e).isClosed_topologicalClosure
  have hm : ∀ n, (toL2 μ (f (σ n)),gradient μ e (f (σ n))) ∈ C :=
    fun n => core_mem_closedGraph μ e (f (σ n))
  exact BFSSNormalAnalysis.strong_weak_mem_closed_convex C hCc hCcl
    (fun n => toL2 μ (f (σ n))) (fun n => gradient μ e (f (σ n))) u v
    hm (hf.comp hσ.tendsto_atTop) hw
end
end BFSSSliceSobolev
namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Measure Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (μ : Measure E) [IsAddHaarMeasure μ]
variable {ι : Type*} [Fintype ι] (e : ι → E)

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma toL2_inner (f g : Core (E := E) (F := F)) :
    inner ℝ (toL2 μ f) (toL2 μ g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [toL2_ae μ f,toL2_ae μ g] with x hf hg
  rw [hf,hg]

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma core_inner_integrable (f g : Core (E := E) (F := F)) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ :=
  (f.continuous.inner g.continuous).integrable_of_hasCompactSupport
    (f.hasCompactSupport.comp₂_left g.hasCompactSupport (by simp))

omit [CompleteSpace F] in
lemma directionalDerivative_skew (f g : Core (E := E) (F := F)) (v : E) :
    inner ℝ (toL2 μ f) (toL2 μ (TestFunction.lineDerivCLM ℝ v g)) =
      -inner ℝ (toL2 μ (TestFunction.lineDerivCLM ℝ v f)) (toL2 μ g) := by
  rw [toL2_inner,toL2_inner]
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := innerSL ℝ) (core_inner_integrable μ (TestFunction.lineDerivCLM ℝ v f) g)
    (core_inner_integrable μ f (TestFunction.lineDerivCLM ℝ v g)) (core_inner_integrable μ f g)
    (fun x _ => (f.contDiff.differentiable (by simp)).differentiableAt)
    (fun x _ => (g.contDiff.differentiable (by simp)).differentiableAt)

omit [CompleteSpace F] in
lemma toL2_dense : DenseRange (toL2 (F := F) μ) := by
  apply (Lp.dense_hasCompactSupport_contDiff (μ := μ) (F := F) (p := 2) (by norm_num)).mono
  rintro f ⟨g,hfg,hgc,hgd⟩
  let k : Core (E := E) (F := F) := ⟨g,hgd,hgc,by intro x hx; trivial⟩
  exact ⟨k,Lp.ext ((toL2_ae μ k).trans hfg.symm)⟩

omit [CompleteSpace F] in
lemma closedGraph_pairing {p : Lp F 2 μ × Gradient (F := F) μ (ι := ι)}
    (hp : p ∈ closedGraph μ e) (j : ι) (f : Core (E := E) (F := F)) :
    inner ℝ (toL2 μ f) (p.2 j) =
      -inner ℝ (toL2 μ (TestFunction.lineDerivCLM ℝ (e j) f)) p.1 := by
  let C : Set (Lp F 2 μ × Gradient (F := F) μ (ι := ι)) :=
    {a | inner ℝ (toL2 μ f) (a.2 j) =
      -inner ℝ (toL2 μ (TestFunction.lineDerivCLM ℝ (e j) f)) a.1}
  have hc : IsClosed C := isClosed_eq
    (continuous_const.inner ((PiLp.continuous_apply 2 _ j).comp continuous_snd))
    (continuous_const.inner continuous_fst).neg
  have hs : (graph (F := F) μ e : Set _) ⊆ C := by
    rintro _ ⟨g,rfl⟩
    exact directionalDerivative_skew μ f g (e j)
  exact closure_minimal hs hc hp

omit [CompleteSpace F] in
lemma closedGraph_vertical {v : Gradient (F := F) μ (ι := ι)}
    (hv : ((0 : Lp F 2 μ),v) ∈ closedGraph μ e) : v = 0 := by
  apply PiLp.ext
  intro j
  apply (toL2_dense (F := F) μ).eq_zero_of_inner_right ℝ
  intro f
  simpa only [inner_zero_right,neg_zero] using closedGraph_pairing μ e hv j f
end
end BFSSSliceSobolev
namespace BFSSSliceSobolev
noncomputable section
open MeasureTheory Set Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def scaledCutoff (φ : ContDiffBump (0 : E)) (h : ℝ) (f : Core (E := E) (F := F)) :
    Core (E := E) (F := F) :=
  ⟨fun x => φ (h • x) • f x,
    (φ.contDiff.comp (contDiff_const.smul contDiff_id)).smul f.contDiff,
    f.hasCompactSupport.smul_left,by intro x hx; trivial⟩

lemma scaledCutoff_apply (φ : ContDiffBump (0 : E)) (h : ℝ)
    (f : Core (E := E) (F := F)) (x : E) : scaledCutoff φ h f x = φ (h • x) • f x := rfl

lemma scaledCutoff_support (φ : ContDiffBump (0 : E)) {h : ℝ} (hh : 0 < h)
    (f : Core (E := E) (F := F)) :
    tsupport (scaledCutoff φ h f : E → F) ⊆ Metric.closedBall 0 (φ.rOut/h) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hn
  have hx' : φ.rOut ≤ ‖h • x‖ := by
    have ht : φ.rOut/h < ‖x‖ := lt_of_not_ge (by simpa only [Metric.mem_closedBall,dist_zero_right] using hn)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hh]
    exact ((div_lt_iff₀ hh).mp ht).le.trans_eq (mul_comm _ _)
  have hz : φ (h • x) = 0 := φ.zero_of_le_dist (by simpa only [dist_zero_right] using hx')
  exact hx (by simp only [scaledCutoff_apply,hz,zero_smul])

lemma scaledCutoff_fderiv (φ : ContDiffBump (0 : E)) (h : ℝ)
    (f : Core (E := E) (F := F)) (x v : E) :
    fderiv ℝ (scaledCutoff φ h f : E → F) x v =
      φ (h • x) • fderiv ℝ (f : E → F) x v +
        (fderiv ℝ (φ : E → ℝ) (h • x) (h • v)) • f x := by
  have hφ : Differentiable ℝ (φ : E → ℝ) := (φ.contDiff : ContDiff ℝ 1 (φ : E → ℝ)).differentiable (by norm_num)
  have hf : Differentiable ℝ (f : E → F) := f.contDiff.differentiable (by simp)
  have hscale : HasFDerivAt (fun x : E => h • x) (h • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul h
  change fderiv ℝ (fun y => φ (h • y) • f y) x v = _
  have hc : DifferentiableAt ℝ (fun y => φ (h • y)) x :=
    hφ.differentiableAt.comp x hscale.differentiableAt
  rw [fderiv_fun_smul hc (hf x)]
  have he : fderiv ℝ (fun y => φ (h • y)) x =
      (fderiv ℝ (φ : E → ℝ) (h • x)).comp (h • ContinuousLinearMap.id ℝ E) :=
    ((hφ (h • x)).hasFDerivAt.comp x hscale).fderiv
  rw [he]
  rfl

lemma scaledCutoff_fderiv_bound (φ : ContDiffBump (0 : E)) {h D : ℝ} (hh : 0 ≤ h)
    (hD : ∀ x, ‖fderiv ℝ (φ : E → ℝ) x‖ ≤ D)
    (f : Core (E := E) (F := F)) (x v : E) (hv : ‖v‖ = 1) :
    ‖fderiv ℝ (scaledCutoff φ h f : E → F) x v‖^2 ≤
      2*‖fderiv ℝ (f : E → F) x‖^2 + 2*(D*h)^2*‖f x‖^2 := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have ha : ‖φ (h • x) • fderiv ℝ (f : E → F) x v‖ ≤ ‖fderiv ℝ (f : E → F) x‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg φ.nonneg]
    apply (mul_le_of_le_one_left (norm_nonneg _) φ.le_one).trans
    simpa only [hv,mul_one] using (fderiv ℝ (f : E → F) x).le_opNorm v
  have hb : ‖fderiv ℝ (φ : E → ℝ) (h • x) (h • v) • f x‖ ≤ D*h*‖f x‖ := by
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ‖fderiv ℝ (φ : E → ℝ) (h • x)‖*‖h • v‖ := (fderiv ℝ (φ : E → ℝ) (h • x)).le_opNorm _
      _ ≤ D*‖h • v‖ := mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)
      _ = D*h := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh,hv,mul_one]
  have hl : ‖fderiv ℝ (scaledCutoff φ h f : E → F) x v‖ ≤
      ‖fderiv ℝ (f : E → F) x‖ + D*h*‖f x‖ := by
    rw [scaledCutoff_fderiv]
    exact (norm_add_le _ _).trans (add_le_add ha hb)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hl 2
  have hd := sq_nonneg (‖fderiv ℝ (f : E → F) x‖ - D*h*‖f x‖)
  nlinarith

end
end BFSSSliceSobolev

end OAI
