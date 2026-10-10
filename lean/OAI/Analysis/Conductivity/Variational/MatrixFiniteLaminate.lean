import Mathlib
import OAI.Analysis.Conductivity.Sobolev.BoundedMultiplier
import OAI.Analysis.Conductivity.Branching.RecoverJoinChild
import OAI.Analysis.Conductivity.Variational.PreliminaryQ

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
namespace ScalarConductivity

def matrixFiniteLaminate (a b : ℝ) : Set Symmetric3 :=
  spectralExtension {α | IsFiniteLaminate a b α}

theorem isOpen_matrixFiniteLaminate {a b : ℝ} (ha : 0 < a) :
    IsOpen (matrixFiniteLaminate a b) :=
  isOpen_spectralExtension (isOpen_finiteLaminate ha) (fun _ h e => h.permute e)

open Set Filter Topology

instance H1_isClosed : IsClosed (H1Space : Set JetSpace) :=
  Submodule.isClosed_topologicalClosure _

instance H1_completeSpace : CompleteSpace H1 :=
  (H1_isClosed : IsClosed (H1Space : Set JetSpace)).completeSpace_coe

instance H10_completeSpace : CompleteSpace H10 :=
  (H10_isClosed : IsClosed (H10 : Set H1)).completeSpace_coe

def jetValue : JetFiber →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => z 0
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

def jetLiftValue : ℝ →L[ℝ] JetFiber :=
  LinearMap.toContinuousLinearMap {
    toFun := fun r => WithLp.toLp 2 (Fin.cases r (fun _ => 0))
    map_add' := by intro x y; ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    map_smul' := by intro c x; ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }

def jetLiftGradient : R3 →L[ℝ] JetFiber :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => WithLp.toLp 2 (Fin.cases 0 (fun i => v i))
    map_add' := by intro x y; ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    map_smul' := by intro c x; ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }

lemma jetValue_smoothJet (f : R3 → ℝ) (x : R3) : jetValue (smoothJet f x) = f x := rfl
lemma jetGradient_smoothJet (f : R3 → ℝ) (x : R3) :
    jetGradient (smoothJet f x) = gradient f x := rfl

lemma jetFiber_decomposition (z : JetFiber) :
    z = jetLiftValue (jetValue z) + jetLiftGradient (jetGradient z) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · change z 0 = z 0 + 0; simp
  · change z i.succ = 0 + z i.succ; simp

lemma smoothJet_zero : smoothJet (fun _ : R3 => (0 : ℝ)) = 0 := by
  ext x i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [smoothJet, gradient]

lemma smoothJet_add {f g : R3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    smoothJet (f + g) = smoothJet f + smoothJet g := by
  ext x i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp [smoothJet, gradient, fderiv_add (hf x) (hg x)]

lemma smoothJet_smul (c : ℝ) {f : R3 → ℝ} (hf : Differentiable ℝ f) :
    smoothJet (c • f) = c • smoothJet f := by
  ext x i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp [smoothJet, gradient, fderiv_const_smul (hf x)]

lemma compactSmoothJets_zero : (0 : JetSpace) ∈ compactSmoothJets := by
  refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_, ?_, ?_⟩
  · simp
  · rw [smoothJet_zero]; exact MemLp.zero
  · simp only [smoothJet_zero, MemLp.toLp_zero]

lemma compactSmoothJets_add {z w : JetSpace} (hz : z ∈ compactSmoothJets)
    (hw : w ∈ compactSmoothJets) : z + w ∈ compactSmoothJets := by
  obtain ⟨f, hf, hfc, hfs, hfm, rfl⟩ := hz
  obtain ⟨g, hg, hgc, hgs, hgm, rfl⟩ := hw
  have hj := smoothJet_add (hf.differentiable (by simp)) (hg.differentiable (by simp))
  have hm : MemLp (smoothJet (f + g)) 2 ballMeasure := by rw [hj]; exact hfm.add hgm
  refine ⟨f + g, hf.add hg, hfc.add hgc,
    (tsupport_add f g).trans (union_subset hfs hgs), hm, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (hfm.toLp _) (hgm.toLp _), hfm.coeFn_toLp,
    hgm.coeFn_toLp, hm.coeFn_toLp] with x hsum hfx hgx hfgx
  rw [hsum, hfgx, hj]
  simp only [Pi.add_apply, hfx, hgx]

lemma compactSmoothJets_smul (c : ℝ) {z : JetSpace} (hz : z ∈ compactSmoothJets) :
    c • z ∈ compactSmoothJets := by
  obtain ⟨f, hf, hfc, hfs, hfm, rfl⟩ := hz
  have hj := smoothJet_smul c (hf.differentiable (by simp))
  have hm : MemLp (smoothJet (c • f)) 2 ballMeasure := by rw [hj]; exact hfm.const_smul c
  refine ⟨c • f, hf.const_smul c, hfc.smul_left,
    (tsupport_smul_subset_right (fun _ : R3 => c) f).trans hfs, hm, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (hfm.toLp _), hfm.coeFn_toLp,
    hm.coeFn_toLp] with x hc hfx hcx
  rw [hc, hcx, hj]
  simp only [Pi.smul_apply, hfx]

lemma span_compactSmoothJets : (Submodule.span ℝ compactSmoothJets : Set JetSpace) =
    compactSmoothJets := by
  let K : Submodule ℝ JetSpace := {
    carrier := compactSmoothJets
    zero_mem' := compactSmoothJets_zero
    add_mem' := compactSmoothJets_add
    smul_mem' := compactSmoothJets_smul }
  exact congrArg SetLike.coe (Submodule.span_eq K)

def ballPoincareConstant : ℝ :=
  eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure R3) ball 2 2

lemma ballPoincareConstant_nonneg : 0 ≤ ballPoincareConstant := by
  exact_mod_cast (eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure R3) ball 2 2).coe_nonneg

lemma norm_gradient_eq_norm_fderiv (f : R3 → ℝ) (x : R3) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ R3).symm.norm_map _

lemma compact_smooth_poincare {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ ball) :
    (eLpNorm f 2 ballMeasure).toReal ≤
      ballPoincareConstant * (eLpNorm (gradient f) 2 ballMeasure).toReal := by
  have hfm : MemLp (fderiv ℝ f) 2 (volume : Measure R3) :=
    (hf.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hfc.fderiv ℝ)
  have he := eLpNorm_le_eLpNorm_fderiv (volume : Measure R3)
    (hf.of_le (by simp) : ContDiff ℝ 1 f) ((subset_tsupport f).trans hfs)
    (p := 2) (by norm_num)
    (by norm_num [R3, finrank_euclideanSpace]) (Metric.isBounded_ball (x := (0 : R3)) (r := 3))
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfm.eLpNorm_ne_top) he
  have hgc : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ R3).symm.continuous.comp (hf.continuous_fderiv (by simp))
  have hg : eLpNorm (gradient f) 2 ballMeasure = eLpNorm (fderiv ℝ f) 2 ballMeasure :=
    eLpNorm_congr_norm_ae hgc.aestronglyMeasurable hfm.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall (norm_gradient_eq_norm_fderiv f))
  rw [hg]
  change (eLpNorm f 2 (volume.restrict ball)).toReal ≤
    ballPoincareConstant * (eLpNorm (fderiv ℝ f) 2 (volume.restrict ball)).toReal
  rw [eLpNorm_restrict_eq_of_support_subset hf.continuous.aestronglyMeasurable
      ((subset_tsupport f).trans hfs),
    eLpNorm_restrict_eq_of_support_subset hfm.aestronglyMeasurable
      ((support_fderiv_subset ℝ).trans hfs)]
  simpa [ENNReal.toReal_mul, ballPoincareConstant] using ht

lemma jetValue_compLp_smooth {f : R3 → ℝ} (hf : MemLp (smoothJet f) 2 ballMeasure) :
    (jetValue.compLp (hf.toLp _) : R3 → ℝ) =ᵐ[ballMeasure] f := by
  filter_upwards [jetValue.coeFn_compLp (hf.toLp _), hf.coeFn_toLp] with x hx hfx
  rw [hx, hfx, jetValue_smoothJet]

lemma jetGradient_compLp_smooth {f : R3 → ℝ} (hf : MemLp (smoothJet f) 2 ballMeasure) :
    (jetGradient.compLp (hf.toLp _) : R3 → R3) =ᵐ[ballMeasure] gradient f := by
  filter_upwards [jetGradient.coeFn_compLp (hf.toLp _), hf.coeFn_toLp] with x hx hfx
  rw [hx, hfx, jetGradient_smoothJet]

lemma compactSmoothJets_poincare {z : JetSpace} (hz : z ∈ compactSmoothJets) :
    ‖jetValue.compLp z‖ ≤ ballPoincareConstant * ‖jetGradient.compLp z‖ := by
  obtain ⟨f, hf, hfc, hfs, hfm, rfl⟩ := hz
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (jetValue_compLp_smooth hfm),
    eLpNorm_congr_ae (jetGradient_compLp_smooth hfm)]
  exact compact_smooth_poincare hf hfc hfs

lemma zeroTraceAmbient_poincare {z : JetSpace} (hz : z ∈ zeroTraceAmbient) :
    ‖jetValue.compLp z‖ ≤ ballPoincareConstant * ‖jetGradient.compLp z‖ := by
  have hc : IsClosed {z : JetSpace | ‖jetValue.compLp z‖ ≤
      ballPoincareConstant * ‖jetGradient.compLp z‖} :=
    isClosed_le ((jetValue.compLpL 2 ballMeasure).continuous.norm)
      (continuous_const.mul ((jetGradient.compLpL 2 ballMeasure).continuous.norm))
  apply closure_minimal (s := compactSmoothJets) (fun _ hz => compactSmoothJets_poincare hz) hc
  change z ∈ closure (Submodule.span ℝ compactSmoothJets : Set JetSpace) at hz
  rwa [span_compactSmoothJets] at hz

lemma jetSpace_decomposition (z : JetSpace) :
    z = jetLiftValue.compLp (jetValue.compLp z) +
      jetLiftGradient.compLp (jetGradient.compLp z) := by
  apply Lp.ext
  filter_upwards [jetLiftValue.coeFn_compLp (jetValue.compLp z),
    jetLiftGradient.coeFn_compLp (jetGradient.compLp z),
    jetValue.coeFn_compLp z, jetGradient.coeFn_compLp z,
    Lp.coeFn_add (jetLiftValue.compLp (jetValue.compLp z))
      (jetLiftGradient.compLp (jetGradient.compLp z))] with x hv hg hvx hgx ha
  rw [ha, Pi.add_apply, hv, hg, hvx, hgx]
  exact jetFiber_decomposition (z x)

def h10PoincareConstant : ℝ :=
  ‖jetLiftValue.compLpL 2 ballMeasure‖ * ballPoincareConstant +
    ‖jetLiftGradient.compLpL 2 ballMeasure‖ + 1

lemma h10PoincareConstant_pos : 0 < h10PoincareConstant := by
  have hp := ballPoincareConstant_nonneg
  unfold h10PoincareConstant
  positivity

lemma zeroTraceAmbient_norm_le {z : JetSpace} (hz : z ∈ zeroTraceAmbient) :
    ‖z‖ ≤ h10PoincareConstant * ‖jetGradient.compLp z‖ := by
  calc
    ‖z‖ ≤ ‖jetLiftValue.compLp (jetValue.compLp z)‖ +
        ‖jetLiftGradient.compLp (jetGradient.compLp z)‖ := by
      conv_lhs => rw [jetSpace_decomposition z]
      exact norm_add_le _ _
    _ ≤ ‖jetLiftValue.compLpL 2 ballMeasure‖ * ‖jetValue.compLp z‖ +
        ‖jetLiftGradient.compLpL 2 ballMeasure‖ * ‖jetGradient.compLp z‖ :=
      add_le_add ((jetLiftValue.compLpL 2 ballMeasure).le_opNorm _)
        ((jetLiftGradient.compLpL 2 ballMeasure).le_opNorm _)
    _ ≤ ‖jetLiftValue.compLpL 2 ballMeasure‖ *
        (ballPoincareConstant * ‖jetGradient.compLp z‖) +
        ‖jetLiftGradient.compLpL 2 ballMeasure‖ * ‖jetGradient.compLp z‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (zeroTraceAmbient_poincare hz)
        (norm_nonneg _)) le_rfl
    _ ≤ h10PoincareConstant * ‖jetGradient.compLp z‖ := by
      dsimp [h10PoincareConstant]
      nlinarith [norm_nonneg (jetGradient.compLp z)]

lemma H10_norm_le_weakGradientL (u : H10) :
    ‖u‖ ≤ h10PoincareConstant * ‖weakGradientL u.val‖ :=
  zeroTraceAmbient_norm_le u.property

lemma boundedMultiplier_inner_lower {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure α) (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂μ, |a x| ≤ C)
    (c : ℝ) (hac : ∀ᵐ x ∂μ, c ≤ a x) (u : Lp E 2 μ) :
    c * ‖u‖ ^ 2 ≤ inner ℝ (boundedMultiplier μ a ha C hC haC u) u := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner u u).const_mul c)
    (L2.integrable_inner _ _)
  filter_upwards [boundedMultiplier_apply_ae μ a ha C hC haC u, hac] with x hx hcx
  rw [hx, real_inner_smul_left]
  exact mul_le_mul_of_nonneg_right hcx (real_inner_self_nonneg)

lemma energyForm_coercive_lower (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂ballMeasure, |a x| ≤ C)
    (c : ℝ) (hc : 0 < c) (hac : ∀ᵐ x ∂ballMeasure, c ≤ a x)
    (u : H10) :
    c / h10PoincareConstant ^ 2 * ‖u‖ * ‖u‖ ≤ energyForm a ha C hC haC u.val u.val := by
  have hnorm := H10_norm_le_weakGradientL u
  have hsq := mul_self_le_mul_self (norm_nonneg u) hnorm
  have hlo := boundedMultiplier_inner_lower ballMeasure a ha C hC haC c hac
    (weakGradientL u.val)
  change c / h10PoincareConstant ^ 2 * ‖u‖ * ‖u‖ ≤
    inner ℝ (boundedMultiplier ballMeasure a ha C hC haC (weakGradientL u.val))
      (weakGradientL u.val)
  calc
    _ = c * (‖u‖ ^ 2 / h10PoincareConstant ^ 2) := by ring
    _ ≤ c * ‖weakGradientL u.val‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      apply (div_le_iff₀ (sq_pos_of_pos h10PoincareConstant_pos)).2
      nlinarith [hsq]
    _ ≤ _ := hlo

theorem exists_DirichletToNeumann (a : R3 → ℝ)
    (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ᵐ x ∂ballMeasure, |a x| ≤ C)
    (c : ℝ) (hc : 0 < c) (hac : ∀ᵐ x ∂ballMeasure, c ≤ a x) :
    ∃ Λ : DNOperator, IsDirichletToNeumann a Λ := by
  obtain ⟨Λ, hΛ⟩ := exists_variational_DN H10 (energyForm a ha C hC haC)
    ⟨c / h10PoincareConstant ^ 2, div_pos hc (sq_pos_of_pos h10PoincareConstant_pos),
      energyForm_coercive_lower a ha C hC haC c hc hac⟩
  refine ⟨Λ, ?_⟩
  intro f
  obtain ⟨u, hu, hh, huniq, hident⟩ := hΛ f
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · intro h hhmem
    rw [← energyForm_apply a ha C hC haC]
    exact hh h hhmem
  · intro u' hu' hhu'
    apply huniq u' hu'
    intro h hhmem
    rw [energyForm_apply a ha C hC haC]
    exact hhu' h hhmem
  · intro v
    rw [← energyForm_apply a ha C hC haC]
    exact hident v

end ScalarConductivity

end

end OAI
