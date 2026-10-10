import Mathlib
import OAI.Geometry.NearbyLagrangian.HomogeneousCritical

namespace OAI

/-! Smooth homogeneous families and regular critical parametrizations. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes.RegularHomogeneous

open scoped Manifold

variable {W E B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [CompleteSpace W] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℝ, E) ∞ B]

def SmoothFamily (f : B → RegularHomogeneous W) : Prop :=
  ∀ p : B × W, p.2 ≠ 0 → ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞
    (fun x : B × W => f x.1 x.2) p

omit [CompleteSpace W] in

lemma contMDiffAt_family_fderiv {f : B → RegularHomogeneous W} {p : B × W}
    (hf : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞
      (fun x : B × W => f x.1 x.2) p) :
    ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, W →L[ℝ] ℝ) ∞
      (fun x : B × W => fderiv ℝ (f x.1) x.2) p := by
  let F : (B × W) → W → ℝ := fun x w => f x.1 w
  have hF : ContMDiffAt ((𝓘(ℝ, E).prod 𝓘(ℝ, W)).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry F) (p, p.2) :=
    hf.comp (p, p.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
  have h := hF.mfderiv (m := ∞) F Prod.snd contMDiffAt_snd (by simp)
  erw [inTangentCoordinates_model_space] at h
  simpa only [F, mfderiv_eq_fderiv] using h

lemma contMDiffAt_family_gradient {f : B → RegularHomogeneous W} {p : B × W}
    (hf : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞
      (fun x : B × W => f x.1 x.2) p) :
    ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, W) ∞
      (fun x : B × W => gradient (f x.1) x.2) p := by
  exact (InnerProductSpace.toDual ℝ W).symm.contDiff.contDiffAt.comp_contMDiffAt
    (contMDiffAt_family_fderiv hf)

variable {n : ℕ} [Fact (Module.finrank ℝ W = n + 1)]

lemma contMDiff_family_gradient {f : B → RegularHomogeneous W} (hf : SmoothFamily (E := E) f) :
    ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) 𝓘(ℝ, W) ∞
      (fun x : B × Metric.sphere (0 : W) 1 => gradient (f x.1) x.2) := by
  intro p
  have hgg : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, W) ∞
      (fun x : B × W => gradient (f x.1) x.2) (p.1, (p.2 : W)) :=
    contMDiffAt_family_gradient (hf (p.1, (p.2 : W)) (ne_zero_of_mem_unit_sphere p.2))
  have hinc : ContMDiffAt (𝓘(ℝ, E).prod (𝓡 n)) (𝓘(ℝ, E).prod 𝓘(ℝ, W)) ∞
      (fun x : B × Metric.sphere (0 : W) 1 => (x.1, (x.2 : W))) p :=
    contMDiffAt_fst.prodMk ((contMDiff_coe_sphere p.2).comp _ contMDiffAt_snd)
  exact ContMDiffAt.comp (f := fun x : B × Metric.sphere (0 : W) 1 =>
    (x.1, (x.2 : W))) (g := fun x : B × W => gradient (f x.1) x.2) p hgg hinc

theorem contMDiff_family_direction {f : B → RegularHomogeneous W} (hf : SmoothFamily (E := E) f) :
    ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) (𝓡 n) ∞
      (fun x : B × Metric.sphere (0 : W) 1 => (f x.1).direction x.2) := by
  have hg := contMDiff_family_gradient (n := n) hf
  have hn : ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun x : B × Metric.sphere (0 : W) 1 => ‖gradient (f x.1) x.2‖) := by
    intro x
    have hnorm : ContDiffAt ℝ ∞ (fun w : W => ‖w‖) (gradient (f x.1) x.2) :=
      contDiffAt_id.norm ℝ ((f x.1).gradient_ne_zero (ne_zero_of_mem_unit_sphere x.2))
    exact ContDiffAt.comp_contMDiffAt (f := fun y : B × Metric.sphere (0 : W) 1 =>
      gradient (f y.1) y.2) (g := fun w : W => ‖w‖) hnorm (hg x)
  have hi := hn.inv₀ (fun x => norm_ne_zero_iff.mpr
    ((f x.1).gradient_ne_zero (ne_zero_of_mem_unit_sphere x.2)))
  exact (hi.smul hg).codRestrict_sphere (fun x => ((f x.1).direction x.2).property)

theorem contMDiff_family_radialSolution {f : B → RegularHomogeneous W} (hf : SmoothFamily (E := E) f)
    {R : B → ℝ} (hR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) :
    ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) 𝓘(ℝ, W) ∞
      (fun x : B × Metric.sphere (0 : W) 1 => (f x.1).radialSolution (R x.1) x.2) := by
  have hg := contMDiff_family_gradient (n := n) hf
  have hn : ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun x : B × Metric.sphere (0 : W) 1 => ‖gradient (f x.1) x.2‖) := by
    intro x
    have hnorm : ContDiffAt ℝ ∞ (fun w : W => ‖w‖) (gradient (f x.1) x.2) :=
      contDiffAt_id.norm ℝ ((f x.1).gradient_ne_zero (ne_zero_of_mem_unit_sphere x.2))
    exact ContDiffAt.comp_contMDiffAt (f := fun y : B × Metric.sphere (0 : W) 1 =>
      gradient (f y.1) y.2) (g := fun w : W => ‖w‖) hnorm (hg x)
  exact ((hR.comp contMDiff_fst).div₀ hn
    (fun x => norm_ne_zero_iff.mpr
      ((f x.1).gradient_ne_zero (ne_zero_of_mem_unit_sphere x.2)))).smul
      (contMDiff_coe_sphere.comp contMDiff_snd)

theorem mfderiv_family_radialSolution_injective {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) (hRp : ∀ b, 0 < R b)
    (x : B × Metric.sphere (0 : W) 1) :
    Function.Injective (mfderiv (𝓘(ℝ, E).prod (𝓡 n)) (𝓘(ℝ, E).prod 𝓘(ℝ, W))
      (fun y : B × Metric.sphere (0 : W) 1 =>
        (y.1, (f y.1).radialSolution (R y.1) y.2)) x) := by
  let j : B × Metric.sphere (0 : W) 1 → B × W :=
    fun y => (y.1, (f y.1).radialSolution (R y.1) y.2)
  let A : B × W → B × W := fun y => (y.1, ‖y.2‖⁻¹ • y.2)
  have hj : ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) (𝓘(ℝ, E).prod 𝓘(ℝ, W)) ∞ j :=
    contMDiff_fst.prodMk (contMDiff_family_radialSolution hf hR)
  have hnorm : ContDiffAt ℝ ∞ (fun w : W => ‖w‖⁻¹ • w) (j x).2 :=
    ((contDiffAt_id.norm ℝ ((f x.1).radialSolution_ne_zero _ (hRp _) x.2)).inv
      (norm_ne_zero_iff.mpr ((f x.1).radialSolution_ne_zero _ (hRp _) x.2))).smul
        contDiffAt_id
  have hA : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) (𝓘(ℝ, E).prod 𝓘(ℝ, W)) ∞ A (j x) :=
    contMDiffAt_fst.prodMk (ContDiffAt.comp_contMDiffAt (f := Prod.snd)
      (g := fun w : W => ‖w‖⁻¹ • w) hnorm contMDiffAt_snd)
  have he : A ∘ j = Prod.map id ((↑) : Metric.sphere (0 : W) 1 → W) := by
    funext y
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val ((f y.1).angularPosition_radialSolution _ (hRp _) y.2)
  have hd := mfderiv_comp x (hA.mdifferentiableAt (by simp))
    (hj.mdifferentiable (by simp) x)
  rw [he] at hd
  have hinc : Function.Injective (mfderiv (𝓘(ℝ, E).prod (𝓡 n))
      (𝓘(ℝ, E).prod 𝓘(ℝ, W)) (Prod.map id
        ((↑) : Metric.sphere (0 : W) 1 → W)) x) := by
    rw [mfderiv_prodMap mdifferentiableAt_id
      ((contMDiff_coe_sphere (m := ∞) x.2).mdifferentiableAt (by simp)), mfderiv_id]
    have hs : Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, W)
        ((↑) : Metric.sphere (0 : W) 1 → W) x.2) := by
      convert! injective_mvfderiv_subtypeVal_sphere (n := n) x.2 using 1
    intro a b hab
    change (a.1, mfderiv (𝓡 n) 𝓘(ℝ, W)
      ((↑) : Metric.sphere (0 : W) 1 → W) x.2 a.2) =
      (b.1, mfderiv (𝓡 n) 𝓘(ℝ, W)
      ((↑) : Metric.sphere (0 : W) 1 → W) x.2 b.2) at hab
    have h₁ : a.1 = b.1 := congrArg (fun z : E × W => z.1) hab
    have h₂ : mfderiv (𝓡 n) 𝓘(ℝ, W)
        ((↑) : Metric.sphere (0 : W) 1 → W) x.2 a.2 =
        mfderiv (𝓡 n) 𝓘(ℝ, W)
        ((↑) : Metric.sphere (0 : W) 1 → W) x.2 b.2 :=
      congrArg (fun z : E × W => z.2) hab
    exact Prod.ext h₁ (hs h₂)
  intro a b hab
  apply hinc
  rw [hd]
  exact congrArg (mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, W))
    (𝓘(ℝ, E).prod 𝓘(ℝ, W)) A (j x)) hab

omit [CompleteSpace W] [IsManifold 𝓘(ℝ, E) ∞ B] in

lemma SmoothFamily.smoothOffZero {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) (b : B) : (f b).SmoothOffZero := by
  intro w hw
  have hw' : w ≠ 0 := by simpa using hw
  have h := (hf (b, w) hw').comp w (contMDiffAt_const.prodMk contMDiffAt_id)
  exact (contMDiffAt_iff_contDiffAt.mp h).contDiffWithinAt

def familyCriticalParam (f : B → RegularHomogeneous W) (R : B → ℝ)
    (p : B × Metric.sphere (0 : W) 1) :
    (B × Metric.sphere (0 : W) 1) × W :=
  ((p.1, (f p.1).direction p.2), (f p.1).radialSolution (R p.1) p.2)

theorem contMDiff_familyCriticalParam {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) :
    ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W)) ∞
      (familyCriticalParam f R) :=
  (contMDiff_fst.prodMk (contMDiff_family_direction hf)).prodMk
    (contMDiff_family_radialSolution hf hR)

abbrev FamilyCriticalLocus (f : B → RegularHomogeneous W) (R : B → ℝ) :=
  {p : (B × Metric.sphere (0 : W) 1) × W //
    gradient (f p.1.1) p.2 = R p.1.1 • (p.1.2 : W)}

def familyCriticalHomeomorph {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) (hRp : ∀ b, 0 < R b) :
    (B × Metric.sphere (0 : W) 1) ≃ₜ FamilyCriticalLocus f R where
  toFun p := ⟨familyCriticalParam f R p, (f p.1).radialSolution_critical _ (hRp _) p.2⟩
  invFun p := (p.val.1.1, angularPosition p.val.2
    ((f p.val.1.1).critical_ne_zero _ (hRp _) ⟨(p.val.2, p.val.1.2), p.property⟩))
  left_inv p := by
    apply Prod.ext
    · rfl
    · exact (f p.1).angularPosition_radialSolution _ (hRp _) p.2
  right_inv p := by
    let p₀ : (f p.val.1.1).CriticalLocus (R p.val.1.1) :=
      ⟨(p.val.2, p.val.1.2), p.property⟩
    have he := (f p.val.1.1).criticalHomeomorph (R p.val.1.1) (hRp _) |>.apply_symm_apply p₀
    have hev := congrArg Subtype.val he
    have hwp : p.val.2 ≠ 0 := (f p.val.1.1).critical_ne_zero _ (hRp _) p₀
    apply Subtype.ext
    change ((p.val.1.1, (f p.val.1.1).direction (angularPosition p.val.2 hwp)),
      (f p.val.1.1).radialSolution (R p.val.1.1) (angularPosition p.val.2 hwp)) = p.val
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact congrArg (fun z : W × Metric.sphere (0 : W) 1 => z.2) hev
    · exact congrArg (fun z : W × Metric.sphere (0 : W) 1 => z.1) hev
  continuous_toFun := (contMDiff_familyCriticalParam (n := n) hf hR).continuous.subtype_mk _
  continuous_invFun := by
    have hw (p : FamilyCriticalLocus f R) : p.val.2 ≠ 0 :=
      (f p.val.1.1).critical_ne_zero _ (hRp _) ⟨(p.val.2, p.val.1.2), p.property⟩
    apply Continuous.prodMk
    · exact continuous_fst.comp (continuous_fst.comp continuous_subtype_val)
    · apply Continuous.subtype_mk
      exact ((continuous_snd.comp continuous_subtype_val).norm.inv₀
        (fun p => norm_ne_zero_iff.mpr (hw p))).smul
          (continuous_snd.comp continuous_subtype_val)

theorem mfderiv_familyCriticalParam_injective {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) (hRp : ∀ b, 0 < R b)
    (x : B × Metric.sphere (0 : W) 1) :
    Function.Injective (mfderiv (𝓘(ℝ, E).prod (𝓡 n))
      ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W)) (familyCriticalParam f R) x) := by
  let P : (B × Metric.sphere (0 : W) 1) × W → B × W := fun p => (p.1.1, p.2)
  have hP : ContMDiff ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W))
      (𝓘(ℝ, E).prod 𝓘(ℝ, W)) ∞ P :=
    (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
  have hd := mfderiv_comp x
    (hP.mdifferentiable (by simp) (familyCriticalParam f R x))
    ((contMDiff_familyCriticalParam hf hR).mdifferentiable (by simp) x)
  intro a b hab
  apply mfderiv_family_radialSolution_injective hf hR hRp x
  change mfderiv _ _ (P ∘ familyCriticalParam f R) x a =
    mfderiv _ _ (P ∘ familyCriticalParam f R) x b
  erw [hd]
  exact congrArg (mfderiv ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W))
    (𝓘(ℝ, E).prod 𝓘(ℝ, W)) P (familyCriticalParam f R x)) hab

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous

open scoped Manifold

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

lemma contDiffAt_gradient {f : RegularHomogeneous W} (hf : f.SmoothOffZero)
    {w : W} (hw : w ≠ 0) : ContDiffAt ℝ ∞ (gradient f) w := by
  have hfw : ContDiffAt ℝ ∞ f w :=
    hf.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hw))
  exact (InnerProductSpace.toDual ℝ W).symm.contDiff.contDiffAt.comp w
    (hfw.fderiv_right (m := ∞) (by simp))

lemma gradient_radial_derivative {f : RegularHomogeneous W} (hf : f.SmoothOffZero)
    {w : W} (hw : w ≠ 0) : fderiv ℝ (gradient f) w w = gradient f w := by
  have hl : HasDerivAt (fun t : ℝ => gradient f (t • w))
      (fderiv ℝ (gradient f) w w) 1 := by
    have hd : HasFDerivAt (gradient f) (fderiv ℝ (gradient f) w) ((1 : ℝ) • w) := by
      simpa using ((f.contDiffAt_gradient hf hw).differentiableAt (by simp)).hasFDerivAt
    convert! hd.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const w) using 1
    simp only [one_smul]
  have hr : HasDerivAt (fun t : ℝ => t • gradient f w) (gradient f w) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const (gradient f w)
  have heq : (fun t : ℝ => gradient f (t • w)) =ᶠ[𝓝 1]
      (fun t => t • gradient f w) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact f.gradient_smul ht w
  exact (hl.congr_of_eventuallyEq heq.symm).unique hr

lemma contDiffAt_gradient_direction {f : RegularHomogeneous W} (hf : f.SmoothOffZero)
    {w : W} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : W => ‖gradient f x‖⁻¹ • gradient f x) w := by
  have hg := f.contDiffAt_gradient hf hw
  exact ((hg.norm ℝ (f.gradient_ne_zero hw)).inv
    (norm_ne_zero_iff.mpr (f.gradient_ne_zero hw))).smul hg

lemma contDiffAt_radial_solution {f : RegularHomogeneous W} (hf : f.SmoothOffZero)
    (R : ℝ) {w : W} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : W => (R / ‖gradient f x‖) • x) w := by
  exact (contDiffAt_const.div ((f.contDiffAt_gradient hf hw).norm ℝ
    (f.gradient_ne_zero hw)) (norm_ne_zero_iff.mpr (f.gradient_ne_zero hw))).smul contDiffAt_id

theorem contMDiff_direction [FiniteDimensional ℝ W] {n : ℕ}
    [Fact (Module.finrank ℝ W = n + 1)] {f : RegularHomogeneous W} (hf : f.SmoothOffZero) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ f.direction := by
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞
      (fun u : Metric.sphere (0 : W) 1 => (f.direction u : W)) := by
    intro u
    exact (f.contDiffAt_gradient_direction hf (ne_zero_of_mem_unit_sphere u)).comp_contMDiffAt
      (contMDiff_coe_sphere u)
  exact hs.codRestrict_sphere (fun u => (f.direction u).property)

theorem contMDiff_radialSolution [FiniteDimensional ℝ W] {n : ℕ}
    [Fact (Module.finrank ℝ W = n + 1)] {f : RegularHomogeneous W}
    (hf : f.SmoothOffZero) (R : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ (f.radialSolution R) := by
  intro u
  exact (f.contDiffAt_radial_solution hf R (ne_zero_of_mem_unit_sphere u)).comp_contMDiffAt
    (contMDiff_coe_sphere u)

theorem contMDiff_criticalParametrization [FiniteDimensional ℝ W] {n : ℕ}
    [Fact (Module.finrank ℝ W = n + 1)] {f : RegularHomogeneous W}
    (hf : f.SmoothOffZero) (R : ℝ) :
    ContMDiff (𝓡 n) (𝓘(ℝ, W).prod (𝓡 n)) ∞
      (fun u : Metric.sphere (0 : W) 1 => (f.radialSolution R u, f.direction u)) :=
  (f.contMDiff_radialSolution hf R).prodMk (f.contMDiff_direction hf)

def criticalEquation (f : RegularHomogeneous W) (R : ℝ)
    (p : W × Metric.sphere (0 : W) 1) : W :=
  gradient f p.1 - R • (p.2 : W)

lemma criticalEquation_mfderiv [FiniteDimensional ℝ W] {n : ℕ}
    [Fact (Module.finrank ℝ W = n + 1)] {f : RegularHomogeneous W}
    (hf : f.SmoothOffZero) (R : ℝ) (p : W × Metric.sphere (0 : W) 1)
    (hw : p.1 ≠ 0) :
    mfderiv (𝓘(ℝ, W).prod (𝓡 n)) 𝓘(ℝ, W) (f.criticalEquation R) p =
      (fderiv ℝ (gradient f) p.1).comp (ContinuousLinearMap.fst ℝ W (EuclideanSpace ℝ (Fin n))) -
        R • ((mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) p.2).comp
          (ContinuousLinearMap.snd ℝ W (EuclideanSpace ℝ (Fin n)))) := by
  have hg := ((f.contDiffAt_gradient hf hw).differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt
  have hc := ((contMDiff_coe_sphere (n := n) (m := (1 : ℕ∞ω)) p.2).mdifferentiableAt
    one_ne_zero).hasMFDerivAt
  have hs := ((hg.comp p (hasMFDerivAt_fst p)).sub
    ((hc.comp p (hasMFDerivAt_snd p)).const_smul R)).mfderiv
  convert! hs using 2

theorem criticalEquation_regular [FiniteDimensional ℝ W] {n : ℕ}
    [Fact (Module.finrank ℝ W = n + 1)] {f : RegularHomogeneous W}
    (hf : f.SmoothOffZero) (R : ℝ) (hR : 0 < R)
    (p : f.CriticalLocus R) :
    Function.Surjective (mfderiv (𝓘(ℝ, W).prod (𝓡 n)) 𝓘(ℝ, W)
      (f.criticalEquation R) p.val) := by
  intro z
  change W at z
  let t : ℝ := ⟪(p.val.2 : W), z⟫_ℝ
  let zt : W := z - t • (p.val.2 : W)
  have hzperp : ⟪(p.val.2 : W), zt⟫_ℝ = 0 := by
    simp [zt, t, inner_sub_right, inner_smul_right]
  have hzr : zt ∈ (mvfderiv (𝓡 n)
      ((↑) : Metric.sphere (0 : W) 1 → W) p.val.2).range := by
    rw [range_mvfderiv_subtypeVal]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hzperp
  obtain ⟨a, ha⟩ := hzr
  change mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) p.val.2 a = zt at ha
  refine ⟨((t / R) • p.val.1, (-R⁻¹) • a), ?_⟩
  rw [f.criticalEquation_mfderiv hf R p.val (f.critical_ne_zero R hR p)]
  change fderiv ℝ (gradient f) p.val.1 ((t / R) • p.val.1) -
    R • (mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) p.val.2 ((-R⁻¹) • a)) = z
  rw [map_smul, f.gradient_radial_derivative hf (f.critical_ne_zero R hR p),
    p.property, smul_smul, div_mul_cancel₀ t hR.ne', map_smul, ha, smul_smul,
    mul_neg, mul_inv_cancel₀ hR.ne', neg_one_smul, sub_neg_eq_add]
  dsimp [zt]
  abel

end NearbyLagrangian.Tubes.RegularHomogeneous

end

end OAI
