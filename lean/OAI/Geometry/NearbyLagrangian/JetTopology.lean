import Mathlib
import OAI.Geometry.NearbyLagrangian.HomogeneousFunctions

namespace OAI

/-! The joint jet topology and continuity of homogeneous operations. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes

variable {W Z B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace B]

theorem continuous_homogeneous_family {A : B → W → Z} {d : ℕ} (hd : d ≠ 0)
    (hzero : ∀ b, A b 0 = 0)
    (hhom : ∀ b (r : ℝ), 0 < r → ∀ w, A b (r • w) = r ^ d • A b w)
    (S : B → C(Metric.sphere (0 : W) 1, Z)) (hS : Continuous S)
    (hSval : ∀ b u, S b u = A b u) :
    Continuous (fun p : B × W => A p.1 p.2) := by
  let u : {w : W // w ≠ 0} → Metric.sphere (0 : W) 1 := fun w =>
    ⟨‖(w : W)‖⁻¹ • (w : W), by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr w.property)⟩
  have hu : Continuous u := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.norm.inv₀
      (fun w => norm_ne_zero_iff.mpr w.property)).smul continuous_subtype_val
  have hrec (w : {w : W // w ≠ 0}) : ‖(w : W)‖ • (u w : W) = w := by
    simp only [u, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr w.property), one_smul]
  have hrad (b : B) (w : {w : W // w ≠ 0}) :
      A b w = ‖(w : W)‖ ^ d • S b (u w) := by
    rw [hSval, ← hhom b ‖(w : W)‖ (norm_pos_iff.mpr w.property), hrec]
  have hbound (b : B) (w : W) : ‖A b w‖ ≤ ‖S b‖ * ‖w‖ ^ d := by
    by_cases hw : w = 0
    · simp [hw, hzero, hd]
    · rw [hrad b ⟨w, hw⟩, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (norm_nonneg w) d), mul_comm ‖S b‖]
      exact mul_le_mul_of_nonneg_left ((S b).norm_coe_le_norm _) (pow_nonneg (norm_nonneg w) d)
  have hon : ContinuousOn (fun p : B × W => A p.1 p.2) {p | p.2 ≠ 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    let v : {p : B × W // p.2 ≠ 0} → {w : W // w ≠ 0} := fun p => ⟨p.1.2, p.2⟩
    have hv : Continuous v := (continuous_snd.comp continuous_subtype_val).subtype_mk _
    have he : Continuous (fun p : {p : B × W // p.2 ≠ 0} =>
        S p.1.1 (u (v p))) :=
      continuous_eval.comp ((hS.comp (continuous_fst.comp continuous_subtype_val)).prodMk (hu.comp hv))
    convert! ((continuous_snd.comp continuous_subtype_val).norm.pow d).smul he using 1
    ext p
    exact hrad p.1.1 (v p)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.2 = 0
  · rw [ContinuousAt, hp, hzero]
    apply squeeze_zero_norm (fun x : B × W => hbound x.1 x.2)
    have hc : Continuous (fun x : B × W => ‖S x.1‖ * ‖x.2‖ ^ d) :=
      (hS.comp continuous_fst).norm.mul (continuous_snd.norm.pow d)
    simpa [ContinuousAt, hp, hd] using hc.continuousAt (x := p)
  · exact hon.continuousAt ((isOpen_ne_fun continuous_snd continuous_const).mem_nhds hp)

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Tubes.RegularHomogeneous

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]

omit [ProperSpace W] in
@[simp] theorem fderiv_zero (f : RegularHomogeneous W) : fderiv ℝ f 0 = 0 := by
  have h := f.fderiv_smul (r := 2) (by norm_num) 0
  simp only [smul_zero, two_smul] at h
  apply add_left_cancel (a := fderiv ℝ f 0)
  simpa only [add_zero] using h.symm

theorem continuous_eval : Continuous (fun p : RegularHomogeneous W × W => p.1 p.2) := by
  apply continuous_homogeneous_family (d := 2) (by decide) (fun f => f.map_zero)
    (fun f r hr w => by simpa only [smul_eq_mul] using f.homogeneity r hr w)
    (fun f => f.jet.1) (continuous_fst.comp continuous_induced_dom)
  intro f u
  rfl

theorem continuous_fderiv_eval :
    Continuous (fun p : RegularHomogeneous W × W => fderiv ℝ p.1 p.2) := by
  apply continuous_homogeneous_family (A := fun (f : RegularHomogeneous W) w => fderiv ℝ f w) (d := 1) (by decide) (fun f => f.fderiv_zero)
    (fun f r hr w => by simpa only [pow_one] using f.fderiv_smul hr w)
    (fun f => f.jet.2) (continuous_snd.comp continuous_induced_dom)
  intro f u
  rfl

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous

variable {W V B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace B]

theorem continuous_of_joint_jet {A : B → RegularHomogeneous W}
    (hval : Continuous (fun p : B × Metric.sphere (0 : W) 1 => A p.1 p.2))
    (hder : Continuous (fun p : B × Metric.sphere (0 : W) 1 => fderiv ℝ (A p.1) p.2)) :
    Continuous A := by
  apply continuous_induced_rng.mpr
  exact (ContinuousMap.continuous_of_continuous_uncurry (fun b => (A b).jet.1) hval).prodMk
    (ContinuousMap.continuous_of_continuous_uncurry (fun b => (A b).jet.2) hder)

@[simp] theorem fderiv_pullback (f : RegularHomogeneous V) (e : W ≃L[ℝ] V) (w : W) :
    fderiv ℝ (f.pullback e) w = (fderiv ℝ f (e w)).comp (e : W →L[ℝ] V) :=
  ((f.differentiable (e w)).hasFDerivAt.comp w e.hasFDerivAt).fderiv

@[simp] theorem fderiv_directSum (f : RegularHomogeneous W) (g : RegularHomogeneous V)
    (w : W × V) : fderiv ℝ (f.directSum g) w =
      (fderiv ℝ f w.1).comp (ContinuousLinearMap.fst ℝ W V) +
      (fderiv ℝ g w.2).comp (ContinuousLinearMap.snd ℝ W V) :=
  (((f.differentiable w.1).hasFDerivAt.comp w
    (ContinuousLinearMap.fst ℝ W V).hasFDerivAt).add
    ((g.differentiable w.2).hasFDerivAt.comp w
    (ContinuousLinearMap.snd ℝ W V).hasFDerivAt)).fderiv

theorem continuous_pullback [ProperSpace V] (e : W ≃L[ℝ] V) :
    Continuous (fun f : RegularHomogeneous V => f.pullback e) := by
  apply continuous_of_joint_jet
  · exact continuous_eval.comp
      (continuous_fst.prodMk (e.continuous.comp (continuous_subtype_val.comp continuous_snd)))
  · simp only [fderiv_pullback]
    exact (continuous_fderiv_eval.comp
      (continuous_fst.prodMk (e.continuous.comp (continuous_subtype_val.comp continuous_snd)))).clm_comp
      continuous_const

theorem continuous_directSum [ProperSpace W] [ProperSpace V] :
    Continuous (fun p : RegularHomogeneous W × RegularHomogeneous V => p.1.directSum p.2) := by
  apply continuous_of_joint_jet
  · exact (continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk
        (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))).add
      (continuous_eval.comp
        ((continuous_snd.comp continuous_fst).prodMk
          (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))))
  · simp only [fderiv_directSum]
    exact ((continuous_fderiv_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk
        (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))).clm_comp
      continuous_const).add
      ((continuous_fderiv_eval.comp
        ((continuous_snd.comp continuous_fst).prodMk
          (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))).clm_comp
        continuous_const)

end NearbyLagrangian.Tubes.RegularHomogeneous

end

end OAI
