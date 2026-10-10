import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowImplicit

namespace OAI

/-! Finite C⁴ dependence of the local path-space fixed point. This is the
regularity construction needed before identifying it with the existing flow. -/

noncomputable section
open Set ContinuousLinearMap
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_c4_rescaled_equation
    (N : FlowPath → FlowPath) (hN : ContDiff ℝ 4 N)
    (c : FlowPhase →L[ℝ] FlowPath) (A : FlowPath →L[ℝ] FlowPath) (a : FlowPhase) :
    ∃ U : (ℝ × FlowPhase) → FlowPath, ∃ S : Set (ℝ × FlowPhase),
      IsOpen S ∧ (0,a) ∈ S ∧ ContDiffOn ℝ 4 U S ∧ U (0,a) = c a ∧
        ∀ z ∈ S, U z = c z.2 + z.1 • A (N (U z)) := by
  let F : (ℝ × FlowPhase) × FlowPath → FlowPath :=
    fun z => z.2-c z.1.2-z.1.1 • A (N z.2)
  let b : FlowPath := c a
  have hF : ContDiff ℝ 4 F :=
    (contDiff_snd.sub (c.contDiff.comp (contDiff_snd.comp contDiff_fst))).sub
      ((contDiff_fst.comp contDiff_fst).smul (A.contDiff.comp (hN.comp contDiff_snd)))
  have hpart : fderiv ℝ F ((0,a),b) ∘L inr ℝ (ℝ × FlowPhase) FlowPath =
      ContinuousLinearMap.id ℝ FlowPath := by
    have hpair : HasFDerivAt (fun p : FlowPath => ((0,a),p))
        (inr ℝ (ℝ × FlowPhase) FlowPath) b :=
      (hasFDerivAt_const ((0:ℝ),a) b).prodMk (hasFDerivAt_id b)
    have hc := (hF.differentiable (by norm_num) ((0,a),b)).hasFDerivAt.comp b hpair
    have hd : HasFDerivAt (fun p : FlowPath => F ((0,a),p))
        (ContinuousLinearMap.id ℝ FlowPath) b := by
      have hi : HasFDerivAt (fun p : FlowPath => p)
          (ContinuousLinearMap.id ℝ FlowPath) b := hasFDerivAt_id b
      change HasFDerivAt (fun p : FlowPath => p-c a-(0:ℝ) • A (N p))
        (ContinuousLinearMap.id ℝ FlowPath) b
      have heq : (fun p : FlowPath => p-c a-(0:ℝ) • A (N p)) =
          (fun p : FlowPath => p-c a) := by
        funext p
        exact (congrArg (fun q : FlowPath => p-c a-q)
          (_root_.zero_smul ℝ (A (N p)))).trans (sub_zero _)
      rw [heq]
      exact hi.sub_const (c a)
    exact hc.unique hd
  have hi : (fderiv ℝ F ((0,a),b) ∘L inr ℝ (ℝ × FlowPhase) FlowPath).IsInvertible := by
    rw [hpart]
    exact ⟨ContinuousLinearEquiv.refl ℝ FlowPath,rfl⟩
  obtain ⟨U,S,hS,ha,hU,hb,hEq⟩ := flow_c4_implicit_neighborhood F hF (0,a) b hi
  refine ⟨U,S,hS,ha,hU,hb,fun z hz => ?_⟩
  have hz' : U z-c z.2-z.1 • A (N (U z)) = 0 := by
    have h := hEq z hz
    change U z-c z.2-z.1 • A (N (U z)) = b-c a-(0:ℝ) • A (N b) at h
    calc
      _ = b-c a-(0:ℝ) • A (N b) := h
      _ = b-c a := (congrArg (fun q : FlowPath => b-c a-q)
        (_root_.zero_smul ℝ (A (N b)))).trans (sub_zero _)
      _ = 0 := sub_self _
  simpa only [add_comm] using eq_add_of_sub_eq (sub_eq_zero.mp hz')

theorem flow_c4_rescaled_family (f : FlowPhase → FlowPhase)
    (hf : ContDiff ℝ 4 f) (a : FlowPhase) :
    ∃ U : (ℝ × FlowPhase) → FlowPath, ∃ S : Set (ℝ × FlowPhase),
      IsOpen S ∧ (0,a) ∈ S ∧ ContDiffOn ℝ 4 U S ∧
      U (0,a) = ContinuousMap.const WeakMTWTransport.UnitTime a ∧
      ∀ z ∈ S, U z = ContinuousMap.const WeakMTWTransport.UnitTime z.2+
        z.1 • WeakMTWTransport.unitPathIntegral
          ((⟨f,hf.continuous⟩ : C(FlowPhase,FlowPhase)).comp (U z)) := by
  let fC : C(FlowPhase,FlowPhase) := ⟨f,hf.continuous⟩
  exact flow_c4_rescaled_equation (fun p => fC.comp p)
    (WeakMTWTransport.contDiff_path_comp_nat 4 fC hf)
    (ContinuousLinearMap.const ℝ WeakMTWTransport.UnitTime) WeakMTWTransport.unitPathIntegral a

end ContinuumCoulomb

end

end OAI
