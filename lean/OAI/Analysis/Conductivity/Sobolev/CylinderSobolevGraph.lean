import Mathlib
import OAI.Analysis.Conductivity.Geometry.CylinderPolynomial

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

abbrev CylinderTraceAmbient (s : Fin 3 → ℝ) (R : ℝ) :=
  FiniteCylinderJets R × (spectralTraceGraph (torusRate s) × spectralTraceGraph (torusRate s))

def cylinderPolynomialGraphL (s : Fin 3 → ℝ) (R : ℝ) :
    (TorusModes →₀ smoothComplexAxis) →ₗ[ℂ] CylinderTraceAmbient s R :=
  (cylinderPolynomialJetL R).prod
    ((cylinderPolynomialTraceL s 0).prod (cylinderPolynomialTraceL s R))

def cylinderSobolevGraph (s : Fin 3 → ℝ) (R : ℝ) : Submodule ℂ (CylinderTraceAmbient s R) :=
  (LinearMap.range (cylinderPolynomialGraphL s R)).topologicalClosure

def cylinderH1Space (R : ℝ) : Submodule ℂ (FiniteCylinderJets R) :=
  (LinearMap.range (cylinderPolynomialJetL R)).topologicalClosure

instance cylinderSobolevGraph_complete (s : Fin 3 → ℝ) (R : ℝ) :
    CompleteSpace (cylinderSobolevGraph s R) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

instance cylinderH1Space_complete (R : ℝ) : CompleteSpace (cylinderH1Space R) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

lemma cylinderSobolevGraph_trace_bound (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R)
    (z : cylinderSobolevGraph s R) :
    ‖z.val.2.1‖^2≤cylinderTraceConstant s R*‖z.val.1‖^2 ∧
    ‖z.val.2.2‖^2≤cylinderTraceConstant s R*‖z.val.1‖^2 := by
  have hc : IsClosed {z : CylinderTraceAmbient s R |
      ‖z.2.1‖^2≤cylinderTraceConstant s R*‖z.1‖^2 ∧
      ‖z.2.2‖^2≤cylinderTraceConstant s R*‖z.1‖^2} := by
    apply IsClosed.inter
    · exact isClosed_le ((continuous_fst.comp continuous_snd).norm.pow 2)
        (continuous_const.mul (continuous_fst.norm.pow 2))
    · exact isClosed_le ((continuous_snd.comp continuous_snd).norm.pow 2)
        (continuous_const.mul (continuous_fst.norm.pow 2))
  have hr : (LinearMap.range (cylinderPolynomialGraphL s R) : Set (CylinderTraceAmbient s R)) ⊆
      {z | ‖z.2.1‖^2≤cylinderTraceConstant s R*‖z.1‖^2 ∧
      ‖z.2.2‖^2≤cylinderTraceConstant s R*‖z.1‖^2} := by
    rintro _ ⟨p,rfl⟩
    exact ⟨cylinderPolynomial_trace_bound s hR p (Or.inl rfl),
      cylinderPolynomial_trace_bound s hR p (Or.inr rfl)⟩
  exact closure_minimal hr hc z.property

def cylinderSobolevJetCLM (s : Fin 3 → ℝ) (R : ℝ) :
    cylinderSobolevGraph s R →L[ℂ] FiniteCylinderJets R :=
  (ContinuousLinearMap.fst ℂ _ _).comp (cylinderSobolevGraph s R).subtypeL

lemma cylinderSobolevGraph_norm_bound (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R)
    (z : cylinderSobolevGraph s R) :
    ‖z‖≤ max 1 (Real.sqrt (cylinderTraceConstant s R))*‖cylinderSobolevJetCLM s R z‖ := by
  have hC := (cylinderTraceConstant_pos s hR).le
  have hL := (cylinderSobolevGraph_trace_bound s hR z).1
  have hT := (cylinderSobolevGraph_trace_bound s hR z).2
  have hs (a : ℝ) (ha : 0≤a) (h : a^2≤cylinderTraceConstant s R*‖z.val.1‖^2) :
      a≤Real.sqrt (cylinderTraceConstant s R)*‖z.val.1‖ := by
    apply (sq_le_sq₀ ha (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow,Real.sq_sqrt hC] using h
  have hB := mul_le_mul_of_nonneg_right (le_max_right 1 (Real.sqrt (cylinderTraceConstant s R)))
    (norm_nonneg z.val.1)
  change max ‖z.val.1‖ (max ‖z.val.2.1‖ ‖z.val.2.2‖)≤_
  apply max_le
  · exact (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))
  · exact max_le ((hs _ (norm_nonneg _) hL).trans hB) ((hs _ (norm_nonneg _) hT).trans hB)

lemma cylinderSobolevJet_antilipschitz (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R) :
    AntilipschitzWith ⟨max 1 (Real.sqrt (cylinderTraceConstant s R)),by positivity⟩
      (cylinderSobolevJetCLM s R) :=
  (cylinderSobolevJetCLM s R).antilipschitz_of_bound (cylinderSobolevGraph_norm_bound s hR)

lemma cylinderSobolevJet_mem_H1 (s : Fin 3 → ℝ) (R : ℝ) (z : cylinderSobolevGraph s R) :
    cylinderSobolevJetCLM s R z∈cylinderH1Space R := by
  let L : CylinderTraceAmbient s R →L[ℂ] FiniteCylinderJets R := ContinuousLinearMap.fst ℂ _ _
  let T := (cylinderH1Space R).comap L.toLinearMap
  have hT : IsClosed (T : Set (CylinderTraceAmbient s R)) :=
    (Submodule.isClosed_topologicalClosure _).preimage L.continuous
  have hr : LinearMap.range (cylinderPolynomialGraphL s R)≤T := by
    rintro _ ⟨p,rfl⟩
    exact Submodule.le_topologicalClosure _ ⟨p,rfl⟩
  exact Submodule.topologicalClosure_minimal _ hr hT z.property

theorem cylinderH1_unique_trace_graph (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R)
    (u : cylinderH1Space R) :
    ∃! z : cylinderSobolevGraph s R,cylinderSobolevJetCLM s R z=u.val := by
  have hc : IsClosed (LinearMap.range (cylinderSobolevJetCLM s R).toLinearMap :
      Set (FiniteCylinderJets R)) :=
    (cylinderSobolevJet_antilipschitz s hR).isClosed_range (cylinderSobolevJetCLM s R).uniformContinuous
  have hr : LinearMap.range (cylinderPolynomialJetL R)≤
      LinearMap.range (cylinderSobolevJetCLM s R).toLinearMap := by
    rintro _ ⟨p,rfl⟩
    exact ⟨⟨cylinderPolynomialGraphL s R p,Submodule.le_topologicalClosure _ ⟨p,rfl⟩⟩,rfl⟩
  obtain ⟨z,hz⟩ := Submodule.topologicalClosure_minimal _ hr hc u.property
  exact ⟨z,hz,fun y hy => (cylinderSobolevJet_antilipschitz s hR).injective (hy.trans hz.symm)⟩

end ScalarConductivity

end

end OAI
