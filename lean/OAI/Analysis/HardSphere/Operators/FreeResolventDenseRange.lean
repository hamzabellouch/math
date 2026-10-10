import Mathlib
import OAI.Analysis.HardSphere.Fourier.CharacterDerivativeFactor
import OAI.Analysis.HardSphere.Geometry.GraphLiftHeatBound

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open ContinuousLinearMap Filter
open scoped Topology

lemma freeResolvent_denseRange (N : ℕ) (L : Length) (a : ℝ) (ha : a<0) :
    DenseRange (formResolvent N L a) := by
  change Dense (Set.range (formResolvent N L a))
  change Dense ((formResolvent N L a).range : Set (ScalarL2 N L))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  rw [← characterL2_span_dense N L]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨k,rfl⟩
  refine ⟨(1+(fourierEnergy N L k:ℂ)) • characterL2 N L k,?_⟩
  change formResolvent N L a ((1+(fourierEnergy N L k:ℂ)) • characterL2 N L k)=_
  rw [map_smul,character_resolvent N L a ha k,smul_smul,mul_inv_cancel₀,one_smul]
  have hreal : (1:ℝ)+fourierEnergy N L k≠0 := ne_of_gt (by linarith [fourierEnergy_nonneg N L k])
  exact_mod_cast hreal

lemma free_graph_lift_of_heat_bound (N : ℕ) (L : Length) (a : ℝ) (ha : a<0)
    (u : ScalarL2 N L) (C : ℝ)
    (hb : ∀ n : ℕ, (1/((n:ℝ)+1))⁻¹ *
      (‖u‖^2-(inner ℂ u (freeTransition N L (1/((n:ℝ)+1)) u)).re)≤C) :
    ∃ v : hilbertDomain N L a, scalarEmbedding N L a v=u ∧ ‖v‖^2≤‖u‖^2+C := by
  rcases subsingleton_or_nontrivial (ScalarL2 N L) with h | h
  · have := h
    refine ⟨0,Subsingleton.elim _ _,?_⟩
    have hz : u=0 := Subsingleton.elim _ _
    simpa [hz] using hb 0
  have := h
  apply exists_graph_lift_of_heat_bound (scalarEmbedding N L a) (scalarEmbedding_norm_le N L a)
    (freeResolvent_denseRange N L a ha) u C
  intro n
  have ht : 0<1/((n:ℝ)+1) := by positivity
  simpa only [formHeat,formResolvent] using
    (show (1/((n:ℝ)+1))⁻¹ * (‖u‖^2-(inner ℂ u
      (formHeat N L a (1/((n:ℝ)+1)) u)).re)≤C by
        rw [← freeTransition_eq_formHeat N L a ha ht]
        exact hb n)

end HardSphere

end

end OAI
