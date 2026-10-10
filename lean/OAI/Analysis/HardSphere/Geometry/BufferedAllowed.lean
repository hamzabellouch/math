import Mathlib
import OAI.Analysis.HardSphere.Geometry.NormSqIntegral
import OAI.Analysis.HardSphere.Comparison.KilledLaplace
import OAI.Analysis.HardSphere.FormDomain.DirichletScalarInjective

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
open MeasureTheory Set Filter
open scoped Topology

lemma killedLaplace_innerRadius_tendsto (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    Tendsto (fun n ↦ killedLaplace N L (innerRadius a n) f) atTop (𝓝 (killedLaplace N L a f)) := by
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ ↦ Real.exp (-t)*‖f‖)
  · intro n
    exact (laplaceIntegrand_integrable (killedTransition N L (innerRadius a n))
      (killedTransition_clamped_continuous N L (innerRadius a n))
      (fun t _ ↦ killedTransition_apply_contraction N L (innerRadius a n) t) f 0).aestronglyMeasurable
  · exact (integrableOn_exp_neg_Ioi 0).mul_const ‖f‖
  · intro n
    apply Eventually.of_forall
    intro t
    rw [laplaceIntegrand_eq_complex]
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (killedTransition_apply_contraction N L (innerRadius a n) _ f)
      (Real.exp_nonneg _)
  · apply Eventually.of_forall
    intro t
    simp_rw [laplaceIntegrand_eq_complex]
    exact tendsto_const_nhds.smul (killedTransition_innerRadius_tendsto N L a (max 0 t) f)

def bufferedAllowed (N : ℕ) (L : Length) (b : ℝ) : Set (Configuration N L) :=
  {X | ∀ i j : Fin N, i<j → b≤torusDistance L (X i) (X j)}

lemma bufferedAllowed_closed (N : ℕ) (L : Length) (b : ℝ) : IsClosed (bufferedAllowed N L b) := by
  let P := {p : Fin N × Fin N // p.1 < p.2}
  have he : bufferedAllowed N L b = ⋂ p : P,
      {X : Configuration N L | b≤torusDistance L (X p.1.1) (X p.1.2)} := by
    ext X
    simp only [bufferedAllowed,mem_ofPred_eq,mem_iInter]
    exact ⟨fun h p ↦ h _ _ p.2,fun h i j hij ↦ h ⟨(i,j),hij⟩⟩
  rw [he]
  apply isClosed_iInter
  intro p
  have hc : Continuous (fun X : Configuration N L ↦ torusDistance L (X p.1.1) (X p.1.2)) := by
    unfold torusDistance
    fun_prop
  exact isClosed_le continuous_const hc

lemma allowed_subset_buffered (N : ℕ) (L : Length) (b : ℝ) :
    allowed N L b⊆bufferedAllowed N L b := fun _ h i j hij ↦ (h i j hij).le

lemma bufferedAllowed_subset (N : ℕ) (L : Length) {a b : ℝ} (hab : a<b) :
    bufferedAllowed N L b⊆allowed N L a := fun _ h i j hij ↦ hab.trans_le (h i j hij)

lemma killedLaplace_buffered_graph (N : ℕ) (L : Length) {a b : ℝ} (hab : a<b) (f : ScalarL2 N L) :
    ∃ v : hilbertDomain N L a, scalarEmbedding N L a v=killedLaplace N L b f ∧
      ‖v‖^2≤(1+4*Real.exp 1)*‖f‖^2 := by
  obtain ⟨u,hu,hub⟩ := killedLaplace_free_graph N L b f
  have hj : hilbertJetEquiv N L (u : HilbertJet N L)∈dirichletDomain N L a := by
    apply dirichletDomain_of_closed_support (isOpen_allowed N L a)
      (bufferedAllowed_closed N L b) (bufferedAllowed_subset N L hab) u.property
    have he : (hilbertJetEquiv N L (u : HilbertJet N L)).1=killedLaplace N L b f := hu
    change ∀ᵐ X ∂(volume : Measure (Configuration N L)), X∉bufferedAllowed N L b →
      (hilbertJetEquiv N L (u : HilbertJet N L)).1 X=0
    rw [he]
    filter_upwards [killedLaplace_support N L b f] with X hX
    intro hn
    exact hX (fun ha ↦ hn (allowed_subset_buffered N L b ha))
  let v : hilbertDomain N L a := ⟨u.val,hj⟩
  refine ⟨v,hu,?_⟩
  have hn := killedLaplace_norm_le N L b f
  change ‖u‖^2≤_
  nlinarith [norm_nonneg (killedLaplace N L b f),norm_nonneg f]

lemma killedLaplace_graph (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    ∃ v : hilbertDomain N L a, scalarEmbedding N L a v=killedLaplace N L a f ∧
      ‖v‖^2≤(1+4*Real.exp 1)*‖f‖^2 := by
  choose v hv hb using fun n ↦ killedLaplace_buffered_graph N L (innerRadius_gt a n) f
  let C := (1+4*Real.exp 1)*‖f‖^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hvb : ∀ n, ‖v n‖≤Real.sqrt C := by
    intro n
    exact (Real.le_sqrt (norm_nonneg _) hC).mpr (hb n)
  have ht : Tendsto (fun n ↦ scalarEmbedding N L a (v n)) atTop (𝓝 (killedLaplace N L a f)) := by
    simp_rw [hv]
    exact killedLaplace_innerRadius_tendsto N L a f
  obtain ⟨u,hub,hu⟩ := exists_bounded_lift_of_tendsto (scalarEmbedding N L a) v hvb ht
  refine ⟨u,hu,?_⟩
  calc
    ‖u‖^2 ≤ (Real.sqrt C)^2 := sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _) |>.mpr hub
    _ = C := Real.sq_sqrt hC

end HardSphere

open ProbabilityTheory

end

end OAI
