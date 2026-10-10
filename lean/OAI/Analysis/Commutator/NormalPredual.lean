import Mathlib
import OAI.Analysis.Commutator.CoefficientForm2
import OAI.Analysis.Commutator.FiniteStrongTest
import OAI.Analysis.Commutator.FiniteTestHahnBanach

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped Topology InnerProductSpace

namespace Kadison.NormalPredual

open FiniteStrongTest

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coefficient (M : VonNeumannAlgebra H) (v : ℕ → H) (N : ℕ)
    (y : PiLp 2 (fun _ : Fin N => H)) : StrongDual ℂ M :=
  (innerSL ℂ y).comp (testMap M v N)

def finiteTests (M : VonNeumannAlgebra H) (v : ℕ → H) : Set (StrongDual ℂ M) :=
  ⋃ N : ℕ,Set.range (coefficient M v N)

lemma finiteTests_separable [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (v : ℕ → H) : TopologicalSpace.IsSeparable (finiteTests M v) := by
  apply TopologicalSpace.IsSeparable.iUnion
  intro N
  apply TopologicalSpace.isSeparable_range
  exact (innerSL ℂ).continuous.clm_comp_const (testMap M v N)

theorem mem_closure_of_strong_null (M : VonNeumannAlgebra H) (v : ℕ → H)
    (hv : DenseRange v) (f : StrongDual ℂ M)
    (hf : ∀ T : ℕ → M,(∀ n,‖T n‖≤1) →
      (∀ x,Tendsto (fun n => (T n : H →L[ℂ] H) x) atTop (𝓝 0)) →
      Tendsto (fun n => f (T n)) atTop (𝓝 0)) :
    f∈closure (finiteTests M v) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_test M v hv f hf (ε/2) (by positivity)
  obtain ⟨ψ,hψ⟩ := FiniteTestHahnBanach.exists_approx_comp f (testMap M v N)
    (by positivity : (0:ℝ)<ε/2) (by positivity : (0:ℝ)<1/((N:ℝ)+1)) (by
      intro a ha htest
      apply hN a ha
      intro j
      exact (PiLp.norm_apply_le (testMap M v N a) j).trans htest)
  let y := (InnerProductSpace.toDual ℂ (PiLp 2 (fun _ : Fin N => H))).symm ψ
  have he : coefficient M v N y=ψ.comp (testMap M v N) := by
    apply ContinuousLinearMap.ext
    intro a
    change inner ℂ ((InnerProductSpace.toDual ℂ (PiLp 2 (fun _ : Fin N => H))).symm ψ)
      (testMap M v N a)=ψ (testMap M v N a)
    exact InnerProductSpace.toDual_symm_apply
  refine ⟨coefficient M v N y,Set.mem_iUnion.mpr ⟨N,Set.mem_range_self y⟩,?_⟩
  rw [he,dist_eq_norm]
  exact hψ.trans_lt (by linarith)

def BoundedWOTContinuous (M : VonNeumannAlgebra H) (f : StrongDual ℂ M) : Prop :=
  ∀ C : ℝ,Continuous (fun a : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} =>
    f ⟨a.val.toCLM,a.property.1⟩)

lemma coefficient_normal (M : VonNeumannAlgebra H) (v : ℕ → H) (N : ℕ)
    (y : PiLp 2 (fun _ : Fin N => H)) : BoundedWOTContinuous M (coefficient M v N y) := by
  intro C
  change Continuous (fun a : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} =>
    inner ℂ y (testMap M v N ⟨a.val.toCLM,a.property.1⟩))
  simp_rw [PiLp.inner_apply,testMap_apply]
  apply continuous_finsetSum
  intro j _
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val (v j) (y j)

theorem normal_of_mem_closure (M : VonNeumannAlgebra H) (v : ℕ → H)
    {f : StrongDual ℂ M} (hf : f∈closure (finiteTests M v)) : BoundedWOTContinuous M f := by
  obtain ⟨g,hg,hlim⟩ := mem_closure_iff_seq_limit.mp hf
  intro C
  let D := {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C}
  let a (T : D) : M := ⟨T.val.toCLM,T.property.1⟩
  have hn : Tendsto (fun n => ‖g n-f‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hlim.sub (tendsto_const_nhds (x:=f))).norm
  have hu : TendstoUniformly (fun n (T:D) => g n (a T)) (fun T => f (a T)) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hev := hn.eventually_lt_const (by positivity : (0:ℝ)<ε/(|C|+1))
    filter_upwards [hev] with n hn
    intro T
    have ha : ‖a T‖≤|C|+1 := (show ‖a T‖≤C from T.property.2).trans
      (by linarith [le_abs_self C])
    have hb : ‖(g n-f) (a T)‖≤‖g n-f‖*(|C|+1) :=
      ((g n-f).le_opNorm (a T)).trans (mul_le_mul_of_nonneg_left ha (norm_nonneg _))
    have hh : ‖g n-f‖*(|C|+1)<ε := (lt_div_iff₀ (by positivity : (0:ℝ)< |C|+1)).mp hn
    rw [dist_eq_norm,norm_sub_rev]
    exact hb.trans_lt hh
  apply hu.continuous
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨N,y,hy⟩ := Set.mem_iUnion.mp (hg n)
  rw [←hy]
  exact coefficient_normal M v N y C

end Kadison.NormalPredual

end

end
end

end OAI
