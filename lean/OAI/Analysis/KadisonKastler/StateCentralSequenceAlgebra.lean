import OAI.Analysis.KadisonKastler.StateCommutatorAlgebra

namespace OAI

/-! # The C-star algebra of state-central bounded sequences

State commutator estimates provide addition, multiplication, adjoints and
norm closure directly, independently of the vector centrality criterion.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def StateAsymptoticallyCentral (ξ : H) (x : BoundedSequence (Algebra M)) : Prop :=
  Tendsto (fun n => ‖vectorStateCommutator ξ (x n)‖) atTop (𝓝 0)

theorem StateAsymptoticallyCentral.add {ξ : H} {x y : BoundedSequence (Algebra M)}
    (hx : StateAsymptoticallyCentral ξ x) (hy : StateAsymptoticallyCentral ξ y) :
    StateAsymptoticallyCentral ξ (x+y) := by
  change Tendsto (fun n => ‖vectorStateCommutator ξ (x n+y n)‖) atTop (𝓝 0)
  simp only [vectorStateCommutator_add]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)
  simpa only [add_zero] using Filter.Tendsto.add hx hy

theorem StateAsymptoticallyCentral.smul {ξ : H} {x : BoundedSequence (Algebra M)}
    (hx : StateAsymptoticallyCentral ξ x) (c : ℂ) : StateAsymptoticallyCentral ξ (c • x) := by
  change Tendsto (fun n => ‖vectorStateCommutator ξ (c • x n)‖) atTop (𝓝 0)
  simp only [vectorStateCommutator_smul,norm_smul]
  simpa only [mul_zero] using hx.const_mul ‖c‖

theorem StateAsymptoticallyCentral.star {ξ : H} {x : BoundedSequence (Algebra M)}
    (hx : StateAsymptoticallyCentral ξ x) : StateAsymptoticallyCentral ξ (star x) := by
  simpa only [StateAsymptoticallyCentral,BoundedContinuousFunction.star_apply,
    vectorStateCommutator_star_norm] using hx

theorem StateAsymptoticallyCentral.mul {ξ : H} {x y : BoundedSequence (Algebra M)}
    (hx : StateAsymptoticallyCentral ξ x) (hy : StateAsymptoticallyCentral ξ y) :
    StateAsymptoticallyCentral ξ (x*y) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (vectorStateCommutator_mul_norm_le ξ (x n) (y n)).trans
      (add_le_add
        (mul_le_mul_of_nonneg_left (y.norm_coe_le_norm n) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (x.norm_coe_le_norm n) (norm_nonneg _))))
  simpa only [zero_mul,mul_zero,add_zero] using (hx.mul_const ‖y‖).add (hy.const_mul ‖x‖)

theorem stateAsymptoticallyCentral_isClosed (ξ : H) :
    IsClosed {x : BoundedSequence (Algebra M) | StateAsymptoticallyCentral ξ x} := by
  apply isClosed_of_closure_subset
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C := 2*‖vectorFunctional (M := M) ξ‖
  have hC : 0 ≤ C := by positivity
  have hden : 0 < 2*(C+1) := by positivity
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx (ε/(2*(C+1))) (div_pos hε hden)
  have hnxy : ‖x-y‖ < ε/(2*(C+1)) := by simpa only [dist_eq_norm] using hxy
  filter_upwards [(Metric.tendsto_nhds.mp hy) (ε/2) (half_pos hε)] with n hn
  have hyn : ‖vectorStateCommutator ξ (y n)‖ < ε/2 := by
    simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hn
  have hsmall : C*‖x-y‖ < ε/2 := by
    have hm := (lt_div_iff₀ hden).mp hnxy
    nlinarith [norm_nonneg (x-y)]
  have he : vectorStateCommutator ξ (x n)=
      vectorStateCommutator ξ ((x-y) n)+vectorStateCommutator ξ (y n) := by
    change vectorStateCommutator ξ (x n)=
      vectorStateCommutator ξ (x n-y n)+vectorStateCommutator ξ (y n)
    rw [vectorStateCommutator_sub,sub_add_cancel]
  have hb : ‖vectorStateCommutator ξ ((x-y) n)‖ ≤ C*‖x-y‖ :=
    (vectorStateCommutator_operator_norm_le ξ _).trans
      (mul_le_mul_of_nonneg_left ((x-y).norm_coe_le_norm n) hC)
  have ht : ‖vectorStateCommutator ξ (x n)‖ < ε := by
    rw [he]
    exact (norm_add_le _ _).trans_lt (by linarith)
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using ht

def stateCentralSequenceAlgebra (ξ : H) : StarSubalgebra ℂ (BoundedSequence (Algebra M)) where
  carrier := {x | StateAsymptoticallyCentral ξ x}
  zero_mem' := by
    change Tendsto (fun _ : ℕ => ‖vectorStateCommutator ξ (0 : Algebra M)‖) atTop (𝓝 0)
    simpa only [vectorStateCommutator_zero,norm_zero] using tendsto_const_nhds
  one_mem' := by
    change Tendsto (fun _ : ℕ => ‖vectorStateCommutator ξ (1 : Algebra M)‖) atTop (𝓝 0)
    simpa only [vectorStateCommutator_one,norm_zero] using tendsto_const_nhds
  add_mem' := StateAsymptoticallyCentral.add
  mul_mem' := StateAsymptoticallyCentral.mul
  star_mem' := StateAsymptoticallyCentral.star
  algebraMap_mem' c := by
    change StateAsymptoticallyCentral ξ (algebraMap ℂ (BoundedSequence (Algebra M)) c)
    rw [Algebra.algebraMap_eq_smul_one]
    apply StateAsymptoticallyCentral.smul
    change Tendsto (fun _ : ℕ => ‖vectorStateCommutator ξ (1 : Algebra M)‖) atTop (𝓝 0)
    simpa only [vectorStateCommutator_one,norm_zero] using tendsto_const_nhds

instance stateCentralSequenceAlgebra_complete (ξ : H) :
    CompleteSpace (stateCentralSequenceAlgebra (M := M) ξ) :=
  (stateAsymptoticallyCentral_isClosed (M := M) ξ).completeSpace_coe

instance stateCentralSequenceAlgebra_cstar (ξ : H) :
    CStarAlgebra (stateCentralSequenceAlgebra (M := M) ξ) where

end

end KadisonKastler

end OAI
