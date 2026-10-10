import Mathlib
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison.FiniteStrongTest

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def evaluation (M : VonNeumannAlgebra H) (x : H) : M →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun a => (a : H →L[ℂ] H) x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    ‖x‖ (fun a => by
      change ‖(a : H →L[ℂ] H) x‖≤‖x‖*‖(a:H →L[ℂ] H)‖
      rw [mul_comm]
      exact (a : H →L[ℂ] H).le_opNorm x)

def testMap (M : VonNeumannAlgebra H) (v : ℕ → H) (N : ℕ) : M →L[ℂ] PiLp 2 (fun _ : Fin N => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin N => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j : Fin N => evaluation M (v j)))

@[simp] lemma testMap_apply (M : VonNeumannAlgebra H) (v : ℕ → H) (N : ℕ) (a : M)
    (j : Fin N) : testMap M v N a j=(a : H →L[ℂ] H) (v j) := rfl

lemma strong_null_of_dense_tests (M : VonNeumannAlgebra H) (v : ℕ → H) (hv : DenseRange v)
    (T : ℕ → M) (hT : ∀ n,‖T n‖≤1)
    (ht : ∀ n,∀ j : Fin n,‖(T n : H →L[ℂ] H) (v j)‖≤1/((n:ℝ)+1)) :
    ∀ x,Tendsto (fun n => (T n : H →L[ℂ] H) x) atTop (𝓝 0) := by
  intro x
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨j,hj⟩ := hv.exists_dist_lt x (by positivity : (0:ℝ)<ε/3)
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const (by positivity : (0:ℝ)<ε/3))
  refine ⟨max N (j+1),?_⟩
  intro n hn
  have hnN : N≤n := le_trans (le_max_left _ _) hn
  have hjn : j<n := by omega
  have he : (T n : H →L[ℂ] H) x=(T n : H →L[ℂ] H) (x-v j)+(T n : H →L[ℂ] H) (v j) := by simp
  have hb : ‖(T n : H →L[ℂ] H) (x-v j)‖≤‖x-v j‖ := by
    calc
      _ ≤ ‖T n‖*‖x-v j‖ := (T n : H →L[ℂ] H).le_opNorm _
      _ ≤ 1*‖x-v j‖ := mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _)
      _ = _ := one_mul _
  have hd : ‖x-v j‖<ε/3 := by simpa only [dist_eq_norm] using hj
  have hb2 := ht n ⟨j,hjn⟩
  have hh : ‖(T n : H →L[ℂ] H) x‖<ε := by
    rw [he]
    have hh := norm_add_le ((T n : H →L[ℂ] H) (x-v j)) ((T n : H →L[ℂ] H) (v j))
    have hsmall := hN n hnN
    change ‖(T n : H →L[ℂ] H) (v j)‖≤1/((n:ℝ)+1) at hb2
    linarith
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_norm] using hh

theorem exists_test (M : VonNeumannAlgebra H) (v : ℕ → H) (hv : DenseRange v)
    (f : StrongDual ℂ M)
    (hf : ∀ T : ℕ → M,(∀ n,‖T n‖≤1) →
      (∀ x,Tendsto (fun n => (T n : H →L[ℂ] H) x) atTop (𝓝 0)) →
      Tendsto (fun n => f (T n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,∀ a : M,‖a‖≤1 → (∀ j : Fin N,‖(a : H →L[ℂ] H) (v j)‖≤1/((N:ℝ)+1)) →
      ‖f a‖≤ε := by
  by_contra h
  push Not at h
  choose T hT ht hlarge using h
  have hlim := (hf T hT (strong_null_of_dense_tests M v hv T hT ht)).norm
  have hsmall : ∀ᶠ n in atTop,‖f (T n)‖<ε := by
    apply hlim.eventually_lt_const
    simpa only [norm_zero] using hε
  obtain ⟨n,hn⟩ := hsmall.exists
  exact (hlarge n).not_ge hn.le

end Kadison.FiniteStrongTest

end

end
end

end OAI
