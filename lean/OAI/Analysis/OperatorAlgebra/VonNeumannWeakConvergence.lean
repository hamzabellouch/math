import OAI.Analysis.OperatorAlgebra.ScalarKernelPairing

namespace OAI

/-! Weak operator limits suffice for removing the two convolution
regularizers from the modular fixed-point reconstruction. -/

noncomputable section
open Filter
open scoped Topology InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vonNeumann_mem_of_matrixCoefficient_limit (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) (F : ℕ → H →L[ℂ] H) (hF : ∀ n, F n ∈ M)
    (hlim : ∀ x y, Tendsto (fun n => inner ℂ (F n x) y) atTop (𝓝 (inner ℂ (T x) y))) :
    T ∈ M := by
  rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  have hl := hlim x (b.adjoint y)
  have hr := hlim (b x) y
  have he (n : ℕ) : inner ℂ (F n x) (b.adjoint y) = inner ℂ (F n (b x)) y := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp hb (F n) (hF n)
    have hc' := congrArg (fun R : H →L[ℂ] H => R x) hc.symm
    change b (F n x) = F n (b x) at hc'
    rw [hc']
  have hv := tendsto_nhds_unique (hl.congr he) hr
  change inner ℂ (b (T x)) y = inner ℂ (T (b x)) y
  rw [← ContinuousLinearMap.adjoint_inner_right]
  exact hv

lemma sandwich_matrixCoefficient_limit (C : ℕ → H →L[ℂ] H)
    (hC : ∀ x, Tendsto (fun n => C n x) atTop (𝓝 x)) (T : H →L[ℂ] H) (x y : H) :
    Tendsto (fun n => inner ℂ ((C n).adjoint (T (C n x))) y) atTop (𝓝 (inner ℂ (T x) y)) := by
  have h := (T.continuous.continuousAt.tendsto.comp (hC x)).inner (𝕜 := ℂ) (hC y)
  simpa only [ContinuousLinearMap.adjoint_inner_left, Function.comp_apply] using h

theorem vonNeumann_mem_of_sandwiches (M : VonNeumannAlgebra H)
    (C : ℕ → H →L[ℂ] H) (hC : ∀ x, Tendsto (fun n => C n x) atTop (𝓝 x))
    (T : H →L[ℂ] H) (hT : ∀ n, (C n).adjoint * T * C n ∈ M) : T ∈ M := by
  apply vonNeumann_mem_of_matrixCoefficient_limit M T
    (fun n => (C n).adjoint * T * C n) hT
  intro x y
  exact sandwich_matrixCoefficient_limit C hC T x y

end WeakPureInfiniteness

end

end OAI
