import OAI.Analysis.KadisonKastler.StrongReferenceTests
import OAI.Analysis.KadisonKastler.ContractiveWeakLimit

namespace OAI

/-! # A bounded algebra sequence converging on a separating vector

Weak compactness supplies an operator in the algebra. Completeness on
the separating reference vector and the dense commutant orbit identify
the strong limit on the whole original Hilbert space.
-/

namespace KadisonKastler

open Generator.Tracial Filter UltrapowerBridge
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_algebra_strong_limit_of_reference_cauchy (ξ : H)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (a : ℕ → Algebra M) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (hc : CauchySeq (fun n => (a n).val ξ)) :
    ∃ b : Algebra M, ‖b‖ ≤ C ∧
      ∀ η : H, Tendsto (fun n => (a n).val η) atTop (𝓝 (b.val η)) := by
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨T,hT,ht⟩ := exists_weak_operator_ultralimit ω (fun n => (a n).val) C hC ha
  have hTM : T ∈ M := weak_operator_limit_mem M a T ht
  let b : Algebra M := ⟨T,hTM⟩
  obtain ⟨ζ,hζ⟩ := cauchy_map_iff_exists_tendsto.mp hc
  have he : T ξ=ζ := by
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht ξ η)
    exact (tendsto_const_nhds.inner hζ).mono_left (Ultrafilter.of_le atTop)
  have href : Tendsto (fun n => (a n-b).val ξ) atTop (𝓝 0) := by
    change Tendsto (fun n => (a n).val ξ-T ξ) atTop (𝓝 0)
    rw [he]
    simpa only [sub_self] using hζ.sub_const ζ
  refine ⟨b,hT,fun η => ?_⟩
  have hall := algebra_strong_tendsto_of_reference ξ
    (commutant_cyclic_of_separating_reference ξ hsep) (fun n => a n-b) (2*C)
    (by positivity) (fun n => (norm_sub_le _ _).trans
      (by have := ha n; change ‖a n‖+‖T‖ ≤ 2*C; linarith)) href η
  change Tendsto (fun n => (a n).val η-b.val η) atTop (𝓝 0) at hall
  exact tendsto_sub_nhds_zero_iff.mp hall

end

end KadisonKastler

end OAI
