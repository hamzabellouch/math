import OAI.Analysis.Hyperinvariant.Specification
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Separation.Hausdorff

namespace OAI

namespace Hyperinvariant
open Filter
open scoped Topology
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Membership is commutation in all bounded operators on H. -/
theorem mem_commutant_iff (T A : H →L[ℂ] H) :
    A ∈ commutant T ↔ A * T = T * A := by
  simp only [commutant, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact eq_comm

/-- The ordinary commutant is closed for the pointwise-norm strong-operator topology. -/
theorem commutant_isClosed_strong [CompleteSpace H] (T : H →L[ℂ] H) :
    @IsClosed (H →L[ℂ] H) strongOperatorTopology (commutant T : Set (H →L[ℂ] H)) := by
  let : TopologicalSpace (H →L[ℂ] H) := strongOperatorTopology
  have heval : ∀ x : H, Continuous (fun A : H →L[ℂ] H => A x) := by
    intro x
    exact (continuous_apply x).comp continuous_induced_dom
  have hset : (commutant T : Set (H →L[ℂ] H)) =
      ⋂ x : H, {A : H →L[ℂ] H | A (T x) = T (A x)} := by
    ext A
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, mem_commutant_iff]
    constructor
    · intro h x
      exact congrArg (fun B : H →L[ℂ] H => B x) h
    · intro h
      ext x
      exact h x
  rw [hset]
  exact isClosed_iInter (fun x => isClosed_eq (heval (T x)) (T.continuous.comp (heval x)))

/-- If an operator commutes with every bounded operator, it is scalar.
The center is scalar because the continuous dual separates points. -/
theorem scalar_of_commutant_top [CompleteSpace H] (T : H →L[ℂ] H)
    (h : commutant T = ⊤) :
    ∃ c : ℂ, algebraMap ℂ (H →L[ℂ] H) c = T := by
  have hc : T ∈ Subalgebra.center ℂ (H →L[ℂ] H) := by
    rw [Subalgebra.mem_center_iff]
    intro A
    apply (mem_commutant_iff T A).mp
    rw [h]
    trivial
  rw [Algebra.IsCentral.center_eq_bot] at hc
  exact Algebra.mem_bot.mp hc

/-- Nonzero norm-quasinilpotence excludes scalar bounded operators. This
uses the actual root-norm limit from the statement, not a spectral surrogate. -/
theorem commutant_ne_top_of_nonzero_quasinilpotent [CompleteSpace H] [Nontrivial H]
    (T : H →L[ℂ] H) (hT : T ≠ 0)
    (hlim : Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    commutant T ≠ ⊤ := by
  intro htop
  obtain ⟨c, hc⟩ := scalar_of_commutant_top T htop
  have hroot (n : ℕ) (hn : n ≠ 0) : ‖T ^ n‖ ^ (1 / (n : ℝ)) = ‖c‖ := by
    rw [← hc, Algebra.algebraMap_eq_smul_one, smul_pow, one_pow,
      norm_smul, norm_pow, norm_one, mul_one, one_div]
    exact Real.pow_rpow_inv_natCast (norm_nonneg c) hn
  have hevent : (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) =ᶠ[atTop]
      (fun _ : ℕ => ‖c‖) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact hroot n (Nat.ne_of_gt hn)
  have hconst : Tendsto (fun _ : ℕ => ‖c‖) atTop (𝓝 0) := hlim.congr' hevent
  have hc0 : ‖c‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  apply hT
  rw [← hc, norm_eq_zero.mp hc0, map_zero]

variable [CompleteSpace H]

/-- Adds the two generic commutant conclusions to a genuine main witness. -/
theorem fullClaim_of_mainClaim [Nontrivial H] (h : MainClaim (H := H)) :
    FullClaim (H := H) := by
  obtain ⟨T, hT, hlim, htrans⟩ := h
  exact ⟨T, hT, hlim, htrans,
    commutant_ne_top_of_nonzero_quasinilpotent T hT hlim,
    commutant_isClosed_strong T⟩

end Hyperinvariant

end OAI
