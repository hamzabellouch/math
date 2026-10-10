import OAI.NumberTheory.Jacobsthal.Primes.DirichletZeroFree

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

theorem uniform_normalized_zero_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ (t : ℝ) (S : Finset ℂ),
      (∀ rho, rho ∈ S ↔ ‖rho‖ ≤ 19/20 ∧ normalizedDirichlet chi t rho = 0) →
      ∑ rho ∈ S, ((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℝ) ≤
        C*modulusHeight q t := by
  classical
  let D : ℝ := Real.log ((39/40:ℝ)/(19/20))
  have hD : 0 < D := Real.log_pos (by norm_num)
  have hZ := one_le_absoluteZetaTwo
  have hlog : 0 ≤ Real.log (4*absoluteZetaTwo) := Real.log_nonneg (by linarith)
  refine ⟨(Real.log (4*absoluteZetaTwo)+1)/D, div_pos (by linarith) hD, ?_⟩
  intro q _ chi hchi t S hS
  let f := normalizedDirichlet chi t
  have he : _root_.Erdos970.zerosetKfR (19/20) (by norm_num) f = (S:Set ℂ) := by
    ext rho
    simp only [_root_.Erdos970.zerosetKfR,Set.mem_ofPred_eq,Metric.mem_closedBall,dist_zero_right,Finset.mem_coe]
    exact (hS rho).symm
  have hf : (_root_.Erdos970.zerosetKfR (19/20) (by norm_num) f).Finite := by rw [he]; exact S.finite_toSet
  have hfin : hf.toFinset = S := by
    ext rho
    rw [Set.Finite.mem_toFinset,he]
    rfl
  have h0 : f 0 = 1 := normalizedDirichlet_zero chi t
  have hn : f 0 ≠ 0 := by rw [h0]; norm_num
  have hj := _root_.Erdos970.jensen_sum_bound_strict (dirichletDiskEnvelope q t) (39/40) (19/20)
    (dirichletDiskEnvelope_gt_one q t) (by norm_num) (by norm_num) (by norm_num)
    f (fun w _ => normalizedDirichlet_analytic chi hchi t w) hn h0 hf
    (fun w hw => normalizedDirichlet_bound chi hchi t (hw.trans (by norm_num)))
  rw [hfin] at hj
  calc
    _ ≤ Real.log (dirichletDiskEnvelope q t)/D := hj
    _ ≤ ((Real.log (4*absoluteZetaTwo)+1)*modulusHeight q t)/D :=
      div_le_div_of_nonneg_right (log_dirichletDiskEnvelope_bound q t) hD.le
    _ = _ := by ring

theorem uniform_local_zero_estimates :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ t : ℝ, ∃ S : Finset ℂ,
        (∀ rho, rho ∈ S ↔ ‖rho‖ ≤ 19/20 ∧
          DirichletCharacter.LFunction chi (dirichletDiskPoint t rho) = 0) ∧
        (∑ rho ∈ S, ((analyticOrderAt (normalizedDirichlet chi t) rho).toNat:ℝ) ≤ C*modulusHeight q t) ∧
        ∀ w : ℂ, ‖w‖ ≤ 17/20 →
          DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0 →
          ‖(5/2:ℂ)*(deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
            DirichletCharacter.LFunction chi (dirichletDiskPoint t w)) -
            ∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat/(w-rho)‖ ≤
            C*modulusHeight q t := by
  classical
  obtain ⟨C0,hC0,hlocal⟩ := uniform_dirichlet_local_log_derivative
  obtain ⟨C1,hC1,hmass⟩ := uniform_normalized_zero_mass
  refine ⟨max C0 C1,lt_of_lt_of_le hC0 (le_max_left _ _),?_⟩
  intro q _ chi hchi t
  obtain ⟨S,hS,_,hb⟩ := hlocal q chi hchi t
  have hn := LFunction_ne_zero_right chi (s := dirichletCenter t) (by simp)
  have hzeros (rho:ℂ) : normalizedDirichlet chi t rho = 0 ↔
      DirichletCharacter.LFunction chi (dirichletDiskPoint t rho) = 0 := by
    unfold normalizedDirichlet
    exact div_eq_zero_iff.trans (or_iff_left hn)
  have hSn : ∀ rho, rho ∈ S ↔ ‖rho‖ ≤ 19/20 ∧ normalizedDirichlet chi t rho = 0 := by
    intro rho
    rw [hzeros]
    exact hS rho
  have hH : 0 ≤ modulusHeight q t := zero_le_one.trans (modulusHeight_ge_one q t)
  refine ⟨S,hS,?_,?_⟩
  · exact (hmass q chi hchi t S hSn).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hH)
  · intro w hw hne
    exact (hb w hw hne).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hH)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
