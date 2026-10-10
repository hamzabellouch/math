import OAI.Analysis.Cotype.TypeUniformL1
import OAI.Analysis.Cotype.CotypeAmplification

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem quadraticTypeBound_l2Amplification {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] {n : ℕ} {A : ℝ} (h : QuadraticTypeBound X n A) :
    QuadraticTypeBound (PiLp 2 (fun _ : Ω => X)) n A := by
  intro x
  rw [cubeL2_piLp_sq]
  simp_rw [rademacherSum_piLp_apply, PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => h (fun i => x i a))

theorem uniform_quadratic_gap_l2Amplification (h : BConvex X) :
    ∃ n : ℕ, 0 < n ∧ ∃ A : ℝ, 0 ≤ A ∧ A < n ∧
      ∀ d : ℕ, QuadraticTypeBound (PiLp 2 (fun _ : Fin d => X)) n A := by
  obtain ⟨n,hn,A,hA,hAn,h⟩ := fixed_quadratic_improvement_of_bConvex h
  exact ⟨n,hn,A,hA,hAn,fun _ => quadraticTypeBound_l2Amplification h⟩

theorem uniform_normalized_type_l2Amplification [Nontrivial X]
    (h : NontrivialType X) :
    ∃ p D : ℝ, 1 < p ∧ p ≤ 2 ∧ 0 ≤ D ∧ ∀ (d N : ℕ)
      (x : Fin N → PiLp 2 (fun _ : Fin d => X)),
      (∑ i, ‖x i‖^p) ≤ 1 →
      cubeL2 (PiLp 2 (fun _ : Fin d => X))
        (rademacherSum (PiLp 2 (fun _ : Fin d => X)) x) ≤ D := by
  obtain ⟨n,hn,A,hA,hAn,hgap⟩ :=
    fixed_quadratic_improvement_of_bConvex (nontrivialType_iff_bConvex.mp h)
  have hA1 := QuadraticTypeBound.one_le hn hgap
  have hn1 : 1 < n := by exact_mod_cast (lt_of_le_of_lt hA1 hAn)
  obtain ⟨p,r,hp,hp2,hr,hrp,_,hq⟩ := exists_type_extrapolation_parameters hn1 hA hAn
  refine ⟨p,Real.sqrt (A*n)*(1-Real.sqrt (A*n)*r⁻¹)⁻¹,hp,hp2,by positivity,?_⟩
  intro d N x hx
  exact normalized_type_bound_of_quadratic_powers hn hA (by linarith) hr hrp hq
    (quadraticTypeBound_pow hA (quadraticTypeBound_l2Amplification hgap)) N x hx

end Cotype

end

end OAI
