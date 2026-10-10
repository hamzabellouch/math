import OAI.GroupTheory.PolycyclicRecognition.Geometry.RayTangentContraction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryLimits

namespace OAI

/-! # Compact sets collapse along a negative quotient ray -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)

/-- The ray contraction holds for an arbitrary sequence of points in a
fixed compact set. This is the compact-shadow limit needed for the inverse
boundary identity. -/
theorem ray_compact_sequence_tendsto_one
    (α : H →ₗ[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
    (Exp : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExp : IsGroupExponential Exp) (hbij : Function.Bijective Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchart : ∀ v, chart v = Exp v)
    (v : H) (hv : α v < 0) (K : Set Q.carrier) (hK : IsCompact K)
    (q : ℕ → Q.carrier) (hq : ∀ n, q n ∈ K) :
    Tendsto (fun n : ℕ => exponentialConjugate Q.equiv Exp hbij
      (M.coneAdjointAutomorphism T (positiveWeightRay α) (positiveWeightRay_add α)
        ((n : ℝ) • v)) (q n)) atTop (𝓝 (1 : Q.carrier)) := by
  obtain ⟨b, p, rate, hrate, hc⟩ := M.exists_ray_tangent_compact_contraction T α Q Exp hbij chart hchart
  obtain ⟨A, hA, hb⟩ := hc K hK
  let C := ‖(finBasis ℝ H).equivFun v‖
  let r := -(rate * α v)
  have hr : 0 < r := neg_pos.mpr (mul_neg_of_pos_of_neg hrate hv)
  let z := fun n : ℕ => exponentialConjugate Q.equiv Exp hbij
    (M.coneAdjointAutomorphism T (positiveWeightRay α) (positiveWeightRay_add α)
      ((n : ℝ) • v)) (q n)
  have hbound (n : ℕ) : ‖b.equivFun (chart.symm (z n))‖ ≤
      (A * (1 + C) ^ p) * (1 + (n : ℝ)) ^ p * Real.exp (-r * n) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnα : α ((n : ℝ) • v) ≤ 0 := by
      rw [map_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hn hv.le
    have hh := hb ((n : ℝ) • v) hnα (q n) (hq n)
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hn,
      map_smul, smul_eq_mul] at hh
    have hp : (1 + (n : ℝ) * C) ^ p ≤ (1 + C) ^ p * (1 + (n : ℝ)) ^ p := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have hC : 0 ≤ C := norm_nonneg _
      nlinarith
    calc
      _ ≤ A * (1 + (n : ℝ) * C) ^ p * Real.exp (rate * ((n : ℝ) * α v)) := hh
      _ ≤ A * ((1 + C) ^ p * (1 + (n : ℝ)) ^ p) * Real.exp (rate * ((n : ℝ) * α v)) := by gcongr
      _ = _ := by
        rw [show rate * ((n : ℝ) * α v) = -r * n by dsimp [r]; ring]; ring
  have hnorm : Tendsto (fun n => ‖b.equivFun (chart.symm (z n))‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hbound
      ((summable_polynomial_exp_decay (A * (1 + C) ^ p) p hr).tendsto_atTop_zero)
  have hz : Tendsto (fun n => b.equivFun (chart.symm (z n))) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hh := (chart.continuous.comp b.equivFun.symm.toContinuousLinearEquiv.continuous).tendsto 0 |>.comp hz
  have he : chart 0 = (1 : Q.carrier) := (hchart 0).trans hExp.map_zero
  simpa only [Function.comp_def, LinearEquiv.coe_toContinuousLinearEquiv', b.equivFun.symm_apply_apply,
    chart.apply_symm_apply, map_zero, he] using hh

/-- Membership in every translated contracting compact shadow determines
the boundary point uniquely. This is the final limit step in the inverse
boundary-map argument. -/
theorem eq_of_mem_all_ray_compact_shadows
    (α : H →ₗ[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay α)))
    (Exp : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExp : IsGroupExponential Exp) (hbij : Function.Bijective Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchart : ∀ v, chart v = Exp v)
    (v : H) (hv : α v < 0) (K : Set Q.carrier) (hK : IsCompact K)
    (e : Q.carrier → Q.carrier) (he : Continuous e) (z : Q.carrier)
    (hshadow : ∀ n : ℕ, ∃ q ∈ K, z = e (exponentialConjugate Q.equiv Exp hbij
      (M.coneAdjointAutomorphism T (positiveWeightRay α) (positiveWeightRay_add α)
        ((n : ℝ) • v)) q)) : z = e 1 := by
  choose q hq hz using hshadow
  have ht := (he.tendsto 1).comp
    (M.ray_compact_sequence_tendsto_one T α Q Exp hExp hbij chart hchart v hv K hK q hq)
  have hh : Tendsto (fun _ : ℕ => z) atTop (𝓝 (e 1)) := by
    simpa only [Function.comp_def, ← hz] using ht
  exact tendsto_nhds_unique tendsto_const_nhds hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
