import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitRecurrence
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootShearing

namespace OAI

/-!
# Integral matrices from recurrence on a subgroup orbit

A late return with close subgroup parameters in the arithmetic quotient
produces a conjugate integral special-linear matrix. This is the orbit
recurrence step in EKL Theorem 5.1.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets

/-- Recurrence on a closed subgroup orbit produces integral conjugates
of late flow elements multiplied by arbitrarily small subgroup elements. -/
theorem exists_integral_return_of_closed_orbit {n : ℕ}
    (H : Subgroup (G n)) (hH : IsClosed (H : Set (G n)))
    (μ : Measure (X n)) [IsFiniteMeasure μ] [NeZero μ]
    (x : X n) (hfull : ∀ᵐ y ∂μ, ∃ h : H, rightAction x (h : G n) = y)
    (a : G n) (hinv : μ.map (fun y => rightAction y a) = μ)
    (U : Set H) (hU : U ∈ 𝓝 1) (N : ℕ) :
    ∃ m > N, ∃ h : H, h ∈ U ∧ ∃ q : G n,
      ∃ γ : Matrix.SpecialLinearGroup (Fin n) ℤ,
        q⁻¹ * (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) * q =
          a ^ m * (h : G n) := by
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let T : X n → X n := fun y => rightAction y a
  have hT : MeasurePreserving T μ μ := ⟨(continuous_rightAction a).measurable, hinv⟩
  have hψ : Continuous (fun h : H => rightAction x (h : G n)) :=
    (continuous_rightAction_uncurry n).comp (continuous_const.prodMk continuous_subtype_val)
  have hV : Inv.inv ⁻¹' U ∈ 𝓝 (1 : H) := by
    have ht : Tendsto (Inv.inv : H → H) (𝓝 1) (𝓝 1) := by
      simpa only [inv_one] using continuous_inv.tendsto (1 : H)
    exact ht.eventually hU
  obtain ⟨m, hm, r, s, hclose, hret⟩ :=
    exists_close_parameters_of_orbit_recurrence μ T hT
      (fun h : H => rightAction x (h : G n)) hψ hfull _ hV N
  have hiter (k : ℕ) (y : X n) : T^[k] y = rightAction y (a ^ k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      change rightAction (rightAction y (a ^ k)) a = rightAction y (a ^ (k + 1))
      rw [rightAction_mul, pow_succ]
  rw [hiter, rightAction_mul] at hret
  obtain ⟨q₀, hq₀⟩ := Quotient.exists_rep x
  rw [← hq₀] at hret
  have heq : Quotient.mk (QuotientGroup.rightRel (integralGroup n))
      (q₀ * ((r : G n) * a ^ m)) =
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (q₀ * (s : G n)) := hret
  have hΓ : (q₀ * ((r : G n) * a ^ m)) * (q₀ * (s : G n))⁻¹ ∈ integralGroup n :=
    (QuotientGroup.rightRel_apply).mp (Quotient.exact heq.symm)
  obtain ⟨γ, hγ⟩ := hΓ
  refine ⟨m, hm, s⁻¹ * r, ?_, q₀ * (r : G n), γ, ?_⟩
  · simpa only [mem_preimage, mul_inv_rev, inv_inv] using hclose
  · rw [hγ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

end DukePrimeDegree

end

end OAI
