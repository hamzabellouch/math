import OAI.Geometry.HeilbronnTriangle.TypedFixedFiberCount
import OAI.Geometry.HeilbronnTriangle.ActualPointLawTriples
import OAI.Geometry.HeilbronnTriangle.PlaneRowTransport

namespace OAI


noncomputable section
attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

namespace Problem355.ActualPointLaw

open Matrix Parameters IntegerSampling OrbitSampling IntegerMatrixEvents
open TypedFixedFiberCount
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem weightedFiberBound_of_matrix_count (K : ℝ)
    (hraw : ∀ {B k q : ℕ} (_ : B.Prime) [Fact q.Prime],
      ∀ (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
        (d : PrimePowerData B k C)
        (L : AuxiliarySampling.Law q ((B ^ k) ^ 2)),
      (B ^ k).Coprime q → ((B : ℝ) ^ k) ^ 26 ≤ (q : ℝ) →
      ∀ (N : ℕ), 1 ≤ N → ∀ (S : Finset IntMatrix),
      (∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
        Section04Orbit.slOrbit C) →
      (∀ A ∈ S, ∀ j, Homogeneous.InBox (N : ℝ) (fun i => (A i j : ℝ))) →
      (∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
        PlaneRowTransport.projectedColumn A i ≠ PlaneRowTransport.projectedColumn A j) →
      ∀ t : ℤ, |t| < (q : ℤ) →
      (∑ A ∈ S.filter (fun A => A.det = t),
        LiftingProbability.auxiliaryWeight q L.size L.weight L.sets
          (A.map (Int.castRingHom (ZMod q))).col) ≤
        K * Real.log (2 * (N : ℝ)) ^ 2 * (N : ℝ) ^ 6 /
          ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2)
    {r : ℕ} [Fact r.Prime] (D : PrimeParameterData heilbronnK r)
    [Fact D.q.Prime] (aux : AuxiliarySampling.Law D.q (D.h ^ 2)) :
    WeightedFiberBound D aux K := by
  classical
  let : NeZero D.B := ⟨D.base_prime.ne_zero⟩
  let : NeZero (D.B ^ heilbronnK) := ⟨pow_ne_zero _ D.base_prime.ne_zero⟩
  unfold WeightedFiberBound
  intro z t ht
  have hparam : ((D.B : ℝ) ^ heilbronnK) ^ 26 ≤ (D.q : ℝ) := by
    exact_mod_cast (Nat.pow_le_pow_right (pow_pos D.base_prime.pos heilbronnK)
      (by norm_num : 26 ≤ 100)).trans D.auxiliary_lower.le
  have htq : |t| < (D.q : ℤ) :=
    ht.trans_lt (by exact_mod_cast D.tau_lt_q)
  have hb := hraw D.base_prime
    (transpose (fun j => MainDigitLaw.column D (z j))) (latentSmith D z) aux
    D.coprime hparam D.N D.N_pos
    (orbitEvent D.N (D.B ^ heilbronnK) (fun j => MainDigitLaw.column D (z j)))
    (fun A hA => orbitEvent_reduction hA)
    (fun A hA j => orbitEvent_box hA j)
    (fun A hA i j hij => orbitEvent_projections hA i j hij) t htq
  change (∑ A ∈ (orbitEvent D.N (D.B ^ heilbronnK)
      (fun j => MainDigitLaw.column D (z j))).filter (fun A => A.det = t),
      matrixWeight D.q aux.size aux.weight aux.sets A) ≤ _ at hb
  rw [orbitEvent_filter_det, ← sum_fixedDet_nested_event] at hb
  have hden : ((D.B : ℝ) ^ (latentSmith D z).b *
      (D.B : ℝ) ^ (latentSmith D z).e) ^ 2 =
      (((D.B ^ (latentSmith D z).b : ℕ) : ℝ) ^ 2 *
        ((D.B ^ (latentSmith D z).e : ℕ) : ℝ) ^ 2) := by
    rw [Nat.cast_pow, Nat.cast_pow, mul_pow]
  rw [hden] at hb
  exact hb

theorem weightedFiberBound {r : ℕ} [Fact r.Prime]
    (D : PrimeParameterData heilbronnK r) [Fact D.q.Prime]
    (aux : AuxiliarySampling.Law D.q (D.h ^ 2)) :
    WeightedFiberBound D aux UniformFixedFiberCount.countConstant :=
  weightedFiberBound_of_matrix_count _ UniformFixedFiberCount.matrix_fiber_le D aux

end Problem355.ActualPointLaw

end

end OAI
