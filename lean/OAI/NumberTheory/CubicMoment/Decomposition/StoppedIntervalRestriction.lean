import OAI.NumberTheory.CubicMoment.Decomposition.StoppingCoefficientShift
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDyadPartition

namespace OAI

/-! Exact conversion of the sharp stopped side to the full analytic
interval at exclusion e=1. Coefficients vanish off their actual product
support, so the interval extension adds no term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedNormDyad_mem_iff {S : Finset Eisenstein} {j : ℕ} {n : Eisenstein}
    (hN : 2 ≤ norm n) :
    n ∈ stoppedNormDyad S j ↔
      n ∈ S ∧ stoppedNormDyadLength j/2 < norm n ∧ norm n ≤ stoppedNormDyadLength j := by
  constructor
  · intro hn
    exact ⟨(Finset.mem_filter.mp hn).1,stoppedNormDyad_bounds hn hN⟩
  · rintro ⟨hn,hlo,hhi⟩
    apply Finset.mem_filter.mpr
    refine ⟨hn,?_⟩
    have he : stoppedNormDyadLength j/2 = (2:ℝ)^j := by
      unfold stoppedNormDyadLength
      rw [pow_succ]
      ring
    rw [he] at hlo
    have hl : (2:ℕ)^j < normNat n := by
      exact_mod_cast (show (2:ℝ)^j < (normNat n:ℝ) by simpa only [normNat_cast] using hlo)
    have hu : normNat n ≤ (2:ℕ)^(j+1) := by
      exact_mod_cast (show (normNat n:ℝ) ≤ (2:ℝ)^(j+1) by
        simpa only [normNat_cast,stoppedNormDyadLength] using hhi)
    exact Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)

lemma primaryPairSupport_self_of_mem {F : ℝ} (hF : 1 ≤ F)
    {n : Eisenstein} (hn : n ∈ primaryElementBall F) :
    n ∈ primaryPairSupport (primaryElementBall F) (primaryElementBall F) := by
  refine Finset.mem_image.mpr ⟨(n,1),Finset.mem_product.mpr ⟨hn,?_⟩,by simp⟩
  exact mem_primaryElementBall.mpr ⟨primary_one,by simpa only [norm_one_eq] using hF⟩

lemma stoppedRowCoefficient_eq_zero_of_not_mem (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) {n : Eisenstein}
    (hn : n ∉ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff X))
      (primaryElementBall X)) :
    stoppedRowCoefficient X w z u W selected n = 0 := by
  unfold stoppedRowCoefficient stoppedBeta primaryPairCoefficient
  suffices hs : (∑ p ∈ primaryPairFiber
      (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X) n,
      if selected p.1 p.2 then
        distinguishedTupleCoefficient (fun _ : ι => primeCutoff X)
          (fun i p => W i (norm p)) primeDetectorCutoff w z p.1 *
            cutoffMoebius primeDetectorCutoff w p.2 else 0) = 0 by rw [hs,zero_mul]
  apply Finset.sum_eq_zero
  intro p hp
  exact (hn (Finset.mem_image.mpr ⟨p,(Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩)).elim

theorem stoppedBeta_interval_sum_to_row {X F B : ℝ}
    (hX : 1 ≤ X) (hXF : X ≤ F) (hBX : B ≤ X)
    (W : ι → ℝ → ℂ) (w z a : ℝ)
    (selected : Eisenstein → Eisenstein → Prop) (K : Eisenstein → ℂ) :
    (∑ n ∈ (primaryPairSupport (primaryElementBall F) (primaryElementBall F)).filter
        (fun n => Squarefree n ∧ a < norm n ∧ norm n ≤ B),
      stoppedBeta (primaryElementBall F) (primaryElementBall F)
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
          (fun i p => W i (norm p)) primeDetectorCutoff w z)
        primeDetectorCutoff w selected n*K n) =
      ∑ n ∈ stoppedIntervalSupport ι X a B 1,
        stoppedRowCoefficient X w z 0 W selected n*K n := by
  let Q := primaryPairSupport (primaryElementBall F) (primaryElementBall F)
  have hQ (n : Eisenstein) (hn : n ∈ Q) : primary n :=
    primaryPairSupport_primary _ _ (fun _ h => (mem_primaryElementBall.mp h).1)
      (fun _ h => (mem_primaryElementBall.mp h).1) hn
  apply Finset.sum_congr_of_eq_on_inter
  · intro n hn hnot
    obtain ⟨hn,hs,hlo,hhi⟩ := Finset.mem_filter.mp hn
    have hp := hQ n hn
    have hb := stoppedBeta_eq_stoppedRowCoefficient hXF W w z selected hp (hhi.trans hBX)
    rw [hb]
    have hsupport : n ∉ primaryPairSupport
        (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X) := by
      intro hh
      apply hnot
      apply Finset.mem_filter.mpr
      exact ⟨hh,hs,isCoprime_one_right,hlo,hhi⟩
    rw [stoppedRowCoefficient_eq_zero_of_not_mem X w z 0 W selected hsupport,zero_mul]
  · intro n hn hnot
    obtain ⟨hp,hs,hhi⟩ := stoppedIntervalSupport_spec X a B 1 hn
    have hh := Finset.mem_filter.mp hn
    have hnQ : n ∈ Q := primaryPairSupport_self_of_mem (hX.trans hXF)
      (mem_primaryElementBall.mpr ⟨hp,(hhi.trans hBX).trans hXF⟩)
    exact (hnot (Finset.mem_filter.mpr ⟨hnQ,hs,hh.2.2.2.1,hhi⟩)).elim
  · intro n hn _
    obtain ⟨hn,_hs,_hlo,hhi⟩ := Finset.mem_filter.mp hn
    rw [stoppedBeta_eq_stoppedRowCoefficient hXF W w z selected (hQ n hn) (hhi.trans hBX)]

end CubicFirstMoment

end

end OAI
