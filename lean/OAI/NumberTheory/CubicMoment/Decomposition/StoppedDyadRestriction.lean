import OAI.NumberTheory.CubicMoment.Decomposition.StoppedIntervalRestriction

namespace OAI

/-! The original squarefree sharp dyad is exactly the full analytic
stopped interval. Its possible norm-one term vanishes by the genuine
stopping lower bound, rather than being discarded from the finite sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedRowCoefficient_geometric_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (W : ι → ℝ → ℂ) (w z u Z Q : ℝ)
    (j k h : ℕ) (early : Bool) (n : Eisenstein) :
    stoppedRowCoefficient X w z u W
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
        (j+(geometricBinCount ρ F-geometricBinCount ρ X)) k
        (h+(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early) n =
      stoppedRowCoefficient X w z u W
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          j k h Z Q early) n := by
  unfold stoppedRowCoefficient
  congr 1
  apply stoppedBeta_selected_congr
  intro r _ d hd _
  have hdp := mem_primaryElementBall.mp hd
  exact geometricStoppedSideTest_shift hρ hX hXF hdp.1 hdp.2 j k h Z Q early r

lemma stoppedRowCoefficient_geometric_shift_of_bounds {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (W : ι → ℝ → ℂ) (w z u Z Q : ℝ)
    (j k h : ℕ) (early : Bool) (n : Eisenstein)
    (hj : geometricBinCount ρ F-geometricBinCount ρ X ≤ j)
    (hh : geometricBinCount ρ F-geometricBinCount ρ X ≤ h) :
    stoppedRowCoefficient X w z u W
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q early) n =
      stoppedRowCoefficient X w z u W
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
          (h-(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early) n := by
  simpa only [Nat.sub_add_cancel hj,Nat.sub_add_cancel hh] using
    stoppedRowCoefficient_geometric_shift hρ hX hXF W w z u Z Q
      (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
      (h-(geometricBinCount ρ F-geometricBinCount ρ X)) early n

theorem stoppedBeta_sharp_dyad_to_row {ρ X F w Z Q : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X) (hXF : X ≤ F)
    (hw : 0 < w) (hZ : 2 ≤ Z) (W : ι → ℝ → ℂ) (z : ℝ)
    (j k h i : ℕ) (hk : 1 ≤ k) (early : Bool) (K : Eisenstein → ℂ)
    (hBX : stoppedNormDyadLength i ≤ X) :
    let selected := stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      j k h Z Q early
    let β := stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun a p => W a (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w selected
    (∑ n ∈ stoppedNormDyad
        ((primaryPairSupport (primaryElementBall F) (primaryElementBall F)).filter
          (fun n => Squarefree n ∧ norm n ≤ F)) i, β n*K n) =
      ∑ n ∈ stoppedIntervalSupport ι X (stoppedNormDyadLength i/2)
        (stoppedNormDyadLength i) 1,
        stoppedRowCoefficient X w z 0 W selected n*K n := by
  let selected := stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
    j k h Z Q early
  let β := stoppedBeta (primaryElementBall F) (primaryElementBall F)
    (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
      (fun a p => W a (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w selected
  let R := primaryPairSupport (primaryElementBall F) (primaryElementBall F)
  let B := stoppedNormDyadLength i
  change (∑ n ∈ stoppedNormDyad (R.filter (fun n => Squarefree n ∧ norm n ≤ F)) i,
      β n*K n) = ∑ n ∈ stoppedIntervalSupport ι X (B/2) B 1,
        stoppedRowCoefficient X w z 0 W selected n*K n
  have hB : 2 ≤ B := by
    have hh : (1:ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
    dsimp [B,stoppedNormDyadLength]
    rw [pow_succ]
    nlinarith
  have hlow (n : Eisenstein) (hs : Squarefree n) (hne : β n ≠ 0) :
      2 ≤ norm n := by
    have hh := stoppedBeta_norm_bounds (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun a p => W a (norm p)) primeDetectorCutoff w z)
      (fun x hx => primeDetectorCutoff_zero hx) hρ hρ₂ (by norm_num : (0:ℝ) ≤ 1)
      (by simpa using hρ₂) (by linarith : 0 < Z) hw
      (fun d hd => mem_primaryElementBall.mp hd) hk early hs hne
    exact hZ.trans hh.1
  have heq : (∑ n ∈ stoppedNormDyad (R.filter (fun n => Squarefree n ∧ norm n ≤ F)) i,
      β n*K n) = ∑ n ∈ R.filter (fun n => Squarefree n ∧ B/2 < norm n ∧ norm n ≤ B),
        β n*K n := by
    apply Finset.sum_congr_of_eq_on_inter
    · intro n hn hnot
      by_cases hz : β n = 0
      · rw [hz,zero_mul]
      · have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.1
        have hr := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
        have hd := stoppedNormDyad_bounds hn (hlow n hs hz)
        exact (hnot (Finset.mem_filter.mpr ⟨hr,hs,hd⟩)).elim
    · intro n hn hnot
      obtain ⟨hr,hs,hlo,hhi⟩ := Finset.mem_filter.mp hn
      have hone : (1:ℝ) < norm n := lt_of_le_of_lt (by linarith) hlo
      have hnat : 1 < normNat n := by
        exact_mod_cast (show (1:ℝ) < (normNat n:ℝ) by simpa only [normNat_cast] using hone)
      have hn2 : (2:ℝ) ≤ norm n := by
        rw [←normNat_cast]
        exact_mod_cast (show 2 ≤ normNat n by omega)
      apply (hnot ((stoppedNormDyad_mem_iff hn2).mpr ?_)).elim
      exact ⟨Finset.mem_filter.mpr ⟨hr,hs,(hhi.trans hBX).trans hXF⟩,hlo,hhi⟩
    · intro _ _ _
      rfl
  rw [heq]
  exact stoppedBeta_interval_sum_to_row hX hXF hBX W w z (B/2) selected K

end CubicFirstMoment

end

end OAI
