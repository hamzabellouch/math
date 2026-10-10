import OAI.Dynamics.StandardMap.BackwardSlice

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma atom_lift_lintegral (A:Set Torus) (hA:MeasurableSet A) (g:Torus → ℝ≥0∞) (hg:Measurable g) :
    (∫⁻z in A,g z ∂area)=∫⁻z in (Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) ∩ liftProjection ⁻¹' A,g (liftProjection z) := by
  rw [← lintegral_indicator hA,← unit_ico_cell_integral _ (hg.indicator hA)]
  have hcomp:(fun z=>A.indicator g (liftProjection z))=
      (liftProjection ⁻¹' A).indicator (g ∘ liftProjection) := by
    funext z
    by_cases hz:liftProjection z∈A <;> simp [hz]
  rw [hcomp,lintegral_indicator (continuous_liftProjection.measurable hA),
    Measure.restrict_restrict (continuous_liftProjection.measurable hA),inter_comm]
  rfl
lemma grid_atom_lintegral (k ε:ℝ) (hk:0≤k) (hε:0≤ε)
    (hε1:2*Real.pi*ε≤1) (hε2:growthBase k*ε≤1)
    (Q N:ℕ) (hQ:0<Q) (hQε:6/(Q:ℝ)≤ε) (hN:0<N) (hN2:2*growthBase k≤(N:ℝ)^2)
    (n:ℕ) (w:Fin (n+1) → Fin (Q*Q+1)) :
    (∫⁻z in blockAtom (torusStep k) (gridPartition Q hQ) (n+1) w,
      ENNReal.ofReal ‖torusSegmentTransfer k z 0 n‖ ∂area)≤
      ENNReal.ofReal (4*ε/(Q:ℝ))*((196*N:ℕ):ℝ≥0∞)^n := by
  let A:=blockAtom (torusStep k) (gridPartition Q hQ) (n+1) w
  have hA:MeasurableSet A := blockAtom_measurable _ (continuous_torusStep k).measurable _ _ _
  by_cases he:A.Nonempty
  · obtain ⟨z0,hz0⟩:=he
    let T:Set CurvePlane:=(Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) ∩ liftProjection ⁻¹' A
    have hT:MeasurableSet T := (measurableSet_Ico.prod measurableSet_Ico).inter (continuous_liftProjection.measurable hA)
    have hword:∀z∈T,∀j≤n,gridLabel Q hQ ((torusStep k)^[j] (liftProjection z))=
        gridLabel Q hQ ((torusStep k)^[j] z0) := by
      intro z hz j hj
      exact ((hz.2 : liftProjection z∈A) ⟨j,by omega⟩).trans (hz0 ⟨j,by omega⟩).symm
    have h:=grid_word_transfer_integral k ε hk hε hε1 hε2 Q N hQ hQε hN hN2 n z0 T hT
      (fun _ hz=>hz.1) hword
    change (∫⁻z in A,ENNReal.ofReal ‖torusSegmentTransfer k z 0 n‖ ∂area)≤_
    rw [atom_lift_lintegral A hA (fun z=>ENNReal.ofReal ‖torusSegmentTransfer k z 0 n‖) (ENNReal.measurable_ofReal.comp (continuous_torusSegmentTransfer k 0 n).norm.measurable)]
    simpa only [torusSegmentTransfer_lift] using h
  · have hzero:A=∅ := not_nonempty_iff_eq_empty.mp he
    change (∫⁻z in A,ENNReal.ofReal ‖torusSegmentTransfer k z 0 n‖ ∂area)≤_
    rw [hzero,Measure.restrict_empty,lintegral_zero_measure]
    exact bot_le
lemma integrable_transfer_norm (k:ℝ) (n:ℕ) : Integrable (fun z=>‖torusSegmentTransfer k z 0 n‖) area :=
  (continuous_torusSegmentTransfer k 0 n).norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma integrable_transfer_log (k:ℝ) (hk:0≤k) (n:ℕ) : Integrable (fun z=>Real.log ‖torusSegmentTransfer k z 0 n‖) area :=
  ((continuous_torusSegmentTransfer k 0 n).norm.log (fun z=>by
    have h:=(torusSegmentTransfer_norm_bounds k hk z 0 n).1; linarith)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma grid_atom_integral (k ε:ℝ) (hk:0≤k) (hε:0≤ε)
    (hε1:2*Real.pi*ε≤1) (hε2:growthBase k*ε≤1)
    (Q N:ℕ) (hQ:0<Q) (hQε:6/(Q:ℝ)≤ε) (hN:0<N) (hN2:2*growthBase k≤(N:ℝ)^2)
    (n:ℕ) (w:Fin (n+1) → Fin (Q*Q+1)) :
    (∫z in blockAtom (torusStep k) (gridPartition Q hQ) (n+1) w,
      ‖torusSegmentTransfer k z 0 n‖ ∂area)≤
      (4*ε/(Q:ℝ))*((196*N:ℕ):ℝ)^n := by
  have h:=grid_atom_lintegral k ε hk hε hε1 hε2 Q N hQ hQε hN hN2 n w
  have hC:0≤4*ε/(Q:ℝ) := by positivity
  have he:ENNReal.ofReal ((4*ε/(Q:ℝ))*((196*N:ℕ):ℝ)^n)=
      ENNReal.ofReal (4*ε/(Q:ℝ))*((196*N:ℕ):ℝ≥0∞)^n := by
    rw [ENNReal.ofReal_mul hC,ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_natCast]
  rw [← he] at h
  have hreal:=ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z=>norm_nonneg _)
    (integrable_transfer_norm k n).integrableOn.aestronglyMeasurable]
  exact hreal
lemma grid_block_entropy_growth (k ε:ℝ) (hk:0≤k) (hε:0<ε)
    (hε1:2*Real.pi*ε≤1) (hε2:growthBase k*ε≤1)
    (Q N:ℕ) (hQ:0<Q) (hQε:6/(Q:ℝ)≤ε) (hN:0<N) (hN2:2*growthBase k≤(N:ℝ)^2)
    (n:ℕ) :
    (∫z,Real.log ‖torusSegmentTransfer k z 0 n‖ ∂area)-
      Real.log (4*ε/(Q:ℝ))-(n:ℝ)*Real.log ((196*N:ℕ):ℝ)≤
      blockEntropy area (torusStep k) (gridPartition Q hQ) (n+1) := by
  have hC:0<4*ε/(Q:ℝ) := by positivity
  have hR:(0:ℝ)<(196*N:ℕ) := by exact_mod_cast Nat.mul_pos (by norm_num : 0<196) hN
  have h:=entropy_from_atom_integrals area (torusStep k) (continuous_torusStep k).measurable (gridPartition Q hQ) (n+1)
    (fun z=>‖torusSegmentTransfer k z 0 n‖) (integrable_transfer_norm k n) (integrable_transfer_log k hk n)
    (fun z=>lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk z 0 n).1)
    ((4*ε/(Q:ℝ))*((196*N:ℕ):ℝ)^n) (by positivity)
    (grid_atom_integral k ε hk hε.le hε1 hε2 Q N hQ hQε hN hN2 n)
  rw [Real.log_mul hC.ne' (pow_pos hR n).ne',Real.log_pow] at h
  linarith
end StandardMapEntropy

end OAI
