import OAI.Analysis.LipschitzHilbert.Geometry.SourcePackingIntegral

namespace OAI

/-! The short-envelope square bound from geometric packing. Centers may
lie outside the top; the reciprocal top weight supplies localization. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

private theorem tileEnvelope_two_le_one (a b ell W : ℝ) (z : ℝ×ℝ) :
    tileEnvelope a b ell W 2 z≤1 := by
  have ht : tileEnvelope a b ell W 2 z≤tileEnvelope a b ell W 1 z :=
    mul_le_mul (lineEnvelope_antitone _ _ _ (by decide : 1≤2))
      (lineEnvelope_antitone _ _ _ (by decide : 1≤2)) (lineEnvelope_nonneg _ _ _ _)
      (lineEnvelope_nonneg _ _ _ _)
  exact ht.trans (topReciprocalWeight_le_one a b ell W z)

theorem packed_envelope_energy {ι : Type*}
    (S : Finset ι) (cx cy ell : ι → ℝ) (a b L W K : ℝ)
    (hL : 0<L) (hW : 0<W) (hell : ∀ i∈S, 0<ell i)
    (hlen : ∀ i∈S, ell i≤L)
    (hcount : ∀ z, ((S.filter fun i => z∈coordinateBox (cx i) (cy i) (ell i) W).card:ℝ)≤K) :
    let H := fun z => topReciprocalWeight a b L W z*
      ∑ i∈S, tileEnvelope (cx i) (cy i) (ell i) W 2 z
    Integrable (fun z => (H z)^2) (volume.prod volume) ∧
      (∫ z, (H z)^2 ∂volume.prod volume)≤(82944*K)^2*1296*Real.pi^2*L*W := by
  classical
  let D := topReciprocalWeight a b L W
  let E := fun z => ∑ i∈S, tileEnvelope (cx i) (cy i) (ell i) W 2 z
  let H := fun z => D z*E z
  have hDm : Measurable D := topReciprocalWeight_measurable a b L W
  have hEm : Measurable E := Finset.measurable_sum _ (fun i _ => tileEnvelope_measurable _ _ _ _ _)
  have hHm : Measurable H := hDm.mul hEm
  have hD0 (z) : 0≤D z := topReciprocalWeight_nonneg a b L W z
  have hE0 (z) : 0≤E z := Finset.sum_nonneg (fun i _ => tileEnvelope_nonneg _ _ _ _ _ _)
  have hH0 (z) : 0≤H z := mul_nonneg (hD0 z) (hE0 z)
  have hDb (z) : ‖D z‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hD0 z)]
    exact topReciprocalWeight_le_one a b L W z
  have hEb (z) : ‖E z‖≤(S.card:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hE0 z)]
    calc
      _ ≤ ∑ _i∈S, (1:ℝ) := Finset.sum_le_sum (fun i _ => tileEnvelope_two_le_one _ _ _ _ z)
      _ = _ := by simp
  have hHb (z) : ‖H z‖≤(S.card:ℝ) := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hDb z) (hEb z) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hDi : Integrable D (volume.prod volume) := tileEnvelope_integrable a b L W (by decide : 1≤1) hL hW
  have hHi : Integrable H (volume.prod volume) :=
    hDi.mul_bdd hEm.aestronglyMeasurable (Filter.Eventually.of_forall hEb)
  have hHs : Integrable (fun z => (H z)^2) (volume.prod volume) := by
    simpa only [pow_two] using hHi.mul_bdd hHm.aestronglyMeasurable (Filter.Eventually.of_forall hHb)
  have hH2 : MemLp H 2 (volume.prod volume) :=
    (memLp_two_iff_integrable_sq hHm.aestronglyMeasurable).mpr hHs
  have hpair := packed_weighted_envelope_pairing S cx cy ell a b L W K hL hW hell hlen hcount
    H hHm hH2 S.card (Nat.cast_nonneg _) hH0 hHb
  have hterm (i : ι) (hi : i∈S) :
      Integrable (fun z => D z*tileEnvelope (cx i) (cy i) (ell i) W 2 z*H z) (volume.prod volume) :=
    (((tileEnvelope_integrable (cx i) (cy i) (ell i) W (by decide : 1≤2) (hell i hi) hW).bdd_mul
      hDm.aestronglyMeasurable (Filter.Eventually.of_forall hDb)).mul_bdd
      hHm.aestronglyMeasurable (Filter.Eventually.of_forall hHb))
  have hsum : (∑ i∈S, ∫ z, D z*tileEnvelope (cx i) (cy i) (ell i) W 2 z*H z
      ∂volume.prod volume)=(∫ z, (H z)^2 ∂volume.prod volume) := by
    rw [←integral_finsetSum _ hterm]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [←Finset.mul_sum,←Finset.sum_mul]
    change D z*E z*H z=(H z)^2
    rw [←pow_two]
  rw [hsum] at hpair
  let M := DyadicLineGrid.threeStrongMaximal H
  have hM := DyadicLineGrid.threeStrongMaximal_energy hHm hH2
  have hD := topReciprocalWeight_energy a b L W hL hW
  have hM0 (z) : 0≤M z := DyadicLineGrid.threeStrongMaximal_nonneg H z
  have hI0 : 0≤∫ z, D z*M z ∂volume.prod volume := integral_nonneg (fun z => mul_nonneg (hD0 z) (hM0 z))
  have hQ0 : 0≤∫ z, (H z)^2 ∂volume.prod volume := integral_nonneg (fun _ => sq_nonneg _)
  have hDE0 : 0≤∫ z, (D z)^2 ∂volume.prod volume := integral_nonneg (fun _ => sq_nonneg _)
  have hME0 : 0≤∫ z, (M z)^2 ∂volume.prod volume := integral_nonneg (fun _ => sq_nonneg _)
  have hcs : (∫ z, D z*M z ∂volume.prod volume)≤
      Real.sqrt (∫ z, (D z)^2 ∂volume.prod volume)*Real.sqrt (∫ z, (M z)^2 ∂volume.prod volume) := by
    simpa only [Real.rpow_two,←Real.sqrt_eq_rpow] using
      integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall hD0) (Filter.Eventually.of_forall hM0)
        (by simpa using hD.1) (by simpa using hM.1)
  have hcssq := pow_le_pow_left₀ hI0 hcs 2
  rw [mul_pow,Real.sq_sqrt hDE0,Real.sq_sqrt hME0] at hcssq
  have hcost : (∫ z, D z*M z ∂volume.prod volume)^2≤
      (Real.pi^2*L*W)*(1296*∫ z, (H z)^2 ∂volume.prod volume) :=
    hcssq.trans (mul_le_mul hD.2 hM.2 hME0 (by positivity))
  have hfinal := pow_le_pow_left₀ hQ0 hpair 2
  rw [mul_pow] at hfinal
  have hlast := hfinal.trans (mul_le_mul_of_nonneg_left hcost (sq_nonneg (82944*K)))
  refine ⟨hHs,?_⟩
  change (∫ z, (H z)^2 ∂volume.prod volume)≤(82944*K)^2*1296*Real.pi^2*L*W
  by_cases hz : (∫ z, (H z)^2 ∂volume.prod volume)=0
  · rw [hz]
    positivity
  · have hpos := lt_of_le_of_ne hQ0 (Ne.symm hz)
    nlinarith only [hlast,hpos]

end LipschitzHilbert

end

end OAI
