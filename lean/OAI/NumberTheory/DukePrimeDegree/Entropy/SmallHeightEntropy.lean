import OAI.NumberTheory.DukePrimeDegree.Geometry.HeightBoundaryCount
import OAI.NumberTheory.DukePrimeDegree.Entropy.RareTernaryEntropy

namespace OAI

/-! # Coarse heights with uniformly small finite-observation entropy

A shift of a sufficiently coarse binning has rare changes. The ternary
reconstruction bound therefore makes every finite truncation have small
entropy rate, without any moment assumption on the original height.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_coarse_height_small_entropy
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (H : Y → ℕ) (hH : Measurable H)
    (hstep : ∀ x, H (T x) ≤ H x+1 ∧ H x ≤ H (T x)+1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (q r : ℕ), 0 < q ∧ r < q ∧ ∀ N : ℕ,
      observationEntropyRate μ T (heightClip (fun x => (H x+r)/q) N) < ε := by
  obtain ⟨δ,hδ,hsmall⟩ := rareTernaryCost_small hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (half_pos hδ)
  let q := k+1
  have hq : 0 < q := Nat.succ_pos k
  have hqδ : 2/(q:ℝ) < δ := by
    have he : 2/(q:ℝ)=2*(1/(k+1:ℝ)) := by dsimp [q]; push_cast; ring
    rw [he]
    linarith
  obtain ⟨r,hr,hchange⟩ := exists_shift_rare_height_changes μ hT H hH hstep q hq
  let J : Y → ℕ := fun x => (H x+r)/q
  have hJ : Measurable J := (measurable_of_countable (fun a : ℕ => (a+r)/q)).comp hH
  have hJstep (x : Y) : J (T x) ≤ J x+1 ∧ J x ≤ J (T x)+1 := by
    have hs := hstep x
    constructor
    · calc
        _ ≤ (H x+r+q)/q := Nat.div_le_div_right (by omega)
        _ = _ := Nat.add_div_right _ hq
    · calc
        _ ≤ (H (T x)+r+q)/q := Nat.div_le_div_right (by omega)
        _ = _ := Nat.add_div_right _ hq
  refine ⟨q,r,hq,hr,?_⟩
  intro N
  obtain ⟨D,decode,hD,hdecode,hmid⟩ := heightClip_increment_model hT.measurable J hJ hJstep N
  have hsub : {x | D x≠1} ⊆ {x | J (T x)≠J x} := by
    intro x hx he
    apply hx
    apply (hmid x).mpr
    apply Fin.ext
    change min (J (T x)) N = min (J x) N
    rw [he]
  have hp : μ.real {x | D x≠1} < δ :=
    ((measureReal_mono hsub (measure_ne_top _ _)).trans hchange).trans_lt hqδ
  exact ((observationEntropyRate_le_incrementEntropy μ hT (heightClip J N)
    (heightClip_measurable hJ N) D hD decode hdecode).trans
      (observationEntropy_ternary_le μ D hD)).trans_lt
        (hsmall _ measureReal_nonneg hp)

end DukePrimeDegree

end

end OAI
