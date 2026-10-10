import OAI.Probability.SLE.Gauge.PrescribedRadiusLevels

namespace OAI

/-! The chronological repeated entries, followed by their cleanup level,
  give a nondecreasing discrete clock for the adapted test calculation. -/
noncomputable section
open Set

namespace SLEExactGauge.Target

def prescribedBatchLevel {J : ℕ} (κ : ℝ) (W : WienerLaw) (n : ℕ)
    (e : Fin J → ℤ×ℕ) (A : ℝ) (z : ℂ) (i : ℕ) : ℝ :=
  if h : i<J then entryPhysicalLevel κ W (n,some (e ⟨i,h⟩)) A z
  else entryPhysicalLevel κ W (n,none) A z

private lemma entryPhysicalLevel_mono_position {κ : ℝ} (hκ : 0<κ)
    (W : WienerLaw) (n : ℕ) (A : ℝ) (z : ℂ)
    (o o' : Option (ℤ×ℕ))
    (hpos : entryPosition κ W (n,o) ≤ entryPosition κ W (n,o')) :
    entryPhysicalLevel κ W (n,o) A z ≤ entryPhysicalLevel κ W (n,o') A z := by
  have hp : (entryPosition κ W (n,o):ℝ) ≤ entryPosition κ W (n,o') := by exact_mod_cast hpos
  have hc : 0 ≤ 2*a κ*((batchLevel κ W n:ℝ)+(n:ℝ)) := by
    have ha := internal_a_pos hκ
    positivity
  have hh := mul_le_mul_of_nonneg_left hp hc
  dsimp only [entryPhysicalLevel]
  nlinarith

lemma prescribedBatchLevel_monotone {κ : ℝ} (hκ : 0<κ) (W : WienerLaw)
    {n J : ℕ} (hn : 1≤n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1^n ≤ moment κ W n) (e : Fin J → ℤ×ℕ)
    (he : ∀ i, (e i).2 < multiplicity κ W n (e i).1)
    (horder : StrictMono (fun i => entryPosition κ W (n,some (e i))))
    (A : ℝ) (z : ℂ) : Monotone (prescribedBatchLevel κ W n e A z) := by
  intro i j hij
  unfold prescribedBatchLevel
  by_cases hj : j<J
  · have hi : i<J := hij.trans_lt hj
    rw [dite_eq_left hi,dite_eq_left hj]
    exact entryPhysicalLevel_mono_position hκ W n A z _ _
      (horder.monotone (show (⟨i,hi⟩:Fin J) ≤ ⟨j,hj⟩ from hij))
  · rw [dite_eq_right hj]
    split_ifs with hi
    · exact entryPhysicalLevel_mono_position hκ W n A z _ _
        (entryPosition_lt_cleanup κ W hn hm1 hJ (he ⟨i,hi⟩)).le
    · exact le_rfl

lemma prescribedBatchLevel_test_end_le_next {κ : ℝ} (hκ : 0<κ) (W : WienerLaw)
    {n J : ℕ} (hn : 1≤n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1^n ≤ moment κ W n) (e : Fin J → ℤ×ℕ)
    (he : ∀ i, (e i).2 < multiplicity κ W n (e i).1)
    (horder : StrictMono (fun i => entryPosition κ W (n,some (e i))))
    (A : ℝ) (z : ℂ) (i : Fin J) :
    entryPhysicalLevel κ W (n,some (e i)) A z+2*a κ*(batchLevel κ W n:ℝ) ≤
      prescribedBatchLevel κ W n e A z (i.val+1) := by
  have ha := internal_a_pos hκ
  have hnon : 0 ≤ 2*a κ*(n:ℝ) := by positivity
  unfold prescribedBatchLevel
  split_ifs with hi
  · have hp := horder (show i < (⟨i.val+1,hi⟩:Fin J) from Nat.lt_succ_self _)
    have hh := entryPhysicalLevel_gap hκ W hn hp A z
    linarith
  · have hh := entryPhysicalLevel_cleanup_gap hκ W hn hm1 hJ (he i) A z
    linarith

lemma prescribedBatchLevel_test_end_le_cleanup {κ : ℝ} (hκ : 0<κ) (W : WienerLaw)
    {n J : ℕ} (hn : 1≤n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1^n ≤ moment κ W n) (e : Fin J → ℤ×ℕ)
    (he : ∀ i, (e i).2 < multiplicity κ W n (e i).1)
    (A : ℝ) (z : ℂ) (i : Fin J) :
    entryPhysicalLevel κ W (n,some (e i)) A z+2*a κ*(batchLevel κ W n:ℝ)+2*a κ*(n:ℝ) ≤
      entryPhysicalLevel κ W (n,none) A z :=
  entryPhysicalLevel_cleanup_gap hκ W hn hm1 hJ (he i) A z

end SLEExactGauge.Target

end

end OAI
