import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRowBinShift
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingSelectedScale
import OAI.NumberTheory.CubicMoment.Estimates.SparseStoppingLabels

namespace OAI

/-! Recovering the smaller-envelope labels on actual nonzero stopped
coefficients, and transporting the independent remaining-side coefficient.
All finite support and both stopping thresholds stay unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppingSideTest_label_shift_bound {ρ X F Z : ℝ}
    (hρ : 1 < ρ) (hX : 0 < X) (hXF : X ≤ F)
    {d r : Eisenstein} (hd : primary d) (hdX : norm d ≤ X)
    {j k : ℕ} (hk : 1 ≤ k)
    (hs : stoppingSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k Z r d) :
    geometricBinCount ρ F-geometricBinCount ρ X ≤ j := by
  have hne : (primeBin (primaryPrimeFactors d) (geometricPrimeBin ρ F) j).Nonempty :=
    Finset.card_pos.mp (by rw [hs.2.1]; omega)
  obtain ⟨p,hp⟩ := hne
  obtain ⟨hpd,hpj⟩ := Finset.mem_filter.mp hp
  have hprime := primaryPrimeFactor_spec hd hpd
  have hpX := (norm_le_of_dvd (primary_ne_zero hd) hprime.2).trans hdX
  have hshift := geometricPrimeBin_shift hρ hX hXF hprime.1 hpX
  rw [hpj] at hshift
  omega

lemma stoppedBeta_label_shift_bound (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) {ρ X F Z Q : ℝ}
    (hρ : 1 < ρ) (hX : 0 < X) (hXF : X ≤ F)
    (hD : ∀ d ∈ D, primary d) {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X)
    {j k h : ℕ} (hk : 1 ≤ k) (early : Bool)
    (hne : stoppedBeta R D v ψ w
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
        j k h Z Q early) b ≠ 0) :
    geometricBinCount ρ F-geometricBinCount ρ X ≤ j := by
  unfold stoppedBeta primaryPairCoefficient at hne
  obtain ⟨p,hp,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
  obtain ⟨_hr,hd⟩ := Finset.mem_product.mp hp
  have hs : stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      j k h Z Q early p.1 p.2 := by
    by_contra hs
    exact hterm (ite_eq_right hs)
  have hdb : p.2 ∣ b := ⟨p.1,by rw [mul_comm,he]⟩
  exact stoppingSideTest_label_shift_bound hρ hX hXF (hD p.2 hd)
    ((norm_le_of_dvd (primary_ne_zero hb) hdb).trans hbX) hk hs.1

theorem stoppedBeta_geometric_eq_row_of_bounds {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (W : ι → ℝ → ℂ) (w z Z Q : ℝ)
    (j k h : ℕ) (early : Bool) {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X)
    (hj : geometricBinCount ρ F-geometricBinCount ρ X ≤ j)
    (hh : geometricBinCount ρ F-geometricBinCount ρ X ≤ h) :
    stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun i p => W i (norm p)) primeDetectorCutoff w z)
      primeDetectorCutoff w
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q early) b =
      stoppedRowCoefficient X w z 0 W
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
          (h-(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early) b := by
  simpa only [Nat.sub_add_cancel hj,Nat.sub_add_cancel hh] using
    stoppedBeta_geometric_eq_row hρ hX hXF W w z Z Q
      (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
      (h-(geometricBinCount ρ F-geometricBinCount ρ X)) early hb hbX

/-- On a surviving early row both original labels have a valid smaller
envelope label; the beta is the literal row used in the analytic theorem. -/
theorem stoppedBeta_early_geometric_eq_row {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (W : ι → ℝ → ℂ) (w z Z Q : ℝ)
    {j k h : ℕ} (hk : 1 ≤ k) (hjh : j < h)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X)
    (hne : stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun i p => W i (norm p)) primeDetectorCutoff w z)
      primeDetectorCutoff w
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q true) b ≠ 0) :
    stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun i p => W i (norm p)) primeDetectorCutoff w z)
      primeDetectorCutoff w
      (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F) j k h Z Q true) b =
      stoppedRowCoefficient X w z 0 W
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          (j-(geometricBinCount ρ F-geometricBinCount ρ X)) k
          (h-(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q true) b := by
  have hj := stoppedBeta_label_shift_bound _ _ _ _ _ hρ hX hXF
    (fun _ hd => (mem_primaryElementBall.mp hd).1) hb hbX hk true hne
  exact stoppedBeta_geometric_eq_row_of_bounds hρ hX hXF W w z Z Q j k h true hb hbX
    hj (hj.trans hjh.le)

lemma geometricStoppingRemainingTest_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) {e : Eisenstein}
    (he : primary e) (heX : norm e ≤ X) (j l : ℕ) :
    stoppingRemainingTest (geometricPrimeBin ρ F)
      (j+(geometricBinCount ρ F-geometricBinCount ρ X)) l e ↔
    stoppingRemainingTest (geometricPrimeBin ρ X) j l e := by
  have hs (p : Eisenstein) (hp : p ∈ primaryPrimeFactors e) :
      primaryPrime p ∧ norm p ≤ X :=
    ⟨(primaryPrimeFactor_spec he hp).1,
      (norm_le_of_dvd (primary_ne_zero he) (primaryPrimeFactor_spec he hp).2).trans heX⟩
  have hall : (∀ p ∈ primaryPrimeFactors e,
      j+(geometricBinCount ρ F-geometricBinCount ρ X) ≤ geometricPrimeBin ρ F p) ↔
      ∀ p ∈ primaryPrimeFactors e, j ≤ geometricPrimeBin ρ X p := by
    constructor
    · intro h p hp
      have hh := h p hp
      rw [geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2] at hh
      omega
    · intro h p hp
      rw [geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2]
      exact Nat.add_le_add_right (h p hp) _
  unfold stoppingRemainingTest
  rw [hall,geometricPrimeBin_finset_shift hρ hX hXF (primaryPrimeFactors e) hs]

theorem stoppedAlpha_geometric_restrict {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (ψ : ℝ → ℝ) (w : ℝ) (j l : ℕ)
    {a : Eisenstein} (ha : primary a) (haX : norm a ≤ X) :
    stoppedAlpha (primaryElementBall F) (primaryElementBall F) ψ w
      (stoppingRemainingTest (geometricPrimeBin ρ F)
        (j+(geometricBinCount ρ F-geometricBinCount ρ X)) l) a =
      stoppedAlpha (primaryElementBall X) (primaryElementBall X) ψ w
        (stoppingRemainingTest (geometricPrimeBin ρ X) j l) a := by
  unfold stoppedAlpha primaryPairCoefficient
  rw [primaryPairFiber_ball_restrict hXF ha haX]
  apply Finset.sum_congr rfl
  intro p hp
  have he := mem_primaryElementBall.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  dsimp only
  rw [propext (geometricStoppingRemainingTest_shift hρ hX hXF he.1 he.2 j l)]

end CubicFirstMoment

end

end OAI
