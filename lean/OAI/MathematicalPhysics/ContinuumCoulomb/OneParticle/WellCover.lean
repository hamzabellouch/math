import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedWellField
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CubeGeometry

namespace OAI

/-! A cover of the actual well support by boxes whose total volume is
linear in the number of wells and the vertical cutoff radius. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def wellCoverBox (u : PlanarPosition) (r S : ℝ) : Set Position :=
  WithLp.ofLp ⁻¹' Set.Icc ![u 0-r,u 1-r,-S] ![u 0+r,u 1+r,S]

theorem mem_wellCoverBox {u : PlanarPosition} {r S : ℝ} {x : Position} :
    x ∈ wellCoverBox u r S ↔ |x 0-u 0| ≤ r ∧ |x 1-u 1| ≤ r ∧ |x 2| ≤ S := by
  constructor
  · rintro ⟨hl,hu⟩
    have h0l := hl 0; have h0u := hu 0
    have h1l := hl 1; have h1u := hu 1
    have h2l := hl 2; have h2u := hu 2
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at *
    exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,
      abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨h2l,h2u⟩⟩
  · rintro ⟨h0,h1,h2⟩
    obtain ⟨h0l,h0u⟩ := abs_le.mp h0
    obtain ⟨h1l,h1u⟩ := abs_le.mp h1
    obtain ⟨h2l,h2u⟩ := abs_le.mp h2
    constructor <;> intro i <;> fin_cases i <;> simp <;> linarith

theorem wellCoverBox_isClosed (u : PlanarPosition) (r S : ℝ) :
    IsClosed (wellCoverBox u r S) :=
  isClosed_Icc.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))

theorem wellCoverBox_measure_ne_top (u : PlanarPosition) (r S : ℝ) :
    volume (wellCoverBox u r S) ≠ ⊤ := by
  unfold wellCoverBox
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_ne_top

theorem wellCoverBox_volume (u : PlanarPosition) {r S : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) :
    volume.real (wellCoverBox u r S) = 8*r^2*S := by
  unfold wellCoverBox Measure.real
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet]
  rw [Real.volume_Icc_pi_toReal (by intro i; fin_cases i <;> simp <;> linarith)]
  simp [Fin.prod_univ_succ]
  ring

theorem manufacturedWellField_support_cover (freq scale : ℝ) {S : ℝ} (hS : 0 < S)
    {m : ℕ} (u : Fin m → PlanarPosition) :
    tsupport (manufacturedWellField freq scale S u) ⊆ ⋃ i, wellCoverBox (u i) 1 S := by
  apply closure_minimal _ (isClosed_iUnion_of_finite (fun i => wellCoverBox_isClosed (u i) 1 S))
  intro x hx
  have hz : |(positionSplitCoordinates x).2| < S := by
    by_contra hn
    exact hx (manufacturedWellField_outer freq scale hS u x (le_of_not_gt hn))
  have hnear : ∃ i, ‖(positionSplitCoordinates x).1-u i‖ < 1 := by
    by_contra hn
    apply hx
    unfold manufacturedWellField
    rw [countertermWellSum_zero_far freq scale u _ (fun i =>
      le_of_not_gt (fun hi => hn ⟨i,hi⟩)),mul_zero]
  obtain ⟨i,hi⟩ := hnear
  apply Set.mem_iUnion.mpr
  refine ⟨i,mem_wellCoverBox.mpr ⟨?_,?_,?_⟩⟩
  · simpa only [Real.norm_eq_abs,PiLp.sub_apply,positionSplitCoordinates_fst_zero] using
      (PiLp.norm_apply_le ((positionSplitCoordinates x).1-u i) 0).trans hi.le
  · simpa only [Real.norm_eq_abs,PiLp.sub_apply,positionSplitCoordinates_fst_one] using
      (PiLp.norm_apply_le ((positionSplitCoordinates x).1-u i) 1).trans hi.le
  · simpa only [positionSplitCoordinates_snd] using hz.le

theorem wellCover_volume_bound {m : ℕ} (u : Fin m → PlanarPosition)
    {r S : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) :
    volume.real (⋃ i, wellCoverBox (u i) r S) ≤ 8*m*r^2*S := by
  apply (measureReal_iUnion_fintype_le (fun i => wellCoverBox (u i) r S)).trans
  simp only [wellCoverBox_volume _ hr hS,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  apply le_of_eq
  ring

end ContinuumCoulomb

end

end OAI
