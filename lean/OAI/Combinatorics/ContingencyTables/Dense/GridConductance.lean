import OAI.Combinatorics.ContingencyTables.Dense.GridMass

namespace OAI

/-!
# Conditional weighted grid-cut estimate

The finite-box Prékopa input is the only published hypothesis here. The
shell cover, tube volume, integral cover, and discrete/continuous mass
comparison yield the discrete cut estimate.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

/-- The actual weighted cut bound before the proposal probability is
inserted. The selected side is the smaller continuous side; the conclusion
uses its own discrete weight and therefore also bounds the smaller discrete
side without identifying the two notions of smaller side. -/
theorem weighted_cut_of_interpolation {q K : ℕ}
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (P : (Fin q → ℤ) → Prop) (t : ℝ) (ht : 0 < t) (ht₁ : t < 1)
    (hr : t * K ≤ 1 / 4) (hsize : (q - 1 : ℕ) * (2 * (t * K)) ≤ (1 / 2 : ℝ))
    (ρ : (Fin q → ℝ) → ℝ) (w : Grid (I := Fin q) K → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hρ : ContinuousOn ρ (ambientBox q K))
    (hpos : ∀ x ∈ ambientBox q K, 0 < ρ x)
    (hlc : PublishedInputs.LogConcaveOn ρ (ambientBox q K))
    (hbin : ∀ a x, x ∈ binSet a → w a / 4 ≤ ρ x)
    (htube : ∀ (e : CutEdge K P) x, x ∈ edgeTube e (t * K) ∩ {x | Cube K x} →
      ρ x ≤ 4 * min (w e.val.1) (w e.val.2.1))
    (hSmass : 0 < ∫ x in selectedBins K P, ρ x)
    (hcut : 2 * (∫ x in selectedBins K P, ρ x) ≤ ∫ x in {x | Cube K x}, ρ x) :
    (((2 : ℝ) ^ t - 1) / 16) * (∑ a : Selected K P, w a.val) ≤
      ∑ e : CutEdge K P, min (w e.val.1) (w e.val.2.1) := by
  let S := selectedBins K P
  let D := {x : Fin q → ℝ | Cube K x}
  let M := PublishedInputs.interpolate t S D
  let E : CutEdge K P → Set (Fin q → ℝ) := fun e => edgeTube e (t * K) ∩ D
  have hS := selectedBins_finiteBox (K := K) P
  have hD := cube_finiteBox (q := q) (K := K)
  have hM := hS.interpolate hD t ht ht₁
  have hMsub : M ⊆ D := by
    rintro z ⟨x, ⟨a, _, hx⟩, y, hy, rfl⟩
    have hx' := openBin_in_cube a x hx
    intro j
    have hxt := mul_pos (sub_pos.mpr ht₁) (hx' j).1
    have hyt := mul_pos ht (hy j).1
    have hxu := mul_lt_mul_of_pos_left (hx' j).2 (sub_pos.mpr ht₁)
    have hyu := mul_lt_mul_of_pos_left (hy j).2 ht
    change 0 < (1 - t) * x j + t * y j ∧ (1 - t) * x j + t * y j < (K : ℝ)
    constructor <;> nlinarith
  have hsub : S ⊆ M := by
    rintro x hx
    refine ⟨x, hx, x, ?_, ?_⟩
    · obtain ⟨a, _, ha⟩ := hx
      exact openBin_in_cube a x ha
    · ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hi : IntegrableOn ρ (ambientBox q K) := hρ.integrableOn_Icc
  have hMc : closure M ⊆ ambientBox q K :=
    PublishedInputs.interpolation_closure_in_box
      (selectedBins_closure P) cube_closure t ht.le ht₁.le
  have hiShell : IntegrableOn ρ (M \ S) := hi.mono_set
    (fun x hx => hMc (subset_closure hx.1))
  have hcover : ∀ᵐ x ∂volume, x ∈ M \ S → ∃ e, x ∈ E e := by
    have hc := interpolation_shell_cover_ae P t ht ht₁ (show t * K ≤ 1 by linarith)
    filter_upwards [hc] with x hx
    intro hxS
    obtain ⟨e, he⟩ := hx hxS
    exact ⟨e, he, hMsub hxS.1⟩
  have hESub (e : CutEdge K P) : E e ⊆ ambientBox q K :=
    fun x hx => ⟨fun j => (hx.2 j).1.le, fun j => (hx.2 j).2.le⟩
  have hEm (e : CutEdge K P) : MeasurableSet (E e) :=
    (faceTube_measurable _ _ _).inter hD.isOpen.measurableSet
  have hcoverInt := ContingencyTables.integral_finite_cover (M \ S) E ρ
    (hM.isOpen.measurableSet.diff hS.isOpen.measurableSet) hEm hiShell
    (fun e => hi.mono_set (hESub e))
    (fun e x hx => (hpos x (hESub e hx)).le) hcover
  have hr₀ : 0 ≤ t * (K : ℝ) := mul_nonneg ht.le (Nat.cast_nonneg _)
  have hupper : (∫ x in M \ S, ρ x) ≤
      4 * ∑ e : CutEdge K P, min (w e.val.1) (w e.val.2.1) := by
    calc
      _ ≤ ∑ e : CutEdge K P, ∫ x in E e, ρ x := hcoverInt
      _ ≤ ∑ e : CutEdge K P, 4 * min (w e.val.1) (w e.val.2.1) := by
        apply Finset.sum_le_sum
        intro e _
        exact edgeTube_mass_upper P e (t * K) hr₀ hr hsize ρ w hw hi (htube e)
      _ = _ := by rw [Finset.mul_sum]
  have hgain := PublishedInputs.interpolation_shell_gain hPL t ht ht₁
    (fun _ => 0) (fun _ => (K : ℝ)) S D ρ hS hD
    (selectedBins_closure P) cube_closure hρ hpos hlc hsub hSmass hcut
  have hlower := selectedBins_mass_lower P ρ w hi hbin
  have hg : 0 ≤ (2 : ℝ) ^ t - 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ht.le
    exact sub_nonneg.mpr (by simpa using h)
  have hscaled := mul_le_mul_of_nonneg_left hlower hg
  dsimp only [S, D, M] at hupper hgain
  nlinarith

end ContingencyTables.GridBoundary

end OAI
