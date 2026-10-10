import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingInversePath
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! # The forced expanding-torus evolution in the interaction picture

The exact free inverse turns a mild solution with continuous forcing into
an ordinary Banach-valued primitive, without any extra spatial derivatives.
-/

open Set Filter Topology MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] expandingFreeInverse expandingInversePath expandingFreeStep
  expandingDuhamel

theorem expandingDuhamel_pullback (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (r : ℝ → FourierL2) (hr : Continuous r) (s : Icc (0 : ℝ) T) :
    let rC : C(Icc (0 : ℝ) T, FourierL2) := ⟨fun t => r t, hr.comp continuous_subtype_val⟩
    let R := expandingInversePath a b k L T ha hk hL rC
    expandingFreeInverse a b k L s ha hk hL s.2.1
      (expandingDuhamel a b k L ha hk hL s r) =
        ∫ τ in (0 : ℝ)..(s : ℝ), R (projIcc 0 T hT τ) := by
  intro rC R
  rw [expandingDuhamel_eq_intervalIntegral a b k L s ha hk hL s.2.1 r,
    ← (expandingFreeInverse a b k L s ha hk hL s.2.1).intervalIntegral_comp_comm
      ((continuousOn_expandingDuhamelIntegrand a b k L ha hk hL s r hr.continuousOn).intervalIntegrable_of_Icc s.2.1)]
  apply intervalIntegral.integral_congr
  intro τ hτ
  rw [uIcc_of_le s.2.1] at hτ
  dsimp only
  rw [expandingDuhamelIntegrand_of_mem a b k L ha hk hL s r τ hτ,
    expandingFreeInverse_after_kernel a b k L s τ ha hk hL hτ]
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans s.2.2⟩
  rw [projIcc_of_mem hT hτT]
  simp only [R, expandingInversePath_apply]
  rfl

theorem expandingMild_pullback (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (r : ℝ → FourierL2) (hr : Continuous r)
    (f : FourierL2)
    (hu : ∀ s : Icc (0 : ℝ) T, u s =
      expandingFreeStep a b k L s ha hk hL s.2.1 f +
        expandingDuhamel a b k L ha hk hL s r)
    (s : Icc (0 : ℝ) T) :
    let rC : C(Icc (0 : ℝ) T, FourierL2) := ⟨fun t => r t, hr.comp continuous_subtype_val⟩
    let R := expandingInversePath a b k L T ha hk hL rC
    expandingInversePath a b k L T ha hk hL u s =
      f + ∫ τ in (0 : ℝ)..(s : ℝ), R (projIcc 0 T hT τ) := by
  intro rC R
  rw [expandingInversePath_apply]
  rw [hu, map_add, expandingFreeInverse_left]
  exact congrArg (f + ·) (expandingDuhamel_pullback a b k L T ha hk hL hT r hr s)

theorem hasDerivAt_expandingMild_pullback (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (r : ℝ → FourierL2) (hr : Continuous r)
    (f : FourierL2)
    (hu : ∀ s : Icc (0 : ℝ) T, u s =
      expandingFreeStep a b k L s ha hk hL s.2.1 f +
        expandingDuhamel a b k L ha hk hL s r)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => expandingInversePath a b k L T ha hk hL u (projIcc 0 T hT s))
      (expandingFreeInverse a b k L t ha hk hL ht.1.le (r t)) t := by
  let rC : C(Icc (0 : ℝ) T, FourierL2) := ⟨fun t => r t, hr.comp continuous_subtype_val⟩
  let R := expandingInversePath a b k L T ha hk hL rC
  let Rext := fun τ => R (projIcc 0 T hT τ)
  have hR : Continuous Rext := R.continuous.comp continuous_projIcc
  have hd := (intervalIntegral.integral_hasDerivAt_right (hR.intervalIntegrable 0 t)
    hR.aestronglyMeasurable.stronglyMeasurableAtFilter (hR.continuousAt (x := t))).const_add f
  have he : (fun s => f + ∫ τ in (0 : ℝ)..s, Rext τ) =ᶠ[𝓝 t]
      (fun s => expandingInversePath a b k L T ha hk hL u (projIcc 0 T hT s)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    rw [projIcc_of_mem hT hsT]
    exact (expandingMild_pullback a b k L T ha hk hL hT u r hr f hu ⟨s, hsT⟩).symm
  apply (hd.congr_of_eventuallyEq he.symm).congr_deriv
  dsimp [Rext]
  rw [projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩]
  simp only [R, expandingInversePath_apply]
  rfl

end DefocusingNLS

end OAI
