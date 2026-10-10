import OAI.Analysis.CircleDomains.Modulus.DisjointHolePayment
import OAI.Analysis.CircleDomains.Selection.ChordTolls
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-!
# Variation across the round holes met by one line

This derives the linewise payment directly from smoothness on the
complement of the actual disks and their cluster oscillations. No
endpoint extension or pre-existing line-payment hypothesis is assumed.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

def diskLineDomain {I : Type*} (c : I → ℂ) (r : I → ℝ) (y : ℝ) : Set ℝ :=
  {x | (⟨x, y⟩ : ℂ) ∈ (⋃ i, closedBall (c i) (r i))ᶜ}

theorem isOpen_diskLineDomain {I : Type*} [Finite I] (c : I → ℂ) (r : I → ℝ) (y : ℝ) :
    IsOpen (diskLineDomain c r y) := by
  have hc : Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ)) :=
    Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk continuous_const)
  exact (isClosed_iUnion_of_finite (fun i => isClosed_closedBall)).isOpen_compl.preimage hc

theorem line_payment_through_disks
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {y a b : ℝ} (hab : a < b)
    (ha : a ∈ diskLineDomain c r y) (hb : b ∈ diskLineDomain c r y)
    {f ρ : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (diskLineDomain c r y))
    (hzero : f a = 0) (hone : f b = 1)
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hmajor : ∀ x ∈ Icc a b ∩ diskLineDomain c r y, |deriv f x| ≤ ρ x)
    (hcluster : ∀ i p q u v,
      (⟨p, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      (⟨q, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[diskLineDomain c r y] p) f →
      MapClusterPt v (𝓝[diskLineDomain c r y] q) f → |v - u| ≤ A i) :
    1 ≤ (∫ x, ρ x) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
  classical
  let F := crossingChords c r y a b
  let E := Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ
  have hED : E ⊆ diskLineDomain c r y := by
    intro x hx
    exact (crossingChords_domain c r hr hx.1).mp hx.2
  have hD := isOpen_diskLineDomain c r y
  have hfa := hf.contDiffAt (hD.mem_nhds ha)
  have hfb := hf.contDiffAt (hD.mem_nhds hb)
  have hp := line_payment_of_disjoint_holes hab F
    (crossingChords_inside c r hr
      (fun i hi => ha (mem_iUnion.mpr ⟨i, hi⟩))
      (fun i hi => hb (mem_iUnion.mpr ⟨i, hi⟩)))
    (crossingChords_disjoint c r hr hdisj) (chordToll c r A y a b)
    (fun x hx => (hf.contDiffAt (hD.mem_nhds (hED hx))).differentiableAt (by norm_num) |>.hasDerivAt)
    ((hf.continuousOn_deriv_of_isOpen hD le_rfl).mono hED)
    hρ hpos (fun x hx => hmajor x ⟨hx.1, hED hx⟩)
    hfa.continuousAt hfb.continuousAt hzero hone (by
      intro z hz u v hu hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hy := crossingDisk_line_hit hi
      have hp := (mem_closedBall_iff_mem_horizontalChord (c i) (hr i) hy).mpr
        (left_mem_Icc.mpr (horizontalChord_valid _ _ _))
      have hq := (mem_closedBall_iff_mem_horizontalChord (c i) (hr i) hy).mpr
        (right_mem_Icc.mpr (horizontalChord_valid _ _ _))
      exact (hcluster i _ _ u v hp hq
        (hu.mono (nhdsWithin_mono _ hED))
        (hv.mono (nhdsWithin_mono _ hED))).trans (le_chordToll c r A y a b hA hi))
  exact hp.trans (add_le_add le_rfl (sum_chordToll_le_line_hits c r A y a b hA))

end CircleDomainRigidity

end OAI
