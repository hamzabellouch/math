import Mathlib
import OAI.Geometry.PrescribedPotential.ChartTransportHigher
import OAI.Geometry.PrescribedPotential.GlobalExtension
import OAI.Geometry.PrescribedPotential.GlobalPartition

namespace OAI

/-! Global Transport. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff SchwartzMap Classical

namespace GlobalElliptic
open Anticanonical EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}

lemma localize_tsupport (i : Fin A.count) (ρ f : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) :
    tsupport (localize A i ρ hρ f : EC d → ℂ) ⊆
      (A.euclideanChart i) '' (tsupport (ρ : X → ℂ) ∩ tsupport (f : X → ℂ)) := by
  let e := A.euclideanChart i
  have hK : IsCompact (tsupport (ρ : X → ℂ) ∩ tsupport (f : X → ℂ)) :=
    (isClosed_tsupport _).isCompact.inter_right (isClosed_tsupport _)
  apply closure_minimal _ (hK.image_of_continuousOn (e.continuousOn.mono
    (fun x hx => hρ hx.1))).isClosed
  intro y hy
  have hn : localize A i ρ hρ f y ≠ 0 := hy
  by_cases ht : y ∈ e.target
  · rw [localize_apply, localizeFun_apply A ρ f ht] at hn
    exact ⟨e.symm y, ⟨subset_tsupport _ (left_ne_zero_of_mul hn),
      subset_tsupport _ (right_ne_zero_of_mul hn)⟩, e.right_inv ht⟩
  · exact (hn (ite_eq_right ht)).elim

def cutoffGlobal (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target) : Smooth A :=
  extend i κ.val (κ.val.smooth ⊤) κ.compact κ.support_sub

omit [CompactSpace X] in
lemma cutoffGlobal_tsupport (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target) :
    tsupport (cutoffGlobal i κ : X → ℂ) ⊆
      (A.euclideanChart i).symm '' tsupport (κ : EC d → ℂ) :=
  extend_tsupport i κ.val (κ.val.smooth ⊤) κ.compact κ.support_sub

 
def overlapCutoff (i j : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target)
    (ρ : Smooth A) (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart j).source) :
    ChartCutoff ((A.euclideanChart j).symm.trans (A.euclideanChart i)).source where
  val := localize A j ρ hρ (cutoffGlobal i κ)
  compact := (localizeFun_smooth_compact A j ρ _ hρ).2
  support_sub := by
    intro y hy
    obtain ⟨x, ⟨hxρ, hxf⟩, rfl⟩ := localize_tsupport j ρ _ hρ hy
    have hxj := hρ hxρ
    have hxi : x ∈ (A.euclideanChart i).source := by
      obtain ⟨z, hz, rfl⟩ := cutoffGlobal_tsupport i κ hxf
      exact (A.euclideanChart i).symm.mapsTo (κ.support_sub hz)
    refine ⟨(A.euclideanChart j).mapsTo hxj, ?_⟩
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage,
      (A.euclideanChart j).left_inv hxj] using hxi

@[simp] lemma overlapCutoff_apply (i j : Fin A.count)
    (κ : ChartCutoff (A.euclideanChart i).target) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart j).source) (y : EC d) :
    overlapCutoff i j κ ρ hρ y = if y ∈ (A.euclideanChart j).target then
      ρ ((A.euclideanChart j).symm y) *
        (if (A.euclideanChart j).symm y ∈ (A.euclideanChart i).source then
          κ (A.euclideanChart i ((A.euclideanChart j).symm y)) else 0) else 0 := rfl

lemma localize_globalize (i j : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target)
    (ρ : Smooth A) (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart j).source)
    (f : 𝓢(EC d, ℂ)) :
    localize A j ρ hρ (globalize i κ f) =
      chartTransport ((A.euclideanChart j).symm.trans (A.euclideanChart i))
        (A.euclidean_transition_smooth j i) (overlapCutoff i j κ ρ hρ) f := by
  ext y
  simp only [localize_apply, localizeFun, globalize_apply, chartTransport_apply,
    overlapCutoff_apply, OpenPartialHomeomorph.trans_apply]
  split_ifs <;> simp_all only [mul_zero, zero_mul, mul_assoc]

 

theorem globalize_even_bound {ι : Type*} [Fintype ι] (D : Localizers A ι)
    (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(EC d, ℂ),
      ‖D.embed (2 * (k : ℝ)) (globalize i κ f)‖ ≤ C * ‖schwartzCoord (2 * (k : ℝ)) f‖ := by
  have hB (j : ι) : CoreBound (2 * (k : ℝ)) (2 * (k : ℝ))
      (fun f => localize A (D.index j) (D.weight j) (D.support_sub j) (globalize i κ f)) := by
    simp_rw [localize_globalize]
    exact chartTransport_even_bound _ (A.euclidean_transition_smooth (D.index j) i)
      (A.euclidean_transition_smooth i (D.index j)) _ k
  choose C hC h using hB
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun f => ?_⟩
  change ‖D.coordinates (2 * (k : ℝ)) (globalize i κ f)‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg (fun j _ => hC j)) (norm_nonneg _))).mpr
  intro j
  exact (h j f).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ j)) (norm_nonneg _))

end GlobalElliptic

end
end

end OAI
