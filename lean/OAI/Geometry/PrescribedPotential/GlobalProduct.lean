import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalTransport
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.SobolevProduct

namespace OAI

/-! Global Product. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped SchwartzMap ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma localization_integer_bound (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Smooth A,
      ‖schwartzCoord (k : ℝ) (localize A i ρ hρ f)‖ ≤ C*‖D.localizers.embed (k : ℝ) f‖ := by
  have hb (p : ι) : CoreBound (k : ℝ) (k : ℝ) (fun v =>
      localize A i ρ hρ (globalize (D.patch p).index (D.cutoff p) v)) := by
    simp_rw [localize_globalize]
    exact chartTransport_integer_bound _ (A.euclidean_transition_smooth i (D.patch p).index)
      (A.euclidean_transition_smooth (D.patch p).index i) _ k
  choose C hC hc using hb
  refine ⟨∑ p, C p, Finset.sum_nonneg (fun p _ => hC p), fun f => ?_⟩
  have he : localize A i ρ hρ f = ∑ p, localize A i ρ hρ
      (globalize (D.patch p).index (D.cutoff p) (D.forcing p f)) := by
    change localizeLinear A i ρ hρ f = _
    conv_lhs => rw [← D.forcing_reconstruction f]
    rw [map_sum]
    rfl
  rw [he, schwartzCoord_sum, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p _
  exact (hc p (D.forcing p f)).trans
    (mul_le_mul_of_nonneg_left (D.forcing_bound p (k : ℝ) f) (hC p))

def outerWeight (p : ι) : Smooth A := cutoffGlobal (D.patch p).index (D.cutoff p)

omit [CompactSpace X] in
lemma outerWeight_support (p : ι) :
    tsupport (D.outerWeight p : X → ℂ) ⊆ (A.euclideanChart (D.patch p).index).source := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := cutoffGlobal_tsupport (D.patch p).index (D.cutoff p) hx
  exact (A.euclideanChart (D.patch p).index).symm.mapsTo ((D.cutoff p).support_sub hy)

lemma product_localization (p : ι) (f h : Smooth A) :
    D.forcing p (f.mul h) = SchwartzMap.smulLeftCLM ℂ (D.forcing p f)
      (localize A (D.patch p).index (D.outerWeight p) (D.outerWeight_support p) h) := by
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply (D.forcing p f).hasTemperateGrowth]
  change localizeFun A (D.localizers.index p) (D.localizers.weight p) (f.mul h) y =
    localizeFun A (D.localizers.index p) (D.localizers.weight p) f y *
      localizeFun A (D.patch p).index (D.outerWeight p) h y
  rw [D.index_eq]
  by_cases hy : y ∈ (A.euclideanChart (D.patch p).index).target
  · rw [localizeFun_apply A _ _ hy, localizeFun_apply A _ _ hy, localizeFun_apply A _ _ hy]
    by_cases hx : (A.euclideanChart (D.patch p).index).symm y ∈
        tsupport (D.localizers.weight p : X → ℂ)
    · have hw : D.outerWeight p ((A.euclideanChart (D.patch p).index).symm y) = 1 := by
        change (if (A.euclideanChart (D.patch p).index).symm y ∈
          (A.euclideanChart (D.patch p).index).source then _ else 0) = 1
        have hys : (A.euclideanChart (D.patch p).index).symm y ∈
            (A.euclideanChart (D.patch p).index).source :=
          (A.euclideanChart (D.patch p).index).symm.mapsTo hy
        rw [ite_eq_left hys]
        exact D.cutoff_one p _ hx
      rw [hw, one_mul]
      exact (mul_assoc _ _ _).symm
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  · simp only [localizeFun, ite_eq_right hy, zero_mul]

theorem smooth_product_bound (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : Smooth A,
      ‖D.localizers.embed (k : ℝ) (f.mul h)‖ ≤
        C*(‖D.localizers.embed (k : ℝ) f‖*‖D.localizers.embed (k : ℝ) h‖) := by
  obtain ⟨B,hB,hb⟩ := schwartz_sobolev_product_bound (E := EC d) k hk
  have hh (p : ι) := D.localization_integer_bound (D.patch p).index (D.outerWeight p)
    (D.outerWeight_support p) k
  choose C hC hc using hh
  refine ⟨B*∑ p, C p, mul_nonneg hB (Finset.sum_nonneg (fun p _ => hC p)), fun f h => ?_⟩
  change ‖D.localizers.coordinates (k : ℝ) (f.mul h)‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hB
    (Finset.sum_nonneg (fun p _ => hC p))) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr
  intro p
  change ‖schwartzCoord (k : ℝ) (D.forcing p (f.mul h))‖ ≤ _
  rw [D.product_localization]
  apply (hb (D.forcing p f) (localize A (D.patch p).index (D.outerWeight p)
    (D.outerWeight_support p) h)).trans
  calc
    _ ≤ B*(‖D.localizers.embed (k : ℝ) f‖*(C p*‖D.localizers.embed (k : ℝ) h‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (D.forcing_bound p (k : ℝ) f) (hc p h)
        (norm_nonneg _) (norm_nonneg _)) hB
    _ ≤ B*(‖D.localizers.embed (k : ℝ) f‖*((∑ q, C q)*‖D.localizers.embed (k : ℝ) h‖)) := by
      gcongr
      exact Finset.single_le_sum (fun q _ => hC q) (Finset.mem_univ p)
    _ = _ := by ring
end GluingData
end GlobalElliptic

end
end

end OAI
