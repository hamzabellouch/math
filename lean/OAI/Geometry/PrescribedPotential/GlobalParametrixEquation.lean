import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalParametrix
import OAI.Geometry.PrescribedPotential.PatchDifferential

namespace OAI

/-! Global Parametrix Equation. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap ContDiff Classical ComplexOrder MatrixOrder

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
  {A : ComplexAtlas d X}

lemma globalize_local (i : Fin A.count)
    (κ : ChartCutoff (A.euclideanChart i).target) (u : 𝓢(EC d, ℂ))
    {y : EC d} (hy : y ∈ (A.euclideanChart i).target) :
    (globalize i κ u ∘ (A.euclideanChart i).symm) =ᶠ[𝓝 y]
      (SchwartzMap.smulLeftCLM ℂ κ.val u : EC d → ℂ) := by
  filter_upwards [(A.euclideanChart i).open_target.mem_nhds hy] with z hz
  have hs : (A.euclideanChart i).symm z ∈ (A.euclideanChart i).source :=
    (A.euclideanChart i).map_target hz
  simp only [Function.comp_apply, globalize_apply, ite_eq_left hs,
    (A.euclideanChart i).right_inv hz,
    SchwartzMap.smulLeftCLM_apply_apply κ.val.hasTemperateGrowth, smul_eq_mul]

lemma globalize_absorb (i : Fin A.count)
    (κ η : ChartCutoff (A.euclideanChart i).target)
    (hη : ∀ y ∈ tsupport (κ : EC d → ℂ), η y = 1) (u : 𝓢(EC d, ℂ)) :
    globalize i η (SchwartzMap.smulLeftCLM ℂ κ.val u) = globalize i κ u := by
  apply Smooth.ext
  intro x
  simp only [globalize_apply, SchwartzMap.smulLeftCLM_apply_apply κ.val.hasTemperateGrowth,
    smul_eq_mul]
  split_ifs with hx
  · by_cases hy : A.euclideanChart i x ∈ tsupport (κ : EC d → ℂ)
    · rw [hη _ hy, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, mul_zero]
  · rfl

lemma complexL_globalize {g : KaehlerMetric A} (p : ParametrixPatch g)
    (κ η : ChartCutoff (A.euclideanChart p.index).target)
    (hκ : tsupport (κ : EC d → ℂ) ⊆ p.domain)
    (hη : ∀ y ∈ tsupport (κ : EC d → ℂ), η y = 1) (u : 𝓢(EC d, ℂ)) :
    complexL g (globalize p.index κ u) =
      globalize p.index η (p.differential (SchwartzMap.smulLeftCLM ℂ κ.val u)) := by
  apply Smooth.ext
  intro x
  let e := A.euclideanChart p.index
  have hDs : tsupport (p.differential (SchwartzMap.smulLeftCLM ℂ κ.val u) : EC d → ℂ) ⊆
      tsupport (κ : EC d → ℂ) :=
    (schwartzDifferential_tsupport _ _).trans
      ((SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans inter_subset_right)
  by_cases hx : x ∈ e.symm '' tsupport (κ : EC d → ℂ)
  · obtain ⟨y, hy, rfl⟩ := hx
    have hys := κ.support_sub hy
    have hsrc : e.symm y ∈ (A.euclideanChart p.index).source := e.map_target hys
    change complexLValue g _ _ = _
    rw [complexLValue_local g _ p.index hsrc]
    change localL g p.index _ (e (e.symm y)) = _
    rw [e.right_inv hys,
      localL_congr g p.index (globalize_local p.index κ u hys),
      ← p.differential_local _ (hκ hy), globalize_apply, ite_eq_left hsrc, e.right_inv hys,
      hη y hy, one_mul]
  · have hv : complexL g (globalize p.index κ u) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hx
        (globalize_tsupport p.index κ u (complexL_tsupport g _ ht)))
    rw [hv, globalize_apply]
    split_ifs with hi
    · have hn : e x ∉ tsupport (κ : EC d → ℂ) := fun hy => hx ⟨e x, hy, e.left_inv hi⟩
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hn (hDs ht)), mul_zero]
    · rfl

omit [T2Space X] in
lemma local_shift_cutoff_equation {g : KaehlerMetric A} (p : ParametrixPatch g)
    (m : ℝ) (hm : 1 ≤ m) (κ f : 𝓢(EC d, ℂ)) :
    (m^2 : ℝ) • SchwartzMap.smulLeftCLM ℂ κ (p.localInverse m hm f) -
      p.differential (SchwartzMap.smulLeftCLM ℂ κ (p.localInverse m hm f)) =
      SchwartzMap.smulLeftCLM ℂ κ f - p.cutoffError κ (p.localInverse m hm f) := by
  have he := congrArg (SchwartzMap.smulLeftCLM ℂ κ) (p.localInverse_equation m hm f)
  simp only [map_sub, map_smul] at he
  rw [← he]
  simp only [ParametrixPatch.cutoffError, schwartzCutoffError,
    _root_.sub_apply, ContinuousLinearMap.comp_apply]
  rw [← Complex.ofReal_pow, Complex.coe_smul]
  simp only [ParametrixPatch.differential]
  abel

lemma global_shift_piece_equation {g : KaehlerMetric A} (p : ParametrixPatch g)
    (κ η : ChartCutoff (A.euclideanChart p.index).target)
    (hκ : tsupport (κ : EC d → ℂ) ⊆ p.domain)
    (hη : ∀ y ∈ tsupport (κ : EC d → ℂ), η y = 1)
    (m : ℝ) (hm : 1 ≤ m) (f : 𝓢(EC d, ℂ)) :
    (m^2 : ℝ) • globalize p.index κ (p.localInverse m hm f) -
      complexL g (globalize p.index κ (p.localInverse m hm f)) =
      globalize p.index κ f - globalize p.index η (p.cutoffError κ.val (p.localInverse m hm f)) := by
  have hh := congrArg (globalize p.index η) (local_shift_cutoff_equation p m hm κ.val f)
  simp only [map_sub, map_smul, globalize_absorb p.index κ η hη] at hh
  rw [complexL_globalize p κ η hκ hη]
  exact hh

variable [CompactSpace X] {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def error (m : ℝ) (hm : 1 ≤ m) : Smooth A →ₗ[ℝ] Smooth A :=
  ∑ p, (globalize (D.patch p).index (D.outerCutoff p)).comp
    ((((D.patch p).cutoffError (D.cutoff p).val).restrictScalars ℝ).toLinearMap.comp
      (((D.patch p).localInverse m hm).comp (D.forcing p)))

lemma error_apply (m : ℝ) (hm : 1 ≤ m) (f : Smooth A) :
    D.error m hm f = ∑ p, globalize (D.patch p).index (D.outerCutoff p)
      ((D.patch p).cutoffError (D.cutoff p).val ((D.patch p).localInverse m hm (D.forcing p f))) := by
  simp only [error, LinearMap.sum_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe]
  rfl

 
theorem parametrix_equation (m : ℝ) (hm : 1 ≤ m) (f : Smooth A) :
    (m^2 : ℝ) • D.parametrix m hm f - complexL g (D.parametrix m hm f) =
      f - D.error m hm f := by
  rw [parametrix_apply, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  simp_rw [global_shift_piece_equation (D.patch _) (D.cutoff _) (D.outerCutoff _)
    (D.cutoff_support _) (D.outerCutoff_one _) m hm]
  rw [Finset.sum_sub_distrib, forcing_reconstruction, error_apply]

end GluingData
end GlobalElliptic

end
end

end OAI
