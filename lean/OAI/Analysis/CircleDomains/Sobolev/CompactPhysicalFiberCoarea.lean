import OAI.Analysis.CircleDomains.Sobolev.CurveCoareaInput
import OAI.Analysis.CircleDomains.Topology.SubarcIntersectionCount
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Coarea for the actual distinct intersections of quotient arcs with
compact physical slices. Length is measured before the coordinate change. -/

open Set Function MeasureTheory
open scoped Topology ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
 theorem pathImageCount_image_le_hausdorffZero (π : ℂ → X) (A : Set ℂ)
    (γ : C(PathTime, X)) :
    pathImageCount (π '' A) γ ≤ (μH[0] : Measure ℂ) (A ∩ π ⁻¹' range γ) := by
  rw [pathImageCount_eq_iSup]
  apply iSup_le
  intro n
  split
  · rename_i hn
    obtain ⟨t, ht, hA⟩ := hn
    choose z hz he using hA
    have hzinj : Injective z := by
      intro i j hij
      apply ht
      change γ (t i) = γ (t j)
      rw [← he i, ← he j, hij]
    have hmem (i : Fin n) : z i ∈ A ∩ π ⁻¹' range γ :=
      ⟨hz i, ⟨t i, (he i).symm⟩⟩
    calc
      (n : ℝ≥0∞) = ∑' i : Fin n,
          if z i ∈ A ∩ π ⁻¹' range γ then (1 : ℝ≥0∞) else 0 := by simp [hmem]
      _ ≤ ∑' w : ℂ, if w ∈ A ∩ π ⁻¹' range γ then (1 : ℝ≥0∞) else 0 :=
        by
          simpa [mem_inter_iff] using ENNReal.tsum_comp_le_tsum_of_injective hzinj
            (fun w : ℂ => if w ∈ A ∩ π ⁻¹' range γ then (1 : ℝ≥0∞) else 0)
      _ ≤ _ := by
        simpa [mem_inter_iff] using
          cardinalitySum_le_hausdorffZero (A ∩ π ⁻¹' range γ)
  · exact bot_le

 theorem measurable_compactPhysicalFiberCount
    (π : ℂ → X) (hπ : Continuous π) {A : Set ℂ} (hA : IsCompact A)
    (f : ℂ → ℝ) (hf : Continuous f) (K : Set C(PathTime, X))
    (hK : ∀ γ ∈ K, Injective γ) :
    Measurable (fun p : K × ℝ => pathImageCount (π '' (A ∩ f ⁻¹' {p.2})) p.1.val) := by
  let H : Set (X × ℝ) := (fun z => (π z, f z)) '' A
  have hH : IsClosed H := (hA.image (hπ.prodMk hf)).isClosed
  let R : Set ((K × ℝ) × PathTime) :=
    {p | (p.1.1.val p.2, p.1.2) ∈ H}
  have hR : IsClosed R := hH.preimage
    ((continuous_eval.comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd)).prodMk
        (continuous_snd.comp continuous_fst))
  convert measurable_timeCount hR using 1
  funext p
  rw [pathImageCount_eq_timeCount_of_injective _ p.1.val (hK _ p.1.property)]
  apply tsum_congr
  intro t
  have heq : p.1.val t ∈ π '' (A ∩ f ⁻¹' {p.2}) ↔ ((p, t) ∈ R) := by
    change (∃ z, (z ∈ A ∧ f z ∈ ({p.2} : Set ℝ)) ∧ π z = p.1.val t) ↔
      ∃ z ∈ A, (π z, f z) = (p.1.val t, p.2)
    simp only [mem_singleton_iff, Prod.mk.injEq]
    aesop
  exact if_congr heq rfl rfl

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
 theorem compactPhysicalFiberCount_integral_le
    (hcoarea : PlanarLipschitzFiberCoarea)
    (π : ℂ → X) (hπ : Continuous π) {A : Set ℂ} (hA : IsCompact A)
    (γ : C(PathTime, X)) (L : ℝ≥0) (f : ℂ → ℝ) (hf : LipschitzWith L f)
    (hfin : (μH[1] : Measure ℂ) (A ∩ π ⁻¹' range γ) < ∞) :
    (∫⁻ y, pathImageCount (π '' (A ∩ f ⁻¹' {y})) γ) ≤
      (L : ℝ≥0∞) * (μH[1] : Measure ℂ) (A ∩ π ⁻¹' range γ) := by
  let E := A ∩ π ⁻¹' range γ
  have hE : IsCompact E := hA.inter_right ((isCompact_range γ.continuous).isClosed.preimage hπ)
  apply (lintegral_mono (fun y =>
    pathImageCount_image_le_hausdorffZero π (A ∩ f ⁻¹' {y}) γ)).trans
  convert (hcoarea E hE.measurableSet hfin L f hf).2 using 1
  congr 1
  funext y
  congr 1
  ext z
  simp only [E, mem_inter_iff, mem_preimage]
  tauto

 theorem mean_compactPhysicalFiberCount_integral_le
    (hcoarea : PlanarLipschitzFiberCoarea)
    (π : ℂ → X) (hπ : Continuous π) {A : Set ℂ} (hA : IsCompact A)
    (K : Set C(PathTime, X)) (hK : ∀ γ ∈ K, Injective γ)
    (η : Measure K) [SFinite η]
    (L : ℝ≥0) (f : ℂ → ℝ) (hf : LipschitzWith L f)
    (hfin : ∀ᵐ γ : K ∂η, (μH[1] : Measure ℂ) (A ∩ π ⁻¹' range γ.val) < ∞) :
    (∫⁻ y, ∫⁻ γ : K, pathImageCount (π '' (A ∩ f ⁻¹' {y})) γ.val ∂η) ≤
      (L : ℝ≥0∞) * ∫⁻ γ : K, (μH[1] : Measure ℂ) (A ∩ π ⁻¹' range γ.val) ∂η := by
  calc
    _ = ∫⁻ γ : K, ∫⁻ y, pathImageCount (π '' (A ∩ f ⁻¹' {y})) γ.val ∂volume ∂η := by
      apply lintegral_lintegral_swap
      exact ((measurable_compactPhysicalFiberCount π hπ hA f hf.continuous K hK).comp
        measurable_swap).aemeasurable
    _ ≤ ∫⁻ γ : K, (L : ℝ≥0∞) * (μH[1] : Measure ℂ) (A ∩ π ⁻¹' range γ.val) ∂η :=
      lintegral_mono_ae (hfin.mono fun γ hγ =>
        compactPhysicalFiberCount_integral_le hcoarea π hπ hA γ.val L f hf hγ)
    _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top

end CircleDomainRigidity

end

end OAI
