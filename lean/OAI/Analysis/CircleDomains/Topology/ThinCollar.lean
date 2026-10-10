import OAI.Analysis.CircleDomains.Transfer.ReciprocalGridSelection
import OAI.Analysis.CircleDomains.Topology.CollarExtension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-!
# Interpolation in a thin exterior neighborhood

For a compact retained core, integrals over shrinking exterior neighborhoods
tend to zero. A continuous family of energy densities can consequently be
interpolated smoothly to its original value near the core with arbitrarily
small added energy. No measure-zero assumption on the core boundary is used.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem reciprocalGridStep_antitone : Antitone reciprocalGridStep := by
  intro m n hmn
  unfold reciprocalGridStep
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hmn 1

theorem iInter_outer_thickenings_eq_empty
    {E : Type*} [MetricSpace E] {K : Set E} (hK : IsClosed K) :
    (⋂ n : ℕ, thickening (reciprocalGridStep n) K \ K) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' := mem_iInter.mp hx
  have hxK : x ∈ closure K := by
    rw [closure_eq_iInter_thickening]
    apply mem_iInter₂.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := (reciprocalGridStep_tendsto_zero.eventually
      (gt_mem_nhds hε)).exists
    exact thickening_mono hn.le K (hx' n).1
  exact (hx' 0).2 (hK.closure_eq ▸ hxK)

theorem tendsto_integral_outer_thickenings
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {K : Set E} (hK : IsClosed K)
    {f : E → ℝ} (hf : IntegrableOn f (thickening 1 K) μ) :
    Tendsto (fun n => ∫ x in thickening (reciprocalGridStep n) K \ K, f x ∂μ)
      atTop (𝓝 0) := by
  have ht := tendsto_setIntegral_of_antitone
    (fun n : ℕ => isOpen_thickening.measurableSet.diff hK.measurableSet)
    (fun m n hmn => sdiff_subset_sdiff_left (thickening_mono
      (reciprocalGridStep_antitone hmn) K))
    (f := f) (μ := μ) ⟨0, by
      simpa only [reciprocalGridStep, Nat.cast_zero, zero_add, div_one]
        using hf.mono_set sdiff_subset⟩
  simpa only [iInter_outer_thickenings_eq_empty hK, setIntegral_empty] using ht

/-- Smoothly select the original member `H (x,0)` near the retained core,
and the new member `H (x,1)` away from a small neighborhood. The absolute
change of its integral outside the core is arbitrarily small. -/
theorem exists_smooth_interpolation_small_change
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {K S U : Set E} (hK : IsCompact K) (hS : Bornology.IsBounded S)
    (hSm : MeasurableSet S) (hU : IsOpen U) (hKU : K ⊆ U)
    (H : E × ℝ → ℝ) (hH : ContinuousOn H (univ ×ˢ Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : Set E) (χ : E → ℝ), IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧
      ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc 0 1) ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 0) ∧ (∀ x ∉ N, χ x = 1) ∧
      (∫ x in S \ K, |H (x, χ x) - H (x, 1)| ∂μ) < ε := by
  have hbox := hK.cthickening (r := 1)
  have hprod : IsCompact (cthickening 1 K ×ˢ Icc (0 : ℝ) 1) := hbox.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hprod.exists_bound_of_continuousOn
    (hH.mono (prod_mono (subset_univ _) Subset.rfl))
  let C : ℝ := 2 * max B 0
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (le_max_right _ _)
  have hbound {x : E} (hx : x ∈ cthickening 1 K) {t : ℝ} (ht : t ∈ Icc 0 1) :
      |H (x,t) - H (x,1)| ≤ C := by
    calc
      |H (x,t) - H (x,1)| ≤ |H (x,t)| + |H (x,1)| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB _ ⟨hx, ht⟩) (hB _ ⟨hx, by norm_num⟩)
      _ ≤ C := by dsimp [C]; linarith [le_max_left B 0]
  have hCi : IntegrableOn (fun _ : E => C) (thickening 1 K) μ :=
    (continuous_const.continuousOn.integrableOn_compact hbox).mono_set
      (thickening_subset_cthickening 1 K)
  have hsmall := (tendsto_integral_outer_thickenings hK.isClosed hCi).eventually
    (gt_mem_nhds hε)
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hthin := reciprocalGridStep_tendsto_zero.eventually (gt_mem_nhds hr)
  obtain ⟨n, hnsmall, hnthin⟩ := (hsmall.and hthin).exists
  let N := thickening (reciprocalGridStep n) K
  have hN : IsOpen N := isOpen_thickening
  have hKN : K ⊆ N := self_subset_thickening (reciprocalGridStep_pos n) K
  have hNU : N ⊆ U := (thickening_subset_cthickening _ K).trans
    ((cthickening_mono hnthin.le K).trans hrU)
  obtain ⟨χ, hzero, hone, hχrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hK.isClosed hN.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hKN) (n := (⊤ : ℕ∞))
  have hχ : ContDiff ℝ ∞ (χ : E → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  have hχone : ∀ x ∉ N, χ x = 1 := fun x hx => hone.self_of_nhdsSet x hx
  have h1 : Continuous (fun x : E => H (x,1)) :=
    hH.comp_continuous (by fun_prop) (by intro x; exact ⟨mem_univ x, by norm_num⟩)
  have hc : Continuous (fun x : E => H (x,χ x)) :=
    hH.comp_continuous (continuous_id.prodMk hχ.continuous)
      (fun x => ⟨mem_univ x, hχrange x⟩)
  let g : E → ℝ := fun x => |H (x,χ x) - H (x,1)|
  have hgi : IntegrableOn g (S \ K) μ :=
    ((hc.sub h1).abs.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set
      (sdiff_subset.trans subset_closure)
  have hT : MeasurableSet (S \ K) := hSm.diff hK.isClosed.measurableSet
  have heq : (∫ x in S \ K, g x ∂μ) = ∫ x in (S \ K) ∩ N, g x ∂μ := by
    have hz : (∫ x in (S \ K) \ N, g x ∂μ) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      simp only [g, hχone x hx.2, sub_self, abs_zero]
    have hadd := integral_inter_add_sdiff hN.measurableSet hgi
    rw [hz, add_zero] at hadd
    exact hadd.symm
  have hCNi : IntegrableOn (fun _ : E => C) (N \ K) μ :=
    hCi.mono_set (sdiff_subset.trans (thickening_mono (reciprocalGridStep_le_one n) K))
  refine ⟨N, χ, hN, hKN, hNU, hχ, hχrange, hzero, hχone, ?_⟩
  change (∫ x in S \ K, g x ∂μ) < ε
  rw [heq]
  calc
    (∫ x in (S \ K) ∩ N, g x ∂μ) ≤ ∫ x in (S \ K) ∩ N, C ∂μ := by
      apply setIntegral_mono_on (hgi.mono_set inter_subset_left)
        (hCNi.mono_set (by intro x hx; exact ⟨hx.2, hx.1.2⟩))
        (hT.inter hN.measurableSet)
      intro x hx
      exact hbound ((thickening_subset_cthickening _ K
        ((thickening_mono (reciprocalGridStep_le_one n) K) hx.2))) (hχrange x)
    _ ≤ ∫ x in N \ K, C ∂μ :=
      setIntegral_mono_set hCNi (Eventually.of_forall (fun _ => hC))
        (Eventually.of_forall (fun _ hx => ⟨hx.2, hx.1.2⟩))
    _ < ε := hnsmall

end CircleDomainRigidity.FiniteTransfer

end

end OAI
