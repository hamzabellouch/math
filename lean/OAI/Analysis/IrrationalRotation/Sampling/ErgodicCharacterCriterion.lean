import Mathlib

namespace OAI

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Invariant233.Characters

theorem integral_eq_zero_of_eigenfunction {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {σ : X → X} (hσ : MeasurePreserving σ μ μ)
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) {z : ℂ} (hz : z ≠ 1)
    (heigen : ∀ᵐ x ∂μ, f (σ x) = z * f x) :
    (∫ x, f x ∂μ) = 0 := by
  have hfm : AEStronglyMeasurable f (μ.map σ) := by rwa [hσ.map_eq]
  have hmap := integral_map hσ.measurable.aemeasurable hfm
  rw [hσ.map_eq] at hmap
  have heq : (∫ x, f x ∂μ) = z * ∫ x, f x ∂μ := by
    calc
      _ = ∫ x, f (σ x) ∂μ := hmap
      _ = ∫ x, z * f x ∂μ := integral_congr_ae heigen
      _ = _ := integral_const_mul z f
  have hzero : (1 - z) * (∫ x, f x ∂μ) = 0 := by
    calc
      _ = (∫ x, f x ∂μ) - z * (∫ x, f x ∂μ) := by ring
      _ = 0 := sub_eq_zero.mpr heq
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hz.symm)

theorem eq_zero_of_dense_inner {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : E) (χ : ι → E)
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hinner : ∀ i, inner ℂ v (χ i) = 0) : v = 0 := by
  let L : E →L[ℂ] ℂ := innerSL ℂ v
  have hspan : Submodule.span ℂ (Set.range χ) ≤ L.toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hinner i
  have htop := (Submodule.span ℂ (Set.range χ)).topologicalClosure_minimal
    hspan L.isClosed_ker
  rw [hdense] at htop
  have hv : L v = 0 := htop (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ E))
  exact inner_self_eq_zero.mp hv

theorem ergodic_of_dense_L2_eigenfunctions {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {σ : X → X}
    (hσ : MeasurePreserving σ μ μ) (i₀ : ι) (χ : ι → X → ℂ) (z : ι → ℂ)
    (hχ : ∀ i, MemLp (χ i) 2 μ)
    (hconst : χ i₀ =ᵐ[μ] fun _ => 1)
    (hdense : (Submodule.span ℂ
      (Set.range (fun i => (hχ i).toLp (χ i)))).topologicalClosure = ⊤)
    (hz : ∀ i, i ≠ i₀ → z i ≠ 1)
    (heigen : ∀ i, i ≠ i₀ → ∀ᵐ x ∂μ, χ i (σ x) = z i * χ i x) :
    Ergodic σ μ := by
  classical
  refine ⟨hσ, ⟨?_⟩⟩
  intro s hs hinv
  let p : ℝ := μ.real s
  let u : Lp ℂ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) 1
  let e : Lp ℂ 2 μ := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) 1
  have hσs : MeasurePreserving σ (μ.restrict s) (μ.restrict s) := by
    simpa only [hinv] using hσ.restrict_preimage hs
  have hpair : ∀ i,
      inner ℂ u ((hχ i).toLp (χ i)) = (p : ℂ) * inner ℂ e ((hχ i).toLp (χ i)) := by
    intro i
    have hfull : inner ℂ e ((hχ i).toLp (χ i)) = ∫ x, χ i x ∂μ := by
      rw [L2.inner_indicatorConstLp_one, setIntegral_univ]
      exact integral_congr_ae (hχ i).coeFn_toLp
    have hset : inner ℂ u ((hχ i).toLp (χ i)) = ∫ x in s, χ i x ∂μ := by
      rw [L2.inner_indicatorConstLp_one]
      exact integral_congr_ae ((hχ i).coeFn_toLp.filter_mono (ae_mono Measure.restrict_le_self))
    rw [hfull, hset]
    by_cases hi : i = i₀
    · subst i
      rw [integral_congr_ae hconst,
        integral_congr_ae (hconst.filter_mono (ae_mono Measure.restrict_le_self))]
      simp [p]
    · have hzero := integral_eq_zero_of_eigenfunction hσ (hχ i).aestronglyMeasurable
        (hz i hi) (heigen i hi)
      have hzeros := integral_eq_zero_of_eigenfunction hσs
        (hχ i).aestronglyMeasurable.restrict (hz i hi)
        ((heigen i hi).filter_mono (ae_mono Measure.restrict_le_self))
      rw [hzero, hzeros, mul_zero]
  have heq : u = (p : ℂ) • e := by
    apply sub_eq_zero.mp
    apply eq_zero_of_dense_inner (u - (p : ℂ) • e)
      (fun i => (hχ i).toLp (χ i)) hdense
    intro i
    rw [inner_sub_left, inner_smul_left, hpair i]
    simp
  have huu : inner ℂ u u = (p : ℂ) := by
    change inner ℂ (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ))
      (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)) = _
    rw [L2.inner_indicatorConstLp_indicatorConstLp]
    simp [p]
  have heu : inner ℂ e u = (p : ℂ) := by
    change inner ℂ (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℂ))
      (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)) = _
    rw [L2.inner_indicatorConstLp_indicatorConstLp]
    simp [p]
  have hpalg := congrArg (fun v : Lp ℂ 2 μ => inner ℂ v u) heq
  rw [huu, inner_smul_left, heu] at hpalg
  have hpalg' := congrArg Complex.re hpalg
  simp at hpalg'
  have hp01 : p = 0 ∨ p = 1 := by
    have hpzero : p * (p - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hpzero with hp | hp
    · exact Or.inl hp
    · exact Or.inr (sub_eq_zero.mp hp)
  apply eventuallyEmptyOrUniv_iff.mpr
  rcases hp01 with hp | hp
  · right
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using (measureReal_eq_zero_iff (μ := μ)).mp hp
  · left
    rw [ae_iff]
    have hpc : μ.real sᶜ = 0 := by rw [measureReal_compl hs, probReal_univ]; exact sub_eq_zero.mpr hp.symm
    exact (measureReal_eq_zero_iff (μ := μ)).mp hpc

theorem ergodic_of_dense_continuous_eigenfunctions {X ι : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]
    {σ : X → X} (hσ : MeasurePreserving σ μ μ)
    (i₀ : ι) (χ : ι → C(X, ℂ)) (z : ι → ℂ)
    (hconst : χ i₀ = 1)
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hz : ∀ i, i ≠ i₀ → z i ≠ 1)
    (heigen : ∀ i, i ≠ i₀ → ∀ x, χ i (σ x) = z i * χ i x) :
    Ergodic σ μ := by
  let hχ : ∀ i, MemLp (χ i) 2 μ := fun i => ContinuousMap.memLp μ ℂ (χ i)
  have hlp : (fun i => (hχ i).toLp (χ i)) =
      (fun i => ContinuousMap.toLp 2 μ ℂ (χ i)) := by
    funext i
    apply Lp.ext
    exact (hχ i).coeFn_toLp.trans (ContinuousMap.coeFn_toLp μ (χ i)).symm
  have hdenseLp : (Submodule.span ℂ
      (Set.range (fun i => (hχ i).toLp (χ i)))).topologicalClosure = ⊤ := by
    rw [hlp]
    have hd := (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).topologicalClosure_map_submodule hdense
    rw [Submodule.map_span, ← Set.range_comp'] at hd
    exact hd
  refine ergodic_of_dense_L2_eigenfunctions hσ i₀ (fun i => χ i) z hχ ?_ hdenseLp hz ?_
  · exact Eventually.of_forall fun x => by rw [hconst]; rfl
  · intro i hi
    exact Eventually.of_forall (heigen i hi)

end Invariant233.Characters

end OAI
