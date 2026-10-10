import OAI.Analysis.FactorGeneration.OperatorLimits
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! # Closed convex constraints on weak scalar limits

Separation retains closed convex conditions under a bounded Hilbert-space
weak limit. Applied in L2, this retains almost-everywhere disk and positivity
conditions for the scalar boundary averages.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

theorem mem_closed_convex_of_dual_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} {l : Filter ι} [l.NeBot] {C : Set E} (hC : IsClosed C)
    (hc : Convex ℝ C) (v : ι → E) (x : E) (hv : ∀ i, v i ∈ C)
    (ht : ∀ f : E →L[ℂ] ℂ, Tendsto (fun i => f (v i)) l (𝓝 (f x))) : x ∈ C := by
  by_contra hx
  obtain ⟨f, a, hf, hax⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hc hC hx
  have hr := (Complex.continuous_re.tendsto _).comp (ht f)
  exact hax.not_ge (le_of_tendsto hr (Eventually.of_forall (fun i => (hf _ (hv i)).le)))

theorem dual_tendsto_of_inner_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} {l : Filter ι} (v : ι → H) (x : H)
    (ht : ∀ y, Tendsto (fun i => inner ℂ y (v i)) l (𝓝 (inner ℂ y x)))
    (f : H →L[ℂ] ℂ) : Tendsto (fun i => f (v i)) l (𝓝 (f x)) := by
  let y := (InnerProductSpace.toDual ℂ H).symm f
  have hy (z : H) : inner ℂ y z = f z := InnerProductSpace.toDual_symm_apply
  simpa only [hy] using ht y

theorem mem_closed_convex_of_inner_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} {l : Filter ι} [l.NeBot] {C : Set H} (hC : IsClosed C)
    (hc : Convex ℝ C) (v : ι → H) (x : H) (hv : ∀ i, v i ∈ C)
    (ht : ∀ y, Tendsto (fun i => inner ℂ y (v i)) l (𝓝 (inner ℂ y x))) : x ∈ C := by
  by_contra hx
  obtain ⟨f, a, hf, hax⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hc hC hx
  let y := (InnerProductSpace.toDual ℂ H).symm f
  have hy (z : H) : inner ℂ y z = f z := InnerProductSpace.toDual_symm_apply
  have hr : Tendsto (fun i => (f (v i)).re) l (𝓝 (f x).re) := by
    simpa only [hy, Function.comp_def] using (Complex.continuous_re.tendsto _).comp (ht y)
  exact hax.not_ge (le_of_tendsto hr (Eventually.of_forall (fun i => (hf _ (hv i)).le)))

theorem mem_closed_convex_of_pair_inner_tendsto
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ι : Type*} {l : Filter ι} [l.NeBot] {C : Set (H × K)} (hC : IsClosed C)
    (hc : Convex ℝ C) (v : ι → H) (w : ι → K) (x : H) (y : K)
    (hv : ∀ i, (v i, w i) ∈ C)
    (ht : ∀ a, Tendsto (fun i => inner ℂ a (v i)) l (𝓝 (inner ℂ a x)))
    (hu : ∀ b, Tendsto (fun i => inner ℂ b (w i)) l (𝓝 (inner ℂ b y))) : (x, y) ∈ C := by
  apply mem_closed_convex_of_dual_tendsto (l := l) hC hc (fun i => (v i, w i)) (x, y) hv
  intro f
  have hs (a : H) (b : K) : f (a, b) =
      (f.comp (ContinuousLinearMap.inl ℂ H K)) a +
      (f.comp (ContinuousLinearMap.inr ℂ H K)) b := by
    change f (a, b) = f (a, 0) + f (0, b)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  simp_rw [hs]
  exact (dual_tendsto_of_inner_tendsto v x ht _).add
    (dual_tendsto_of_inner_tendsto w y hu _)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem isClosed_L2_ae_mem {C : Set ℂ} (hC : IsClosed C) :
    IsClosed {f : Lp ℂ 2 μ | ∀ᵐ x ∂μ, f x ∈ C} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  filter_upwards [ae_all_iff.mpr hf, hns] with x hx hlim
  exact hC.mem_of_tendsto hlim (Eventually.of_forall (fun n => hx (ns n)))

theorem convex_L2_ae_mem {C : Set ℂ} (hC : Convex ℝ C) :
    Convex ℝ {f : Lp ℂ 2 μ | ∀ᵐ x ∂μ, f x ∈ C} := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g),
    Lp.coeFn_smul a f, Lp.coeFn_smul b g] with x hfx hgx hs hfsm hgsm
  simp only [Pi.add_apply, Pi.smul_apply] at hs hfsm hgsm
  rw [hs, hfsm, hgsm]
  exact hC hfx hgx ha hb hab

theorem L2_ae_mem_of_inner_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {C : Set ℂ} (hC : IsClosed C) (hc : Convex ℝ C)
    (f : ι → Lp ℂ 2 μ) (g : Lp ℂ 2 μ) (hf : ∀ i, ∀ᵐ x ∂μ, f i x ∈ C)
    (ht : ∀ y, Tendsto (fun i => inner ℂ y (f i)) l (𝓝 (inner ℂ y g))) :
    ∀ᵐ x ∂μ, g x ∈ C :=
  mem_closed_convex_of_inner_tendsto (isClosed_L2_ae_mem hC) (convex_L2_ae_mem hc) f g hf ht

end

end KadisonKastler

end OAI
