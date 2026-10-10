import OAI.Geometry.SurfaceImmersion.Whitney.FiniteCrosscapCleanup
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapGeometricCancellation

namespace OAI

/-! Reprepare the double points between genuine cancellations. The singular
set strictly decreases, while all remaining quadratic germs are retained. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem cancel_finite_quadratic_pair {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : QuadraticCrosscapGerms f) (p : M)
    (hp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)} ⊂
        {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)} ∧
      QuadraticCrosscapGerms g := by
  classical
  obtain ⟨F,hF,hI,hreg,hsimple,hrepF⟩ := clean_finite_quadratic_map hf hfin hrep
  have hfinF : {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F x)}.Finite :=
    hfin.subset (fun x hx => (hI x).not.mp hx)
  have hpF := (hI p).not.mpr hp
  obtain ⟨q,_hqp,_hqF,⟨A⟩⟩ := exists_crosscap_connecting_arc hF hfinF hreg hsimple hrepF p hpF
  obtain ⟨g,hg,hIg,hgerm⟩ := cancel_crosscap_pair hF A
  have hsub : {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)} ⊆
      {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)} := by
    intro x hx
    apply (hI x).not.mp
    intro hFx
    exact hx ((hIg x).mpr (Or.inr (Or.inr hFx)))
  have hpG : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p) :=
    (hIg p).mpr (Or.inl rfl)
  refine ⟨g,hg,Set.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩,?_⟩
  · intro he
    have hpin : p ∈ {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)} := by
      rw [he]
      exact hp
    exact hpin hpG
  · intro x hx
    have hFx : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F x) := by
      intro hi
      exact hx ((hIg x).mpr (Or.inr (Or.inr hi)))
    have hxp : x ≠ p := fun he => hx ((hIg x).mpr (Or.inl he))
    have hxq : x ≠ q := fun he => hx ((hIg x).mpr (Or.inr (Or.inl he)))
    obtain ⟨c,φ,b,t,hxc,hφ,he,hz,hR⟩ := hrepF x hFx
    exact ⟨c,φ,b,t,hxc,hφ,(hgerm x hFx hxp hxq).trans he,hz,hR⟩

theorem remove_finite_quadratic_crosscaps {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : QuadraticCrosscapGerms f) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) := by
  classical
  have h : ∀ n : ℕ, ∀ f : M → ProjectionTarget 3,
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f →
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite →
      QuadraticCrosscapGerms f →
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.ncard = n →
      ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
        ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf hfin hrep hn
      by_cases he : {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)} = ∅
      · refine ⟨f,hf,?_⟩
        intro x
        by_contra hx
        have : x ∈ (∅ : Set M) := by
          rw [←he]
          exact hx
        exact this.elim
      · obtain ⟨p,hp⟩ := Set.nonempty_iff_ne_empty.mpr he
        obtain ⟨g,hg,hsub,hrepG⟩ := cancel_finite_quadratic_pair hf hfin hrep p hp
        have hfinG := hfin.subset hsub.subset
        have hlt := Set.ncard_lt_ncard hsub hfin
        rw [hn] at hlt
        exact ih _ hlt g hg hfinG hrepG rfl
  exact h _ f hf hfin hrep rfl

/-- Whitney's compact surface immersion, with smoothness retained. -/
theorem smooth_three_space_immersion :
    ∃ f : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f ∧
      ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) := by
  obtain ⟨f,hf,hfin,hrep⟩ := exists_finite_quadratic_crosscap_map (M := M)
  exact remove_finite_quadratic_crosscaps hf hfin hrep

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
