import OAI.Geometry.RCD.Transport.PairedBranchLaws
import OAI.Geometry.RCD.Transport.PairedEntropyChords
import OAI.Geometry.RCD.Transport.ResolvedSubplanEntropyBounds

namespace OAI

/-! # The quantitative entropy obstruction for an actual separated pair -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem paired_entropy_deficit (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ] (hσ : σ univ ≠ 0)
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π) (q s t : Time)
    (hs : 0 < s) (hst : s < t) (ht : t < 1)
    (hcommon : ∀ r : Time, r ≤ s →
      σ.map (fun z => z.1 r)=σ.map (fun z => resolvePathBranch q z r))
    (hsing : σ.map (fun z => z.1 t) ⟂ₘ σ.map (fun z => resolvePathBranch q z t)) :
    (s:ℝ)*(1-(s:ℝ))*Real.log 2 ≤ ((t:ℝ)-(s:ℝ))*
      (Real.log (2*(C:ℝ)/σ.real univ)+Real.log ((hausdorff n X).real (closedBall p (3*R)))+
        ((|K|/2)*(2*R)^2)*(s:ℝ)*(1-(s:ℝ))) := by
  let τ₀ := ((σ univ)⁻¹ • σ).map Prod.fst
  let τ₁ := ((σ univ)⁻¹ • σ).map (resolvePathBranch q)
  let τm := (2:ℝ≥0∞)⁻¹ • (τ₀+τ₁)
  let E₀ := fun u : Time => boltzmannEntropy (hausdorff n X) (τ₀.map (fun γ => γ u))
  let E₁ := fun u : Time => boltzmannEntropy (hausdorff n X) (τ₁.map (fun γ => γ u))
  let Em := fun u : Time => boltzmannEntropy (hausdorff n X) (τm.map (fun γ => γ u))
  let : NeZero σ := ⟨by intro he; apply hσ; rw [he]; rfl⟩
  let : IsProbabilityMeasure ((σ univ)⁻¹ • σ) := inferInstance
  let : IsProbabilityMeasure τ₀ := inferInstance
  let : IsProbabilityMeasure τ₁ := inferInstance
  have hmass : (σ.map diagonalFirst) univ=σ univ := by
    rw [Measure.map_apply measurable_diagonalFirst MeasurableSet.univ,preimage_univ]
  have hleft : (((σ.map diagonalFirst) univ)⁻¹ • σ.map diagonalFirst).map (resolvePathBranch q)=τ₀ := by
    rw [hmass,Measure.map_smul _ (measurable_resolvePathBranch q).aemeasurable,
      diagonalFirst_resolved]
    exact (Measure.map_smul _ measurable_fst.aemeasurable).symm
  have hld : (σ.map diagonalFirst).map Prod.fst ≤ π := by rwa [diagonalFirst_fst]
  have hrd : (σ.map diagonalFirst).map Prod.snd ≤ π := by rwa [diagonalFirst_snd]
  have hb₀ (u : Time) := hX.resolved_subplan_entropy_bounds p hR π hg hp hC hc hs₀ hs₁
    (σ.map diagonalFirst) (by rwa [hmass]) hld hrd q u
  simp only [hleft] at hb₀
  simp only [Measure.real,hmass] at hb₀
  have hb₁ (u : Time) := hX.resolved_subplan_entropy_bounds p hR π hg hp hC hc hs₀ hs₁ σ hσ hl hr q u
  have hequal (u : Time) (hu : u ≤ s) : τ₀.map (fun γ => γ u)=τ₁.map (fun γ => γ u) :=
    normalized_pair_eval_eq σ q u (hcommon u hu)
  have hem (u : Time) (hu : u ≤ s) : τm.map (fun γ => γ u)=τ₀.map (fun γ => γ u) :=
    half_mixture_eval_eq τ₀ τ₁ u (hequal u hu)
  have hc₀ : E₀ s=Em s := congrArg (boltzmannEntropy (hausdorff n X)) (hem s le_rfl).symm
  have hc₁ : E₁ s=Em s := by
    change boltzmannEntropy _ _=boltzmannEntropy _ _
    rw [hem s le_rfl,hequal s le_rfl]
  have ha₁ : τ₁.map (fun γ => γ t) ≪ hausdorff n X :=
    Measure.absolutelyContinuous_of_le_smul
      (normalized_resolved_compression (hausdorff n X) π σ hl hr hc q t)
  have ha₀ : τ₀.map (fun γ => γ t) ≪ hausdorff n X := by
    rw [←hleft]
    exact Measure.absolutelyContinuous_of_le_smul
      (normalized_resolved_compression (hausdorff n X) π (σ.map diagonalFirst) hld hrd hc q t)
  have hsep : Em t=(E₀ t+E₁ t)/2-Real.log 2 := by
    dsimp only [Em,E₀,E₁,τm]
    rw [half_mixture_map_eval]
    exact boltzmannEntropy_half_mixture (hausdorff n X) _ _ ha₀ ha₁
      (normalized_pair_eval_singular σ q t hsing) (hb₀ t).2.2 (hb₁ t).2.2
  obtain ⟨hch₀,hch₁,hchm⟩ := hX.paired_entropy_chords hn p hR π hg hp hc hs₀ hs₁ σ hσ hl hr q
  have hMm : Em 0 ≤ Real.log (2*(C:ℝ)/σ.real univ) := by
    dsimp only [Em]
    rw [hem 0 s.property.1]
    exact (hb₀ 0).2.1
  have hB : -Real.log ((hausdorff n X).real (closedBall p (3*R))) ≤ Em s := by
    rw [←hc₀]
    exact (hb₀ s).1
  have h := entropy_chord_branch_deficit hch₀ hch₁ hchm s t hs hst ht hc₀ hc₁ hsep
    (hb₀ 1).2.1 (hb₁ 1).2.1 hMm hB
  simpa only [Measure.real,sub_neg_eq_add] using h

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
