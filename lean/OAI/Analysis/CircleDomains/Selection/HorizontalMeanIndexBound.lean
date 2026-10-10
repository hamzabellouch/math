import OAI.Analysis.CircleDomains.Transfer.TransportedMeanIndex
import OAI.Analysis.CircleDomains.Sobolev.PlanarSliceIntegrals
import OAI.Analysis.CircleDomains.Sobolev.LipschitzIntervalPaths

namespace OAI

/-! On a physical horizontal segment, a local logarithmic lift of the
actual mean index is bounded by the original-law intersection count. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
 theorem pathImageCount_mono_set {S T : Set X} (h : S ⊆ T) (γ : C(PathTime, X)) :
    pathImageCount S γ ≤ pathImageCount T γ := by
  unfold pathImageCount
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z ∈ range γ ∩ S
  · simp only [hz, show z ∈ range γ ∩ T from ⟨hz.1, h hz.2⟩, ite_true, le_refl]
  · simp only [hz, ite_false, zero_le]

omit [BorelSpace C(PathTime, X)] in
 theorem meanIndex_horizontal_segment_bound
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (Q : C(ℂ, X)) (I J : Set ℝ)
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox I J))
    (hpos : ∀ z ∈ planarSliceBox I J, 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox I J, diskRayProjection (Ψ z) = F (Q z))
    (v : ℂ → ℝ) (hv : ∀ z (hz : z ∈ planarSliceBox I J),
      v z = meanGeometricIndex hsch K hKS (η.map f) ⟨Ψ z, hpos z hz⟩)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ Q '' planarSliceBox I J))
    (hinj : InjOn (F ∘ Q) (planarSliceBox I J))
    {x y s : ℝ} (hxy : x < y) (hI : Icc x y ⊆ I) (hs : s ∈ J) :
    ENNReal.ofReal |v ⟨y, s⟩ - v ⟨x, s⟩| ≤
      ∫⁻ γ : A, pathImageCount
        (Q '' (planarSliceBox (Icc x y) J ∩ Complex.im ⁻¹' {s})) γ.val ∂(η : Measure A) := by
  let β : C(PathTime, ℂ) := ⟨fun t => ⟨realIntervalPath x y t, s⟩,
    Complex.equivRealProdCLM.symm.continuous.comp
      ((realIntervalPath x y).continuous.prodMk continuous_const)⟩
  have hβ (t : PathTime) : β t ∈ planarSliceBox I J :=
    ⟨hI (realIntervalPath_mem hxy.le t), hs⟩
  let α := Q.comp β
  let δ : C(PathTime, ℂ) := ⟨Ψ ∘ β, hΨ.comp_continuous β.continuous hβ⟩
  have hδ (t : PathTime) : 0 ≤ (δ t).im := hpos (β t) (hβ t)
  have hδproj (t : PathTime) : diskRayProjection (δ t) = F (α t) :=
    hproj (β t) (hβ t)
  have hβinj : Injective β := by
    intro t u he
    exact (realIntervalPath_antilipschitz hxy.ne).injective (congrArg Complex.re he)
  have hδinj : Injective (diskRayProjection ∘ δ) := by
    intro t u he
    apply hβinj
    apply hinj (hβ t) (hβ u)
    exact (hδproj t).symm.trans (he.trans (hδproj u))
  have hα : range α ⊆ Q '' planarSliceBox I J := by
    rintro _ ⟨t, rfl⟩
    exact ⟨β t, hβ t, rfl⟩
  have hb := meanGeometricIndex_mapped_difference_le_intersections hsch hsep A K hK hKS η F f hf
    hmap α δ hδ hδproj hδinj (fun γ => (hF γ).mono (union_subset_union Subset.rfl hα))
  have hx : (⟨x, s⟩ : ℂ) ∈ planarSliceBox I J := ⟨hI ⟨le_rfl, hxy.le⟩, hs⟩
  have hy : (⟨y, s⟩ : ℂ) ∈ planarSliceBox I J := ⟨hI ⟨hxy.le, le_rfl⟩, hs⟩
  have h0 : δ 0 = Ψ ⟨x, s⟩ := by
    change Ψ ⟨realIntervalPath x y ⊥, s⟩ = _
    rw [realIntervalPath_zero]
  have h1 : δ 1 = Ψ ⟨y, s⟩ := by
    change Ψ ⟨realIntervalPath x y ⊤, s⟩ = _
    rw [realIntervalPath_one]
  have he0 : (⟨δ 0, hδ 0⟩ : ClosedUpperHalfPlane) = ⟨Ψ ⟨x, s⟩, hpos _ hx⟩ := Subtype.ext h0
  have he1 : (⟨δ 1, hδ 1⟩ : ClosedUpperHalfPlane) = ⟨Ψ ⟨y, s⟩, hpos _ hy⟩ := Subtype.ext h1
  rw [he0, he1, ← hv _ hx, ← hv _ hy] at hb
  apply hb.trans
  apply lintegral_mono
  intro γ
  apply pathImageCount_mono_set
  rintro _ ⟨t, rfl⟩
  exact ⟨β t, ⟨⟨realIntervalPath_mem hxy.le t, hs⟩, rfl⟩, rfl⟩

end CircleDomainRigidity

end

end OAI
