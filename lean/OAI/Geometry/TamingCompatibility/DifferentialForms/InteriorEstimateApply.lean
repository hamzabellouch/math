import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricSquareEstimate
import OAI.Geometry.TamingCompatibility.Elliptic.RawH1Bound

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Set
open scoped SchwartzMap
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma interior_estimate_apply (U : Set E) (n : ℕ) (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (χ : 𝓢(E,ℂ)) (T : localSolutionSpace U n P →L[ℂ] H E F ((n:ℝ)+2))
    (hT : ∀ w, toDistribution E F ((n:ℝ)+2) (T w) =
      smulLeftCLM F χ (toDistribution E F 1 w.val.1))
    (j : Z →L[ℝ] H E F 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Z) (f : H E F n),
      (∀ ψ : 𝓢(E,ℂ), HasCompactSupport (ψ : E → ℂ) → tsupport ψ ⊆ U →
        smulLeftCLM F ψ (P (toDistribution E F 1 (j u))) =
          smulLeftCLM F ψ (toDistribution E F n f)) →
      ∃ v : H E F ((n:ℝ)+2),
        toDistribution E F ((n:ℝ)+2) v = smulLeftCLM F χ (toDistribution E F 1 (j u)) ∧
        ‖v‖ ≤ C * (‖u‖+‖f‖) := by
  refine ⟨‖T‖ * max ‖j‖ 1,by positivity,fun u f heq => ?_⟩
  let w : localSolutionSpace U n P := ⟨(j u,f), (mem_localSolutionSpace_iff U n P (j u,f)).mpr heq⟩
  refine ⟨T w,hT w,?_⟩
  have hj := j.le_opNorm u
  have hju : ‖j u‖ ≤ max ‖j‖ 1 * (‖u‖+‖f‖) := by
    calc
      ‖j u‖ ≤ ‖j‖ * ‖u‖ := hj
      _ ≤ max ‖j‖ 1 * ‖u‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max ‖j‖ 1 * (‖u‖+‖f‖) := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (norm_nonneg _)) (le_trans (norm_nonneg j) (le_max_left ‖j‖ 1))
  have hf : ‖f‖ ≤ max ‖j‖ 1 * (‖u‖+‖f‖) := by
    calc
      ‖f‖ ≤ 1 * (‖u‖+‖f‖) := by nlinarith [norm_nonneg u]
      _ ≤ max ‖j‖ 1 * (‖u‖+‖f‖) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  calc
    ‖T w‖ ≤ ‖T‖ * ‖w‖ := T.le_opNorm w
    _ ≤ ‖T‖ * (max ‖j‖ 1 * (‖u‖+‖f‖)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
      change max ‖j u‖ ‖f‖ ≤ _
      exact max_le hju hf
    _ = _ := by ring

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma raw_uniform_estimate (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∀ (n : ℕ) (χ : 𝓢(Space,ℂ)), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
        (g : 𝓢(Space,EuclideanEnergy.Pair)),
        (∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
        (∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
          ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
        ∃ v : H Space (C 2) ((n:ℝ)+2),
          toDistribution Space (C 2) ((n:ℝ)+2) v =
            smulLeftCLM (C 2) χ (rawDistribution A J α hs ht D hD p τ u) ∧
          ‖v‖ ≤ K * (‖u‖+‖schwartzToH (n:ℝ) (SchwartzMap.postcompCLM (embed 2) g)‖) := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,a,b,ρ,ha,hb,hρ,hest⟩ :=
    exists_geometric_square_estimate A J α hs ht D p hU hUD q hq
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,fun n χ hc hχV => ?_⟩
  obtain ⟨T,hT⟩ := hest n χ hc hχV
  obtain ⟨K,hK,hbound⟩ := interior_estimate_apply W n (square EuclideanEnergy.e a b ρ) χ T hT
    (rawH1 A J α hs ht D hD p τ)
  refine ⟨K,hK,fun f u g hg heq => ?_⟩
  have he : ∀ ψ : 𝓢(Space,ℂ), HasCompactSupport (ψ : Space → ℂ) → tsupport ψ ⊆ W →
      smulLeftCLM (C 2) ψ (square EuclideanEnergy.e a b ρ
        (toDistribution Space (C 2) 1 (rawH1 A J α hs ht D hD p τ u))) =
      smulLeftCLM (C 2) ψ (toDistribution Space (C 2) n
        (schwartzToH n (SchwartzMap.postcompCLM (embed 2) g))) := by
    intro ψ hψ hψW
    rw [rawH1_spec,schwartzToH_spec]
    exact raw_square_source A J α hs ht D hD p τ hW (hWU.trans hUD)
      (fun z hz => hτ z (hWU hz)) a b ρ ha hb hρ f u heq g hg ψ hψ hψW
  have hb := hbound u (schwartzToH n (SchwartzMap.postcompCLM (embed 2) g))
  dsimp only [Space,EuclideanEnergy.V,ScalarPair.F,C] at hb he
  obtain ⟨v,hv,hvb⟩ := hb he
  rw [rawH1_spec] at hv
  exact ⟨v,hv,hvb⟩

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def localizedRawSchwartz (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (a : antiPre A J α hs ht) : 𝓢(Space,C 2) :=
  SchwartzMap.smulLeftCLM (C 2) χ (SchwartzMap.postcompCLM (embed 2)
    (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p a.val)))

omit [T2Space X] in
lemma localizedRawSchwartz_spec (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (a : antiPre A J α hs ht) :
    (localizedRawSchwartz A J α hs ht D hD p τ χ a : 𝓢'(Space,C 2)) =
      smulLeftCLM (C 2) χ (rawDistribution A J α hs ht D hD p τ
        (antiToEnergy A J α hs ht a)) := by
  rw [rawDistribution_smooth,product_schwartz]
  rfl

lemma raw_schwartz_estimate (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∀ (n : ℕ) (χ : 𝓢(Space,ℂ)), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair)),
        (∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
        (∀ v : antiEnergy A J α hs ht,
          ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
            ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
        ‖schwartzToH ((n:ℝ)+2) (localizedRawSchwartz A J α hs ht D hD p τ χ a)‖ ≤
          K * (‖antiToEnergy A J α hs ht a‖+‖schwartzToH (n:ℝ) (SchwartzMap.postcompCLM (embed 2) g)‖) := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,hest⟩ :=
    raw_uniform_estimate A J α hs ht D hD p τ hU hUD hτ q hq
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,fun n χ hc hχV => ?_⟩
  obtain ⟨K,hK,hbound⟩ := hest n χ hc hχV
  refine ⟨K,hK,fun f a g hg heq => ?_⟩
  obtain ⟨v,hv,hvb⟩ := hbound f (antiToEnergy A J α hs ht a) g hg heq
  have he : schwartzToH ((n:ℝ)+2) (localizedRawSchwartz A J α hs ht D hD p τ χ a) = v := by
    apply toDistribution_injective ((n:ℝ)+2)
    rw [schwartzToH_spec,localizedRawSchwartz_spec,hv]
  rw [he]
  exact hvb

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
