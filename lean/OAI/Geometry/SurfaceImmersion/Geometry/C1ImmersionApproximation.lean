import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionJets

namespace OAI

/-! Smoothing a compact C1 immersion while keeping its differential injective. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def coreThreshold : ℝ := 1 / ((Fintype.card A.centers : ℝ)+1)
def weightCore (i : A.centers) : Set M := {p | A.coreThreshold ≤ (A.weight i p)^2}
def coordinateCore (i : A.centers) : Set Base := (chart (i : M)) '' A.weightCore i

omit [CompactSpace M] in
lemma coreThreshold_pos : 0 < A.coreThreshold := by unfold coreThreshold; positivity

omit [CompactSpace M] in
lemma weightCore_nonzero (i : A.centers) {p : M} (hp : p ∈ A.weightCore i) :
    A.weight i p ≠ 0 := by
  intro hz
  have h := A.coreThreshold_pos
  change A.coreThreshold ≤ (A.weight i p)^2 at hp
  rw [hz,zero_pow (by decide : 2 ≠ 0)] at hp
  exact (not_lt_of_ge hp) h

omit [CompactSpace M] in
lemma weightCore_source (i : A.centers) : A.weightCore i ⊆ (chart (i : M)).source :=
  fun _ hp => A.weight_support i (subset_tsupport _ (A.weightCore_nonzero i hp))

lemma weightCore_compact (i : A.centers) : IsCompact (A.weightCore i) :=
  (isClosed_le continuous_const ((A.weight_smooth i).continuous.pow 2)).isCompact

lemma coordinateCore_compact (i : A.centers) : IsCompact (A.coordinateCore i) :=
  (A.weightCore_compact i).image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (A.weightCore_source i))

omit [CompactSpace M] in
lemma mem_some_weightCore (p : M) : ∃ i : A.centers, p ∈ A.weightCore i := by
  classical
  by_contra hn
  have hi (i : A.centers) : (A.weight i p)^2 ≤ A.coreThreshold :=
    le_of_lt (lt_of_not_ge (fun h => hn ⟨i,h⟩))
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset A.centers)) (fun i _ => hi i)
  rw [A.partition p] at hs
  have hcount : (∑ _i : A.centers, A.coreThreshold) =
      (Fintype.card A.centers : ℝ) / ((Fintype.card A.centers : ℝ)+1) := by
    simp [coreThreshold,div_eq_mul_inv]
  rw [hcount] at hs
  have hlt : (Fintype.card A.centers : ℝ) / ((Fintype.card A.centers : ℝ)+1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  exact (not_lt_of_ge hs) hlt

omit [CompactSpace M] in
lemma coordinateCore_target (i : A.centers) : A.coordinateCore i ⊆ (chart (i : M)).target := by
  rintro _ ⟨p,hp,rfl⟩
  exact (chart (i : M)).map_source (A.weightCore_source i hp)

omit [CompactSpace M] in
lemma coordinateCore_weight_nonzero (i : A.centers) {x : Base}
    (hx : x ∈ A.coordinateCore i) : A.weight i ((chart (i : M)).symm x) ≠ 0 := by
  obtain ⟨p,hp,rfl⟩ := hx
  rw [(chart (i : M)).left_inv (A.weightCore_source i hp)]
  exact A.weightCore_nonzero i hp

/-- Every C1 immersion has a positive tolerance in the finite localized C1
norm within which all C1 maps remain immersions. -/
theorem immersion_C1_tolerance {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f)
    (hI : ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : M → V, ContMDiff planeModel 𝓘(ℝ,V) 1 g →
      A.C1Bound ε (g-f) → ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) g p) := by
  classical
  let w : A.centers → Base → ℝ := fun i => localizedWeight (i : M) (A.weight i)
  let l : A.centers → (M → V) → Base → V := fun i h => localize (i : M) (A.weight i) h
  have hw (i : A.centers) : ContDiff ℝ 1 (w i) :=
    (localizedWeight_smooth (i : M) (A.weight_smooth i) (A.weight_support i)).of_le (by simp)
  have hl (i : A.centers) : ContDiff ℝ 1 (l i f) :=
    localize_C1 (i : M) (A.weight_smooth i) (A.weight_support i) hf
  have hdata (i : A.centers) : ∃ r D : ℝ, 0 < r ∧ 0 < D ∧
      (∀ x ∈ A.coordinateCore i, ‖w i x‖+‖fderiv ℝ (w i) x‖ ≤ D) ∧
      ∀ x ∈ A.coordinateCore i, ∀ H : Base →L[ℝ] V,
        ‖H-weightedJet (w i) (l i f) x‖ < r → Function.Injective H := by
    obtain ⟨r,hr,hrb⟩ := compact_injective_stability
      ((A.coordinateCore_compact i).image (continuous_weightedJet (hw i) (hl i)))
      (by
        rintro _ ⟨x,hx,rfl⟩
        exact (localized_weightedJet_injective_iff hf (i : M) (A.weight_smooth i)
          (A.weight_support i) (A.coordinateCore_target i hx)
          (A.coordinateCore_weight_nonzero i hx)).mpr (hI _))
    obtain ⟨C,hC⟩ := (A.coordinateCore_compact i).exists_bound_of_continuousOn
      (((hw i).continuous.norm.add ((hw i).continuous_fderiv one_ne_zero).norm).continuousOn)
    refine ⟨r,1+|C|,hr,by positivity,?_,?_⟩
    · intro x hx
      exact (le_abs_self _).trans ((hC x hx).trans (by linarith [le_abs_self C]))
    · intro x hx H hH
      exact hrb _ (mem_image_of_mem _ hx) H hH
  choose r D hr hD hDb hrb using hdata
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : A.centers, ε < r i / D i :=
    Filter.eventually_all.mpr (fun i => gt_mem_nhds (div_pos (hr i) (hD i)))
  obtain ⟨η,hη,hηb⟩ := Metric.eventually_nhds_iff.mp hev
  let ε := η/2
  have hε : 0 < ε := half_pos hη
  have hεi (i : A.centers) : ε < r i / D i :=
    hηb (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hε] using half_lt_self hη) i
  refine ⟨ε,hε,?_⟩
  intro g hg hb p
  obtain ⟨i,hi⟩ := A.mem_some_weightCore p
  let x := chart (i : M) p
  have hx : x ∈ A.coordinateCore i := mem_image_of_mem _ hi
  have hgl : ContDiff ℝ 1 (l i g) :=
    localize_C1 (i : M) (A.weight_smooth i) (A.weight_support i) hg
  have hclose : ‖weightedJet (w i) (l i g) x-weightedJet (w i) (l i f) x‖ < r i := by
    have he : weightedJet (w i) (localize (i : M) (A.weight i) (g-f)) x =
        weightedJet (w i) (l i g) x-weightedJet (w i) (l i f) x := by
      have hlsub : localize (i : M) (A.weight i) (g-f) = l i g-l i f := by
        funext y
        by_cases hy : y ∈ (chart (i : M)).target
        · simp only [l,localize,indicator_of_mem hy,Pi.sub_apply,smul_sub]
        · simp only [l,localize,indicator_of_notMem hy,Pi.sub_apply,sub_self]
      rw [hlsub]
      exact weightedJet_sub ((hl i).differentiable one_ne_zero x)
        (hgl.differentiable one_ne_zero x)
    rw [← he]
    calc
      _ ≤ (‖w i x‖+‖fderiv ℝ (w i) x‖)*ε := norm_weightedJet_le (hb i x).1 (hb i x).2
      _ ≤ D i*ε := mul_le_mul_of_nonneg_right (hDb i x hx) hε.le
      _ < r i := by simpa only [mul_comm] using (lt_div_iff₀ (hD i)).mp (hεi i)
  have hgi := (localized_weightedJet_injective_iff hg (i : M) (A.weight_smooth i)
    (A.weight_support i) (A.coordinateCore_target i hx)
    (A.coordinateCore_weight_nonzero i hx)).mp (hrb i x hx _ hclose)
  change Function.Injective (mfderiv planeModel 𝓘(ℝ,V) g
    ((chart (i : M)).symm (chart (i : M) p))) at hgi
  rw [(chart (i : M)).left_inv (A.weightCore_source i hi)] at hgi
  exact hgi

variable [CompleteSpace V]

include A in
/-- The C1 immersion input is promoted to a smooth immersion by the actual
finite-atlas convolution smoother. -/
theorem smooth_immersion_of_C1 {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f)
    (hI : ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f p)) :
    ∃ g : M → V, ContMDiff planeModel 𝓘(ℝ,V) ∞ g ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) g p) := by
  obtain ⟨ε,hε,hstable⟩ := immersion_C1_tolerance A hf hI
  obtain ⟨η,hη,happrox⟩ := A.smooth_C1_approximation hf hε
  obtain ⟨hs,hb⟩ := happrox (η/2) (half_pos hη) (half_lt_self hη)
  exact ⟨A.smooth 1 (η/2) f,hs,hstable _ (hs.of_le (by simp)) hb⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
