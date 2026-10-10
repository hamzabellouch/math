import OAI.GroupTheory.Thompson.InvariantMean
import Mathlib.Topology.Ultrafilter
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! # Constructing an invariant mean from approximate finite averages

Compactness is applied to the actual bounded-function space. The conclusion
is the invariant mean used by the height-correction argument, not a separate
amenability predicate.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Set
open scoped Topology ENNReal

variable {G : Type*} [Group G]

omit [Group G] in
/-- Positivity and normalization control every bounded real function. -/
theorem positive_normalized_bound
    (L : BoundedReal G →ₗ[ℝ] ℝ)
    (hpos : ∀ f, (∀ g, 0 ≤ f g) → 0 ≤ L f) (hone : L 1 = 1)
    (f : BoundedReal G) : |L f| ≤ ‖f‖ := by
  have hmono {a b : BoundedReal G} (h : ∀ g, a g ≤ b g) : L a ≤ L b := by
    have hh := hpos (b - a) (fun g => sub_nonneg.mpr (h g))
    rw [map_sub] at hh
    exact sub_nonneg.mp hh
  have hlo := hmono (a := (-‖f‖) • (1 : BoundedReal G)) (b := f) (fun g => by
    have hh := lp.norm_apply_le_norm ENNReal.top_ne_zero f g
    simp only [BoundedReal.smul_one_apply]
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hh)).1)
  have hhi := hmono (a := f) (b := ‖f‖ • (1 : BoundedReal G)) (fun g => by
    have hh := lp.norm_apply_le_norm ENNReal.top_ne_zero f g
    simp only [BoundedReal.smul_one_apply]
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hh)).2)
  simp only [map_smul, smul_eq_mul, hone, mul_one] at hlo hhi
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- Compactness simultaneously preserves positivity, normalization and
vanishing translation defects for any prescribed set of group elements. -/
theorem exists_partially_invariantMean_of_approximate
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (L : ι → BoundedReal G →ₗ[ℝ] ℝ)
    (hpos : ∀ i f, (∀ g, 0 ≤ f g) → 0 ≤ L i f)
    (hone : ∀ i, L i 1 = 1)
    (S : Set G)
    (hdefect : ∀ g ∈ S, ∀ f, Tendsto (fun i => L i (leftPull g f) - L i f) l (𝓝 0)) :
    ∃ M : BoundedReal G →ₗ[ℝ] ℝ,
      (∀ f, (∀ g, 0 ≤ f g) → 0 ≤ M f) ∧ M 1 = 1 ∧
        ∀ g ∈ S, ∀ f, M (leftPull g f) = M f := by
  let K (f : BoundedReal G) := Icc (-‖f‖) ‖f‖
  have (f : BoundedReal G) : CompactSpace (K f) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (K f))
  let Z := (f : BoundedReal G) → K f
  let p : ι → Z := fun i f => ⟨L i f,
    abs_le.mp (positive_normalized_bound (L i) (hpos i) (hone i) f)⟩
  obtain ⟨z, _, hz⟩ := (isCompact_univ : IsCompact (univ : Set Z)).exists_mapClusterPt
    (show Filter.map p l ≤ 𝓟 univ by simp)
  obtain ⟨u, hul, huz⟩ := mapClusterPt_iff_ultrafilter.mp hz
  have hlim (f : BoundedReal G) : Tendsto (fun i => L i f) u (𝓝 (z f).val) := by
    exact (continuous_subtype_val.comp (continuous_apply f)).tendsto z |>.comp huz
  let M : BoundedReal G →ₗ[ℝ] ℝ :=
    { toFun := fun f => (z f).val
      map_add' := by
        intro f g
        apply tendsto_nhds_unique (hlim (f + g))
        simpa only [map_add] using (hlim f).add (hlim g)
      map_smul' := by
        intro r f
        apply tendsto_nhds_unique (hlim (r • f))
        simpa only [map_smul, smul_eq_mul, RingHom.id_apply] using (hlim f).const_mul r }
  refine ⟨M, ?_, ?_, ?_⟩
  · intro f hf
    exact ge_of_tendsto (hlim f) (Eventually.of_forall (fun i => hpos i f hf))
  · change (z 1).val = 1
    apply tendsto_nhds_unique (hlim 1)
    simpa only [hone] using (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℝ)) u (𝓝 1))
  · intro g hg f
    change (z (leftPull g f)).val = (z f).val
    apply sub_eq_zero.mp
    exact tendsto_nhds_unique ((hlim (leftPull g f)).sub (hlim f))
      ((hdefect g hg f).mono_left hul)

/-- A nontrivial net of positive normalized linear averages whose translation
defects tend to zero yields the actual invariant mean used for height correction. -/
theorem exists_invariantMean_of_approximate
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (L : ι → BoundedReal G →ₗ[ℝ] ℝ)
    (hpos : ∀ i f, (∀ g, 0 ≤ f g) → 0 ≤ L i f)
    (hone : ∀ i, L i 1 = 1)
    (hdefect : ∀ g f, Tendsto (fun i => L i (leftPull g f) - L i f) l (𝓝 0)) :
    Nonempty (InvariantMean G) := by
  obtain ⟨M, hM, hMone, hMinv⟩ := exists_partially_invariantMean_of_approximate
    (l := l) L hpos hone univ (fun g _ => hdefect g)
  exact ⟨⟨M, hM, hMone, fun g => hMinv g (mem_univ g)⟩⟩

end PolycyclicRecognition

end

end OAI
