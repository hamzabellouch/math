import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicTranslationImage
import Mathlib.Topology.Ultrafilter
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! # Limits of normalized approximately harmonic functions

Pointwise compactness suffices for the scalar functions obtained by projecting
normalized regular-representation coboundaries. In particular, no Hilbert-space
ultralimit or nonconstant-harmonic-function existence hypothesis is introduced.
-/
noncomputable section
namespace PolycyclicRecognition
open Filter Set Finset
open scoped Topology
variable {G : Type*} [Group G] [DecidableEq G]

omit [DecidableEq G] in
theorem exists_harmonic_limit
    {ι : Type*} {l : Filter ι} [l.NeBot] (S : Finset G)
    (f : ι → G → ℝ) (B : G → ℝ)
    (hbound : ∀ i g, |f i g| ≤ B g)
    (hzero : ∀ i, f i 1 = 0) {c : ℝ} (hc : 0 < c)
    (hnonzero : ∀ i, c ≤ ∑ s ∈ S, (f i s) ^ 2)
    (hdefect : ∀ g, Tendsto (fun i => ∑ s ∈ S, (f i (g * s) - f i g)) l (𝓝 0)) :
    ∃ F : G → ℝ, CayleyHarmonic S F ∧ F 1 = 0 ∧
      (∀ g, |F g| ≤ B g) ∧ ∃ s ∈ S, F s ≠ 0 := by
  let K (g : G) := Icc (-B g) (B g)
  have (g : G) : CompactSpace (K g) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (K g))
  let Z := (g : G) → K g
  let p : ι → Z := fun i g => ⟨f i g, abs_le.mp (hbound i g)⟩
  obtain ⟨z, _, hz⟩ := (isCompact_univ : IsCompact (univ : Set Z)).exists_mapClusterPt
    (show Filter.map p l ≤ 𝓟 univ by simp)
  obtain ⟨u, hul, huz⟩ := mapClusterPt_iff_ultrafilter.mp hz
  have hlim (g : G) : Tendsto (fun i => f i g) u (𝓝 (z g).val) := by
    have hc : Continuous (fun z : Z => (z g).val) :=
      continuous_subtype_val.comp (continuous_apply g)
    exact (hc.tendsto z).comp huz
  refine ⟨fun g => (z g).val, ?_, ?_, fun g => abs_le.mpr (z g).property, ?_⟩
  · intro g
    exact tendsto_nhds_unique
      (tendsto_finsetSum S (fun s _ => (hlim (g * s)).sub (hlim g)))
      ((hdefect g).mono_left hul)
  · exact tendsto_nhds_unique (hlim 1)
      (by simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) u (𝓝 0)))
  · have hpos : c ≤ ∑ s ∈ S, ((z s).val) ^ 2 :=
      ge_of_tendsto (tendsto_finsetSum S (fun s _ => (hlim s).pow 2))
        (Eventually.of_forall hnonzero)
    by_contra! h
    have he : (∑ s ∈ S, ((z s).val) ^ 2) = 0 := by
      apply sum_eq_zero
      intro s hs
      rw [h s hs, zero_pow (by decide)]
    linarith

theorem exists_nonconstant_polynomial_harmonic_of_approximate
    {ι : Type*} {l : Filter ι} [l.NeBot] (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (f : ι → G → ℝ)
    (hbound : ∀ i g, |f i g| ≤ cayleyWordLength S hS hgen g)
    (hzero : ∀ i, f i 1 = 0) {c : ℝ} (hc : 0 < c)
    (hnonzero : ∀ i, c ≤ ∑ s ∈ S, (f i s) ^ 2)
    (hdefect : ∀ g, Tendsto (fun i => ∑ s ∈ S, (f i (g * s) - f i g)) l (𝓝 0)) :
    ∃ F : polynomialHarmonicFunctions S 1, ∃ s ∈ S, F.val s ≠ F.val 1 := by
  obtain ⟨F, hF, hFone, hFB, s, hs, hFs⟩ :=
    exists_harmonic_limit S f _ hbound hzero hc hnonzero hdefect
  have hp : PolynomiallyBoundedOnWords S 1 F := by
    refine ⟨1, zero_le_one, fun n x hx => ?_⟩
    have hn : (cayleyWordLength S hS hgen x : ℝ) ≤ n :=
      Nat.cast_le.mpr ((cayleyWordLength_le_iff S hS hgen x n).mpr hx)
    simpa only [pow_one, one_mul] using (hFB x).trans (by linarith :
      (cayleyWordLength S hS hgen x : ℝ) ≤ 1 + (n : ℝ))
  exact ⟨⟨F, hp, hF⟩, s, hs, by simpa only [hFone] using hFs⟩

end PolycyclicRecognition

end

end OAI
