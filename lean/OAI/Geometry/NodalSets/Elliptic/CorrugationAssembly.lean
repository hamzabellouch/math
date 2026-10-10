import OAI.Geometry.NodalSets.Charts.CorrugationFrozenFrame
import OAI.Geometry.NodalSets.Elliptic.CorrugationPeriodicBounds
import OAI.Geometry.NodalSets.Elliptic.CorrugationScaledJetsLemmas

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section
variable {ι : Type*}

def corrugationSum (I : Finset ι) (χ : Coord → ℝ) (amp J R : ℝ)
    (s : ι → ℝ) (e : ι → Coord ≃L[ℝ] Coord) (y : ι → Coord) (x : Coord) : ℝ :=
  ∑ i ∈ I, localizedCorrugation χ (corrugationPeriodicWell amp) (s i) J R
    (frozenFrameCovector (e i) 2) (frozenFrameCovector (e i) 3) (y i) x

lemma corrugationSum_smooth (I : Finset ι) (χ : Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (amp J R : ℝ) (s : ι → ℝ) (e : ι → Coord ≃L[ℝ] Coord) (y : ι → Coord) :
    ContDiff ℝ ∞ (corrugationSum I χ amp J R s e y) := by
  apply ContDiff.sum
  intro i _
  exact localizedCorrugation_smooth χ _ hχ (corrugationPeriodicWell_smooth amp) _ _ _ _ _ _

lemma corrugationSum_compact (I : Finset ι) (χ : Coord → ℝ)
    (hχ : tsupport χ ⊆ ball (0:Coord) (1/2))
    (amp J : ℝ) {R : ℝ} (hR : 0 < R)
    (s : ι → ℝ) (e : ι → Coord ≃L[ℝ] Coord) (y : ι → Coord) :
    HasCompactSupport (corrugationSum I χ amp J R s e y) :=
  finite_sum_compact_support I _ (fun _ _ ↦ localizedCorrugation_compact χ _ hχ _ _ hR _ _ _)

lemma corrugationSum_support (I : Finset ι) (χ : Coord → ℝ)
    (hχ : tsupport χ ⊆ ball (0:Coord) (1/2))
    (amp J : ℝ) {R : ℝ} (hR : 0 < R)
    (s : ι → ℝ) (e : ι → Coord ≃L[ℝ] Coord) (y : ι → Coord)
    (U : Set Coord) (hU : ∀ i ∈ I, ball (y i) (R/2) ⊆ U) :
    tsupport (corrugationSum I χ amp J R s e y) ⊆ U :=
  finite_sum_support_subset I _ U (fun i hi ↦
    (localizedCorrugation_cube χ _ hχ _ _ hR _ _ _).trans (hU i hi))

lemma corrugationSum_collar (I : Finset ι) (χ : Coord → ℝ)
    (hχ : tsupport χ ⊆ ball (0:Coord) (1/2))
    (amp J : ℝ) {R : ℝ} (hR : 0 < R)
    (s : ι → ℝ) (e : ι → Coord ≃L[ℝ] Coord) (y : ι → Coord)
    (U : Set Coord) (hU : ∀ i ∈ I, ball (y i) (R/2) ⊆ U) (x : Coord) (hx : x ∉ U) :
    corrugationSum I χ amp J R s e y =ᶠ[𝓝 x] 0 :=
  notMem_tsupport_iff_eventuallyEq.mp
    (fun h ↦ hx (corrugationSum_support I χ hχ amp J hR s e y U hU h))

theorem corrugationSum_uniform_bound (amp : ℝ) : ∃ B : ℝ, 0 < B ∧
    ∀ (I : Finset ι) (χ : Coord → ℝ),
      tsupport χ ⊆ ball (0:Coord) (1/2) → (∀ z, |χ z| ≤ 1) →
      ∀ (J R M : ℝ), 0 < J → 0 < R → 0 ≤ M →
      ∀ (s : ι → ℝ) (e : ι → Coord ≃L[ℝ] Coord) (y : ι → Coord),
      (∀ i ∈ I, 0 ≤ s i ∧ s i ≤ M) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (ball (y i) (R/2)) (ball (y j) (R/2))) →
      ∀ x, |corrugationSum I χ amp J R s e y x| ≤ M/J*B := by
  obtain ⟨B,hB,hf⟩ := corrugationPeriodicWell_bounded amp
  refine ⟨B,hB,?_⟩
  intro I χ hχ hχb J R M hJ hR hM s e y hs hd x
  apply finite_disjoint_sum_bound I _ _ (by positivity) _ x
  · intro i hi j hj hij
    exact (hd i hi j hj hij).mono (localizedCorrugation_cube χ _ hχ _ _ hR _ _ _)
      (localizedCorrugation_cube χ _ hχ _ _ hR _ _ _)
  · intro i hi z
    exact (localizedCorrugation_bound χ _ hχb hf (hs i hi).1 hJ R _ _ _ z).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hs i hi).2 hJ.le) hB.le)

end
end Yau.Geometry

end OAI
