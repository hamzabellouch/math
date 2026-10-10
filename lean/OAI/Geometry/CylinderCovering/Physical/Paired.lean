import OAI.Geometry.CylinderCovering.Physical.PairedDefinitions
import OAI.Geometry.CylinderCovering.Physical.Cost
import OAI.Geometry.CylinderCovering.Convexity.TriangularSimilarity

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace CylinderCovering.UnitEdgeFootprints
open TriangularCovering

private def translation : Space := !₂[0, 0, height]

private def reflectionIsometry : Space ≃ₗᵢ[ℝ] Space where
  toFun := linearReflection
  invFun z := !₂[z 1, -z 0, -z 2]
  left_inv z := by ext i; fin_cases i <;> simp [linearReflection]
  right_inv z := by ext i; fin_cases i <;> simp [linearReflection]
  map_add' z w := by ext i; fin_cases i <;> simp [linearReflection] <;> ring
  map_smul' c z := by ext i; fin_cases i <;> simp [linearReflection]
  norm_map' z := by
    change ‖linearReflection z‖ = ‖z‖
    have hsq : ‖linearReflection z‖ ^ 2 = ‖z‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, linearReflection, Fin.sum_univ_succ]
      ring
    nlinarith [norm_nonneg (linearReflection z), norm_nonneg z]

private lemma similarity_map_eq : Similarity.map translation 1 reflectionIsometry = reflection := by
  funext z
  ext i
  fin_cases i <;> simp [Similarity.map, translation, reflectionIsometry, linearReflection, reflection]
  ring

lemma sourceCap_neg (η s : ℝ) : sourceCap η (-s) = sourceCap η s := by
  unfold sourceCap
  congr 1
  ring

lemma reflection_representedPoint (η s ρ y : ℝ) :
    reflection (representedPoint η (-s) ρ y) = secondRepresentedPoint η s ρ y := by
  ext i
  fin_cases i <;> simp [reflection, representedPoint, secondRepresentedPoint] <;> ring

theorem secondSweep_eq (η : ℝ) : secondSweep η = reflection '' sweep η (sourceCap η) := by
  ext z
  constructor
  · rintro ⟨s, hs, ρ, hρ, y, hy, rfl⟩
    refine ⟨representedPoint η (-s) ρ y, ?_, reflection_representedPoint η s ρ y⟩
    refine ⟨-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ρ, ?_, y, hy, rfl⟩
    simpa only [sourceCap_neg] using hρ
  · rintro ⟨z, ⟨s, hs, ρ, hρ, y, hy, rfl⟩, rfl⟩
    refine ⟨-s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ρ, ?_, y, hy, ?_⟩
    · simpa only [sourceCap_neg] using hρ
    · simpa only [neg_neg] using reflection_representedPoint η (-s) ρ y

private lemma transported_base_eq (η d M m : ℝ) :
    Similarity.transportedBase (base η d M m) (axis η m) translation 1 reflectionIsometry =
      secondBase η d M m := by
  unfold base secondBase
  change (Similarity.baseMap (axis η m) translation 1 reflectionIsometry) ''
      (Similarity.project (axis η m) '' foot η d M m) =
      Similarity.project (reflectionIsometry (axis η m)) '' (reflection '' foot η d M m)
  rw [image_image, image_image]
  congr 1
  funext z
  rw [← similarity_map_eq]
  exact (Similarity.project_map (axis η m) translation z 1 reflectionIsometry).symm

theorem paired_family_realization : PairedFamilyStatement := by
  intro η hη
  obtain ⟨C₁, hspec, hcover, hlimit⟩ := family_realization η hη (sourceCap η)
    (sourceCap_continuous η).continuousOn (fun s _ => (sourceCap_pos η s).le)
  let C₂ : (N : ℕ) → Fin N → TriCylinder :=
    fun N i => (C₁ N i).similarity translation (by norm_num : (1 : ℝ) ≠ 0) reflectionIsometry
  have harea : ∀ N (i : Fin N), area (C₂ N i).base = area (C₁ N i).base := by
    intro N i
    simp [C₂, TriCylinder.similarity_area]
  have hsum : ∀ N, totalArea (C₂ N) = totalArea (C₁ N) := by
    intro N
    unfold totalArea
    exact Finset.sum_congr rfl fun i _ => harea N i
  refine ⟨C₁, C₂, ?_, ?_, ?_⟩
  · intro N i
    obtain ⟨ha, hb, hc⟩ := hspec N i
    refine ⟨ha, hb, ?_, ?_, hc, (harea N i).trans hc⟩
    · change reflectionIsometry (C₁ N i).axis = secondAxis η (midpoint N i)
      rw [ha]
      rfl
    · change Similarity.transportedBase (C₁ N i).base (C₁ N i).axis
        translation 1 reflectionIsometry = _
      rw [ha, hb, transported_base_eq]
  · intro N hN z hz
    rcases hz with hz | hz
    · obtain ⟨i, hi⟩ := hcover N hN z hz
      exact ⟨i, Or.inl hi⟩
    · rw [secondSweep_eq] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨i, hi⟩ := hcover N hN y hy
      refine ⟨i, Or.inr ?_⟩
      change reflection y ∈ ((C₁ N i).similarity translation
        (by norm_num : (1 : ℝ) ≠ 0) reflectionIsometry).carrier
      rw [TriCylinder.similarity_carrier, similarity_map_eq]
      exact ⟨y, hi, rfl⟩
  · simp_rw [hsum]
    convert hlimit.add hlimit using 1
    ring_nf

end CylinderCovering.UnitEdgeFootprints

end

end OAI
