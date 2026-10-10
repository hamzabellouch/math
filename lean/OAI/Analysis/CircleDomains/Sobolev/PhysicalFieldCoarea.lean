import OAI.Analysis.CircleDomains.Sobolev.PhysicalLipschitzCoarea
import OAI.Analysis.CircleDomains.Sobolev.WeakCovectorGradient

namespace OAI

/-! Weighted coarea identities retaining a specified actual weak-gradient
field, and their disjoint countable assembly. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

def PhysicalFieldCoareaIdentity (E : Set EuclideanPlane) (u : EuclideanPlane → ℝ)
    (V : EuclideanPlane → EuclideanPlane) (q : EuclideanPlane → ℝ≥0∞) : Prop :=
  AEMeasurable (sobolevLevelIntegral E u q) volume ∧
    (∫⁻ t, sobolevLevelIntegral E u q t) = ∫⁻ x in E, q x*ENNReal.ofReal ‖V x‖

lemma physical_field_coarea_piece {u g : EuclideanPlane → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {A : Set EuclideanPlane} (hA : MeasurableSet A)
    (hb : Bornology.IsBounded A) (heq : EqOn u g A)
    {V : EuclideanPlane → EuclideanPlane}
    (hV : ∀ᵐ x ∂volume.restrict A, ∀ i : Fin 2,
      fderiv ℝ g x (EuclideanSpace.single i 1) = V x i)
    {q : EuclideanPlane → ℝ≥0∞} (hq : Measurable q) :
    PhysicalFieldCoareaIdentity A u V q := by
  obtain ⟨hm,hi⟩ := physical_lipschitz_weighted_coarea hg hA hb hq
  have hlev : sobolevLevelIntegral A g q = sobolevLevelIntegral A u q := by
    funext t
    have hs : A ∩ {x | g x = t} = A ∩ {x | u x = t} := by
      ext x
      constructor
      · rintro ⟨hx,ht⟩
        exact ⟨hx,(heq hx).trans ht⟩
      · rintro ⟨hx,ht⟩
        exact ⟨hx,(heq hx).symm.trans ht⟩
    simp only [sobolevLevelIntegral,hs]
  rw [hlev] at hm hi
  refine ⟨hm,hi.trans ?_⟩
  apply lintegral_congr_ae
  filter_upwards [hV] with x hx
  have he : planeCovectorGradient (fderiv ℝ g x) = V x := by
    unfold planeCovectorGradient
    rw [hx 0,hx 1,planePair_coordinates]

  rw [← planeCovectorGradient_norm,he]

lemma physical_field_coarea_iUnion {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (V : EuclideanPlane → EuclideanPlane) (q : EuclideanPlane → ℝ≥0∞)
    (A : ℕ → Set EuclideanPlane) (hA : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (Disjoint on A))
    (hco : ∀ n, PhysicalFieldCoareaIdentity (A n) u V q) :
    PhysicalFieldCoareaIdentity (⋃ n, A n) u V q := by
  have hlev : sobolevLevelIntegral (⋃ n, A n) u q =
      fun t => ∑' n, sobolevLevelIntegral (A n) u q t := by
    funext t
    unfold sobolevLevelIntegral
    rw [iUnion_inter]
    apply lintegral_iUnion
    · exact fun n => (hA n).inter (measurableSet_eq_fun hu.measurable measurable_const)
    · exact fun i j hij => (hd hij).mono inter_subset_left inter_subset_left
  refine ⟨by rw [hlev]; exact AEMeasurable.tsum (fun n => (hco n).1),?_⟩
  rw [hlev,lintegral_tsum (fun n => (hco n).1)]
  calc
    _ = ∑' n, ∫⁻ x in A n, q x*ENNReal.ofReal ‖V x‖ := tsum_congr (fun n => (hco n).2)
    _ = _ := (lintegral_iUnion hA hd _).symm

lemma physical_field_coarea_union {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (V : EuclideanPlane → EuclideanPlane) (q : EuclideanPlane → ℝ≥0∞)
    {A B : Set EuclideanPlane} (hB : MeasurableSet B) (hd : Disjoint A B)
    (hAco : PhysicalFieldCoareaIdentity A u V q) (hBco : PhysicalFieldCoareaIdentity B u V q) :
    PhysicalFieldCoareaIdentity (A ∪ B) u V q := by
  have hs : sobolevLevelIntegral (A ∪ B) u q =
      fun t => sobolevLevelIntegral A u q t + sobolevLevelIntegral B u q t := by
    funext t
    unfold sobolevLevelIntegral
    rw [union_inter_distrib_right]
    exact lintegral_union (hB.inter (measurableSet_eq_fun hu.measurable measurable_const))
      (hd.mono inter_subset_left inter_subset_left)
  refine ⟨by rw [hs]; exact hAco.1.add hBco.1,?_⟩
  rw [hs,lintegral_add_left' hAco.1,hAco.2,hBco.2,lintegral_union hB hd]

end CircleDomainRigidity

end

end OAI
