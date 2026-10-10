import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.NearAngularEnergyProfileBound
import OAI.MeasureTheory.FalconerCompletion.Graphs.AmbientDescendants
import OAI.MeasureTheory.FalconerCompletion.Sphere.SpherePlaneWave3

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory
variable {V : Type*} [MeasurableSpace V]

noncomputable def farAngularEnergyND (d : ℕ) (μ : Measure V) (a : ℝ) (h : ℕ)
    (v lam₁ lam₂ : ℝ) (Ψ : ℝ → ℝ) (A B : Finset (Fin d → ℤ))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ) : ℝ :=
  lam₁^2*lam₂^2*(2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
    ‖∫ p : ℝ × (V × V), (Ψ (p.1/(2:ℝ)^v):ℂ)*farRetainedND h A B U W p.1 p.2
      ∂volume.prod (μ.prod μ)‖

theorem sourceAngularHND_near_far_profile_bound (d : ℕ) {N : ℕ} (hN : 0<N)
    (μ : Measure V) [IsFiniteMeasure μ]
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (a : ℝ) (h : ℕ) (v ma mb err : ℝ)
    (A B : Finset (Fin d → ℤ)) (hAB : (A.product B).Nonempty)
    (X Y : Set (EuclideanSpace ℝ (Fin d)))
    (hs₁ : ∀ i∈A, ambientGridCell h i⊆X) (hs₂ : ∀ j∈B, ambientGridCell h j⊆Y)
    (hl₁ : ∀ i∈A, ((2:ℝ)^N)^(-mb-err)≤(ρ (ambientGridCell h i)).toReal)
    (hl₂ : ∀ j∈B, ((2:ℝ)^N)^(-mb-err)≤(κ (ambientGridCell h j)).toReal)
    (hu₁ : (ρ X).toReal≤((2:ℝ)^N)^(-ma+err))
    (hu₂ : (κ Y).toReal≤((2:ℝ)^N)^(-ma+err))
    (U W : (Fin d → ℤ) → ℝ × V → ℂ)
    (hU : ∀ i∈A, Measurable (U i)) (hW : ∀ j∈B, Measurable (W j))
    (C E : (Fin d → ℤ) → ℝ)
    (hbU : ∀ i∈A, ∀ r, ∀ᵐ w ∂μ, ‖U i (r,w)‖≤C i)
    (hbW : ∀ j∈B, ∀ r, ∀ᵐ w ∂μ, ‖W j (r,w)‖≤E j)
    {Ψ : ℝ → ℝ} (hmΨ : Measurable Ψ) (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v)))
    (hΨpos : ∀ r, 0≤Ψ r) :
    sourceAngularHND d μ a v Ψ (fun p => (((2:ℝ)^N)^(-(mb-ma))) • ∑ i∈A, U i p)
      (fun p => (((2:ℝ)^N)^(-(mb-ma))) • ∑ j∈B, W j p) ≤
      (20*(d+1:ℝ)+5)^(2*d)*((2:ℝ)^N)^(-2*((mb-(d:ℝ)*(h:ℝ)/(2*N))-
        (ma-(d:ℝ)*a/(2*N)))+4*err)*graphChildMaxND d μ h v Ψ A B hAB U W +
      farAngularEnergyND d μ a h v (((2:ℝ)^N)^(-(mb-ma)))
        (((2:ℝ)^N)^(-(mb-ma))) Ψ A B U W := by
  have hh := sourceAngularHND_near_far_bound d h μ a v
    (((2:ℝ)^N)^(-(mb-ma))) (((2:ℝ)^N)^(-(mb-ma))) A B U W hU hW C E hbU hbW hmΨ hΨ hΨpos
  exact hh.trans (add_le_add (nearAngularEnergyND_profile_bound d hN μ ρ κ a h v ma mb err
    A B hAB X Y hs₁ hs₂ hl₁ hl₂ hu₁ hu₂ U W hU hW C E hbU hbW hΨ hΨpos) le_rfl)

end Attempt4Near
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ComplexConjugate
variable {d : ℕ}

lemma original_parent_integral_descendantsND
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) {a h : ℕ} (hah : a≤h) (X : Fin d → ℤ)
    (F : EuclideanSpace ℝ (Fin d) → ℂ) (hF : IntegrableOn F (ambientGridCell a X) ρ) :
    (∫ x in ambientGridCell a X, F x ∂ρ) =
      ∑ Q∈ambientDescendantsND a h X, ∫ x in ambientGridCell h Q, F x ∂ρ := by
  have hcover : (⋃ Q∈ambientDescendantsND a h X, ambientGridCell h Q)=ambientGridCell a X :=
    ambientDescendantsND_cover hah X
  rw [← hcover]
  exact integral_biUnion_finset _ (fun Q _ => measurableSet_ambientGridCell h Q)
    (fun Q _ R _ hQR => ambientGridCell_disjoint hQR)
    (fun Q hQ => hF.mono_set (ambientDescendantsND_subset hah hQ))

lemma original_parent_integral_occupiedND
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) {a h : ℕ} (hah : a≤h) (X : Fin d → ℤ)
    (F : EuclideanSpace ℝ (Fin d) → ℂ) (hF : IntegrableOn F (ambientGridCell a X) ρ) :
    (∫ x in ambientGridCell a X, F x ∂ρ) =
      ∑ Q∈occupiedDescendantsND ρ a h X, ∫ x in ambientGridCell h Q, F x ∂ρ := by
  classical
  rw [original_parent_integral_descendantsND ρ hah X F hF]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro Q hQ hnQ
  have hz : ρ (ambientGridCell h Q)=0 := by
    by_contra hz
    exact hnQ (Finset.mem_filter.mpr ⟨hQ,hz⟩)
  rw [Measure.restrict_eq_zero.mpr hz,integral_zero_measure]

lemma sourceAngularTransformND_parent_partition
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
    {a h : ℕ} (hah : a≤h) (X : Fin d → ℤ) (M Nt r : ℝ) (hNt : Nt≠0)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
    (hb : Measurable (Function.uncurry b)) (w : EuclideanSpace ℝ (Fin d)) {B : ℝ}
    (hB : ∀ x, ‖b x w‖≤B) :
    sourceAngularTransformND ρ (ambientGridCell a X) M b r w =
      (M⁻¹*Nt) • ∑ Q∈occupiedDescendantsND ρ a h X,
        sourceAngularTransformND ρ (ambientGridCell h Q) Nt b r w := by
  have hm : Measurable (fun x => spherePlaneWaveND r x w*b x w) :=
    (show Measurable (fun x => spherePlaneWaveND r x w) by unfold spherePlaneWaveND; fun_prop).mul
      (hb.comp (measurable_id.prodMk measurable_const))
  have hi : IntegrableOn (fun x => spherePlaneWaveND r x w*b x w) (ambientGridCell a X) ρ := by
    apply Integrable.of_bound hm.aestronglyMeasurable B
    filter_upwards with x
    simpa only [norm_mul,spherePlaneWaveND_norm,one_mul] using hB x
  simp only [sourceAngularTransformND]
  rw [original_parent_integral_occupiedND ρ hah X _ hi,← Finset.smul_sum,smul_smul]
  rw [mul_assoc, mul_inv_cancel₀ hNt,mul_one]

lemma sourceAngularMomentND_congr_ae (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (U W : ℝ × EuclideanSpace ℝ (Fin d) → ℂ)
    (hUW : ∀ r, ∀ᵐ w ∂μ, U (r,w)=W (r,w)) (r : ℝ) :
    Attempt4Near.sourceAngularMomentND μ U r=Attempt4Near.sourceAngularMomentND μ W r := by
  apply integral_congr_ae
  filter_upwards [hUW r] with w hw
  rw [hw]

lemma sourceAngularHND_congr_ae (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (a v : ℝ) (Ψ : ℝ → ℝ)
    (U U' W W' : ℝ × EuclideanSpace ℝ (Fin d) → ℂ)
    (hU : ∀ r, ∀ᵐ w ∂μ, U (r,w)=U' (r,w))
    (hW : ∀ r, ∀ᵐ w ∂μ, W (r,w)=W' (r,w)) :
    Attempt4Near.sourceAngularHND d μ a v Ψ U W=
      Attempt4Near.sourceAngularHND d μ a v Ψ U' W' := by
  unfold Attempt4Near.sourceAngularHND
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  rw [sourceAngularMomentND_congr_ae μ U U' hU r,sourceAngularMomentND_congr_ae μ W W' hW r]

lemma original_occupied_nonemptyND
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) {a h : ℕ} (hah : a≤h) (X : Fin d → ℤ)
    (hX : ρ (ambientGridCell a X)≠0) : (occupiedDescendantsND ρ a h X).Nonempty := by
  classical
  by_contra hn
  have hz : ∀ Q∈ambientDescendantsND a h X, ρ (ambientGridCell h Q)=0 := by
    intro Q hQ
    by_contra hz
    exact hn ⟨Q,Finset.mem_filter.mpr ⟨hQ,hz⟩⟩
  have hcover : (⋃ Q∈ambientDescendantsND a h X, ambientGridCell h Q)=ambientGridCell a X :=
    ambientDescendantsND_cover hah X
  exact hX (hcover ▸ (measure_biUnion_null_iff (Finset.countable_toSet _)).mpr hz)

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
