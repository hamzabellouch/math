import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.PatternInvariant
import OAI.Combinatorics.IndependentSets.Reduction.Circle

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Set ProductAveraging
open scoped BigOperators Classical NNReal

theorem arbitrary_real_junta (L : ℝ≥0) {u : ℝ} (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ f : (ι → ℝ) → ℝ, LipschitzWith L f → (∀ x, |f x| ≤ 1) →
      ∃ S : Finset ι, S.card ≤ J ∧
        (∫ x, (f x-average BooleanJunta.unitLaw S f x)^2
          ∂Measure.pi (fun _ : ι => BooleanJunta.unitLaw)) < u := by
  obtain ⟨J,hJ,H⟩ := BooleanJunta.real_cube_junta_uniform L hu
  refine ⟨J,hJ,?_⟩
  intro ι _ _ f hf hb
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let g := f ∘ reindex (α:=ℝ) e
  have hg : LipschitzWith L g := by simpa only [mul_one] using hf.comp (reindex_lipschitz e)
  obtain ⟨S,hS,hi,he⟩ := H _ g hg (fun x => hb _)
  refine ⟨S.image e,(Finset.card_image_le).trans hS,?_⟩
  have ham := average_measurable BooleanJunta.unitLaw (S.image e) hf.continuous.measurable
  have h := integral_preserving (reindex_preserving BooleanJunta.unitLaw e)
    ((hf.continuous.measurable.sub ham).pow_const 2).aestronglyMeasurable
  have hp (x : Fin (Fintype.card ι) → ℝ) :
      (f (reindex e x)-average BooleanJunta.unitLaw (S.image e) f (reindex e x))^2 =
      (g x-average BooleanJunta.unitLaw S g x)^2 := by
    rw [← average_reindex BooleanJunta.unitLaw e S hf.continuous.measurable]
    rfl
  change (∫ x, (f (reindex e x)-average BooleanJunta.unitLaw (S.image e) f (reindex e x))^2
    ∂Measure.pi (fun _ : Fin (Fintype.card ι) => BooleanJunta.unitLaw)) =
    (∫ x, (f x-average BooleanJunta.unitLaw (S.image e) f x)^2
      ∂Measure.pi (fun _ : ι => BooleanJunta.unitLaw)) at h
  simp only [hp] at h
  rw [← h]
  exact he
end LargeIndependentSets

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set
open scoped BigOperators Classical NNReal
abbrev Circle := AddCircle (1:ℝ)
instance circleProbability : IsProbabilityMeasure (volume : Measure Circle) where
  measure_univ := by simp [Circle]
noncomputable def rotationLaw : Measure ℝ := volume.restrict (Ico 0 1)
instance rotationProbability : IsProbabilityMeasure rotationLaw where
  measure_univ := by simp [rotationLaw]
noncomputable def representative (x : Circle) : ℝ := (AddCircle.equivIco (1:ℝ) 0 x).val
lemma representative_mem (x : Circle) : representative x ∈ Ico (0:ℝ) 1 := by
  simpa [representative] using (AddCircle.equivIco (1:ℝ) 0 x).property
lemma representative_measurable : Measurable representative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1:ℝ) 0).measurable
lemma representative_coe (x : Circle) : (representative x : Circle) = x := AddCircle.coe_equivIco
lemma representative_eq {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) : representative (x : Circle) = x := by
  have h := AddCircle.equivIco_coe_eq (p:=(1:ℝ)) (a:=0) (x:=x) (by simpa using hx)
  exact congrArg Subtype.val h
lemma quotient_preserving : MeasurePreserving (fun x : ℝ => (x : Circle)) rotationLaw volume := by
  have h := AddCircle.measurePreserving_mk (1:ℝ) 0
  simpa only [zero_add, restrict_Ioc_eq_restrict_Icc, rotationLaw,
    restrict_Ico_eq_restrict_Icc] using h
lemma representative_preserving : MeasurePreserving representative volume rotationLaw := by
  refine ⟨representative_measurable,?_⟩
  rw [← quotient_preserving.map_eq, Measure.map_map representative_measurable quotient_preserving.measurable]
  have he : (fun x : ℝ => representative (x : Circle)) =ᵐ[rotationLaw] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    exact representative_eq hx
  change Measure.map (fun x : ℝ => representative (x : Circle)) rotationLaw = rotationLaw
  rw [Measure.map_congr he, Measure.map_id]
noncomputable def rotate (z : Circle) (x : ℝ) : ℝ := representative ((x : Circle)+z)
lemma rotate_preserving (z : Circle) : MeasurePreserving (rotate z) rotationLaw rotationLaw :=
  representative_preserving.comp ((measurePreserving_add_right volume z).comp quotient_preserving)
lemma rotate_coe (z : Circle) (x : ℝ) : ((rotate z x : ℝ) : Circle) = (x : Circle)+z := representative_coe _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ i, Fintype (M i)]
variable {κ τ : Type*}

noncomputable def phase (p : ∀ j, κ → M j) (t : ι → ℝ) (θ : (Sigma M) → ℝ) : κ → Circle :=
  fun k => ∑ j, ((t j * θ ⟨j,p j k⟩ : ℝ) : Circle)
noncomputable def auxiliary (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t : ι → ℝ) (θ : Sigma M → ℝ) (z : ι → Circle) : κ → Circle :=
  fun k => z (a (r k)) + phase p t θ k
noncomputable def blockShift (q : ∀ j, M j → τ) (a : τ → ι) (j : ι)
    (z : ι → Circle) (θ : Sigma M → ℝ) : Sigma M → ℝ :=
  fun c => if c.1 = j then rotate (z (a (q c.1 c.2))) (θ c) else θ c

lemma blockShift_preserving (q : ∀ j, M j → τ) (a : τ → ι) (j : ι) (z : ι → Circle) :
    MeasurePreserving (blockShift q a j z)
      (Measure.pi (fun _ : Sigma M => rotationLaw)) (Measure.pi (fun _ : Sigma M => rotationLaw)) := by
  apply measurePreserving_pi (fun _ : Sigma M => rotationLaw) (fun _ : Sigma M => rotationLaw)
    (f:=fun c x => if c.1 = j then rotate (z (a (q c.1 c.2))) x else x)
  intro c
  by_cases hc : c.1 = j
  · simpa only [blockShift, hc, ↓reduceIte] using rotate_preserving (z (a (q c.1 c.2)))
  · simp only [hc, ↓reduceIte]
    exact ⟨measurable_id, Measure.map_id⟩

omit [∀ index, Fintype (M index)] in
lemma full_block_absorption (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ)
    (hc : ∀ j k, q j (p j k) = r k) (a : τ → ι) (j : ι)
    (t : ι → ℝ) (ht : t j = 1) (θ : Sigma M → ℝ) (z : ι → Circle) :
    phase p t (blockShift q a j z θ) = auxiliary p r a t θ z := by
  funext k
  unfold phase auxiliary
  change (∑ l, ((t l * blockShift q a j z θ ⟨l,p l k⟩ : ℝ) : Circle)) =
    z (a (r k)) + ∑ l, ((t l * θ ⟨l,p l k⟩ : ℝ) : Circle)
  calc
    _ = ∑ l, (((t l * θ ⟨l,p l k⟩ : ℝ) : Circle) + if l=j then z (a (r k)) else 0) := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : l = j
      · subst l
        simp only [blockShift, ↓reduceIte, ht, one_mul, rotate_coe, hc]
      · simp only [blockShift, hl, ↓reduceIte, add_zero]
    _ = _ := by rw [Finset.sum_add_distrib]; simp [add_comm]

lemma absorption_integral [Fintype κ] (p : ∀ j, κ → M j) (q : ∀ j, M j → τ) (r : κ → τ)
    (hc : ∀ j k, q j (p j k) = r k) (a : τ → ι) (j : ι)
    (t : ι → ℝ) (ht : t j = 1) (z : ι → Circle)
    (F : (κ → Circle) → ℝ) (hF : Measurable F) :
    (∫ θ, F (auxiliary p r a t θ z) ∂Measure.pi (fun _ : Sigma M => rotationLaw)) =
      ∫ θ, F (phase p t θ) ∂Measure.pi (fun _ : Sigma M => rotationLaw) := by
  have hp : Measurable (phase p t) := by
    apply Measurable.of_eval
    intro k
    exact Finset.measurable_sum _ (fun l _ => quotient_preserving.measurable.comp
      (measurable_const.mul (measurable_pi_apply (⟨l,p l k⟩ : Sigma M))))
  have he (θ : Sigma M → ℝ) : F (auxiliary p r a t θ z) = F (phase p t (blockShift q a j z θ)) := by
    rw [full_block_absorption p q r hc a j t ht]
  simp_rw [he]
  exact ProductAveraging.integral_preserving (blockShift_preserving q a j z) (hF.comp hp).aestronglyMeasurable

omit [DecidableEq ι] [∀ index, Fintype (M index)] in
lemma auxiliary_lipschitz [Fintype κ] (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t : ι → ℝ) (θ : Sigma M → ℝ) : LipschitzWith 1 (auxiliary p r a t θ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro k
  simpa only [auxiliary, dist_add_right] using dist_le_pi_dist z w (a (r k))

omit [DecidableEq ι] [∀ index, Fintype (M index)] in
lemma auxiliary_mean_zero [Fintype κ] (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t : ι → ℝ) (θ : Sigma M → ℝ) (F : (κ → Circle) → ℝ)
    (hF : Measurable F) (hodd : ∀ x, F (fun k => x k + ((1/2:ℝ):Circle)) = -F x) :
    (∫ z, F (auxiliary p r a t θ z)) = 0 := by
  let v : ι → Circle := fun _ => ((1/2:ℝ):Circle)
  have hm := hF.comp (auxiliary_lipschitz p r a t θ).continuous.measurable
  have he (z : ι → Circle) : F (auxiliary p r a t θ (z+v)) = -F (auxiliary p r a t θ z) := by
    convert hodd (auxiliary p r a t θ z) using 1
    congr 1
    funext k
    simp [auxiliary, v, add_assoc, add_comm, add_left_comm]
  have hp := ProductAveraging.integral_preserving (measurePreserving_add_right (volume : Measure (ι→Circle)) v)
    hm.aestronglyMeasurable
  change (∫ z, F (auxiliary p r a t θ (z+v))) = (∫ z, F (auxiliary p r a t θ z)) at hp
  simp only [he, integral_neg] at hp
  linarith
end LargeIndependentSets.PhaseTest

end OAI
