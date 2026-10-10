import OAI.Dynamics.TriangleBilliards.Unfolding

namespace OAI

universe uAlpha

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section

namespace TriangularBilliards

/-- On a measurable set, an injective measurable map that locally agrees
with one of countably many measure-preserving embeddings preserves the
measure of that set. The pieces need not be open. -/
lemma measure_image_countably_piecewise
    {α : Type uAlpha} [MeasurableSpace α] [MeasurableEq α]
    (μ : Measure α) {f : α → α} (hf : Measurable f) {R : Set α}
    (hR : MeasurableSet R) (hi : InjOn f R) (F : ℕ → α → α)
    (hF : ∀ n, MeasurePreserving (F n) μ μ)
    (hE : ∀ n, MeasurableEmbedding (F n))
    (hcover : ∀ x ∈ R, ∃ n, f x = F n x) : μ (f '' R) = μ R := by
  let S : ℕ → Set α := fun n => R ∩ {x | f x = F n x}
  let D : ℕ → Set α := disjointed S
  have hSm (n : ℕ) : MeasurableSet (S n) :=
    hR.inter (measurableSet_eq_fun hf (hF n).measurable)
  have hDm (n : ℕ) : MeasurableSet (D n) := MeasurableSet.disjointed hSm n
  have hDS (n : ℕ) : D n ⊆ S n := disjointed_subset S n
  have hDR (n : ℕ) : D n ⊆ R := fun _ hx => (hDS n hx).1
  have hDeq : (⋃ n, D n) = R := by
    rw [show (⋃ n, D n) = ⋃ n, S n from iUnion_disjointed]
    ext x
    simp only [mem_iUnion, S, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => by
      obtain ⟨n, hn⟩ := hcover x hx
      exact ⟨n, hx, hn⟩⟩
  have himage (n : ℕ) : f '' D n = F n '' D n := by
    apply image_congr
    intro x hx
    exact (hDS n hx).2
  have hIm (n : ℕ) : MeasurableSet (f '' D n) := by
    rw [himage]
    exact (hE n).measurableSet_image.mpr (hDm n)
  have hId : Pairwise (Function.onFun Disjoint (fun n => f '' D n)) := by
    intro n m hnm
    change Disjoint (f '' D n) (f '' D m)
    rw [disjoint_left]
    rintro y ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
    have hab := hi (hDR m hb) (hDR n ha) he
    subst b
    exact Set.disjoint_left.mp (disjoint_disjointed S hnm) ha hb
  have hmeasure (n : ℕ) : μ (f '' D n) = μ (D n) := by
    rw [himage]
    have hh := (hF n).measure_preimage ((hE n).measurableSet_image.mpr (hDm n)).nullMeasurableSet
    rw [preimage_image_eq _ (hE n).injective] at hh
    exact hh.symm
  calc
    μ (f '' R) = μ (⋃ n, f '' D n) := by rw [← hDeq, image_iUnion]
    _ = ∑' n, μ (f '' D n) := measure_iUnion hId hIm
    _ = ∑' n, μ (D n) := tsum_congr hmeasure
    _ = μ R := by rw [← measure_iUnion (disjoint_disjointed S) hDm, hDeq]

end TriangularBilliards

namespace TriangularBilliards

lemma phaseWord_injective (Q : Triangle) (w : List (Fin 3)) :
    Function.Injective (phaseWord Q w) := by
  induction w with
  | nil => exact Function.injective_id
  | cons i w hw =>
    exact (Function.LeftInverse.injective (wallPhase_involutive Q i)).comp hw

lemma freeFlow_add (s t : ℝ) (z : Phase) : freeFlow s (freeFlow t z) = freeFlow (s + t) z := by
  apply Prod.ext
  · simp only [freeFlow, add_smul]
    abel
  · rfl

lemma freeFlow_zero (z : Phase) : freeFlow 0 z = z := by simp [freeFlow]

lemma freeFlow_injective (t : ℝ) : Function.Injective (freeFlow t) := by
  have h : Function.LeftInverse (freeFlow (-t)) (freeFlow t) := by
    intro z
    rw [freeFlow_add, neg_add_cancel, freeFlow_zero]
  exact h.injective

lemma measurableEmbedding_branch (Q : Triangle) (t : ℝ) (w : List (Fin 3)) :
    MeasurableEmbedding (phaseWord Q w ∘ freeFlow t) :=
  (((measurePreserving_phaseWord Q w).comp (measurePreserving_freeFlow t)).measurable).measurableEmbedding
    ((phaseWord_injective Q w).comp (freeFlow_injective t))

lemma phaseMeasure_eq_regularAt (Q : Triangle) (t : ℝ) :
    phaseMeasure Q = (volume Q.table)⁻¹ • ambientMeasure.restrict (regularAt Q t) := by
  calc
    phaseMeasure Q = (phaseMeasure Q).restrict (regularAt Q t) :=
      (Measure.restrict_eq_self_of_ae_mem (ae_regularAt Q t)).symm
    _ = _ := by rw [phaseMeasure_eq_restrict, Measure.restrict_smul,
      Measure.restrict_restrict_of_subset (regularAt_subset_table Q t)]

/-- Exact Liouville-measure preservation of every actual billiard time map.
The proof uses finite unfolding and injectivity, not an assumed dynamical
invariance or a numerical/recurrence input. -/
lemma measurePreserving_billiardFlow (Q : Triangle) (t : ℝ) :
    MeasurePreserving (billiardFlow Q t) (phaseMeasure Q) (phaseMeasure Q) := by
  refine ⟨measurable_billiardFlow_time Q t, ?_⟩
  apply Measure.eq_of_le_of_measure_univ_eq
  · apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.map_apply (measurable_billiardFlow_time Q t) hA]
    obtain ⟨e, he⟩ := exists_surjective_nat (List (Fin 3))
    let R := (billiardFlow Q t) ⁻¹' A ∩ regularAt Q t
    have hR : MeasurableSet R := (hA.preimage (measurable_billiardFlow_time Q t)).inter
      (measurableSet_regularAt Q t)
    have hsub : R ⊆ regularAt Q t := inter_subset_right
    have hcover : ∀ z ∈ R, ∃ n, billiardFlow Q t z =
        (phaseWord Q (e n) ∘ freeFlow t) z := by
      intro z hz
      obtain ⟨c⟩ := hz.2.1
      obtain ⟨w, hw⟩ := c.at_unfold t
      obtain ⟨n, rfl⟩ := he w
      exact ⟨n, (billiardFlow_eq_chain c t).trans hw⟩
    have hmeasure := measure_image_countably_piecewise ambientMeasure
      (measurable_billiardFlow_time Q t) hR
      ((flow_injective_regularAt Q t).mono hsub)
      (fun n => phaseWord Q (e n) ∘ freeFlow t)
      (fun n => (measurePreserving_phaseWord Q (e n)).comp (measurePreserving_freeFlow t))
      (fun n => measurableEmbedding_branch Q t (e n)) hcover
    have hcontain : billiardFlow Q t '' R ⊆ A ∩ (Q.table ×ˢ univ) := by
      rintro y ⟨z, hz, rfl⟩
      exact ⟨hz.1, flow_mem_table_of_regularAt hz.2⟩
    calc
      phaseMeasure Q ((billiardFlow Q t) ⁻¹' A) =
          (volume Q.table)⁻¹ * ambientMeasure R := by
        rw [phaseMeasure_eq_regularAt Q t, Measure.smul_apply,
          Measure.restrict_apply (hA.preimage (measurable_billiardFlow_time Q t)), smul_eq_mul]
      _ = (volume Q.table)⁻¹ * ambientMeasure (billiardFlow Q t '' R) := by rw [hmeasure]
      _ ≤ (volume Q.table)⁻¹ * ambientMeasure (A ∩ (Q.table ×ˢ univ)) :=
        by gcongr
      _ = phaseMeasure Q A := by
        rw [phaseMeasure_eq_restrict, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
  · rw [Measure.map_apply (measurable_billiardFlow_time Q t) MeasurableSet.univ, preimage_univ]

/-- Geometric and nonvacuity conclusions for every nondegenerate triangle.
Only ergodicity requires an irrational angle. -/
theorem geometric_obligations (Q : Triangle) :
    phaseMeasure Q univ = 1 ∧
    (∀ᵐ z ∂phaseMeasure Q, Nonempty (FlightChain Q z)) ∧
    (∀ (z : Phase) (c d : FlightChain Q z), c = d) ∧
    (∀ t : ℝ, MeasurePreserving (billiardFlow Q t) (phaseMeasure Q) (phaseMeasure Q)) ∧
    (∀ s t : ℝ, billiardFlow Q (s + t) =ᵐ[phaseMeasure Q]
      (billiardFlow Q s ∘ billiardFlow Q t)) :=
  ⟨phaseMeasure_univ Q, ae_exists_chain Q, fun _ c d => c.unique d,
    measurePreserving_billiardFlow Q, billiardFlow_cocycle Q⟩

end TriangularBilliards

end

end OAI
