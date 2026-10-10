import Mathlib
import OAI.Probability.Perceptron.Variational.FocusedShapeProbability
import OAI.Probability.Perceptron.Cascade.IndexedPoisson
import OAI.Probability.Perceptron.Variational.InfinitePiSplit

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

lemma law_count_iid_zip {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (r : ℝ≥0) (ρ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] :
    (((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => ρ))).prod
      (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => (p.1.1, fun j => (p.1.2 j,p.2 j))) =
      (poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => ρ.prod ν)) := by
  let z : ((ℕ → A) × (ℕ → B)) → ℕ → A × B := fun p j => (p.1 j,p.2 j)
  have hz : Measurable z := by fun_prop
  calc
    _ = ((((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => ρ))).prod
      (Measure.infinitePi (fun _ : ℕ => ν))).map
        (MeasurableEquiv.prodAssoc : ((ℕ × (ℕ → A)) × (ℕ → B)) ≃ᵐ (ℕ × ((ℕ → A) × (ℕ → B))))).map (Prod.map id z) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [Measure.prodAssoc_prod, ← Measure.map_prod_map _ _ measurable_id hz,
        Measure.map_id, infinitePi_zip]

lemma indexedMarkedPoisson_law {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (r : ℕ → ℝ≥0) (ρ : ℕ → Measure A) (ν : Measure B)
    [∀ i, IsProbabilityMeasure (ρ i)] [IsProbabilityMeasure ν] :
    ((Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
      (Measure.infinitePi (fun _ : ℕ => ρ i)))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν)))).map
        (fun p => indexedPoissonMeasure (fun i => (p.1 i |>.1,
          fun j => ((p.1 i).2 j,p.2 i j)))) =
        countablePoissonLaw r (fun i => (ρ i).prod ν) := by
  let z : (ℕ × (ℕ → A)) × (ℕ → B) → ℕ × (ℕ → A × B) :=
    fun p => (p.1.1,fun j => (p.1.2 j,p.2 j))
  have hz : Measurable z := by fun_prop
  let L := Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
      (Measure.infinitePi (fun _ : ℕ => ρ i)))
  let M := Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν))
  have hp : (L.prod M).map (fun p i => z (p.1 i,p.2 i)) =
      Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
        (Measure.infinitePi (fun _ : ℕ => (ρ i).prod ν))) := by
    calc
      _ = ((L.prod M).map (fun p i => (p.1 i,p.2 i))).map (fun p i => z (p i)) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = _ := by
        dsimp [L,M]
        rw [infinitePi_zip, Measure.infinitePi_map_pi]
        simp_rw [show ∀ i, ((poissonMeasure (r i)).prod
          (Measure.infinitePi (fun _ : ℕ => ρ i)) |>.prod
            (Measure.infinitePi (fun _ : ℕ => ν))).map z =
            (poissonMeasure (r i)).prod (Measure.infinitePi (fun _ : ℕ => (ρ i).prod ν))
          from fun i => law_count_iid_zip (r i) (ρ i) ν]
        exact fun _ => hz
  change (L.prod M).map (indexedPoissonMeasure ∘ (fun p i => z (p.1 i,p.2 i))) = _
  rw [← Measure.map_map indexedPoissonMeasure_measurable (by fun_prop),hp,
    indexedPoissonMeasure_law]

lemma countablePoissonLaw_product_intensity {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [Nonempty A] [Nonempty B]
    (κ : Measure A) [SFinite κ] (ν : Measure B) [IsProbabilityMeasure ν] :
    countablePoissonLaw (fun i => ((sfiniteSeq κ i) univ).toNNReal)
      (fun i => (finiteIntensityMarks (sfiniteSeq κ i)).prod ν) =
        poissonRandomMeasureLaw (κ.prod ν) := by
  apply measureLaw_eq_of_laplace
  intro f hf hf0
  rw [countablePoissonLaw_laplace_intensity _ _ hf hf0,
    poissonRandomMeasureLaw_laplace _ hf hf0]
  congr 2
  have he : countablePoissonIntensity (fun i => ((sfiniteSeq κ i) univ).toNNReal)
      (fun i => (finiteIntensityMarks (sfiniteSeq κ i)).prod ν) = κ.prod ν := by
    unfold countablePoissonIntensity
    simp_rw [← Measure.prod_smul_left, finiteIntensityMarks_smul]
    rw [← Measure.prod_sum_left,sum_sfiniteSeq]
  rw [he]

lemma indexedMarkedPoisson_canonical_law {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [Nonempty A] [Nonempty B]
    (κ : Measure A) [SFinite κ] (ν : Measure B) [IsProbabilityMeasure ν] :
    ((Measure.infinitePi (fun i =>
      (poissonMeasure (((sfiniteSeq κ i) univ).toNNReal)).prod
        (Measure.infinitePi (fun _ : ℕ => finiteIntensityMarks (sfiniteSeq κ i))))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν)))).map
        (fun p => indexedPoissonMeasure (fun i => ((p.1 i).1,
          fun j => ((p.1 i).2 j,p.2 i j)))) =
        poissonRandomMeasureLaw (κ.prod ν) := by
  rw [indexedMarkedPoisson_law,countablePoissonLaw_product_intensity]

@[reducible] def IndexedCascadeBase : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (ℕ → ℕ × (ℕ → ℝ × IndexedCascadeBase n))

@[reducible] def IndexedCascadeMarks (S : Type) [MeasurableSpace S] : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (ℕ → ℕ → S × IndexedCascadeMarks S n)

instance indexedCascadeBase_nonempty (n : ℕ) : Nonempty (IndexedCascadeBase n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => dsimp [IndexedCascadeBase]; infer_instance

instance indexedCascadeMarks_nonempty (S : Type) [MeasurableSpace S] [Nonempty S] (n : ℕ) :
    Nonempty (IndexedCascadeMarks S n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => dsimp [IndexedCascadeMarks]; infer_instance

def indexedCascadeBaseLaw : (n : ℕ) → (Fin n → ℝ) → ProbabilityMeasure (IndexedCascadeBase n)
  | 0,_ => ⟨Measure.dirac (),inferInstance⟩
  | n+1,z => ⟨Measure.infinitePi (fun i =>
      (poissonMeasure (((sfiniteSeq (stableLogIntensity (z 0)) i) univ).toNNReal)).prod
        (Measure.infinitePi (fun _ : ℕ =>
          (finiteIntensityMarks (sfiniteSeq (stableLogIntensity (z 0)) i)).prod
            (indexedCascadeBaseLaw n (fun j => z j.succ))))),by infer_instance⟩

def indexedCascadeMarksLaw {S : Type} [MeasurableSpace S] (ν : ProbabilityMeasure S) :
    (n : ℕ) → ProbabilityMeasure (IndexedCascadeMarks S n)
  | 0 => ⟨Measure.dirac (),inferInstance⟩
  | n+1 => ⟨Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      (ν : Measure S).prod (indexedCascadeMarksLaw ν n))),by infer_instance⟩

def indexedCascadeRealize {S : Type} [MeasurableSpace S] : (n : ℕ) →
    IndexedCascadeBase n × IndexedCascadeMarks S n → DecoratedCascade S n
  | 0,_ => ()
  | n+1,p => indexedPoissonMeasure (fun i => ((p.1 i).1,fun j =>
      (((p.1 i).2 j).1,((p.2 i j).1,
        indexedCascadeRealize n (((p.1 i).2 j).2,(p.2 i j).2)))))

lemma indexedCascadeRealize_measurable {S : Type} [MeasurableSpace S] (n : ℕ) :
    Measurable (indexedCascadeRealize (S := S) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    dsimp only [indexedCascadeRealize]
    apply indexedPoissonMeasure_measurable.comp
    fun_prop

instance countablePoissonIntensity_sfinite {A : Type*} [MeasurableSpace A]
    (r : ℕ → ℝ≥0) (ρ : ℕ → Measure A) [∀ i, IsProbabilityMeasure (ρ i)] :
    SFinite (countablePoissonIntensity r ρ) := by
  unfold countablePoissonIntensity
  infer_instance

lemma countablePoissonLaw_eq_canonical {A : Type*} [MeasurableSpace A] [Nonempty A]
    (r : ℕ → ℝ≥0) (ρ : ℕ → Measure A) [∀ i, IsProbabilityMeasure (ρ i)] :
    countablePoissonLaw r ρ = poissonRandomMeasureLaw (countablePoissonIntensity r ρ) := by
  apply measureLaw_eq_of_laplace
  intro f hf hf0
  rw [countablePoissonLaw_laplace_intensity _ _ hf hf0,
    poissonRandomMeasureLaw_laplace _ hf hf0]

lemma prod_rotate_front {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (τ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite τ] :
    (μ.prod (ν.prod τ)).map (fun p => (p.2.1,(p.1,p.2.2))) = ν.prod (μ.prod τ) := by
  have h := (measurePreserving_prodAssoc ν μ τ).comp
    (((Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id τ)).comp
      (measurePreserving_prodAssoc μ ν τ).symm)
  exact h.map_eq

lemma indexedPoissonMeasure_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {g : A → B} (hg : Measurable g) (a : ℕ → ℕ × (ℕ → A)) :
    (indexedPoissonMeasure a).map g =
      indexedPoissonMeasure (fun i => ((a i).1,fun j => g ((a i).2 j))) := by
  unfold indexedPoissonMeasure indexedFiniteCloud finitePointMeasure
  rw [Measure.map_sum hg.aemeasurable]
  simp_rw [Measure.map_finset_sum hg.aemeasurable,Measure.map_dirac' hg]

lemma prod_interlace_law {A B C D E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E]
    (α : Measure A) (β : Measure B) (γ : Measure C) (δ : Measure D) (ε : Measure E)
    [SFinite α] [SFinite β] [SFinite γ] [SFinite δ] [SFinite ε]
    {g : B × D → E} (hg : MeasurePreserving g (β.prod δ) ε) :
    ((α.prod β).prod (γ.prod δ)).map
      (fun p => (p.1.1,(p.2.1,g (p.1.2,p.2.2)))) = α.prod (γ.prod ε) := by
  have h₁ := measurePreserving_prodAssoc α β (γ.prod δ)
  have h₂ : MeasurePreserving (fun p : B × (C × D) => (p.2.1,(p.1,p.2.2)))
      (β.prod (γ.prod δ)) (γ.prod (β.prod δ)) :=
    ⟨by fun_prop,prod_rotate_front β γ δ⟩
  exact (((MeasurePreserving.id α).prod ((MeasurePreserving.id γ).prod hg)).comp
    (((MeasurePreserving.id α).prod h₂).comp h₁)).map_eq

lemma indexedCascadeRealize_law {S : Type} [MeasurableSpace S] [Nonempty S]
    (ν : ProbabilityMeasure S) (n : ℕ) (z : Fin n → ℝ) :
    ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n)).map (indexedCascadeRealize n) =
        (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) := by
  induction n with
  | zero => simp [indexedCascadeBaseLaw,indexedCascadeMarksLaw,indexedCascadeRealize,decoratedCascadeLaw]
  | succ n ih =>
    let κ := stableLogIntensity (z 0)
    let r : ℕ → ℝ≥0 := fun i => ((sfiniteSeq κ i) univ).toNNReal
    let ρ := fun i => finiteIntensityMarks (sfiniteSeq κ i)
    let B := (indexedCascadeBaseLaw n (fun j => z j.succ) : Measure (IndexedCascadeBase n))
    let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))
    let D := (decoratedCascadeLaw ν n (fun j => z j.succ) : Measure (DecoratedCascade S n))
    let f : ((ℝ × IndexedCascadeBase n) × (S × IndexedCascadeMarks S n)) →
        ℝ × (S × DecoratedCascade S n) :=
      fun p => (p.1.1,(p.2.1,indexedCascadeRealize n (p.1.2,p.2.2)))
    have hf : Measurable f := by
      exact measurable_fst.fst.prodMk (measurable_snd.fst.prodMk
        ((indexedCascadeRealize_measurable n).comp (measurable_fst.snd.prodMk measurable_snd.snd)))
    have hR : MeasurePreserving (indexedCascadeRealize (S := S) n) (B.prod M) D :=
      ⟨indexedCascadeRealize_measurable n,ih (fun j => z j.succ)⟩
    have hi : (countablePoissonIntensity r (fun i => (ρ i).prod B |>.prod ((ν : Measure S).prod M))).map f =
        κ.prod ((ν : Measure S).prod D) := by
      unfold countablePoissonIntensity
      rw [Measure.map_sum hf.aemeasurable]
      simp_rw [Measure.map_smul _ hf.aemeasurable]
      have hfi (i : ℕ) : (((ρ i).prod B).prod ((ν : Measure S).prod M)).map f =
          (ρ i).prod ((ν : Measure S).prod D) :=
        prod_interlace_law (ρ i) B (ν : Measure S) M D hR
      simp_rw [hfi]
      dsimp only [r,ρ]
      simp_rw [← Measure.prod_smul_left,finiteIntensityMarks_smul]
      rw [← Measure.prod_sum_left,sum_sfiniteSeq]
    let P := Measure.infinitePi (fun i => (poissonMeasure (r i)).prod
      (Measure.infinitePi (fun _ : ℕ => (ρ i).prod B)))
    let Q := Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (ν : Measure S).prod M))
    let a : ((ℕ → ℕ × (ℕ → ℝ × IndexedCascadeBase n)) ×
      (ℕ → ℕ → S × IndexedCascadeMarks S n)) →
        ℕ → ℕ × (ℕ → (ℝ × IndexedCascadeBase n) × (S × IndexedCascadeMarks S n)) :=
      fun p i => ((p.1 i).1,fun j => ((p.1 i).2 j,p.2 i j))
    have ha : Measurable a := by fun_prop
    have he : indexedCascadeRealize (S := S) (n+1) =
        Measure.map f ∘ (indexedPoissonMeasure ∘ a) := by
      funext p
      exact (indexedPoissonMeasure_map hf (a p)).symm
    change (P.prod Q).map (indexedCascadeRealize (S := S) (n+1)) =
      poissonRandomMeasureLaw (κ.prod ((ν : Measure S).prod D))
    rw [he,← Measure.map_map (Measure.measurable_map f hf)
      (indexedPoissonMeasure_measurable.comp ha)]
    have hP := indexedMarkedPoisson_law r (fun i => (ρ i).prod B) ((ν : Measure S).prod M)
    change (P.prod Q).map (indexedPoissonMeasure ∘ a) = _ at hP
    rw [hP,countablePoissonLaw_eq_canonical,poissonRandomMeasureLaw_map _ hf]
    congr 1

end SphericalPerceptronFreeEnergy

end

end OAI
