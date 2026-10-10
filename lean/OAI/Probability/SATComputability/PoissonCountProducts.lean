import OAI.Probability.SATComputability.FinitePushforward
import OAI.Probability.DilutedSpin.FiniteEncoding

namespace OAI

namespace FixedClauseThreshold.Computability

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

noncomputable def poissonCountLaw (A : Type*) [Fintype A] (r : ℝ≥0) : Measure (A → ℕ) :=
  Measure.pi (fun _ : A => poissonMeasure r)

instance poissonCountLaw_probability (A : Type*) [Fintype A] (r : ℝ≥0) :
    IsProbabilityMeasure (poissonCountLaw A r) := by unfold poissonCountLaw; infer_instance

theorem poissonCountLaw_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (r : ℝ≥0) (f : (B → ℕ) → ℝ) :
    (∫ c, f (fun b => c (e.symm b)) ∂poissonCountLaw A r) =
      ∫ c, f c ∂poissonCountLaw B r := by
  have hp (c : A → ℕ) : (MeasurableEquiv.piCongrLeft (fun _ : B => ℕ) e) c =
      fun b => c (e.symm b) := by
    funext b
    change (Equiv.piCongrLeft (fun _ : B => ℕ) e) c b = _
    rw [Equiv.piCongrLeft_apply]
    simp
  simpa only [poissonCountLaw, hp] using
    (measurePreserving_piCongrLeft (fun _ : B => poissonMeasure r) e).integral_comp' f

theorem poissonCountLaw_sum {A B : Type*} [Fintype A] [Fintype B]
    (r : ℝ≥0) (f : (A ⊕ B → ℕ) → ℝ) (C : ℝ) (hC : ∀ c, |f c| ≤ C) :
    (∫ c, f c ∂poissonCountLaw (A ⊕ B) r) =
      ∫ a, ∫ b, f (Sum.elim a b) ∂poissonCountLaw B r ∂poissonCountLaw A r := by
  have he := (measurePreserving_sumPiEquivProdPi_symm
    (fun _ : A ⊕ B => poissonMeasure r)).integral_comp' f
  unfold poissonCountLaw
  rw [← he]
  change (∫ p : (A → ℕ) × (B → ℕ), f (Sum.elim p.1 p.2)
    ∂(poissonCountLaw A r).prod (poissonCountLaw B r)) = _
  apply integral_prod
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs] using hC (Sum.elim p.1 p.2)

theorem poisson_zero_eq_dirac : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n <;> simp

theorem poissonCountLaw_hasLaw_sum {A : Type*} [Fintype A]
    (r : A → ℝ≥0) :
    HasLaw (fun c : A → ℕ => ∑ a, c a) (poissonMeasure (∑ a, r a))
      (Measure.pi (fun a => poissonMeasure (r a))) := by
  let μ := Measure.pi (fun a => poissonMeasure (r a))
  have hi : iIndepFun (fun a (c : A → ℕ) => c a) μ :=
    iIndepFun_pi (fun a => measurable_id.aemeasurable)
  have hcoord (a : A) : HasLaw (fun c : A → ℕ => c a) (poissonMeasure (r a)) μ :=
    ⟨(measurable_pi_apply a).aemeasurable, (measurePreserving_eval _ a).map_eq⟩
  have hs (S : Finset A) : HasLaw (fun c : A → ℕ => ∑ a ∈ S, c a)
      (poissonMeasure (∑ a ∈ S, r a)) μ := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, poisson_zero_eq_dirac]
      exact ⟨measurable_const.aemeasurable, by simp⟩
    | @insert a S ha ih =>
      have hind := (hi.indepFun_finsetSum_of_notMem (fun a => measurable_pi_apply a) ha).symm
      have he : (∑ j ∈ S, fun c : A → ℕ => c j) = (fun c => ∑ j ∈ S, c j) := by
        funext c
        simp only [Finset.sum_apply]
      rw [he] at hind
      have h := hind.hasLaw_add_poissonMeasure (hcoord a) ih
      have hf : ((fun c : A → ℕ => c a) + (fun c => ∑ j ∈ S, c j)) =
          (fun c => c a + ∑ j ∈ S, c j) := rfl
      rw [hf] at h
      simpa only [Finset.sum_insert ha] using h
  exact hs Finset.univ

theorem poissonCountLaw_sum_integral {A : Type*} [Fintype A]
    (r : A → ℝ≥0) (f : ℕ → ℝ) :
    (∫ c : A → ℕ, f (∑ a, c a) ∂Measure.pi (fun a => poissonMeasure (r a))) =
      ∫ k, f k ∂poissonMeasure (∑ a, r a) :=
  (poissonCountLaw_hasLaw_sum r).integral_comp (measurable_of_countable f).aestronglyMeasurable

theorem poissonCountLaw_embedding {A B : Type*} [Fintype A] [Fintype B]
    (e : B → A) (he : Function.Injective e) (r : ℝ≥0) :
    Measure.map (fun c : A → ℕ => c ∘ e) (poissonCountLaw A r) =
      poissonCountLaw B r := by
  have hi : iIndepFun (fun a (c : A → ℕ) => c a) (poissonCountLaw A r) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have h := (hi.precomp he).map_fun_eq_pi_map
    (fun b => (measurable_pi_apply (e b)).aemeasurable)
  simpa only [Function.comp_def, poissonCountLaw,
    (measurePreserving_eval (fun _ : A => poissonMeasure r) _).map_eq] using h

theorem poissonCountLaw_embedding_integral {A B : Type*} [Fintype A] [Fintype B]
    (e : B → A) (he : Function.Injective e) (r : ℝ≥0) (f : (B → ℕ) → ℝ) :
    (∫ c, f (c ∘ e) ∂poissonCountLaw A r) = ∫ c, f c ∂poissonCountLaw B r := by
  rw [← poissonCountLaw_embedding e he r]
  exact (integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable).symm

theorem poissonCountLaw_row_sums {A B : Type*} [Fintype A] [Fintype B]
    (r : ℝ≥0) :
    Measure.map (fun c : A → B → ℕ => fun a => ∑ b, c a b)
      (Measure.pi (fun _ : A => poissonCountLaw B r)) =
      poissonCountLaw A (Fintype.card B * r) := by
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)]
  congr 1
  funext a
  simpa only [poissonCountLaw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    (poissonCountLaw_hasLaw_sum (fun _ : B => r)).map_eq

end FixedClauseThreshold.Computability

end OAI
