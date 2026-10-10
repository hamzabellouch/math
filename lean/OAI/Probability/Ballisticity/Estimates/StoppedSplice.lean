import Mathlib
import OAI.Probability.Ballisticity.Estimates.IndependentRandomTestBound

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma independent_diagonal_lintegral {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V)
    (hind : IndepFun U V μ) (F : A × B → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, F (U ω,V ω) ∂μ) = ∫⁻ η, ∫⁻ ξ, F (U η,V ξ) ∂μ ∂μ := by
  rw [←lintegral_map hF (hU.prodMk hV),
    hind.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable,
    lintegral_prod _ hF.aemeasurable]
  have hm : Measurable (fun a => ∫⁻ b, F (a,b) ∂μ.map V) :=
    Measurable.lintegral_prod_right (f:=fun a b => F (a,b)) hF
  rw [lintegral_map hm hU]
  apply lintegral_congr
  intro η
  exact lintegral_map (hF.comp measurable_prodMk_left) hV

lemma fresh_rows_diagonal_lintegral {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (F : Environment d × Environment d → ℝ≥0∞)
    (hF : @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma T)) _ F) :
    (∫⁻ ω, F (ω,ω) ∂environmentLaw ν)=
      ∫⁻ η, ∫⁻ ξ, F (η,ξ) ∂environmentLaw ν ∂environmentLaw ν := by
  have hU : @Measurable (Environment d) (Environment d) inferInstance (rowSigma S) id :=
    measurable_id.mono le_rfl (rowSigma_le S)
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  exact @independent_diagonal_lintegral (Environment d) (Environment d) (Environment d)
    inferInstance (rowSigma S) (rowSigma T) (environmentLaw ν) inferInstance id id hU hV
    (@indepFun_of_disjoint_rows d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
      ν _ S T hST id id measurable_id measurable_id) F hF

noncomputable def rowGraft {d : ℕ} (S : Set (Lattice d))
    (η ξ : Environment d) : Environment d := fun x => if x∈S then η x else ξ x

lemma rowGraft_diagonal {d : ℕ} (S : Set (Lattice d)) (ω : Environment d) :
    rowGraft S ω ω=ω := by ext x; simp [rowGraft]

lemma rowGraft_measurable_rows {d : ℕ} (S : Set (Lattice d)) :
    @Measurable (Environment d×Environment d) (Environment d)
      (MeasurableSpace.prod (rowSigma S) (rowSigma Sᶜ)) inferInstance
      (fun p => rowGraft S p.1 p.2) := by
  apply @Measurable.of_eval (Environment d×Environment d) (Lattice d) (fun _ => Row d)
    (MeasurableSpace.prod (rowSigma S) (rowSigma Sᶜ)) (fun _ => inferInstance)
  intro x
  by_cases hx : x∈S
  · simp only [rowGraft,ite_eq_left hx]
    exact (measurable_row_on hx).comp measurable_fst
  · simp only [rowGraft,ite_eq_right hx]
    exact (measurable_row_on hx).comp measurable_snd

lemma rowGraft_measurable {d : ℕ} (S : Set (Lattice d)) :
    Measurable (fun p : Environment d×Environment d => rowGraft S p.1 p.2) := by
  apply Measurable.of_eval
  intro x
  by_cases hx : x∈S
  · simp only [rowGraft,ite_eq_left hx]
    exact (measurable_pi_apply x).comp measurable_fst
  · simp only [rowGraft,ite_eq_right hx]
    exact (measurable_pi_apply x).comp measurable_snd

lemma rowGraft_event_lintegral {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (S : Set (Lattice d)) (A : Set (Environment d))
    (hA : MeasurableSet[rowSigma S] A)
    (f : Environment d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ η, ∫⁻ ξ, A.indicator (fun ω => f (rowGraft S ω ξ)) η
      ∂environmentLaw ν ∂environmentLaw ν)=
      ∫⁻ ω, A.indicator f ω ∂environmentLaw ν := by
  have hF : @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma Sᶜ)) _
      (fun p : Environment d×Environment d => A.indicator
        (fun ω => f (rowGraft S ω p.2)) p.1) := by
    change @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma Sᶜ)) _
      ((Prod.fst ⁻¹' A).indicator (fun p => f (rowGraft S p.1 p.2)))
    exact (hf.comp (rowGraft_measurable_rows S)).indicator (hA.preimage measurable_fst)
  rw [←fresh_rows_diagonal_lintegral ν disjoint_compl_right _ hF]
  apply lintegral_congr
  intro ω
  by_cases hω : ω∈A
  · simp [hω,rowGraft_diagonal]
  · simp [hω]

noncomputable def stoppedRowGraft {d : ℕ} (S : ℕ → Set (Lattice d))
    (τ : Environment d → ℕ) (η ξ : Environment d) : Environment d :=
  rowGraft (S (τ η)) η ξ

lemma stoppedRowGraft_measurable {d : ℕ} (S : ℕ → Set (Lattice d))
    (τ : Environment d → ℕ) (hτ : Measurable τ) :
    Measurable (fun p : Environment d×Environment d => stoppedRowGraft S τ p.1 p.2) := by
  have hm : Measurable (fun p : (Environment d×Environment d)×ℕ =>
      rowGraft (S p.2) p.1.1 p.1.2) :=
    measurable_from_prod_countable_left (fun n => rowGraft_measurable (S n))
  exact hm.comp (measurable_id.prodMk (hτ.comp measurable_fst))

theorem stoppedRowGraft_lintegral {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (f : Environment d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ η, ∫⁻ ξ, f (stoppedRowGraft S τ η ξ) ∂environmentLaw ν ∂environmentLaw ν)=
      ∫⁻ ω, f ω ∂environmentLaw ν := by
  let G (n : ℕ) (η ξ : Environment d) := {ω | τ ω=n}.indicator
    (fun ω => f (rowGraft (S n) ω ξ)) η
  have hG (n : ℕ) : Measurable (Function.uncurry (G n)) := by
    change Measurable ((Prod.fst ⁻¹' {ω | τ ω=n}).indicator
      (fun p : Environment d×Environment d => f (rowGraft (S n) p.1 p.2)))
    exact (hf.comp (rowGraft_measurable (S n))).indicator
      (((rowSigma_le _) _ (hτ n)).preimage measurable_fst)
  have he (η ξ : Environment d) : f (stoppedRowGraft S τ η ξ)=∑' n, G n η ξ := by
    rw [tsum_eq_single (τ η)]
    · simp [G,stoppedRowGraft]
    · intro n hn
      simp [G,Ne.symm hn]
  simp_rw [he]
  have hin (η : Environment d) :
      (∫⁻ ξ, ∑' n, G n η ξ ∂environmentLaw ν)=
        ∑' n, ∫⁻ ξ, G n η ξ ∂environmentLaw ν :=
    lintegral_tsum (fun n => ((hG n).comp (measurable_const.prodMk measurable_id)).aemeasurable)
  simp_rw [hin]
  rw [lintegral_tsum (fun n => (hG n).lintegral_prod_right.aemeasurable)]
  simp_rw [show ∀ n, (∫⁻ η, ∫⁻ ξ, G n η ξ ∂environmentLaw ν ∂environmentLaw ν)=
      ∫⁻ ω, {ω | τ ω=n}.indicator f ω ∂environmentLaw ν from
    fun n => rowGraft_event_lintegral ν (S n) _ (hτ n) f hf]
  rw [←lintegral_tsum (fun n => (hf.indicator ((rowSigma_le _) _ (hτ n))).aemeasurable)]
  apply lintegral_congr
  intro ω
  rw [tsum_eq_single (τ ω)]
  · simp
  · intro n hn
    simp [Ne.symm hn]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma rowSigma_eq_comap {d : ℕ} (S : Set (Lattice d)) :
    rowSigma S=MeasurableSpace.comap (fun ω : Environment d => S.domRestrict ω) inferInstance := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    have hr : @Measurable (Environment d) (S → Row d)
        (MeasurableSpace.comap (fun ω : Environment d => S.domRestrict ω) inferInstance) inferInstance
        (fun ω => S.domRestrict ω) := Measurable.of_comap_le le_rfl
    exact ((measurable_pi_apply (⟨x,hx⟩ : S)).comp hr).comap_le
  · apply Measurable.comap_le
    exact @Measurable.of_eval (Environment d) S (fun _ => Row d) (rowSigma S)
      (fun _ => inferInstance) (fun ω => S.domRestrict ω) (fun x => measurable_row_on x.property)

lemma rowSigma_event_congr {d : ℕ} (S : Set (Lattice d)) (A : Set (Environment d))
    (hA : MeasurableSet[rowSigma S] A) {η ξ : Environment d}
    (hrows : ∀ x∈S, η x=ξ x) : η∈A ↔ ξ∈A := by
  rw [rowSigma_eq_comap] at hA
  obtain ⟨B,_,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
  have he : S.domRestrict η=S.domRestrict ξ := funext fun x => hrows x.val x.property
  change S.domRestrict η∈B ↔ S.domRestrict ξ∈B
  rw [he]

lemma rowGraft_rows {d : ℕ} (S : Set (Lattice d)) (η ξ : Environment d) :
    ∀ x∈S, rowGraft S η ξ x=η x := by intro x hx; simp [rowGraft,hx]

lemma stoppedRowGraft_stop {d : ℕ} (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n}) (η ξ : Environment d) :
    τ (stoppedRowGraft S τ η ξ)=τ η := by
  exact (rowSigma_event_congr (S (τ η)) _ (hτ (τ η))
    (rowGraft_rows (S (τ η)) η ξ)).mpr rfl

def StoppedRowsEvent {d : ℕ} (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (A : Set (Environment d)) : Prop :=
  ∀ n, MeasurableSet[rowSigma (S n)] (A∩{ω | τ ω=n})

lemma stoppedRowGraft_event {d : ℕ} (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (A : Set (Environment d)) (hA : StoppedRowsEvent S τ A) (η ξ : Environment d) :
    stoppedRowGraft S τ η ξ∈A ↔ η∈A := by
  have hh := rowSigma_event_congr (S (τ η)) _ (hA (τ η))
    (rowGraft_rows (S (τ η)) η ξ)
  change (stoppedRowGraft S τ η ξ∈A ∧ τ (stoppedRowGraft S τ η ξ)=τ η) ↔
    (η∈A ∧ τ η=τ η) at hh
  simpa only [stoppedRowGraft_stop S τ hτ η ξ,and_true] using hh

lemma stoppedRowGraft_observable {d : ℕ} {D : Type*} [MeasurableSpace D]
    [MeasurableSingletonClass D] (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (U : Environment d → D)
    (hU : ∀ B, MeasurableSet B → StoppedRowsEvent S τ (U ⁻¹' B)) (η ξ : Environment d) :
    U (stoppedRowGraft S τ η ξ)=U η := by
  exact (stoppedRowGraft_event S τ hτ _ (hU {U η} (measurableSet_singleton _)) η ξ).mpr rfl

lemma measurable_of_stop_events {d : ℕ} (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n}) : Measurable τ := by
  apply measurable_to_countable
  intro ω
  exact (rowSigma_le _) _ (hτ (τ ω))

theorem stoppedRowGraft_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n}) :
    ((environmentLaw ν).prod (environmentLaw ν)).map
      (fun p => stoppedRowGraft S τ p.1 p.2)=environmentLaw ν := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (stoppedRowGraft_measurable S τ (measurable_of_stop_events S τ hτ))]
  have hm : Measurable (fun p : Environment d×Environment d => f (stoppedRowGraft S τ p.1 p.2)) :=
    hf.comp (stoppedRowGraft_measurable S τ (measurable_of_stop_events S τ hτ))
  exact (lintegral_prod _ hm.aemeasurable).trans (stoppedRowGraft_lintegral ν S τ hτ f hf)

theorem stoppedRowGraft_joint_map {d : ℕ} {D : Type*} [MeasurableSpace D]
    [MeasurableSingletonClass D] (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (U : Environment d → D) (hUm : Measurable U)
    (hU : ∀ B, MeasurableSet B → StoppedRowsEvent S τ (U ⁻¹' B)) :
    ((environmentLaw ν).prod (environmentLaw ν)).map
      (fun p => (U p.1,stoppedRowGraft S τ p.1 p.2))=
        (environmentLaw ν).map (fun ω => (U ω,ω)) := by
  calc
    _ = ((environmentLaw ν).prod (environmentLaw ν)).map
        ((fun ω => (U ω,ω)) ∘ fun p => stoppedRowGraft S τ p.1 p.2) := by
      congr 1
      funext p
      simp only [Function.comp_apply,stoppedRowGraft_observable S τ hτ U hU]
    _ = (((environmentLaw ν).prod (environmentLaw ν)).map
        (fun p => stoppedRowGraft S τ p.1 p.2)).map (fun ω => (U ω,ω)) :=
      (Measure.map_map (hUm.prodMk measurable_id)
        (stoppedRowGraft_measurable S τ (measurable_of_stop_events S τ hτ))).symm
    _ = _ := by rw [stoppedRowGraft_map ν S τ hτ]

end DirectionalTransience

end

end OAI
