import Mathlib
import OAI.Probability.Ballisticity.Coupling.StoppedFreshField

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma stop_observable {d : ℕ} (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (B : Set ℕ) : StoppedRowsEvent S τ (τ ⁻¹' B) := by
  intro n
  by_cases hn : n∈B
  · have he : (τ ⁻¹' B)∩{ω | τ ω=n}={ω | τ ω=n} := by
      ext ω; simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq]
      exact ⟨And.right,fun h => ⟨h ▸ hn,h⟩⟩
    rw [he]; exact hτ n
  · have he : (τ ⁻¹' B)∩{ω | τ ω=n}=∅ := by
      ext ω; simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      rintro ⟨hb,h⟩; exact hn (h ▸ hb)
    rw [he]; exact @MeasurableSet.empty _ (rowSigma (S n))

lemma upperField_joint_measurable {d : ℕ} (e : Direction d) :
    Measurable (fun p : Environment d×ℕ => upperField e p.2 p.1) := by
  apply measurable_from_prod_countable_left
  intro n
  exact (upperField_measurable_rows e n).mono (rowSigma_le _) le_rfl

lemma belowHeight_mono {d : ℕ} (e : Direction d) :
    Monotone (fun n : ℕ => BelowHeight (realPosition (step e)) n) := by
  intro n m h x hx
  change dot (realPosition x) (realPosition (step e))<(n:ℝ) at hx
  change dot (realPosition x) (realPosition (step e))<(m:ℝ)
  exact lt_of_lt_of_le hx (by exact_mod_cast h)

theorem twoStopSplice_fresh {d : ℕ} {D : Type*} [MeasurableSpace D]
    [MeasurableSingletonClass D] (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (U : Environment d → D) (hUm : Measurable U)
    (hU : ∀ B, MeasurableSet B →
      StoppedRowsEvent (fun n => BelowHeight (realPosition (step e)) n) τ (U ⁻¹' B)) :
    ((environmentLaw ν).prod (environmentLaw ν)).map
      (fun p => (U p.1,upperField e (τ p.1)
        (stoppedRowGraft (fun n => BelowHeight (realPosition (step e)) n) σ p.1 p.2))) =
    ((environmentLaw ν).map U).prod (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)) := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  let G : Environment d×Environment d → Environment d := fun p => stoppedRowGraft S σ p.1 p.2
  have hUσ : ∀ B, MeasurableSet B → StoppedRowsEvent S σ (U ⁻¹' B) := by
    intro B hB
    exact stoppedRowsEvent_mono S (belowHeight_mono e) τ σ hτσ hσ _ (hU B hB)
  have hτσobs : ∀ B, MeasurableSet B → StoppedRowsEvent S σ (τ ⁻¹' B) := by
    intro B _
    exact stoppedRowsEvent_mono S (belowHeight_mono e) τ σ hτσ hσ _ (stop_observable S τ hτ B)
  have hUG (p : Environment d×Environment d) : U (G p)=U p.1 :=
    stoppedRowGraft_observable S σ hσ U hUσ p.1 p.2
  have hτG (p : Environment d×Environment d) : τ (G p)=τ p.1 :=
    stoppedRowGraft_observable S σ hσ τ hτσobs p.1 p.2
  have hFm : Measurable (fun ω => (U ω,upperField e (τ ω) ω)) :=
    hUm.prodMk ((upperField_joint_measurable e).comp
      (measurable_id.prodMk (measurable_of_stop_events S τ hτ)))
  have hGm : Measurable G := stoppedRowGraft_measurable S σ (measurable_of_stop_events S σ hσ)
  calc
    _ = ((environmentLaw ν).prod (environmentLaw ν)).map
        ((fun ω => (U ω,upperField e (τ ω) ω)) ∘ G) := by
      congr 1
      funext p
      simp only [Function.comp_apply,hUG,hτG]
      rfl
    _ = (((environmentLaw ν).prod (environmentLaw ν)).map G).map
        (fun ω => (U ω,upperField e (τ ω) ω)) := (Measure.map_map hFm hGm).symm
    _ = (environmentLaw ν).map (fun ω => (U ω,upperField e (τ ω) ω)) := by
      rw [show ((environmentLaw ν).prod (environmentLaw ν)).map G=environmentLaw ν from
        stoppedRowGraft_map ν S σ hσ]
    _ = _ := stopped_fresh_joint_map ν S τ hτ U hUm hU (upperField e)
      (upperField_measurable_rows e) _ (upperField_map e ν)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

instance row_standardBorel (d : ℕ) : StandardBorelSpace (Row d) :=
  (show MeasurableSet {p : Direction d → ℝ≥0 | ∑ e, p e = 1} from
    (isClosed_eq (by fun_prop) continuous_const).measurableSet).standardBorel

noncomputable def stoppedObservation {d : ℕ} (S : ℕ → Set (Lattice d))
    (τ : Environment d → ℕ) (filler : Environment d) : Environment d → Environment d :=
  fun ω => stoppedRowGraft S τ ω filler

lemma stoppedObservation_measurable {d : ℕ} (S : ℕ → Set (Lattice d))
    (τ : Environment d → ℕ) (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (filler : Environment d) : Measurable (stoppedObservation S τ filler) :=
  (stoppedRowGraft_measurable S τ (measurable_of_stop_events S τ hτ)).comp
    (measurable_id.prodMk measurable_const)

lemma rowGraft_fixed_measurable_rows {d : ℕ} (S : Set (Lattice d))
    (filler : Environment d) :
    @Measurable (Environment d) (Environment d) (rowSigma S) inferInstance
      (fun ω => rowGraft S ω filler) :=
  (rowGraft_measurable_rows S).comp (measurable_id.prodMk measurable_const)

lemma stoppedObservation_observable {d : ℕ} (S : ℕ → Set (Lattice d))
    (τ : Environment d → ℕ) (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (filler : Environment d) (B : Set (Environment d)) (hB : MeasurableSet B) :
    StoppedRowsEvent S τ (stoppedObservation S τ filler ⁻¹' B) := by
  intro n
  have he : (stoppedObservation S τ filler ⁻¹' B) ∩ {ω | τ ω=n} =
      ((fun ω => rowGraft (S n) ω filler) ⁻¹' B) ∩ {ω | τ ω=n} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨hb, hn⟩ <;> refine ⟨?_, hn⟩
    · simpa only [stoppedObservation, stoppedRowGraft, hn] using hb
    · simpa only [stoppedObservation, stoppedRowGraft, hn] using hb
  rw [he]
  exact (hB.preimage (rowGraft_fixed_measurable_rows (S n) filler)).inter (hτ n)

lemma stoppedObservation_nested {d : ℕ} (S : ℕ → Set (Lattice d)) (hS : Monotone S)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (hσ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | σ ω=n})
    (filler η ξ : Environment d) :
    stoppedObservation S τ filler (stoppedRowGraft S σ η ξ) =
      stoppedObservation S τ filler η := by
  apply stoppedRowGraft_observable S σ hσ
  intro B hB
  exact stoppedRowsEvent_mono S hS τ σ hτσ hσ _
    (stoppedObservation_observable S τ hτ filler B hB)

lemma stoppedObservation_nested_stop {d : ℕ} (S : ℕ → Set (Lattice d)) (hS : Monotone S)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (hσ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | σ ω=n})
    (filler η : Environment d) : τ (stoppedObservation S σ filler η)=τ η := by
  apply stoppedRowGraft_observable S σ hσ
  intro B _
  exact stoppedRowsEvent_mono S hS τ σ hτσ hσ _ (stop_observable S τ hτ B)

lemma stoppedObservation_regraft {d : ℕ} (S : ℕ → Set (Lattice d))
    (σ : Environment d → ℕ) (hσ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | σ ω=n})
    (filler η ξ : Environment d) :
    stoppedRowGraft S σ (stoppedObservation S σ filler η) ξ = stoppedRowGraft S σ η ξ := by
  have ht : σ (stoppedObservation S σ filler η)=σ η :=
    stoppedRowGraft_stop S σ hσ η filler
  change rowGraft (S (σ (stoppedObservation S σ filler η)))
    (stoppedObservation S σ filler η) ξ = rowGraft (S (σ η)) η ξ
  rw [ht]
  funext x
  by_cases hx : x ∈ S (σ η) <;> simp [rowGraft, hx, stoppedObservation, stoppedRowGraft]

end DirectionalTransience

end

end OAI
