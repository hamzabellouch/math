import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.FreshSet

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open scoped Classical
open Set MeasureTheory Real
open scoped Interval

namespace CriticalPercolation.Priority
variable {I : Type*} [Fintype I]

instance : NullSingletonClass uniform01 := by
  unfold uniform01
  infer_instance

lemma ae_eval_ne (i j : I) (hji : j ≠ i) :
    ∀ᵐ u : I → ℝ ∂law, u i ≠ u j := by
  have hj : ∀ t : ℝ, ∀ᵐ v : {k : I // k ≠ i} → ℝ ∂law,
      t ≠ v ⟨j,hji⟩ := by
    intro t
    apply ae_iff.mpr
    have hz := Measure.pi_eval_preimage_null
      (fun _ : {k : I // k ≠ i} => uniform01)
      (i := ⟨j,hji⟩) (measure_singleton t)
    have he : {v : {k : I // k ≠ i} → ℝ | ¬t ≠ v ⟨j,hji⟩} =
        (Function.eval ⟨j,hji⟩ : ({k : I // k ≠ i} → ℝ) → ℝ) ⁻¹' {t} := by
      ext v
      simp [eq_comm]
    change law {v : {k : I // k ≠ i} → ℝ | ¬t ≠ v ⟨j,hji⟩} = 0
    rw [he]
    exact hz
  have hp : ∀ᵐ z : ℝ × ({k : I // k ≠ i} → ℝ)
      ∂uniform01.prod law, z.1 ≠ z.2 ⟨j,hji⟩ := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    exact Filter.Eventually.of_forall hj
  exact (split_preserving i).quasiMeasurePreserving.ae hp

lemma ae_injective : ∀ᵐ u : I → ℝ ∂law, Function.Injective u := by
  have h : ∀ i j : I, ∀ᵐ u : I → ℝ ∂law, u i = u j → i = j := by
    intro i j
    by_cases hji : j = i
    · subst j; exact Filter.Eventually.of_forall (fun _ _ => rfl)
    · filter_upwards [ae_eval_ne i j hji] with u hu
      exact fun he => False.elim (hu he)
  change ∀ᵐ u : I → ℝ ∂law, ∀ i j, u i = u j → i = j
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  exact h i

lemma ae_exists_cell : ∀ᵐ u : I → ℝ ∂law, ∃ o : Order I, u ∈ cell o := by
  filter_upwards [ae_injective] with u hu
  exact exists_cell u hu

lemma sum_cell_indicator (f : (I → ℝ) → ℝ) :
    (fun u => ∑ o : Order I, (cell o).indicator f u) =ᵐ[law] f := by
  filter_upwards [ae_exists_cell] with u hu
  obtain ⟨o,ho⟩ := hu
  rw [Finset.sum_eq_single o]
  · exact Set.indicator_of_mem ho f
  · intro b _ hb
    apply Set.indicator_of_notMem
    exact fun hub => Set.disjoint_left.mp (cell_disjoint hb) hub ho
  · simp

lemma sum_integral_cells (f : (I → ℝ) → ℝ) (hf : Integrable f law) :
    (∑ o : Order I, ∫ u in cell o, f u ∂law) = ∫ u, f u ∂law := by
  simp_rw [← integral_indicator (measurableSet_cell _)]
  rw [← integral_finsetSum]
  · exact integral_congr_ae (sum_cell_indicator f)
  · intro o _
    exact hf.indicator (measurableSet_cell o)

end CriticalPercolation.Priority

end
end

end OAI
