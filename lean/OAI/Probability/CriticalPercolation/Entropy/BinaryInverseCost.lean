import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryTranscript

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

omit [Fintype V] in
lemma pairQuery_valid (i : Fin n) : (pairQuery G d x n D i).Valid ∅ :=
  SearchTree.bare_valid _ _ (ExactExposure.compile_valid G _ _)

omit [Fintype V] in
lemma selected_entropy_le (hp : p ∈ Set.Ioo 0 1) (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (i : Fin n) (hi : i ∈ activeSteps n D) :
    divergence (pushMass (selectedTranscript G d x n D i) P)
      (pushMass (selectedTranscript G d x n D i) (FiniteProduct.density (QueryTree.bitWeight p))) ≤
      divergence (pushMass (pairQuery G d x n D i).run P) ((pairQuery G d x n D i).reference p) := by
  let t := pairQuery G d x n D i
  let r := representative t.run (fun _ => false)
  let μ : (E → Bool) → ℝ := FiniteProduct.density (QueryTree.bitWeight p)
  have ht : selectedTranscript G d x n D i = r ∘ t.run := by
    funext ω
    exact ite_eq_left (Finset.mem_filter.mp hi).2
  rw [ht,← pushMass_comp,← pushMass_comp]
  have href := QueryTree.reference_eq_product_push p t ∅ (pairQuery_valid G d x n D i)
  rw [href]
  exact divergence_pushMass_le r (pushMass t.run P) (t.reference p)
    (pushMass_nonneg _ _ hP) (fun y => (QueryTree.reference_pos hp t y).le)
    (fun y _ => QueryTree.reference_pos hp t y)

lemma selected_contactLog_le (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (ω : E → Bool) :
    logContactMass (fun i η => selectedWeight G order d x p w n D i
      (selectedTranscript G d x n D i η)) ω ≤
      logContactMass (fun i η => scheduleWeight G order d x p w n (fun j => (D j).1)
        i (configuration η)) ω := by
  apply Finset.sum_le_sum
  intro i _
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left 1 _))
  apply max_le_max_left
  apply Finset.sum_le_sum
  intro m _
  change selectedWeight G order d x p w n D i (selectedTranscript G d x n D i ω) m ≤
    scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m
  rw [(selected_run G order d x p w n D i ω m).1]
  exact selectedWeight_le_raw G order d x p w n D hp h0 h1 i ω m

noncomputable section Cost
local instance inverseCostFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

lemma selected_density_le (hd : 0 < d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hconn : ∀ j, 0 < j → j < d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D)
    (z : (E → Bool) × (Fin n → Option E)) :
    conditionedMass G order d x p w s n D z ≤
      Real.exp (constructionCost G order d x p w c s n D) *
        FiniteProduct.density (QueryTree.bitWeight p) z.1 *
        ∏ i, selectedWeight G order d x p w n D i (selectedTranscript G d x n D i z.1) (z.2 i) := by
  by_cases hz : conditionedMass G order d x p w s n D z = 0
  · rw [hz]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (FiniteProduct.density_nonneg (QueryTree.bitWeight_nonneg ⟨hp.1.le,hp.2.le⟩) _))
      (Finset.prod_nonneg fun i _ => (selected_nonneg G order d x p w n D hp h0 h1 i _ _).1)
  · have he : (∏ i, selectedWeight G order d x p w n D i
          (selectedTranscript G d x n D i z.1) (z.2 i)) =
        ∏ i, scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration z.1) (z.2 i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [(selected_run G order d x p w n D i z.1 (z.2 i)).1]
      exact supported_selected_eq G order d x p w n D s z.1 z.2 hz i
    rw [he]
    exact conditionedMass_density_le G order d x p w hd hp h0 h1 hc hc1 hconn s n D hδ hD z

theorem conditioned_inverse_cost (horder : LazyDFS.GoodDarts G order)
    (ho : LazyDFS.Exhaustive G order) (hd : 0 < d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hconn : ∀ j, 0 < j → j < d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let Q := conditionedMass G order d x p w s n D
    let L := constructionCost G order d x p w c s n D
    (∑ i ∈ activeSteps n D, ∑ z, Q z * Real.log (1+selectedCost G order d x p w n D i z.1 (z.2 i))) ≤
      (16/(2*p*(1-p)))*(2*L+n*Real.log 4) + 2*L+2*n*Real.log 4 := by
  dsimp only
  let Q := conditionedMass G order d x p w s n D
  let μ : (E → Bool) → ℝ := FiniteProduct.density (QueryTree.bitWeight p)
  let P := pushMass Prod.fst Q
  let L := constructionCost G order d x p w c s n D
  have hQ : ∀ z, 0 ≤ Q z := conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD
  have hQ1 : ∑ z, Q z = 1 := by
    have he := conditionedMass_normalized G order d x p w s n D hD
    refine Eq.trans ?_ he
    apply Finset.sum_congr
    · ext z; simp only [Finset.mem_univ]
    · intro z _; rfl
  have hμ : ∀ ω, 0 < μ ω := fun ω => Finset.prod_pos fun e _ => QueryTree.bitWeight_pos hp e (ω e)
  have hh := active_inverse_cost_le Q hQ hQ1 μ hμ
    (selectedTranscript G d x n D) (selectedWeight G order d x p w n D)
    (selectedCost G order d x p w n D) L (activeSteps n D)
    (fun i ω m => (selected_nonneg G order d x p w n D hp h0 h1 i ω m).1)
    (fun i z hz => supported_selected_positive G order d x p w n D s hp h0 h1 z hz i)
    (fun i ω m => (selected_nonneg G order d x p w n D hp h0 h1 i ω m).2)
    (selected_density_le G order d x p w s n D hd hp h0 h1 hc hc1 hconn hδ hD)
    (selected_moment G order d x p w n D horder ho hp h0 h1)
  simp_rw [(selected_run G order d x p w n D _ _ _).2] at hh
  have hpair : (∑ i ∈ activeSteps n D,
      divergence (pushMass (fun z => selectedTranscript G d x n D i z.1) Q)
        (pushMass (selectedTranscript G d x n D i) μ)) ≤ (16/(2*p*(1-p)))*divergence P μ := by
    calc
      _ = ∑ i ∈ activeSteps n D,
        divergence (pushMass (selectedTranscript G d x n D i) P)
          (pushMass (selectedTranscript G d x n D i) μ) := by
        simp only [P,pushMass_comp,Function.comp_def]
      _ ≤ ∑ i ∈ activeSteps n D,
        divergence (pushMass (pairQuery G d x n D i).run P) ((pairQuery G d x n D i).reference p) :=
          Finset.sum_le_sum fun i hi => selected_entropy_le G d x p n D hp P (pushMass_nonneg _ _ hQ) i hi
      _ ≤ _ := by
        rw [Finset.sum_subtype (activeSteps n D) (p := fun i => (D i).2.2 = true)
          (fun i => by simp only [activeSteps,Finset.mem_filter,Finset.mem_univ,true_and])]
        exact conditioned_pair_entropy G order d x p w s n D hp h0 h1 hδ hD
  have hconf := conditioned_configuration_entropy G order d x p w ho hd hp h0 h1 hc hc1 hconn s n D hδ hD
  have hlog : (∑ z, Q z * logContactMass (fun i ω => selectedWeight G order d x p w n D i
      (selectedTranscript G d x n D i ω)) z.1) ≤ L+n*Real.log 4 := by
    exact (Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
      (selected_contactLog_le G order d x p w n D hp h0 h1 z.1) (hQ z)).trans hconf.2
  have hdiv : 0 ≤ divergence P μ := by
    have he := mass_sub_le_divergence P μ (pushMass_nonneg _ _ hQ) (fun ω => (hμ ω).le) (fun ω _ => hμ ω)
    have hm : ∑ ω, μ ω = 1 := FiniteProduct.sum_density _ (QueryTree.bitWeight_sum p)
    rw [pushMass_sum,hQ1,hm,sub_self] at he
    exact he
  have hcard : ((activeSteps n D).card : ℝ) ≤ n := by
    have he : (activeSteps n D).card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    simpa using (Nat.cast_le (α := ℝ)).mpr he
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hCp : 0 ≤ 16/(2*p*(1-p)) :=
    div_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hp.1.le) (sub_nonneg.mpr hp.2.le))
  have hbound := mul_le_mul_of_nonneg_left hconf.1 hCp
  have hcard' := mul_le_mul_of_nonneg_right hcard hlog4
  change _ ≤ (16/(2*p*(1-p)))*(2*L+n*Real.log 4)+2*L+2*n*Real.log 4
  linarith

end Cost
end CriticalPercolation.BinaryLaw
end
end

end OAI
