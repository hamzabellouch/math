import Mathlib.Probability.Independence.Conditional
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical

namespace Invariant233.ConditionalAvoidance

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]

omit mΩ [IsFiniteMeasure μ] in

theorem measurableSet_filter_selection_eq (I S : Finset ι) (P : ι → Ω → Prop)
    (hP : ∀ i ∈ I, MeasurableSet[m] {ω | P i ω}) :
    MeasurableSet[m] {ω | I.filter (fun i => P i ω) = S} := by
  classical
  by_cases hSI : S ⊆ I
  · have heq : {ω | I.filter (fun i => P i ω) = S} =
        ⋂ i ∈ I, {ω | P i ω ↔ i ∈ S} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h i hi
        have := Finset.ext_iff.mp h i
        simpa only [Finset.mem_filter, hi, true_and] using this
      · intro h
        ext i
        by_cases hi : i ∈ I
        · simpa only [Finset.mem_filter, hi, true_and] using h i hi
        · simp only [Finset.mem_filter, hi, false_and, false_iff]
          exact fun his => hi (hSI his)
    rw [heq]
    apply MeasurableSet.biInter I.countable_toSet
    intro i hi
    by_cases his : i ∈ S
    · simpa only [his, iff_true] using hP i hi
    · simpa only [his, iff_false, ← Set.compl_ofPred] using (hP i hi).compl
  · have heq : {ω | I.filter (fun i => P i ω) = S} = (∅ : Set Ω) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hSI (hω ▸ Finset.filter_subset _ _)
    rw [heq]
    exact MeasurableSet.empty

theorem condProb_compl (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet A) :
    μ⟦Aᶜ | m⟧ =ᵐ[μ] fun ω => 1 - (μ⟦A | m⟧) ω := by
  have heq : Aᶜ.indicator (fun _ : Ω => (1 : ℝ)) =
      (fun _ => (1 : ℝ)) - A.indicator (fun _ => (1 : ℝ)) := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  change μ[Aᶜ.indicator (fun _ => (1 : ℝ)) | m] =ᵐ[μ] _
  rw [heq]
  have hsub := condExp_sub (μ := μ) (integrable_const (1 : ℝ))
    ((integrable_const (1 : ℝ)).indicator hA) m
  filter_upwards [hsub] with ω hω
  simpa only [Pi.sub_apply, condExp_const hm] using hω

omit [IsFiniteMeasure μ] in

theorem condProb_nonneg (A : Set Ω) :
    ∀ᵐ ω ∂μ, 0 ≤ (μ⟦A | m⟧) ω := by
  apply condExp_nonneg
  exact Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ A <;> simp [hω]

theorem condProb_le_on_of_ae_inter_subset (hm : m ≤ mΩ)
    {H K B : Set Ω} (hH : MeasurableSet H) (hK : MeasurableSet[m] K)
    (hB : MeasurableSet B) (hsub : (H ∩ K : Set Ω) ≤ᵐ[μ] B) :
    ∀ᵐ ω ∂μ, ω ∈ K → (μ⟦H | m⟧) ω ≤ (μ⟦B | m⟧) ω := by
  have hpull := condExp_indicator (μ := μ)
    ((integrable_const (1 : ℝ)).indicator hH) hK
  have hmono := condExp_mono (μ := μ) (m := m)
    (((integrable_const (1 : ℝ)).indicator hH).indicator (hm _ hK))
    ((integrable_const (1 : ℝ)).indicator hB)
    (hsub.mono fun ω hsubω => show
      K.indicator (H.indicator (fun _ => (1 : ℝ))) ω ≤
        B.indicator (fun _ => (1 : ℝ)) ω from by
      by_cases hωK : ω ∈ K
      · by_cases hωH : ω ∈ H
        · have hωB : ω ∈ B := hsubω ⟨hωH, hωK⟩
          simp [hωK, hωH, hωB]
        · simp [hωK, hωH, Set.indicator_nonneg]
      · simp [hωK, Set.indicator_nonneg])
  filter_upwards [hpull, hmono] with ω hp hmω hωK
  simpa only [hp, Set.indicator_of_mem hωK] using hmω

theorem condProb_le_on_of_inter_subset (hm : m ≤ mΩ)
    {H K B : Set Ω} (hH : MeasurableSet H) (hK : MeasurableSet[m] K)
    (hB : MeasurableSet B) (hsub : H ∩ K ⊆ B) :
    ∀ᵐ ω ∂μ, ω ∈ K → (μ⟦H | m⟧) ω ≤ (μ⟦B | m⟧) ω :=
  condProb_le_on_of_ae_inter_subset hm hH hK hB (Eventually.of_forall hsub)

theorem prod_one_sub_le_exp (S : Finset ι) (q : ι → ℝ) {p : ℝ}
    (hq : ∀ i ∈ S, 0 ≤ 1 - q i) (hp : ∀ i ∈ S, p ≤ q i) :
    (∏ i ∈ S, (1 - q i)) ≤ Real.exp (-p * S.card) := by
  calc
    (∏ i ∈ S, (1 - q i)) ≤ ∏ _i ∈ S, Real.exp (-p) := by
      apply Finset.prod_le_prod₀ hq
      intro i hi
      calc
        1 - q i ≤ 1 - p := sub_le_sub_left (hp i hi) 1
        _ ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
    _ = Real.exp (-p) ^ S.card := by simp
    _ = Real.exp (-p * S.card) := by rw [← Real.exp_nat_mul]; congr 1; ring

section ConditionalIndependence

variable [StandardBorelSpace Ω]

theorem condProb_avoid_eq_prod (hm : m ≤ mΩ) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iCondIndepSet m hm A μ)
    (S : Finset ι) :
    μ⟦⋂ i ∈ S, (A i)ᶜ | m⟧ =ᵐ[μ]
      fun ω => ∏ i ∈ S, (1 - (μ⟦A i | m⟧) ω) := by
  have hmA : ∀ i, MeasurableSpace.generateFrom {A i} ≤ mΩ := by
    intro i
    apply MeasurableSpace.generateFrom_le
    intro s hs
    rcases Set.mem_singleton_iff.mp hs with rfl
    exact hA i
  have hi := (iCondIndepSet_iff_iCondIndep m hm A μ).mp hind
  have hprod := (iCondIndep_iff m hm _ hmA μ).mp hi S
    (f := fun i => (A i)ᶜ) (fun i _ =>
      (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton (A i))).compl)
  have hcomp : ∀ᵐ ω ∂μ, ∀ i ∈ S,
      (μ⟦(A i)ᶜ | m⟧) ω = 1 - (μ⟦A i | m⟧) ω := by
    exact (ae_ball_iff S.countable_toSet).mpr (fun i _ => condProb_compl hm (hA i))
  filter_upwards [hprod, hcomp] with ω hω hc
  rw [hω, Finset.prod_apply]
  exact Finset.prod_congr rfl hc

theorem condProb_avoid_random_selection_le_exp_ae
    (hm : m ≤ mΩ) (I : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iCondIndepSet m hm A μ)
    (J : Ω → Finset ι)
    (hJ : ∀ S : Finset ι, MeasurableSet[m] {ω | J ω = S})
    (hJI : ∀ ω, J ω ⊆ I) {H : Set Ω} (hH : MeasurableSet H)
    {p r : ℝ} (hp : 0 ≤ p)
    (hposterior : ∀ i ∈ I, ∀ᵐ ω ∂μ, i ∈ J ω → p ≤ (μ⟦A i | m⟧) ω)
    (hcard : ∀ᵐ ω ∂μ, ω ∈ H → r ≤ ((J ω).card : ℝ))
    (havoid : ∀ᵐ ω ∂μ, ω ∈ H → ∀ i ∈ J ω, ω ∉ A i) :
    ∀ᵐ ω ∂μ, (μ⟦H | m⟧) ω ≤ Real.exp (-p * r) := by
  classical
  have hlocal : ∀ S ∈ I.powerset, ∀ᵐ ω ∂μ,
      J ω = S → (μ⟦H | m⟧) ω ≤ Real.exp (-p * r) := by
    intro S hS
    have hSI : S ⊆ I := Finset.mem_powerset.mp hS
    by_cases hSr : r ≤ (S.card : ℝ)
    · have hsub : (H ∩ {ω | J ω = S} : Set Ω) ≤ᵐ[μ] (⋂ i ∈ S, (A i)ᶜ : Set Ω) := by
        filter_upwards [havoid] with ω ha hω
        change ω ∈ (⋂ i ∈ S, (A i)ᶜ : Set Ω)
        simp only [Set.mem_iInter, Set.mem_compl_iff]
        intro i hi
        exact ha hω.1 i (hω.2.symm ▸ hi)
      have hloc := condProb_le_on_of_ae_inter_subset (μ := μ) hm hH (hJ S)
        (MeasurableSet.biInter S.countable_toSet (fun i _ => (hA i).compl)) hsub
      have hprod := condProb_avoid_eq_prod (μ := μ) hm A hA hind S
      have hpost : ∀ᵐ ω ∂μ, ∀ i ∈ S,
          i ∈ J ω → p ≤ (μ⟦A i | m⟧) ω :=
        (ae_ball_iff S.countable_toSet).mpr (fun i hi => hposterior i (hSI hi))
      have hnonneg : ∀ᵐ ω ∂μ, ∀ i ∈ S, 0 ≤ 1 - (μ⟦A i | m⟧) ω := by
        apply (ae_ball_iff S.countable_toSet).mpr
        intro i _
        filter_upwards [condProb_nonneg (μ := μ) (m := m) (A i)ᶜ,
          condProb_compl hm (hA i)] with ω hn hc
        simpa only [hc] using hn
      filter_upwards [hloc, hprod, hpost, hnonneg] with ω hl he hpo hnn hωS
      calc
        (μ⟦H | m⟧) ω ≤ (μ⟦⋂ i ∈ S, (A i)ᶜ | m⟧) ω := hl hωS
        _ = ∏ i ∈ S, (1 - (μ⟦A i | m⟧) ω) := he
        _ ≤ Real.exp (-p * S.card) := prod_one_sub_le_exp S _ hnn
          (fun i hi => hpo i hi (hωS.symm ▸ hi))
        _ ≤ Real.exp (-p * r) := Real.exp_le_exp.mpr (by nlinarith)
    · have hsub : (H ∩ {ω | J ω = S} : Set Ω) ≤ᵐ[μ] (∅ : Set Ω) := by
        filter_upwards [hcard] with ω hc hω
        have heq : J ω = S := hω.2
        exact (hSr (by simpa only [heq] using hc hω.1)).elim
      have hloc := condProb_le_on_of_ae_inter_subset (μ := μ) hm hH (hJ S)
        MeasurableSet.empty hsub
      filter_upwards [hloc] with ω hl hωS
      have hz : (μ⟦H | m⟧) ω ≤ 0 := by simpa using hl hωS
      exact hz.trans (Real.exp_pos _).le
  have hall := (ae_ball_iff I.powerset.countable_toSet).mpr hlocal
  filter_upwards [hall] with ω hω
  exact hω (J ω) (Finset.mem_powerset.mpr (hJI ω)) rfl

theorem condProb_avoid_random_selection_le_exp
    (hm : m ≤ mΩ) (I : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iCondIndepSet m hm A μ)
    (J : Ω → Finset ι)
    (hJ : ∀ S : Finset ι, MeasurableSet[m] {ω | J ω = S})
    (hJI : ∀ ω, J ω ⊆ I) {H : Set Ω} (hH : MeasurableSet H)
    {p r : ℝ} (hp : 0 ≤ p)
    (hposterior : ∀ i ∈ I, ∀ᵐ ω ∂μ, i ∈ J ω → p ≤ (μ⟦A i | m⟧) ω)
    (hcard : ∀ ω ∈ H, r ≤ ((J ω).card : ℝ))
    (havoid : ∀ ω ∈ H, ∀ i ∈ J ω, ω ∉ A i) :
    ∀ᵐ ω ∂μ, (μ⟦H | m⟧) ω ≤ Real.exp (-p * r) :=
  condProb_avoid_random_selection_le_exp_ae hm I A hA hind J hJ hJI hH hp
    hposterior (Eventually.of_forall hcard) (Eventually.of_forall havoid)

theorem condProb_half_selection_le_exp
    (hm : m ≤ mΩ) (I : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iCondIndepSet m hm A μ)
    (J : Ω → Finset ι)
    (hJ : ∀ S : Finset ι, MeasurableSet[m] {ω | J ω = S})
    (hJI : ∀ ω, J ω ⊆ I) {H : Set Ω} (hH : MeasurableSet H)
    {ρ M : ℝ} (hρ : 0 ≤ ρ) (hI : M / 20 ≤ (I.card : ℝ))
    (hposterior : ∀ i ∈ I, ∀ᵐ ω ∂μ, i ∈ J ω → ρ / 10 ≤ (μ⟦A i | m⟧) ω)
    (hcard : ∀ ω ∈ H, (I.card : ℝ) / 2 ≤ ((J ω).card : ℝ))
    (havoid : ∀ ω ∈ H, ∀ i ∈ J ω, ω ∉ A i) :
    ∀ᵐ ω ∂μ, (μ⟦H | m⟧) ω ≤ Real.exp (-M * ρ / 400) := by
  have h := condProb_avoid_random_selection_le_exp hm I A hA hind J hJ hJI hH
    (div_nonneg hρ (by norm_num : (0 : ℝ) ≤ 10)) hposterior hcard havoid
  filter_upwards [h] with ω hω
  apply hω.trans
  apply Real.exp_le_exp.mpr
  nlinarith

theorem condProb_avoid_intensity_le_exp_ae
    (hm : m ≤ mΩ) (I : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iCondIndepSet m hm A μ)
    (J : Ω → Finset ι)
    (hJ : ∀ S : Finset ι, MeasurableSet[m] {ω | J ω = S})
    (hJI : ∀ ω, J ω ⊆ I) {H : Set Ω} (hH : MeasurableSet H)
    {ρ M L : ℝ} (hρ : 0 ≤ ρ) (hL : L ≤ M * ρ)
    (hI : M / 20 ≤ (I.card : ℝ))
    (hposterior : ∀ i ∈ I, ∀ᵐ ω ∂μ, i ∈ J ω → ρ / 10 ≤ (μ⟦A i | m⟧) ω)
    (hcard : ∀ᵐ ω ∂μ, ω ∈ H → (I.card : ℝ) / 2 ≤ ((J ω).card : ℝ))
    (havoid : ∀ᵐ ω ∂μ, ω ∈ H → ∀ i ∈ J ω, ω ∉ A i) :
    ∀ᵐ ω ∂μ, (μ⟦H | m⟧) ω ≤ Real.exp (-L / 400) := by
  have h := condProb_avoid_random_selection_le_exp_ae hm I A hA hind J hJ hJI hH
    (div_nonneg hρ (by norm_num : (0 : ℝ) ≤ 10)) hposterior hcard havoid
  filter_upwards [h] with ω hω
  apply hω.trans
  apply Real.exp_le_exp.mpr
  have hi := mul_le_mul_of_nonneg_right hI hρ
  nlinarith

theorem iCondIndepSet_preimages {β : ι → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)]
    (hm : m ≤ mΩ) (f : ∀ i, Ω → β i) (hf : ∀ i, Measurable (f i))
    (hind : iCondIndepFun m hm f μ) (C : ∀ i, Set (β i))
    (hC : ∀ i, MeasurableSet (C i)) :
    iCondIndepSet m hm (fun i => f i ⁻¹' C i) μ := by
  rw [iCondIndepSet_iff m hm _ (fun i => (hf i) (hC i)) μ]
  intro S
  exact (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mβ f hf).mp hind S
    (fun i _ => hC i)

end ConditionalIndependence
end Invariant233.ConditionalAvoidance

end

end OAI
