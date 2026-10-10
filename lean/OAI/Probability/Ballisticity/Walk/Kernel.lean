import Mathlib
import OAI.Probability.Ballisticity.Estimates.MeasurableCountableSample

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TailDecorrelation

section Randomization
variable {D I A J E : Type*} [MeasurableSpace D] [MeasurableSpace A]
variable [MeasurableSpace E] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
variable (δ : Measure D) (σ : Measure E) (ν : Measure A)
variable [IsProbabilityMeasure δ] [IsProbabilityMeasure σ] [IsProbabilityMeasure ν]

lemma randomization_projection_preserving :
    MeasurePreserving (fun x : (D × E) × (I → A) => (x.1.1, x.2))
      ((δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν)))
      (δ.prod (Measure.infinitePi (fun _ : I => ν))) := by
  exact measurePreserving_fst.prod (MeasurePreserving.id _)

lemma randomized_density {f : D × (I → A) → ℝ}
    (hf : Measurable f) (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hH : Integrable (fun x => entropyPlus (f x)) (δ.prod (Measure.infinitePi (fun _ : I => ν)))) :
    Integrable (fun x : (D × E) × (I → A) => f (x.1.1, x.2))
      ((δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν))) ∧
    Integrable (fun x : (D × E) × (I → A) => entropyPlus (f (x.1.1, x.2)))
      ((δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν))) ∧
    (∫ x : (D × E) × (I → A), f (x.1.1, x.2)
      ∂(δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν))) =
      (∫ x, f x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) := by
  have hp := randomization_projection_preserving δ σ ν (I := I)
  refine ⟨(hp.integrable_comp hf.aestronglyMeasurable).mpr hfi,
    (hp.integrable_comp (measurable_entropyPlus.comp hf).aestronglyMeasurable).mpr hH, ?_⟩
  have hh : AEStronglyMeasurable f
      (((δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν))).map
        (fun x : (D × E) × (I → A) => (x.1.1, x.2))) := by
    rw [hp.map_eq]
    exact hf.aestronglyMeasurable
  have he := integral_map hp.measurable.aemeasurable hh
  rw [hp.map_eq] at he
  exact he.symm

end Randomization
end TailDecorrelation

namespace TailDecorrelation

lemma measurableSet_eventually_nat {X : Type*} [MeasurableSpace X]
    {p : ℕ → X → Prop} (hp : ∀ n, MeasurableSet {x | p n x}) :
    MeasurableSet {x | ∀ᶠ n in atTop, p n x} := by
  simp only [eventually_atTop, Set.ofPred_exists, Set.ofPred_forall]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun m =>
    MeasurableSet.iInter fun _ => hp m

section KernelTransfer
variable {D E W J : Type*} [MeasurableSpace D] [MeasurableSpace E]
variable [MeasurableSpace W] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
variable (δ : Measure D) (σ : Measure E) (P : Measure W)
variable [IsProbabilityMeasure δ] [IsProbabilityMeasure σ] [IsProbabilityMeasure P]

lemma integral_comp_preserving {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ρ : Measure Y} {T : X → Y} (hT : MeasurePreserving T μ ρ)
    {g : Y → ℝ} (hg : Measurable g) :
    (∫ x, g (T x) ∂μ) = ∫ y, g y ∂ρ := by
  have hm : AEStronglyMeasurable g (μ.map T) := by
    rw [hT.map_eq]
    exact hg.aestronglyMeasurable
  have he := integral_map hT.measurable.aemeasurable hm
  rw [hT.map_eq] at he
  exact he.symm

lemma swap_seed_preserving :
    MeasurePreserving (fun x : (D × W) × E => ((x.1.1,x.2),x.1.2))
      ((δ.prod P).prod σ) ((δ.prod σ).prod P) := by
  exact ((measurePreserving_prodAssoc δ σ P).symm MeasurableEquiv.prodAssoc).comp
    (((MeasurePreserving.id δ).prod Measure.measurePreserving_swap).comp
      (measurePreserving_prodAssoc δ P σ))

lemma sampled_kernel_integral (κ : Kernel D J) (s : D → E → J)
    (hs : Measurable (Function.uncurry s)) (hmap : ∀ d, σ.map (s d) = κ d)
    {f : D × W → ℝ} (hf : Measurable f) {Z : J → W → ℝ}
    (hZ : ∀ a, Measurable (Z a))
    (hi : Integrable (fun x : (D × E) × W => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2)
      ((δ.prod σ).prod P)) :
    (∫ x : (D × E) × W, f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2 ∂(δ.prod σ).prod P) =
      (∫ x : D × W, f x * (∫ a, Z a x.2 ∂κ x.1) ∂δ.prod P) := by
  have hz : Measurable (Function.uncurry Z) := measurable_from_prod_countable_right hZ
  let G : (D × E) × W → ℝ := fun x => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2
  have hG : Measurable G :=
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hz.comp ((hs.comp measurable_fst).prodMk measurable_snd))
  have hp := swap_seed_preserving δ σ P
  have hj : Integrable (fun x : (D × W) × E => f x.1 * Z (s x.1.1 x.2) x.1.2)
      ((δ.prod P).prod σ) := (hp.integrable_comp hG.aestronglyMeasurable).mpr hi
  rw [← integral_comp_preserving hp hG]
  change (∫ x : (D × W) × E, f x.1 * Z (s x.1.1 x.2) x.1.2 ∂(δ.prod P).prod σ) = _
  rw [integral_prod _ hj]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change (∫ u, f x * Z (s x.1 u) x.2 ∂σ) = f x * (∫ a, Z a x.2 ∂κ x.1)
  rw [integral_const_mul]
  congr 1
  have he := integral_map ((hs.comp measurable_prodMk_left).aemeasurable)
    (show AEStronglyMeasurable (fun a => Z a x.2) (σ.map (s x.1)) from
      Measurable.of_discrete.aestronglyMeasurable)
  change (∫ a, Z a x.2 ∂σ.map (s x.1)) = (∫ u, Z (s x.1 u) x.2 ∂σ) at he
  rw [hmap] at he
  exact he.symm

lemma sampled_kernel_integrable (κ : Kernel D J) (s : D → E → J)
    (hs : Measurable (Function.uncurry s)) (hmap : ∀ d, σ.map (s d) = κ d)
    {f : D × W → ℝ} (hf : Measurable f) {Z : J → W → ℝ}
    (hZ : ∀ a, Measurable (Z a))
    (hi : Integrable (fun x : (D × E) × W => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2)
      ((δ.prod σ).prod P)) :
    Integrable (fun x : D × W => f x * (∫ a, Z a x.2 ∂κ x.1)) (δ.prod P) := by
  have hz : Measurable (Function.uncurry Z) := measurable_from_prod_countable_right hZ
  let G : (D × E) × W → ℝ := fun x => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2
  have hG : Measurable G :=
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hz.comp ((hs.comp measurable_fst).prodMk measurable_snd))
  have hp := swap_seed_preserving δ σ P
  have hj : Integrable (fun x : (D × W) × E => f x.1 * Z (s x.1.1 x.2) x.1.2)
      ((δ.prod P).prod σ) := (hp.integrable_comp hG.aestronglyMeasurable).mpr hi
  apply hj.integral_prod_left.congr
  apply Eventually.of_forall
  intro x
  change (∫ u, f x * Z (s x.1 u) x.2 ∂σ) = f x * (∫ a, Z a x.2 ∂κ x.1)
  rw [integral_const_mul]
  congr 1
  have he := integral_map ((hs.comp measurable_prodMk_left).aemeasurable)
    (show AEStronglyMeasurable (fun a => Z a x.2) (σ.map (s x.1)) from
      Measurable.of_discrete.aestronglyMeasurable)
  change (∫ a, Z a x.2 ∂σ.map (s x.1)) = (∫ u, Z (s x.1 u) x.2 ∂σ) at he
  rw [hmap] at he
  exact he.symm

omit [IsProbabilityMeasure δ] in
lemma kernel_escape_sampled (κ : ℕ → Kernel D J) (s : ℕ → D → E → J)
    (hs : ∀ r, Measurable (Function.uncurry (s r)))
    (hmap : ∀ r d, σ.map (s r d) = κ r d)
    (good : ℕ → J → Prop)
    (hesc : ∀ᵐ d ∂δ, ∀ᶠ r in atTop, ∀ᵐ a ∂κ r d, good r a) :
    ∀ᵐ x ∂δ.prod σ, ∀ᶠ r in atTop, good r (s r x.1 x.2) := by
  have hm : ∀ r, MeasurableSet {x : D × E | good r (s r x.1 x.2)} := fun r =>
    (hs r) (Set.to_countable _).measurableSet
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eventually_nat hm)).mpr
  filter_upwards [hesc] with d hd
  obtain ⟨N,hN⟩ := eventually_atTop.mp hd
  have hforall : ∀ r : ℕ, ∀ᵐ u ∂σ, N ≤ r → good r (s r d u) := by
    intro r
    by_cases hr : N ≤ r
    · have hh := hN r hr
      rw [← hmap r d] at hh
      have htrans := (ae_map_iff (hs r |>.comp measurable_prodMk_left |>.aemeasurable)
        (Set.to_countable _).measurableSet).mp hh
      exact htrans.mono fun u hu _ => hu
    · exact Eventually.of_forall fun _ h => (hr h).elim
  filter_upwards [ae_all_iff.mpr hforall] with u hu
  exact eventually_atTop.mpr ⟨N,hu⟩

end KernelTransfer
end TailDecorrelation

namespace TailDecorrelation
section KernelCompletion
variable {D I A J : Type*} [MeasurableSpace D] [MeasurableSpace A] [Encodable I]
variable [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
variable [Nonempty J] [StandardBorelSpace J]
variable (δ : Measure D) (ν : Measure A) [IsProbabilityMeasure δ] [IsProbabilityMeasure ν]

omit [Encodable I] in
lemma kernel_density_integrable {f : D × (I → A) → ℝ} {Z : J → (I → A) → ℝ}
    {c Q : ℝ} (hc : 0 < c)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hH : Integrable (fun x => entropyPlus (f x)) (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hZ : ∀ a, Measurable (Z a)) (hZ0 : ∀ a ω, 0 ≤ Z a ω)
    (he : ∀ a, Integrable (fun ω => Real.exp (c * Z a ω)) (Measure.infinitePi (fun _ : I => ν)))
    (heQ : ∀ a, (∫ ω, Real.exp (c * Z a ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ Q)
    (κ : Kernel D J) [IsMarkovKernel κ] :
    Integrable (fun x : D × (I → A) => f x * (∫ a, Z a x.2 ∂κ x.1))
      (δ.prod (Measure.infinitePi (fun _ : I => ν))) := by
  obtain ⟨s,hs,hmap⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  let σ : Measure unitInterval := volume
  let g : (D × unitInterval) × (I → A) → ℝ := fun x => f (x.1.1,x.2)
  have hg : Measurable g := hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨_,hgH,_⟩ := randomized_density δ σ ν hf hfi hH
  have hi := integrable_density_mul_of_entropy hc hg
    (measurable_countable_sample hZ hs) (fun x => hf0 _) (fun x => hZ0 _ _) hgH
    (sampled_exponential_integrable (δ.prod σ) ν hZ he heQ hs).1
  exact sampled_kernel_integrable δ σ (Measure.infinitePi (fun _ : I => ν))
    κ s hs hmap hf hZ hi

lemma kernel_entropy_decorrelation {f : D × (I → A) → ℝ} {Z : J → (I → A) → ℝ}
    {c Q C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hf1 : (∫ x, f x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) = 1)
    (hH : Integrable (fun x => entropyPlus (f x)) (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hZ : ∀ a, Measurable (Z a)) (hZ0 : ∀ a ω, 0 ≤ Z a ω)
    (he : ∀ a, Integrable (fun ω => Real.exp ((2 * c) * Z a ω)) (Measure.infinitePi (fun _ : I => ν)))
    (heQ : ∀ a, (∫ ω, Real.exp ((2 * c) * Z a ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ Q)
    (hZi : ∀ a, Integrable (Z a) (Measure.infinitePi (fun _ : I => ν)))
    (hZC : ∀ a, (∫ ω, Z a ω ∂Measure.infinitePi (fun _ : I => ν)) ≤ C)
    (N : ℕ → J → Set I) (κ : ℕ → Kernel D J) [∀ r, IsMarkovKernel (κ r)]
    (hloc : ∀ K η : ℝ, 0 < K → 0 < η → ∃ n : ℕ, ∃ F : J → (I → A) → ℝ,
      (∀ a, @Measurable _ _ (rows (N n a)) _ (F a)) ∧
      (∀ a ω, 0 ≤ F a ω ∧ F a ω ≤ K) ∧
      (∀ a, (∫ ω, |min K (Z a ω) - F a ω| ∂Measure.infinitePi (fun _ : I => ν)) ≤ η))
    (hescape : ∀ n (S : Set I), S.Finite → ∀ᵐ d ∂δ,
      ∀ᶠ r in atTop, ∀ᵐ a ∂κ r d, Disjoint S (N n a)) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      (∫ x : D × (I → A), f x * (∫ a, Z a x.2 ∂κ r x.1)
        ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤ C + ε := by
  classical
  let σ : Measure unitInterval := volume
  choose s hs hmap using fun r => Kernel.exists_measurable_map_eq_unitInterval (κ r)
  let g : (D × unitInterval) × (I → A) → ℝ := fun x => f (x.1.1,x.2)
  have hg : Measurable g := hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨hgi,hgH,hg1⟩ := randomized_density δ σ ν hf hfi hH
  have hesc : ∀ n (S : Set I), S.Finite → ∀ᵐ d ∂δ.prod σ,
      ∀ᶠ r in atTop, Disjoint S (N n (s r d.1 d.2)) := by
    intro n S hS
    exact kernel_escape_sampled δ σ κ s hs hmap (fun _ a => Disjoint S (N n a)) (hescape n S hS)
  have hbound := sampled_entropy_decorrelation (δ.prod σ) ν hc hC hg
    (fun x => hf0 _) hgi (hg1.trans hf1) hgH hZ hZ0 he heQ hZi hZC N
    (fun r => Function.uncurry (s r)) hs hloc hesc
  have heq : ∀ r, (∫ x : (D × unitInterval) × (I → A),
      g x * Z (s r x.1.1 x.1.2) x.2 ∂(δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν))) =
      (∫ x : D × (I → A), f x * (∫ a, Z a x.2 ∂κ r x.1)
        ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) := by
    intro r
    have hi := integrable_density_mul_of_entropy (by linarith : 0 < 2*c) hg
      (measurable_countable_sample hZ (hs r)) (fun x => hf0 _) (fun x => hZ0 _ _) hgH
      (sampled_exponential_integrable (δ.prod σ) ν hZ he heQ (hs r)).1
    exact sampled_kernel_integral δ σ (Measure.infinitePi (fun _ : I => ν))
      (κ r) (s r) (hs r) (hmap r) hf hZ hi
  intro ε hε
  filter_upwards [hbound ε hε] with r hr
  rw [← heq r]
  exact hr

end KernelCompletion
end TailDecorrelation

end

end OAI
