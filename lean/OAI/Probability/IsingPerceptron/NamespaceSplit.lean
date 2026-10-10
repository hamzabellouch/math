import Mathlib
import OAI.Probability.IsingPerceptron.EnergyShift

namespace OAI

/-! Namespace Split. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

abbrev OtherNamespaces (j : ℕ) := {k : ℕ // k ≠ j} → ℕ → ℝ

def otherNamespacesLaw (j : ℕ) : Measure (OtherNamespaces j) :=
  Measure.infinitePi (fun _ : {k : ℕ // k ≠ j} => gaussianCoordinates)

instance otherNamespacesLaw_probability (j : ℕ) : IsProbabilityMeasure (otherNamespacesLaw j) := by
  unfold otherNamespacesLaw
  infer_instance

def gaussianNamespaceSplit (j : ℕ) (g : ℕ → ℝ) : (ℕ → ℝ) × OtherNamespaces j :=
  ((fun i => g (Nat.pair j i)),fun k i => g (Nat.pair k i))

lemma measurable_gaussianNamespaceSplit (j : ℕ) : Measurable (gaussianNamespaceSplit j) := by
  unfold gaussianNamespaceSplit
  fun_prop

lemma gaussianNamespaceSplit_law (j : ℕ) :
    gaussianCoordinates.map (gaussianNamespaceSplit j) =
      gaussianCoordinates.prod (otherNamespacesLaw j) := by
  let e := Equiv.optionSubtypeNe j
  let t : Option {k : ℕ // k ≠ j} × ℕ → ℕ := fun p => Nat.pair (e p.1) p.2
  have ht : Function.Injective t := by
    intro p q h
    have he := Nat.pair_eq_pair.mp h
    exact Prod.ext (e.injective he.1) he.2
  have hp := gaussian_pullback_measurePreserving t ht
  let F : (ℕ → ℝ) → Option {k : ℕ // k ≠ j} → ℕ → ℝ := fun g k i => g (t (k,i))
  have hmF : Measurable F := by unfold F; fun_prop
  have hF : gaussianCoordinates.map F = Measure.infinitePi
      (fun _ : Option {k : ℕ // k ≠ j} => gaussianCoordinates) := by
    change gaussianCoordinates.map
      ((MeasurableEquiv.curry (Option {k : ℕ // k ≠ j}) ℕ ℝ) ∘
        (fun g => fun p => g (t p))) = _
    rw [← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hp.measurable,hp.map_eq,
      Measure.infinitePi_map_curry (fun (_ : Option {k : ℕ // k ≠ j}) (_ : ℕ) => gaussianReal 0 1)]
    rfl
  have hs := infinitePi_option_split gaussianCoordinates
    (fun _ : {k : ℕ // k ≠ j} => gaussianCoordinates)
  have hc : (fun i : Option {k : ℕ // k ≠ j} =>
      i.elim gaussianCoordinates (fun _ => gaussianCoordinates)) = (fun _ => gaussianCoordinates) := by
    funext i; cases i <;> rfl
  rw [hc] at hs
  have he : gaussianNamespaceSplit j =
      (fun q : Option {k : ℕ // k ≠ j} → ℕ → ℝ => (q none,fun k => q (some k))) ∘ F := by
    rfl
  rw [he,← Measure.map_map (by fun_prop) hmF,hF]
  exact hs

def gaussianNamespaceJoin (j : ℕ) (p : (ℕ → ℝ) × OtherNamespaces j) (i : ℕ) : ℝ :=
  if h : (Nat.unpair i).1 = j then p.1 (Nat.unpair i).2
    else p.2 ⟨(Nat.unpair i).1,h⟩ (Nat.unpair i).2

lemma measurable_gaussianNamespaceJoin (j : ℕ) : Measurable (gaussianNamespaceJoin j) := by
  apply Measurable.of_eval
  intro i
  by_cases h : (Nat.unpair i).1 = j
  · simp only [gaussianNamespaceJoin,dite_eq_left h]
    fun_prop
  · simp only [gaussianNamespaceJoin,dite_eq_right h]
    fun_prop

lemma gaussianNamespaceJoin_split (j : ℕ) (g : ℕ → ℝ) :
    gaussianNamespaceJoin j (gaussianNamespaceSplit j g) = g := by
  funext i
  simp only [gaussianNamespaceJoin,gaussianNamespaceSplit]
  split_ifs with h
  · rw [← h,Nat.pair_unpair]
  · rw [Nat.pair_unpair]

lemma gaussianNamespaceJoin_law (j : ℕ) :
    (gaussianCoordinates.prod (otherNamespacesLaw j)).map (gaussianNamespaceJoin j) =
      gaussianCoordinates := by
  rw [← gaussianNamespaceSplit_law,Measure.map_map
    (measurable_gaussianNamespaceJoin j) (measurable_gaussianNamespaceSplit j)]
  simp only [Function.comp_def,gaussianNamespaceJoin_split,Measure.map_id']

lemma gaussianNamespaceJoin_selected (j : ℕ) (z : ℕ → ℝ) (g : OtherNamespaces j) (i : ℕ) :
    gaussianNamespaceJoin j (z,g) (Nat.pair j i) = z i := by
  simp [gaussianNamespaceJoin,Nat.unpair_pair]

lemma gaussianNamespaceJoin_other (j : ℕ) (z : ℕ → ℝ) (g : OtherNamespaces j)
    (k : {k : ℕ // k ≠ j}) (i : ℕ) :
    gaussianNamespaceJoin j (z,g) (Nat.pair k i) = g k i := by
  simp [gaussianNamespaceJoin,Nat.unpair_pair,k.property]

theorem gaussianNamespaceJoin_preserving (j : ℕ) :
    MeasurePreserving (gaussianNamespaceJoin j)
      (gaussianCoordinates.prod (otherNamespacesLaw j)) gaussianCoordinates :=
  ⟨measurable_gaussianNamespaceJoin j,gaussianNamespaceJoin_law j⟩

lemma cylinderField_enriched_expand {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (s : Spin N × LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (enrichedCoefficients n h u s) g =
      cylinderField (externalFieldCoefficients n h s) (fun i => g (Nat.pair 0 i)) +
        ∑ j : Fin N, (Real.sqrt N*perturbationScale N*perturbationWeight j*u j) *
          cylinderField (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 s)
            (fun i => g (Nat.pair (j+1) i)) := by
  rw [enrichedCoefficients,cylinderField_finset_sum,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Fin.val_zero,Fin.val_succ,
    cylinderField_tag,cylinderField_smul]

lemma cylinderField_enriched_update {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (j : Fin N) (v : ℝ) (s : Spin N × LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (enrichedCoefficients n h (Function.update u j v) s) g =
      cylinderField (enrichedCoefficients n h (Function.update u j 0) s) g +
        (Real.sqrt N*perturbationScale N*perturbationWeight j*v) *
          cylinderField (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 s)
            (fun i => g (Nat.pair (j+1) i)) := by
  classical
  let a : Fin N → ℝ := fun k => Real.sqrt N*perturbationScale N*perturbationWeight k
  let Y : Fin N → ℝ := fun k =>
    cylinderField (monomialCoefficients n (monomialIndex k).1 (monomialIndex k).2 s)
      (fun i => g (Nat.pair (k+1) i))
  have he (k : Fin N) : a k * Function.update u j v k * Y k =
      a k * Function.update u j 0 k * Y k + if k = j then a j*v*Y j else 0 := by
    by_cases hk : k = j
    · subst k; simp
    · simp [hk]
  simp_rw [cylinderField_enriched_expand]
  change _ + ∑ k : Fin N, a k * Function.update u j v k * Y k = _
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact (add_assoc (cylinderField (externalFieldCoefficients n h s)
    (fun i => g (Nat.pair 0 i))) (∑ k, a k * Function.update u j 0 k * Y k)
      (a j * v * Y j)).symm

lemma cylinderField_enriched_frozen {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (j : Fin N) (s : Spin N × LabeledLeaf n) (z : ℕ → ℝ)
    (g : OtherNamespaces (j+1)) :
    cylinderField (enrichedCoefficients n h (Function.update u j 0) s)
        (gaussianNamespaceJoin (j+1) (z,g)) =
      cylinderField (enrichedCoefficients n h (Function.update u j 0) s)
        (gaussianNamespaceJoin (j+1) (0,g)) := by
  classical
  simp_rw [cylinderField_enriched_expand]
  congr 1
  · congr 1
    funext i
    exact (gaussianNamespaceJoin_other (j+1) z g ⟨0,by omega⟩ i).trans
      (gaussianNamespaceJoin_other (j+1) 0 g ⟨0,by omega⟩ i).symm
  · apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = j
    · subst k
      simp
    · congr 1
      congr 1
      funext i
      have hv : (k:ℕ)+1 ≠ (j:ℕ)+1 := by
        intro he
        apply hk
        apply Fin.ext
        omega
      exact (gaussianNamespaceJoin_other (j+1) z g ⟨k+1,hv⟩ i).trans
        (gaussianNamespaceJoin_other (j+1) 0 g ⟨k+1,hv⟩ i).symm

lemma cylinderField_enriched_insert {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (j : Fin N) (v : ℝ) (s : Spin N × LabeledLeaf n) (z : ℕ → ℝ)
    (g : OtherNamespaces (j+1)) :
    cylinderField (enrichedCoefficients n h (Function.update u j v) s)
        (gaussianNamespaceJoin (j+1) (z,g)) =
      cylinderField (enrichedCoefficients n h (Function.update u j 0) s)
        (gaussianNamespaceJoin (j+1) (0,g)) +
      (Real.sqrt N*perturbationScale N*perturbationWeight j*v) *
        cylinderField (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 s) z := by
  rw [cylinderField_enriched_update,cylinderField_enriched_frozen]
  simp only [gaussianNamespaceJoin_selected]

lemma namespaceInsertion_preserving {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (j : ℕ) :
    MeasurePreserving (fun p : (Ω × OtherNamespaces j) × (ℕ → ℝ) =>
      (p.1.1,gaussianNamespaceJoin j (p.2,p.1.2)))
      ((P.prod (otherNamespacesLaw j)).prod gaussianCoordinates)
      (P.prod gaussianCoordinates) := by
  have h1 := measurePreserving_prodAssoc P (otherNamespacesLaw j) gaussianCoordinates
  have h2 := (MeasurePreserving.id P).prod
    (gaussianNamespaceJoin_preserving j |>.comp Measure.measurePreserving_swap)
  exact h2.comp h1

end IsingPerceptron

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace IsingPerceptron

def gibbsProbability {X : Type*} [MeasurableSpace X] (ν : Measure X) (H : X → ℝ) : Measure X :=
  if referencePartition ν H = 0 then ν else ν.tilted H

instance gibbsProbability_probability {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) :
    IsProbabilityMeasure (gibbsProbability ν H) := by
  unfold gibbsProbability
  split_ifs with h
  · infer_instance
  · apply isProbabilityMeasure_tilted
    by_contra he
    exact h (integral_undef he)

lemma gibbsProbability_eq_tilted {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) :
    gibbsProbability ν H = ν.tilted H := by
  exact ite_eq_right (ne_of_gt (_root_.MeasureTheory.integral_exp_pos he))

lemma measurable_random_tilted_measure {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H) :
    Measurable (fun ω => (ν ω).tilted (fun x => H (ω,x))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he (ω : Ω) : (ν ω).tilted (fun x => H (ω,x)) s =
      ∑' x, s.indicator (fun x => (ν ω).tilted (fun x => H (ω,x)) {x}) x :=
    (Measure.tsum_indicator_apply_singleton _ s hs).symm
  simp_rw [he]
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx,tilted_singleton]
    exact (((hH.comp (measurable_id.prodMk measurable_const)).exp.div
      (measurable_random_referencePartition hν hH)).ennreal_ofReal).mul
      ((Measure.measurable_coe (measurableSet_singleton x)).comp hν)
  · simp only [Set.indicator_of_notMem hx]
    exact measurable_const

lemma measurable_gibbsProbability {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H) :
    Measurable (fun ω => gibbsProbability (ν ω) (fun x => H (ω,x))) := by
  exact Measurable.ite (measurableSet_eq_fun (measurable_random_referencePartition hν hH) measurable_const)
    hν (measurable_random_tilted_measure hν hH)

lemma integrable_exp_bounded_add {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {H B : X → ℝ} (he : Integrable (fun x => Real.exp (H x)) ν)
    (hB : Measurable B) {K : ℝ} (hbound : ∀ x, B x ≤ K) :
    Integrable (fun x => Real.exp (B x+H x)) ν := by
  have hm : AEStronglyMeasurable (fun x => Real.exp (H x)*Real.exp (B x)) ν :=
    he.aestronglyMeasurable.mul hB.exp.aestronglyMeasurable
  apply (he.const_mul (Real.exp K)).mono'
  · simpa only [Real.exp_add,mul_comm,Pi.mul_apply] using hm
  · exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_add]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbound x)) (Real.exp_pos _).le)

lemma gibbsProbability_fold {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H G : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν)
    (heg : Integrable (fun x => Real.exp (H x+G x)) ν) :
    gibbsProbability (gibbsProbability ν H) G = gibbsProbability ν (fun x => H x+G x) := by
  rw [gibbsProbability_eq_tilted ν H he]
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  have hg : Integrable (fun x => Real.exp (G x)) (ν.tilted H) := by
    rw [integrable_tilted_iff he]
    simpa only [smul_eq_mul,← Real.exp_add] using heg
  rw [gibbsProbability_eq_tilted _ G hg,gibbsProbability_eq_tilted _ _ heg,tilted_tilted he]
  rfl

lemma cgf_fold {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H Y : X → ℝ) (t : ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν)
    (het : Integrable (fun x => Real.exp (H x+t*Y x)) ν) :
    cgf Y (gibbsProbability ν H) t =
      Real.log (referencePartition ν (fun x => H x+t*Y x)) - Real.log (referencePartition ν H) := by
  rw [gibbsProbability_eq_tilted _ _ he]
  unfold cgf mgf
  rw [integral_exp_tilted]
  simp only [Pi.add_apply]
  rw [Real.log_div (ne_of_gt (_root_.MeasureTheory.integral_exp_pos het))
    (ne_of_gt (_root_.MeasureTheory.integral_exp_pos he))]
  rfl

lemma quadratic_minimum_subtract_constant {I : Set ℝ} {g : ℝ → ℝ} {v c a b : ℝ}
    (h : ∀ t ∈ I, -g v+c*(v-a)^2 ≤ -g t+c*(t-a)^2) :
    ∀ t ∈ I, -(g v-b)+c*(v-a)^2 ≤ -(g t-b)+c*(t-a)^2 := by
  intro t ht
  linarith [h t ht]

lemma centered_sub_L1_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {F B : Ω → ℝ} (hF : Integrable F P) (hB : Integrable B P)
    {δF δB : ℝ}
    (hcF : (∫ ω, |F ω-∫ ω', F ω' ∂P| ∂P) ≤ δF)
    (hcB : (∫ ω, |B ω-∫ ω', B ω' ∂P| ∂P) ≤ δB) [IsFiniteMeasure P] :
    (∫ ω, |F ω-B ω-∫ ω', (F ω'-B ω') ∂P| ∂P) ≤ δF+δB := by
  rw [integral_sub hF hB]
  have hiF : Integrable (fun ω => |F ω-∫ ω', F ω' ∂P|) P := (hF.sub (integrable_const _)).abs
  have hiB : Integrable (fun ω => |B ω-∫ ω', B ω' ∂P|) P := (hB.sub (integrable_const _)).abs
  calc
    _ ≤ ∫ ω, |F ω-∫ ω', F ω' ∂P|+|B ω-∫ ω', B ω' ∂P| ∂P := by
      apply integral_mono ((hF.sub hB).sub (integrable_const _)).abs (hiF.add hiB)
      intro ω
      change |F ω-B ω-((∫ ω', F ω' ∂P)-(∫ ω', B ω' ∂P))| ≤ _
      rw [show F ω-B ω-((∫ ω', F ω' ∂P)-(∫ ω', B ω' ∂P)) =
        (F ω-∫ ω', F ω' ∂P)-(B ω-∫ ω', B ω' ∂P) by ring]
      exact abs_sub _ _
    _ = (∫ ω, |F ω-∫ ω', F ω' ∂P| ∂P)+(∫ ω, |B ω-∫ ω', B ω' ∂P| ∂P) :=
      integral_add hiF hiB
    _ ≤ _ := add_le_add hcF hcB

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_labeledSpinReference {N : ℕ} (n : ℕ) (ν : Measure (Spin N))
    [IsProbabilityMeasure ν] : Measurable (labeledSpinReference n ν) := by
  let κ : Kernel (LabeledTree n) (LabeledLeaf n) :=
    ⟨labeledLeafLaw n,measurable_labeledLeafLaw n⟩
  have : IsMarkovKernel κ := ⟨fun T => by
    change IsProbabilityMeasure (labeledLeafLaw n T)
    infer_instance⟩
  have he : (fun T => ((Kernel.const (LabeledTree n) ν).prod κ) T) =
      labeledSpinReference n ν := by
    funext T
    rw [Kernel.prod_apply,Kernel.const_apply]
    rfl
  rw [← he]
  exact ((Kernel.const (LabeledTree n) ν).prod κ).measurable

abbrev EnrichedFrozenData (n : ℕ) (j : ℕ) (A : Type*) :=
  EnrichedCylinderBase n A × OtherNamespaces (j+1)

def enrichedFrozenLaw {A : Type*} [MeasurableSpace A] (P : Measure A)
    (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) (j : ℕ) : Measure (EnrichedFrozenData n j A) :=
  (enrichedCylinderBaseLaw P r n b).prod (otherNamespacesLaw (j+1))

instance enrichedFrozenLaw_probability {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) (j : ℕ) :
    IsProbabilityMeasure (enrichedFrozenLaw P r n b j) := by
  unfold enrichedFrozenLaw
  infer_instance

def enrichedInsert (n j : ℕ) {A : Type*}
    (p : EnrichedFrozenData n j A × (ℕ → ℝ)) : EnrichedCylinderData n A :=
  (p.1.1,gaussianNamespaceJoin (j+1) (p.2,p.1.2))

lemma enrichedInsert_preserving {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) (j : ℕ) :
    MeasurePreserving (enrichedInsert (A := A) n j)
      ((enrichedFrozenLaw P r n b j).prod gaussianCoordinates) (enrichedCylinderLaw P r n b) :=
  namespaceInsertion_preserving (enrichedCylinderBaseLaw P r n b) (j+1)

def enrichedFrozenHamiltonian {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (j : Fin N) (φ : A → Spin N → ℝ)
    (ω : EnrichedFrozenData n j A) (s : Spin N × LabeledLeaf n) : ℝ :=
  patternBase φ (fun i : Fin ω.1.1.1 => ω.1.1.2 i) s.1 +
    cylinderField (enrichedCoefficients n h (Function.update u j 0) s)
      (gaussianNamespaceJoin (j+1) (0,ω.2))

lemma measurable_patternBase_infinite {N : ℕ} {A : Type*} [MeasurableSpace A]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (fun p : (ℕ × (ℕ → A)) × Spin N =>
      patternBase φ (fun i : Fin p.1.1 => p.1.2 i) p.2) := by
  have hφm : Measurable (fun p : A × Spin N => φ p.1 p.2) :=
    measurable_from_prod_countable_left (fun x => (measurable_pi_apply x).comp hm)
  let F : ℕ × ((ℕ → A) × Spin N) → ℝ := fun p =>
    patternBase φ (fun i : Fin p.1 => p.2.1 i) p.2.2
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro M
    change Measurable (fun p : (ℕ → A) × Spin N => ∑ i : Fin M, φ (p.1 i) p.2)
    apply Finset.measurable_sum
    intro i _
    have hi : Measurable (fun p : (ℕ → A) × Spin N => (p.1 (i:ℕ),p.2)) := by fun_prop
    exact hφm.comp hi
  exact hF.comp (show Measurable (fun p : (ℕ × (ℕ → A)) × Spin N =>
    (p.1.1,(p.1.2,p.2))) from by fun_prop)

lemma measurable_enrichedFrozenHamiltonian {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (j : Fin N)
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (fun p : EnrichedFrozenData n j A × (Spin N × LabeledLeaf n) =>
      enrichedFrozenHamiltonian n h u j φ p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro s
  unfold enrichedFrozenHamiltonian
  apply Measurable.add
  · have hg : Measurable (fun ω : EnrichedFrozenData n j A => (ω.1.1,s.1)) :=
      measurable_fst.fst.prodMk measurable_const
    exact (measurable_patternBase_infinite hm).comp hg
  · have hg : Measurable (fun p : EnrichedFrozenData n j A =>
        gaussianNamespaceJoin (j+1) (0,p.2)) :=
      (measurable_gaussianNamespaceJoin (j+1)).comp
        (measurable_const.prodMk measurable_snd)
    exact (measurable_cylinderField (enrichedCoefficients n h (Function.update u j 0) s)).comp hg

def enrichedFrozenReference {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (j : Fin N) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (ω : EnrichedFrozenData n j A) : Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability (labeledSpinReference n ν ω.1.2) (enrichedFrozenHamiltonian n h u j φ ω)

instance enrichedFrozenReference_probability {N : ℕ} {A : Type*}
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (j : Fin N)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν] (φ : A → Spin N → ℝ)
    (ω : EnrichedFrozenData n j A) :
    IsProbabilityMeasure (enrichedFrozenReference n h u j ν φ ω) := by
  unfold enrichedFrozenReference
  infer_instance

lemma measurable_enrichedFrozenReference {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (j : Fin N)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν] {φ : A → Spin N → ℝ}
    (hm : Measurable φ) : Measurable (enrichedFrozenReference n h u j ν φ) := by
  exact measurable_gibbsProbability
    (ν := fun ω : EnrichedFrozenData n j A => labeledSpinReference n ν ω.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd)
    (measurable_enrichedFrozenHamiltonian n h u j hm)

lemma update_abs_le_two {N : ℕ} {u : Fin N → ℝ} (hu : ∀ j, |u j| ≤ 2)
    (j : Fin N) {v : ℝ} (hv : |v| ≤ 2) : ∀ k, |Function.update u j v k| ≤ 2 := by
  intro k
  by_cases hk : k = j
  · subst k; simpa using hv
  · simpa [hk] using hu k

lemma enrichedCylinder_exp_ae {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (r : ℝ≥0) :
    ∀ᵐ p ∂enrichedCylinderLaw P r n b,
      Integrable (fun s => Real.exp
        (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i) s.1 +
        cylinderField (enrichedCoefficients n h u s) p.2)) (labeledSpinReference n ν p.1.2) := by
  have he := random_cylinder_all_exp_ae (P := enrichedCylinderBaseLaw P r n b)
    (ν := fun p : EnrichedCylinderBase n A => labeledSpinReference n ν p.2)
    ((measurable_labeledSpinReference n ν).comp measurable_snd)
    (enrichedCoefficients n h u) (enrichedCoefficients_variance_le hN n hh h0 u hu)
  filter_upwards [he] with p hp
  apply integrable_exp_bounded_add (by simpa using hp 1) (measurable_of_countable _)
    (K := (p.1.1.1:ℝ)*K)
  intro s
  let y : Fin p.1.1.1 → A := fun i => p.1.1.2 i
  have hb : |patternBase φ y s.1| ≤ ‖patternBase φ y‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (patternBase φ y) s.1
  exact (le_abs_self _).trans (hb.trans (patternBase_bound hK hφ y))

def perturbationAmplitude (N j : ℕ) : ℝ :=
  Real.sqrt N*perturbationScale N*perturbationWeight j

lemma perturbationAmplitude_pos {N : ℕ} (hN : 0 < N) (j : ℕ) :
    0 < perturbationAmplitude N j := by
  unfold perturbationAmplitude perturbationScale perturbationWeight
  positivity

lemma enrichedInsertedPressure_eq {N : ℕ} {A : Type*}
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (j : Fin N)
    (ν : Measure (Spin N)) (φ : A → Spin N → ℝ) (v : ℝ)
    (p : EnrichedFrozenData n j A × (ℕ → ℝ)) :
    enrichedCylinderPressure n h (Function.update u j v) ν φ (enrichedInsert n j p) =
      (Real.log (referencePartition (labeledSpinReference n ν p.1.1.2)
        (fun s => enrichedFrozenHamiltonian n h u j φ p.1 s +
          (perturbationAmplitude N j*v)*
          cylinderField (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 s) p.2)) -
        N*h n/2)/N := by
  unfold enrichedCylinderPressure enrichedInsert referencePartition
  dsimp only
  congr 3
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  rw [cylinderField_enriched_insert]
  unfold enrichedFrozenHamiltonian perturbationAmplitude
  ring

lemma enrichedFrozen_exp_ae {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (j : Fin N)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (r : ℝ≥0) :
    ∀ᵐ ω ∂enrichedFrozenLaw P r n b j,
      Integrable (fun s => Real.exp (enrichedFrozenHamiltonian n h u j φ ω s))
        (labeledSpinReference n ν ω.1.2) := by
  have hp := enrichedInsert_preserving P r n b j
  have he := enrichedCylinder_exp_ae hN n b hh h0 (Function.update u j 0)
    (update_abs_le_two hu j (by norm_num)) ν P hK hφ r
  have he' := ae_of_ae_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ he)
  have hg : ∀ᵐ p ∂(enrichedFrozenLaw P r n b j).prod gaussianCoordinates,
      Integrable (fun s => Real.exp (enrichedFrozenHamiltonian n h u j φ p.1 s))
        (labeledSpinReference n ν p.1.1.2) := by
    filter_upwards [he'] with p hp'
    apply hp'.congr
    filter_upwards [] with s
    change Real.exp (patternBase φ (fun i : Fin p.1.1.1.1 => p.1.1.1.2 i) s.1 +
      cylinderField (enrichedCoefficients n h (Function.update u j 0) s)
        (gaussianNamespaceJoin (j+1) (p.2,p.1.2))) = _
    rw [cylinderField_enriched_insert]
    simp only [mul_zero,zero_mul,add_zero,enrichedFrozenHamiltonian]

  filter_upwards [Measure.ae_ae_of_ae_prod hg] with ω hω
  obtain ⟨g,hg⟩ := hω.exists
  exact hg

lemma enrichedInserted_exp_ae {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (j : Fin N) {v : ℝ} (hv : |v| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (r : ℝ≥0) :
    ∀ᵐ p ∂(enrichedFrozenLaw P r n b j).prod gaussianCoordinates,
      Integrable (fun s => Real.exp (enrichedFrozenHamiltonian n h u j φ p.1 s +
        (perturbationAmplitude N j*v)*
          cylinderField (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 s) p.2))
        (labeledSpinReference n ν p.1.1.2) := by
  have hp := enrichedInsert_preserving P r n b j
  have he := enrichedCylinder_exp_ae hN n b hh h0 (Function.update u j v)
    (update_abs_le_two hu j hv) ν P hK hφ r
  have he' := ae_of_ae_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ he)
  filter_upwards [he'] with p hp'
  apply hp'.congr
  filter_upwards [] with s
  change Real.exp (patternBase φ (fun i : Fin p.1.1.1.1 => p.1.1.1.2 i) s.1 +
    cylinderField (enrichedCoefficients n h (Function.update u j v) s)
      (gaussianNamespaceJoin (j+1) (p.2,p.1.2))) = _
  rw [cylinderField_enriched_insert]
  simp only [enrichedFrozenHamiltonian,perturbationAmplitude,add_assoc]

theorem enriched_cgf_eq_pressure_difference {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (j : Fin N) {v : ℝ} (hv : |v| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (r : ℝ≥0) :
    ∀ᵐ p ∂(enrichedFrozenLaw P r n b j).prod gaussianCoordinates,
      cgf (fun s => cylinderField (monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 s) p.2)
        (enrichedFrozenReference n h u j ν φ p.1) (perturbationAmplitude N j*v) =
      N*(enrichedCylinderPressure n h (Function.update u j v) ν φ (enrichedInsert n j p) -
        enrichedCylinderPressure n h (Function.update u j 0) ν φ (enrichedInsert n j p)) := by
  have he0 := (Measure.quasiMeasurePreserving_fst
    (μ := enrichedFrozenLaw P r n b j) (ν := gaussianCoordinates)).tendsto_ae.eventually
      (enrichedFrozen_exp_ae hN n b hh h0 u hu j ν P hK hφ r)
  have he := enrichedInserted_exp_ae hN n b hh h0 u hu j hv ν P hK hφ r
  filter_upwards [he0,he] with p hp0 hp
  rw [enrichedFrozenReference,cgf_fold _ _ _ _ hp0 hp]
  rw [enrichedInsertedPressure_eq,enrichedInsertedPressure_eq]
  simp only [mul_zero,zero_mul,add_zero]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp
  ring

end IsingPerceptron

end

end OAI
