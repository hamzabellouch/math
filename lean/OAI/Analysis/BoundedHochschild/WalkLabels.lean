import Mathlib
import OAI.Analysis.BoundedHochschild.PrimitiveAverages
import OAI.Analysis.BoundedHochschild.RareScales

namespace OAI

/-! Bad-path probability bounds and symmetric rare-label random walks. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildRare
variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) [IsProbabilityMeasure ν]

lemma finite_coordinates_mass {I : Type*} [Fintype I] (s : Finset I) (A : Set X) :
    (Measure.pi (fun _ : I => ν)).real {w | ∀ i ∈ s, w i ∈ A} = ν.real A ^ s.card := by
  change ((Measure.pi (fun _ : I => ν)) ((s : Set I).pi (fun _ => A))).toReal = _
  rw [Measure.pi_pi_finset]
  simp only [Finset.prod_const, ENNReal.toReal_pow, Measure.real_def]

lemma some_coordinate_mass_le {I : Type*} [Fintype I] (A : Set X)
    (hA : MeasurableSet A) :
    (Measure.pi (fun _ : I => ν)).real {w | ∃ i, w i ∈ A} ≤ Fintype.card I * ν.real A := by
  have he : {w : I → X | ∃ i, w i ∈ A} = ⋃ i : I, Function.eval i ⁻¹' A := by
    ext w; simp
  rw [he]
  calc
    _ ≤ ∑ i : I, (Measure.pi (fun _ : I => ν)).real (Function.eval i ⁻¹' A) :=
      measureReal_iUnion_fintype_le _
    _ = _ := by
      simp only [(measurePreserving_eval (fun _ : I => ν) _).measureReal_preimage hA.nullMeasurableSet,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

 

lemma label_collision_mass_le {I J : Type*} [Fintype I] [Fintype J]
    (A : J → Set X) :
    (Measure.pi (fun _ : I => ν)).real
      {w | ∃ i j : I, i ≠ j ∧ ∃ a : J, w i ∈ A a ∧ w j ∈ A a} ≤
      ((Fintype.card I).choose 2 : ℝ) * ∑ a : J, ν.real (A a)^2 := by
  classical
  let Z := (Finset.univ : Finset I).powersetCard 2
  let E (s : Finset I) (a : J) := {w : I → X | ∀ i ∈ s, w i ∈ A a}
  have hsub : {w : I → X | ∃ i j : I, i ≠ j ∧ ∃ a : J, w i ∈ A a ∧ w j ∈ A a} ⊆
      ⋃ s ∈ Z, ⋃ a : J, E s a := by
    rintro w ⟨i,j,hij,a,hi,hj⟩
    refine Set.mem_iUnion.mpr ⟨{i,j},Set.mem_iUnion.mpr ⟨?_,Set.mem_iUnion.mpr ⟨a,?_⟩⟩⟩
    · simp [Z,Finset.mem_powersetCard,hij]
    · intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption
  calc
    _ ≤ (Measure.pi (fun _ : I => ν)).real (⋃ s ∈ Z, ⋃ a : J, E s a) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ s ∈ Z, (Measure.pi (fun _ : I => ν)).real (⋃ a : J, E s a) :=
      measureReal_biUnion_finset_le Z _
    _ ≤ ∑ s ∈ Z, ∑ a : J, (Measure.pi (fun _ : I => ν)).real (E s a) := by
      gcongr with s hs
      exact measureReal_iUnion_fintype_le _
    _ = _ := by
      have hc (s : Finset I) (hs : s ∈ Z) : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
      simp_rw [E,finite_coordinates_mass]
      rw [Finset.sum_congr rfl (fun s hs => by rw [hc s hs])]
      simp [Z,Finset.card_powersetCard,nsmul_eq_mul]

lemma uniform_label_collision_mass_le {I J : Type*} [Fintype I] [Fintype J]
    (A : J → Set X) (p : ℝ) (hA : ∀ j, ν.real (A j) = p / Fintype.card J)
    (hJ : 0 < Fintype.card J) :
    (Measure.pi (fun _ : I => ν)).real
      {w | ∃ i j : I, i ≠ j ∧ ∃ a : J, w i ∈ A a ∧ w j ∈ A a} ≤
      ((Fintype.card I).choose 2 : ℝ) * p^2 / Fintype.card J := by
  have h : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
  convert label_collision_mass_le ν A using 1
  simp only [hA,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

 
lemma path_miss_mass {r n : ℕ} (i : Fin r) (A : Set X) :
    (Measure.pi (fun _ : Fin r × Fin n => ν)).real {w | ∀ j, w (i,j) ∉ A} =
      ν.real Aᶜ ^ n := by
  classical
  let s : Finset (Fin r × Fin n) := Finset.univ.image (fun j : Fin n => (i,j))
  have hs : s.card = n := by
    rw [Finset.card_image_of_injective _ (by intro a b h; exact (Prod.mk.inj h).2)]
    exact Finset.card_fin n
  have he : {w : Fin r × Fin n → X | ∀ j, w (i,j) ∉ A} = {w | ∀ a ∈ s, w a ∈ Aᶜ} := by
    ext w
    simp [s]
  rw [he,finite_coordinates_mass,hs]

lemma some_path_miss_mass_le {r n : ℕ} (A : Set X) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : Fin r × Fin n => ν)).real {w | ∃ i, ∀ j, w (i,j) ∉ A} ≤
      r * (1-ν.real A)^n := by
  have he : {w : Fin r × Fin n → X | ∃ i, ∀ j, w (i,j) ∉ A} =
      ⋃ i : Fin r, {w | ∀ j, w (i,j) ∉ A} := by ext w; simp
  rw [he]
  calc
    _ ≤ ∑ i : Fin r, (Measure.pi (fun _ : Fin r × Fin n => ν)).real {w | ∀ j, w (i,j) ∉ A} :=
      measureReal_iUnion_fintype_le _
    _ = _ := by simp only [path_miss_mass, measureReal_compl hA, probReal_univ,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

def badPaths {r n : ℕ} {J : Type*} (T B A : Set X) (L : J → Set X) : Set (Fin r × Fin n → X) :=
  {w | (∃ i, w i ∈ T) ∨ (∃ i, w i ∈ B) ∨
    (∃ i j, i ≠ j ∧ ∃ a, w i ∈ L a ∧ w j ∈ L a) ∨
      ∃ i, ∀ j, w (i,j) ∉ A}

 

theorem badPaths_mass_le {r n : ℕ} {J : Type*} [Fintype J]
    (T B A : Set X) (L : J → Set X) (hT : MeasurableSet T) (hB : MeasurableSet B)
    (hA : MeasurableSet A) (p : ℝ) (hL : ∀ j, ν.real (L j) = p / Fintype.card J)
    (hJ : 0 < Fintype.card J) :
    (Measure.pi (fun _ : Fin r × Fin n => ν)).real (badPaths T B A L) ≤
      (r*n:ℕ) * ν.real T + (r*n:ℕ) * ν.real B +
      (((r*n).choose 2:ℕ):ℝ) * p^2 / Fintype.card J + r*(1-ν.real A)^n := by
  let E₁ : Set (Fin r × Fin n → X) := {w | ∃ i, w i ∈ T}
  let E₂ : Set (Fin r × Fin n → X) := {w | ∃ i, w i ∈ B}
  let E₃ : Set (Fin r × Fin n → X) := {w | ∃ i j, i ≠ j ∧ ∃ a, w i ∈ L a ∧ w j ∈ L a}
  let E₄ : Set (Fin r × Fin n → X) := {w | ∃ i, ∀ j, w (i,j) ∉ A}
  have h₁ := some_coordinate_mass_le (I := Fin r × Fin n) ν T hT
  have h₂ := some_coordinate_mass_le (I := Fin r × Fin n) ν B hB
  have h₃ := uniform_label_collision_mass_le (I := Fin r × Fin n) ν L p hL hJ
  have h₄ := some_path_miss_mass_le (r := r) (n := n) ν A hA
  simp only [Fintype.card_prod,Fintype.card_fin] at h₁ h₂ h₃
  have he : badPaths (r := r) (n := n) T B A L = E₁ ∪ (E₂ ∪ (E₃ ∪ E₄)) := rfl
  rw [he]
  have hb₁ := measureReal_union_le (μ := Measure.pi (fun _ : Fin r × Fin n => ν)) E₁ (E₂ ∪ (E₃ ∪ E₄))
  have hb₂ := measureReal_union_le (μ := Measure.pi (fun _ : Fin r × Fin n => ν)) E₂ (E₃ ∪ E₄)
  have hb₃ := measureReal_union_le (μ := Measure.pi (fun _ : Fin r × Fin n => ν)) E₃ E₄
  dsimp [E₁,E₂,E₃,E₄] at hb₁ hb₂ hb₃
  linarith

end HochschildRare

 

open MeasureTheory Filter Topology
open scoped ENNReal Function
namespace HochschildRare

def baseMass : ℝ := 1 - ∑' n, p n
lemma baseMass_le_one : baseMass ≤ 1 := by
  have : 0 ≤ ∑' n, p n := tsum_nonneg (fun n => (p_pos n).le)
  unfold baseMass
  linarith
lemma baseMass_pos : 0 < baseMass := by unfold baseMass; linarith [sum_p_le]

def baseWeight (j : ℕ) : ℝ := (1/2:ℝ)^(j+1)
lemma baseWeight_pos (j : ℕ) : 0 < baseWeight j := by unfold baseWeight; positivity
lemma summable_baseWeight : Summable baseWeight := by
  exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).comp_injective
    Nat.succ_injective
lemma sum_baseWeight : ∑' j, baseWeight j = 1 := by
  simp only [baseWeight,pow_succ]
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)]
  norm_num

 
abbrev Label := ℕ ⊕ ((n : ℕ) × Fin (labels n))
instance : MeasurableSpace Label := ⊤
instance : MeasurableSingletonClass Label := ⟨fun _ => trivial⟩

def labelWeight : Label → ℝ≥0∞
  | .inl j => ENNReal.ofReal (baseMass * baseWeight j)
  | .inr a => ENNReal.ofReal (p a.1 / labels a.1)

lemma sum_uniform_weight (n : ℕ) :
    ∑' _j : Fin (labels n), ENNReal.ofReal (p n / labels n) = ENNReal.ofReal (p n) := by
  have hd : (labels n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (labels_pos n))
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => div_nonneg (p_pos n).le (Nat.cast_nonneg _))]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  field_simp

lemma tsum_labelWeight : ∑' a, labelWeight a = 1 := by
  change (∑' a : ℕ ⊕ ((n : ℕ) × Fin (labels n)), labelWeight a) = _
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  simp only [labelWeight]
  rw [ENNReal.tsum_sigma']
  simp only [sum_uniform_weight]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg baseMass_pos.le (baseWeight_pos j).le)
      (summable_baseWeight.mul_left baseMass), tsum_mul_left, sum_baseWeight, mul_one,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => (p_pos n).le) summable_p,
    ← ENNReal.ofReal_add baseMass_pos.le (tsum_nonneg (fun n => (p_pos n).le))]
  simp [baseMass]

def labelPMF : PMF Label := ⟨labelWeight, by
  simpa only [tsum_labelWeight] using (ENNReal.summable (f := labelWeight)).hasSum⟩
def labelLaw : Measure Label := labelPMF.toMeasure
instance : IsProbabilityMeasure labelLaw := by unfold labelLaw; infer_instance

lemma labelLaw_singleton (a : Label) : labelLaw {a} = labelWeight a :=
  labelPMF.toMeasure_apply_singleton a (measurableSet_singleton a)

lemma stage_label_mass (n : ℕ) (j : Fin (labels n)) :
    labelLaw.real {Sum.inr ⟨n,j⟩} = p n / labels n := by
  rw [Measure.real_def,labelLaw_singleton]
  exact ENNReal.toReal_ofReal (div_nonneg (p_pos n).le (Nat.cast_nonneg _))

lemma stage_mass (n : ℕ) :
    labelLaw.real {a | ∃ j : Fin (labels n), a = Sum.inr ⟨n,j⟩} = p n := by
  classical
  have he : {a : Label | ∃ j : Fin (labels n), a = Sum.inr ⟨n,j⟩} =
      ⋃ j : Fin (labels n), {Sum.inr ⟨n,j⟩} := by ext a; simp [eq_comm]
  rw [he,measureReal_iUnion_fintype]
  · simp only [stage_label_mass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hd : (labels n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (labels_pos n))
    field_simp
  · intro i j hij
    simpa only [Function.onFun,Set.disjoint_singleton,ne_eq,Sum.inr.injEq,Sigma.mk.inj_iff,
      true_and,heq_eq_eq] using hij
  · intro j
    exact measurableSet_singleton _

def stageSet (n : ℕ) : Set Label := {a | ∃ j : Fin (labels n), a = Sum.inr ⟨n,j⟩}
def tailSet (n : ℕ) : Set Label := {a | ∃ k, n < k ∧ a ∈ stageSet k}
def baseTail (N : ℕ) : Set Label := {a | ∃ j, N ≤ j ∧ a = Sum.inl j}

lemma stageSet_disjoint : Pairwise (Disjoint on stageSet) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  rintro a ⟨i,rfl⟩ ⟨j,hj⟩
  exact hnm (congrArg Sigma.fst (Sum.inr.inj hj))

lemma tail_mass (n : ℕ) : labelLaw.real (tailSet n) = ∑' k, p (n+1+k) := by
  have he : tailSet n = ⋃ k : ℕ, stageSet (n+1+k) := by
    ext a
    simp only [tailSet,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨j,hj,ha⟩
      exact ⟨j-(n+1),by simpa [Nat.add_sub_of_le (by omega : n+1 ≤ j)] using ha⟩
    · rintro ⟨k,hk⟩
      exact ⟨n+1+k,by omega,hk⟩
  rw [Measure.real_def,he,measure_iUnion]
  · rw [ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
    exact tsum_congr (fun k => stage_mass (n+1+k))
  · intro i j hij
    exact stageSet_disjoint (by omega)
  · intro k
    exact Set.Countable.measurableSet (Set.to_countable _)

lemma base_label_mass (j : ℕ) : labelLaw.real {Sum.inl j} = baseMass * baseWeight j := by
  rw [Measure.real_def,labelLaw_singleton]
  exact ENNReal.toReal_ofReal (mul_nonneg baseMass_pos.le (baseWeight_pos j).le)

lemma base_tail_mass (N : ℕ) : labelLaw.real (baseTail N) = baseMass * (1/2:ℝ)^N := by
  have he : baseTail N = ⋃ k : ℕ, {Sum.inl (N+k)} := by
    ext a
    simp only [baseTail,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_singleton_iff]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ⟨j-N,by simp [Nat.add_sub_of_le hj]⟩
    · rintro ⟨k,hk⟩
      exact ⟨N+k,by omega,hk⟩
  have hd : Pairwise (Disjoint on (fun k : ℕ => ({Sum.inl (N+k)} : Set Label))) := by
    intro i j hij
    simp only [Function.onFun,Set.disjoint_singleton,ne_eq,Sum.inl.injEq]
    omega
  rw [Measure.real_def,he,measure_iUnion hd (fun _ => measurableSet_singleton _),
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  simp only [← Measure.real_def,base_label_mass]
  simp_rw [baseWeight,show ∀ k : ℕ, N+k+1 = N+(k+1) by omega,pow_add]
  rw [tsum_mul_left,tsum_mul_left]
  simp_rw [← pow_add]
  change baseMass * ((1/2:ℝ)^N * ∑' k,baseWeight k) = _
  rw [sum_baseWeight,mul_one]

lemma exists_base_cut (n : ℕ) : ∃ N, labelLaw.real (baseTail N) < (slots n:ℝ)⁻¹^2 := by
  have hp : 0 < (slots n:ℝ)⁻¹^2 := by have := slots_pos n; positivity
  have ht : Tendsto (fun N => baseMass * (1/2:ℝ)^N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul baseMass
  obtain ⟨N,hN⟩ := (ht.eventually (gt_mem_nhds hp)).exists
  exact ⟨N,by simpa [base_tail_mass] using hN⟩

def signLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
instance : IsProbabilityMeasure signLaw := by unfold signLaw; infer_instance

lemma signLaw_singleton (b : Bool) : signLaw {b} = (2:ℝ≥0∞)⁻¹ := by
  rw [signLaw,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp

lemma sign_flip_preserving : MeasurePreserving Bool.not signLaw signLaw := by
  refine ⟨measurable_of_countable _,Measure.ext_of_singleton (fun b => ?_)⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : Bool.not ⁻¹' {b} = {(!b)} := by ext c; cases b <;> cases c <;> simp
  rw [he,signLaw_singleton,signLaw_singleton]

abbrev Increment := Label × Bool
def incrementLaw : Measure Increment := labelLaw.prod signLaw
instance : IsProbabilityMeasure incrementLaw := by unfold incrementLaw; infer_instance

lemma increment_fst_preserving : MeasurePreserving Prod.fst incrementLaw labelLaw :=
  measurePreserving_fst
lemma increment_flip_preserving :
    MeasurePreserving (fun a : Increment => (a.1,!a.2)) incrementLaw incrementLaw :=
  (MeasurePreserving.id labelLaw).prod sign_flip_preserving

lemma increment_label_mass (A : Set Label) : incrementLaw.real (Prod.fst ⁻¹' A) = labelLaw.real A :=
  increment_fst_preserving.measureReal_preimage
    (Set.Countable.measurableSet (Set.to_countable _)).nullMeasurableSet

abbrev WalkGroup := FreeGroup Label
instance : MeasurableSpace WalkGroup := ⊤
instance : MeasurableSingletonClass WalkGroup := ⟨fun _ => trivial⟩

def incrementValue (a : Increment) : WalkGroup :=
  if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹

def walkLaw : Measure WalkGroup := incrementLaw.map incrementValue
instance : IsProbabilityMeasure walkLaw :=
  inferInstanceAs (IsProbabilityMeasure (incrementLaw.map incrementValue))

lemma incrementValue_preserving : MeasurePreserving incrementValue incrementLaw walkLaw :=
  ⟨measurable_of_countable _,rfl⟩

lemma walkLaw_symmetric : walkLaw.map (fun g => g⁻¹) = walkLaw := by
  have he := incrementValue_preserving.comp increment_flip_preserving
  rw [walkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  change incrementLaw.map ((fun g : WalkGroup => g⁻¹) ∘ incrementValue) = walkLaw
  have hh : (fun g : WalkGroup => g⁻¹) ∘ incrementValue =
      incrementValue ∘ (fun a : Increment => (a.1,!a.2)) := by
    funext a
    rcases a with ⟨a,b⟩
    cases b <;> simp [incrementValue]
  rw [hh]
  exact he.map_eq

lemma base_atom_pos (j : ℕ) : 0 < walkLaw {FreeGroup.of (Sum.inl j)} := by
  rw [walkLaw,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hsub : ({(Sum.inl j,true)} : Set Increment) ⊆
      incrementValue ⁻¹' {FreeGroup.of (Sum.inl j)} := by
    rintro a rfl
    simp [incrementValue]
  apply lt_of_lt_of_le _ (measure_mono hsub)
  have he : ({(Sum.inl j,true)} : Set Increment) = {Sum.inl j} ×ˢ {true} := by ext a; simp
  rw [he,incrementLaw,Measure.prod_prod,labelLaw_singleton,signLaw_singleton]
  apply ENNReal.mul_pos
  · exact (ENNReal.ofReal_pos.mpr (mul_pos baseMass_pos (baseWeight_pos j))).ne'
  · norm_num

end HochschildRare

 

open MeasureTheory Filter Topology
namespace HochschildRare

def badBound (k : ℕ) : ℝ :=
  (16/15:ℝ)*(k+1)*q k + (slots k:ℝ)⁻¹ + (1/2:ℝ)*(slots k:ℝ)⁻¹^2 +
    (k+1:ℝ)*(1-p k)^time k

lemma badBound_tendsto : Tendsto badBound atTop (𝓝 0) := bad_bound_tendsto

lemma rare_four_terms_le (k r : ℕ) (hr : r ≤ k+1) (t b : ℝ)
    (ht : t ≤ (16/15:ℝ)*p k^2) (hb : b ≤ (slots k:ℝ)⁻¹^2) :
    (r*time k:ℕ)*t + (r*time k:ℕ)*b +
      (((r*time k).choose 2:ℕ):ℝ)*p k^2/labels k + r*(1-p k)^time k ≤ badBound k := by
  have hK : 0 < (slots k:ℝ) := by exact_mod_cast slots_pos k
  have hm : (r*time k:ℕ) ≤ slots k := Nat.mul_le_mul_right _ hr
  have hmR : ((r*time k:ℕ):ℝ) ≤ slots k := by exact_mod_cast hm
  have htail : ((r*time k:ℕ):ℝ)*t ≤ (16/15:ℝ)*(k+1)*q k := calc
    _ ≤ ((r*time k:ℕ):ℝ)*((16/15:ℝ)*p k^2) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ (slots k:ℝ)*((16/15:ℝ)*p k^2) := mul_le_mul_of_nonneg_right hmR (by positivity)
    _ = _ := by rw [← mul_assoc,mul_comm (slots k:ℝ),mul_assoc,slots_mul_p_sq]; ring
  have hbase : ((r*time k:ℕ):ℝ)*b ≤ (slots k:ℝ)⁻¹ := calc
    _ ≤ ((r*time k:ℕ):ℝ)*(slots k:ℝ)⁻¹^2 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (slots k:ℝ)*(slots k:ℝ)⁻¹^2 := mul_le_mul_of_nonneg_right hmR (by positivity)
    _ = _ := by field_simp
  have hc : (((r*time k).choose 2:ℕ):ℝ) ≤ (slots k:ℝ)^2/2 := by
    rw [Nat.cast_choose_two]
    have hz : 0 ≤ ((r*time k:ℕ):ℝ) := by positivity
    nlinarith [mul_self_le_mul_self hz hmR]
  have hp : p k^2 ≤ 1 := by nlinarith [p_pos k,p_le k]
  have hlabel : 0 < (labels k:ℝ) := by exact_mod_cast labels_pos k
  have hcoll : (((r*time k).choose 2:ℕ):ℝ)*p k^2/labels k ≤ (1/2:ℝ)*(slots k:ℝ)⁻¹^2 := calc
    _ ≤ (((r*time k).choose 2:ℕ):ℝ)/labels k := by
      apply div_le_div_of_nonneg_right _ hlabel.le
      nlinarith [show (0:ℝ) ≤ ((r*time k).choose 2:ℕ) by positivity]
    _ ≤ ((slots k:ℝ)^2/2)/labels k := div_le_div_of_nonneg_right hc hlabel.le
    _ = _ := by simp only [labels,Nat.cast_pow]; field_simp
  have hmiss : (r:ℝ)*(1-p k)^time k ≤ (k+1:ℝ)*(1-p k)^time k := by
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hr)
    exact pow_nonneg (by linarith [p_le k]) _
  unfold badBound
  linarith

variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) [IsProbabilityMeasure ν]

theorem rare_badPaths_le (k r : ℕ) (hr : r ≤ k+1)
    (T B A : Set X) (L : Fin (labels k) → Set X)
    (hT : MeasurableSet T) (hB : MeasurableSet B) (hA : MeasurableSet A)
    (ht : ν.real T ≤ (16/15:ℝ)*p k^2) (hb : ν.real B ≤ (slots k:ℝ)⁻¹^2)
    (ha : ν.real A = p k) (hl : ∀ j, ν.real (L j) = p k / labels k) :
    (Measure.pi (fun _ : Fin r × Fin (time k) => ν)).real (badPaths T B A L) ≤ badBound k := by
  have hh := badPaths_mass_le (r := r) (n := time k) ν T B A L hT hB hA (p k)
    (by simpa only [Fintype.card_fin] using hl) (by simpa using labels_pos k)
  rw [ha,Fintype.card_fin] at hh
  exact hh.trans (rare_four_terms_le k r hr _ _ ht hb)

end HochschildRare

 

open MeasureTheory Filter Topology
namespace HochschildRare
open HochschildWalk

def baseCut (k : ℕ) : ℕ := (exists_base_cut k).choose
lemma baseCut_spec (k : ℕ) : labelLaw.real (baseTail (baseCut k)) < (slots k:ℝ)⁻¹^2 :=
  (exists_base_cut k).choose_spec

def stageBad (k r : ℕ) : Set (Fin r × Fin (time k) → Increment) :=
  badPaths (Prod.fst ⁻¹' tailSet k) (Prod.fst ⁻¹' baseTail (baseCut k))
    (Prod.fst ⁻¹' stageSet k) (fun j : Fin (labels k) => Prod.fst ⁻¹' {Sum.inr ⟨k,j⟩})

lemma stageBad_mass_le (k r : ℕ) (hr : r ≤ k+1) :
    (Measure.pi (fun _ : Fin r × Fin (time k) => incrementLaw)).real (stageBad k r) ≤ badBound k := by
  apply rare_badPaths_le incrementLaw k r hr
  · exact measurable_fst (Set.to_countable _).measurableSet
  · exact measurable_fst (Set.to_countable _).measurableSet
  · exact measurable_fst (Set.to_countable _).measurableSet
  · rw [increment_label_mass,tail_mass]
    exact sum_tail_le k
  · rw [increment_label_mass]
    exact (baseCut_spec k).le
  · rw [increment_label_mass]
    exact stage_mass k
  · intro j
    rw [increment_label_mass]
    exact stage_label_mass k j

 

def StageTests (φ : WalkGroup → ℝ) : Prop :=
  ∀ k r, r ≤ k+1 → ∀ w : Fin r × Fin (time k) → Increment, w ∉ stageBad k r →
    ∀ q : FreeGroup (Fin r), q ≠ 1 → q.toWord.length ≤ k+1 →
      φ (FreeGroup.lift (fun i => word (fun j => incrementValue (w (i,j)))) q) < 1/(k+1:ℝ)

lemma stages_time_atTop : Tendsto time atTop atTop := by
  apply tendsto_atTop_mono (f := fun k => k+1) _ (tendsto_add_atTop_nat 1)
  intro k
  have hk := successor_le_two_pow k
  exact hk.trans (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ 3*2^k))

 

theorem finite_tests_freeMoments (φ : WalkGroup → ℝ) (hf : StageTests φ) :
    FreeMomentsInProbability walkLaw φ time := by
  intro r q hq δ hδ
  have ht : Tendsto (fun k : ℕ => 1/(k+1:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ badBound_tendsto
  filter_upwards [eventually_ge_atTop (max r q.toWord.length), ht.eventually (gt_mem_nhds hδ)] with k hk hb
  have hr : r ≤ k+1 := by omega
  have hqk : q.toWord.length ≤ k+1 := by omega
  let E : Set (Fin r × Fin (time k) → WalkGroup) :=
    {w | δ ≤ φ (FreeGroup.lift (fun i => word (fun j => w (i,j))) q)}
  have he := measurePreserving_pi (fun _ : Fin r × Fin (time k) => incrementLaw)
    (fun _ : Fin r × Fin (time k) => walkLaw) (fun _ => incrementValue_preserving)
  have hm := he.measureReal_preimage (s := E) (Set.to_countable E).measurableSet.nullMeasurableSet
  change (Measure.pi (fun _ : Fin r × Fin (time k) => walkLaw)).real E ≤ _
  rw [← hm]
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (stageBad_mass_le k r hr)
  intro w hw
  by_contra hw'
  have hh := hf k r hr w hw' q hq hqk
  change δ ≤ φ (FreeGroup.lift (fun i => word (fun j => incrementValue (w (i,j)))) q) at hw
  linarith

end HochschildRare

 

open MeasureTheory Filter Topology
open scoped ENNReal
namespace HochschildRare
open HochschildWalk

lemma countable_atom_sum {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (μ : Measure G) [IsProbabilityMeasure μ] :
    ∑' g, μ {g} = 1 := by
  have hh := congrArg (fun ν : Measure G => ν Set.univ) μ.sum_smul_dirac
  simpa only [Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one,measure_univ] using hh

lemma countable_real_atom_sum {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (μ : Measure G) [IsProbabilityMeasure μ] :
    HasSum (fun g => μ.real {g}) 1 := by
  have hs := ENNReal.summable_toReal (by rw [countable_atom_sum μ]; norm_num : ∑' g, μ {g} ≠ ∞)
  apply hs.hasSum_iff.mpr
  rw [← ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _),countable_atom_sum μ,ENNReal.toReal_one]

lemma probability_eq_atomicLaw {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (μ : Measure G) [IsProbabilityMeasure μ] (e : ℕ ≃ G) :
    atomicLaw (fun j => μ.real {e j}) e = μ := by
  simp only [atomicLaw,Measure.real_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change Measure.sum ((fun g => μ {g} • Measure.dirac g) ∘ e) = μ
  rw [Measure.sum_comp_equiv e,Measure.sum_smul_dirac]

instance : Infinite WalkGroup := Infinite.of_injective FreeGroup.of FreeGroup.of_injective

def walkEnum : ℕ ≃ WalkGroup := Classical.choice inferInstance
def walkWeights (j : ℕ) : ℝ := walkLaw.real {walkEnum j}
lemma walkWeights_nonneg (j : ℕ) : 0 ≤ walkWeights j := measureReal_nonneg
lemma walkWeights_sum : HasSum walkWeights 1 :=
  walkEnum.hasSum_iff.mpr (countable_real_atom_sum walkLaw)
lemma walkLaw_eq_atomic : atomicLaw walkWeights walkEnum = walkLaw :=
  probability_eq_atomicLaw walkLaw walkEnum

end HochschildRare
end

end OAI
