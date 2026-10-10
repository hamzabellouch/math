import OAI.Dynamics.SmoothObstruction.FiniteEntropy

namespace OAI

section

open Finset

namespace SmoothObstruction.PartitionEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.FiniteEntropy
open scoped Topology
variable {X α β : Type*} [MeasurableSpace X] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  (μ : Measure X) [IsProbabilityMeasure μ]

noncomputable def mass (f : X → α) (a : α) : ℝ := μ.real (f ⁻¹' {a})
noncomputable def entropy (f : X → α) : ℝ := natEntropy (mass μ f)

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
lemma mass_nonneg (f : X → α) (a : α) : 0 ≤ mass μ f a := ENNReal.toReal_nonneg

lemma sum_mass {f : X → α} (hf : Measurable f) : ∑ a, mass μ f a = 1 := by
  have h := sum_measureReal_preimage_singleton (μ := μ) univ
    (fun a _ => (measurableSet_singleton a).preimage hf)
  simpa [mass] using h

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma push_mass {f : X → α} (hf : Measurable f) (g : α → β) :
    pushMass (mass μ f) g = mass μ (g ∘ f) := by
  classical
  funext b
  unfold pushMass
  rw [← sum_filter]
  have h := sum_measureReal_preimage_singleton (μ := μ) (univ.filter (fun a => g a = b))
    (fun a _ => (measurableSet_singleton a).preimage hf)
  rw [show f ⁻¹' ↑(univ.filter (fun a => g a = b)) = (g ∘ f) ⁻¹' {b} by
    ext x; simp] at h
  exact h

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma entropy_comp_le {f : X → α} (hf : Measurable f) (g : α → β) :
    entropy μ (g ∘ f) ≤ entropy μ f := by
  unfold entropy
  rw [← push_mass μ hf g]
  exact entropy_push_le (mass_nonneg μ f) g

lemma entropy_nonnegative {f : X → α} (hf : Measurable f) : 0 ≤ entropy μ f :=
  entropy_nonneg (mass_nonneg μ f) (sum_mass μ hf)

lemma entropy_card_bound {f : X → α} (hf : Measurable f) :
    entropy μ f ≤ Real.log (Fintype.card α) :=
  entropy_le_log_card (mass_nonneg μ f) (sum_mass μ hf)

lemma leftMass_pair {f : X → α} {g : X → β} (hf : Measurable f) (hg : Measurable g) :
    leftMass (mass μ (fun x => (f x,g x))) = mass μ f := by
  have h := push_mass μ (hf.prodMk hg) Prod.fst
  rw [show (Prod.fst ∘ fun x => (f x,g x)) = f by rfl] at h
  rw [← h]
  funext a
  classical
  simp only [leftMass, pushMass, Fintype.sum_prod_type]
  rw [sum_comm]
  simp

lemma rightMass_pair {f : X → α} {g : X → β} (hf : Measurable f) (hg : Measurable g) :
    rightMass (mass μ (fun x => (f x,g x))) = mass μ g := by
  have h := push_mass μ (hf.prodMk hg) Prod.snd
  rw [show (Prod.snd ∘ fun x => (f x,g x)) = g by rfl] at h
  rw [← h]
  funext b
  classical
  simp [rightMass, pushMass, Fintype.sum_prod_type]

lemma entropy_pair_le {f : X → α} {g : X → β} (hf : Measurable f) (hg : Measurable g) :
    entropy μ (fun x => (f x,g x)) ≤ entropy μ f + entropy μ g := by
  have h := entropy_subadd (mass_nonneg μ (fun x => (f x,g x)))
    (sum_mass μ (hf.prodMk hg))
  rw [leftMass_pair μ hf hg, rightMass_pair μ hf hg] at h
  exact h

omit [IsProbabilityMeasure μ] in
lemma entropy_preserving {T : X → X} (hT : MeasurePreserving T μ μ)
    {f : X → α} (hf : Measurable f) : entropy μ (f ∘ T) = entropy μ f := by
  unfold entropy mass
  congr 1
  funext a
  exact hT.measureReal_preimage ((measurableSet_singleton a).preimage hf).nullMeasurableSet

/-- The actual forward partition name, not an independent copy. -/
def name (T : X → X) (P : X → α) (n : ℕ) (x : X) : Fin n → α :=
  fun j => P ((T^[j.val]) x)

omit [Fintype α] [MeasurableSingletonClass α] in
lemma measurable_name {T : X → X} (hT : Measurable T) {P : X → α} (hP : Measurable P)
    (n : ℕ) : Measurable (name T P n) :=
  Measurable.of_eval (fun j => hP.comp (hT.iterate j.val))

omit [MeasurableSpace X] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma name_add (T : X → X) (P : X → α) (m n : ℕ) :
    name T P (m+n) = (fun w => Fin.append w.1 w.2) ∘
      (fun x => (name T P m x, name T P n ((T^[m]) x))) := by
  funext x j
  change P ((T^[j.val]) x) = Fin.append _ _ j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [name, Fin.append]
  · simp [name, Fin.append, Function.iterate_add_apply, Nat.add_comm m]

/-- Exact subadditivity for finite partition names of a stationary system. -/
theorem block_subadditive {T : X → X} (hT : MeasurePreserving T μ μ)
    {P : X → α} (hP : Measurable P) :
    Subadditive (fun n => entropy μ (name T P n)) := by
  intro m n
  change entropy μ (name T P (m+n)) ≤ entropy μ (name T P m) + entropy μ (name T P n)
  rw [name_add]
  have hm := measurable_name hT.measurable hP m
  have hn := measurable_name hT.measurable hP n
  calc
    _ ≤ entropy μ (fun x => (name T P m x, name T P n ((T^[m]) x))) :=
      entropy_comp_le μ (hm.prodMk (hn.comp (hT.measurable.iterate m))) _
    _ ≤ entropy μ (name T P m) + entropy μ ((name T P n) ∘ T^[m]) :=
      entropy_pair_le μ hm (hn.comp (hT.measurable.iterate m))
    _ = _ := by rw [entropy_preserving μ (hT.iterate m) hn]

/-- Every individual finite partition has an entropy rate, by Fekete's lemma.
The main theorem still needs a *uniform* bound over arbitrary partitions. -/
theorem exists_block_rate {T : X → X} (hT : MeasurePreserving T μ μ)
    {P : X → α} (hP : Measurable P) :
    ∃ h : ℝ, 0 ≤ h ∧ h ≤ Real.log (Fintype.card α) ∧
      Tendsto (fun n : ℕ => entropy μ (name T P n) / n) atTop (𝓝 h) := by
  have hs := block_subadditive μ hT hP
  have hb : BddBelow (Set.range (fun n : ℕ => entropy μ (name T P n) / n)) :=
    ⟨0, by rintro _ ⟨n,rfl⟩; exact div_nonneg (entropy_nonnegative μ
      (measurable_name hT.measurable hP n)) (Nat.cast_nonneg n)⟩
  refine ⟨hs.lim, ?_, ?_, hs.tendsto_lim hb⟩
  · exact ge_of_tendsto (hs.tendsto_lim hb) (Filter.Eventually.of_forall
      (fun n => div_nonneg (entropy_nonnegative μ (measurable_name hT.measurable hP n))
        (Nat.cast_nonneg n)))
  · have h1 := hs.lim_le_div hb (n := 1) (by decide)
    have hc := entropy_card_bound μ (measurable_name hT.measurable hP 1)
    simp only [Nat.cast_one, div_one] at h1
    simpa using h1.trans hc

end SmoothObstruction.PartitionEntropy

namespace SmoothObstruction.PartitionEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.FiniteEntropy
open scoped Topology
variable {X α : Type*} [MeasurableSpace X] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] (μ : Measure X) [IsProbabilityMeasure μ]

local instance : MeasurableSpace (Option α) := ⊤
local instance : MeasurableSingletonClass (Option α) := ⟨fun _ => trivial⟩

noncomputable def errorCode (P Q : X → α) (x : X) : Option α := by
  classical
  exact if P x = Q x then none else some (P x)

def recover (q : α) : Option α → α
  | none => q
  | some a => a

omit [MeasurableSpace X] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma recover_error (P Q : X → α) (x : X) : recover (Q x) (errorCode P Q x) = P x := by
  classical
  unfold errorCode
  split_ifs with h
  · exact h.symm
  · rfl

lemma measurable_error {P Q : X → α} (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (errorCode P Q) := by
  classical
  unfold errorCode
  exact Measurable.ite (measurableSet_eq_fun hP hQ) measurable_const
    ((measurable_of_finite Option.some).comp hP)

lemma error_mass {P Q : X → α} (hP : Measurable P) (hQ : Measurable Q) :
    (∑ a, mass μ (errorCode P Q) (some a)) = μ.real {x | P x ≠ Q x} := by
  classical
  have ht := sum_mass μ (measurable_error hP hQ)
  rw [Fintype.sum_option] at ht
  have hm : (errorCode P Q) ⁻¹' {none} = {x | P x = Q x} := by
    ext x
    simp [errorCode]
  have hc := measureReal_compl (μ := μ) (measurableSet_eq_fun hP hQ)
  simp only [mass, hm] at ht
  have hcompl : {x | P x ≠ Q x} = {x | P x = Q x}ᶜ := rfl
  rw [hcompl, hc]
  simp only [probReal_univ, mass]
  linarith

lemma error_entropy_bound {P Q : X → α} (hP : Measurable P) (hQ : Measurable Q) :
    entropy μ (errorCode P Q) ≤ Real.log 2 + μ.real {x | P x ≠ Q x} *
      Real.log (Fintype.card α) := by
  have h := entropy_option (mass_nonneg μ (errorCode P Q))
    (sum_mass μ (measurable_error hP hQ))
  rw [error_mass μ hP hQ] at h
  exact h

lemma entropy_recover_le {P Q : X → α} (hP : Measurable P) (hQ : Measurable Q) :
    entropy μ P ≤ entropy μ Q + entropy μ (errorCode P Q) := by
  have hfor := entropy_comp_le μ (hQ.prodMk (measurable_error hP hQ))
    (fun z : α × Option α => recover z.1 z.2)
  have he : ((fun z : α × Option α => recover z.1 z.2) ∘
      (fun x => (Q x,errorCode P Q x))) = P := by funext x; exact recover_error P Q x
  rw [he] at hfor
  exact hfor.trans (entropy_pair_le μ hQ (measurable_error hP hQ))

/-- Compare genuine orbit names through pointwise error coding. -/
lemma names_error_le {T : X → X} (hT : Measurable T) {P Q : X → α}
    (hP : Measurable P) (hQ : Measurable Q) (n : ℕ) :
    entropy μ (name T P n) ≤ entropy μ (name T Q n) +
      entropy μ (name T (errorCode P Q) n) := by
  have hfor := entropy_comp_le μ
    ((measurable_name hT hQ n).prodMk (measurable_name hT (measurable_error hP hQ) n))
    (fun z : (Fin n → α) × (Fin n → Option α) => fun j => recover (z.1 j) (z.2 j))
  have he : ((fun z : (Fin n → α) × (Fin n → Option α) => fun j => recover (z.1 j) (z.2 j)) ∘
      (fun x => (name T Q n x,name T (errorCode P Q) n x))) = name T P n := by
    funext x j
    exact recover_error P Q ((T^[j.val]) x)
  rw [he] at hfor
  exact hfor.trans (entropy_pair_le μ (measurable_name hT hQ n)
    (measurable_name hT (measurable_error hP hQ) n))

end SmoothObstruction.PartitionEntropy

namespace SmoothObstruction.PartitionEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.FiniteEntropy
open scoped Topology
variable {X α : Type*} [MeasurableSpace X] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] (μ : Measure X) [IsProbabilityMeasure μ]

lemma entropy_name_one {T : X → X} {P : X → α} (hP : Measurable P) :
    entropy μ (name T P 1) = entropy μ P := by
  have he : name T P 1 = (fun a => fun _ : Fin 1 => a) ∘ P := by
    funext x j
    simp [name, Fin.eq_zero j]
  rw [he]
  apply le_antisymm (entropy_comp_le μ hP _)
  have h := entropy_comp_le μ ((measurable_of_finite (fun a : α => fun _ : Fin 1 => a)).comp hP)
    (fun w : Fin 1 → α => w 0)
  exact h

/-- If the genuine name entropy has a limit, its rate is at most the entropy
of the one-time partition. No independence is assumed. -/
lemma block_rate_le_entropy {T : X → X} (hT : MeasurePreserving T μ μ)
    {P : X → α} (hP : Measurable P) {h : ℝ}
    (hh : Tendsto (fun n : ℕ => entropy μ (name T P n) / n) atTop (𝓝 h)) :
    h ≤ entropy μ P := by
  have hs := block_subadditive μ hT hP
  have hb : BddBelow (Set.range (fun n : ℕ => entropy μ (name T P n) / n)) :=
    ⟨0, by rintro _ ⟨n,rfl⟩; exact div_nonneg (entropy_nonnegative μ
      (measurable_name hT.measurable hP n)) (Nat.cast_nonneg n)⟩
  have hid : hs.lim = h := tendsto_nhds_unique (hs.tendsto_lim hb) hh
  have hone := hs.lim_le_div hb (n := 1) (by decide)
  simpa only [hid, Nat.cast_one, div_one, entropy_name_one μ hP] using hone

local instance : MeasurableSpace (Option α) := ⊤
local instance : MeasurableSingletonClass (Option α) := ⟨fun _ => trivial⟩

/-- Quantitative approximation of rates by a finite observation. This is a
real stationary-process entropy argument, not an assertion of a generator. -/
lemma rate_approximation {T : X → X} (hT : MeasurePreserving T μ μ)
    {P Q : X → α} (hP : Measurable P) (hQ : Measurable Q) {h k : ℝ}
    (hh : Tendsto (fun n : ℕ => entropy μ (name T P n) / n) atTop (𝓝 h))
    (hk : Tendsto (fun n : ℕ => entropy μ (name T Q n) / n) atTop (𝓝 k)) :
    h ≤ k + Real.log 2 + μ.real {x | P x ≠ Q x} * Real.log (Fintype.card α) := by
  obtain ⟨e, he0, heCard, he⟩ := exists_block_rate μ hT (measurable_error hP hQ)
  have hlim : h ≤ k + e := le_of_tendsto_of_tendsto hh (hk.add he)
    (Filter.Eventually.of_forall (fun n => by
      dsimp only
      rw [← add_div]
      exact div_le_div_of_nonneg_right (names_error_le μ hT.measurable hP hQ n)
        (Nat.cast_nonneg n)))
  have hbound := (block_rate_le_entropy μ hT (measurable_error hP hQ) he).trans
    (error_entropy_bound μ hP hQ)
  linarith

/-- Sufficient approximation criterion for a uniform finite KS bound.
The criterion requires actual measurable approximants with small error and
uniform rate bound; it does not postulate the KS conclusion. -/
theorem finite_rate_of_approximants {T : X → X} (hT : MeasurePreserving T μ μ)
    {C : ℝ} {P : X → α} (hP : Measurable P)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ Q : X → α, Measurable Q ∧
      μ.real {x | P x ≠ Q x} ≤ δ ∧ ∃ k : ℝ, k ≤ C ∧
        Tendsto (fun n : ℕ => entropy μ (name T Q n) / n) atTop (𝓝 k)) :
    ∃ h : ℝ, 0 ≤ h ∧ h ≤ C + Real.log 2 + 1 ∧
      Tendsto (fun n : ℕ => entropy μ (name T P n) / n) atTop (𝓝 h) := by
  obtain ⟨h, hh0, _, hh⟩ := exists_block_rate μ hT hP
  let L := max (Real.log (Fintype.card α)) 0
  have hL : 0 ≤ L := le_max_right _ _
  let δ := (1 + L)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (by linarith)
  obtain ⟨Q,hQ,herr,k,hk,hklim⟩ := happrox δ hδ
  refine ⟨h,hh0,?_,hh⟩
  have hrare : μ.real {x | P x ≠ Q x} * Real.log (Fintype.card α) ≤ 1 := calc
    _ ≤ μ.real {x | P x ≠ Q x} * L :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) measureReal_nonneg
    _ ≤ δ * L := mul_le_mul_of_nonneg_right herr hL
    _ ≤ δ * (1 + L) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
    _ = 1 := inv_mul_cancel₀ (by linarith : 1 + L ≠ 0)
  linarith [rate_approximation μ hT hP hQ hh hklim]

end SmoothObstruction.PartitionEntropy

end

end OAI
