import OAI.Dynamics.SmoothObstruction.PartitionEntropy

namespace OAI

section

open Finset
open MeasureTheory Set MeasurableSpace
open scoped ENNReal symmDiff

namespace SmoothObstruction.CylinderApproximation

variable {X ι : Type*} {A : ι → Type*} [MeasurableSpace X]
  [∀ i, MeasurableSpace (A i)] (π : X → ∀ i, A i)

/-- Cylinders pulled back along the actual coordinate map. -/
def cylinders : Set (Set X) := Set.preimage π '' measurableCylinders A

omit [MeasurableSpace X] in
lemma algebra : IsSetAlgebra (cylinders π) where
  empty_mem := ⟨∅,empty_mem_measurableCylinders A,preimage_empty⟩
  compl_mem := by
    rintro s ⟨t,ht,rfl⟩
    exact ⟨tᶜ,compl_mem_measurableCylinders ht,rfl⟩
  union_mem := by
    rintro s t ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩
    exact ⟨u ∪ v,union_mem_measurableCylinders hu hv,rfl⟩

lemma generates (hπ : ‹MeasurableSpace X› = MeasurableSpace.comap π MeasurableSpace.pi) :
    ‹MeasurableSpace X› = generateFrom (cylinders π) := by
  rw [hπ, ← generateFrom_measurableCylinders, comap_generateFrom]
  rfl

/-- Genuine approximation of arbitrary measurable sets by finite-coordinate
sets, in an arbitrary finite measure on a coordinate subspace. -/
lemma approximate_set (μ : Measure X) [IsFiniteMeasure μ]
    (hπ : ‹MeasurableSpace X› = MeasurableSpace.comap π MeasurableSpace.pi)
    {s : Set X} (hs : MeasurableSet s) {ε : ℝ} (hε : 0 < ε) :
    ∃ (I : Finset ι) (S : Set (∀ i : I, A i)), MeasurableSet S ∧
      μ.real ((π ⁻¹' cylinder I S) ∆ s) < ε := by
  have hcover : ∃ D : Set (Set X), D.Countable ∧ D ⊆ cylinders π ∧ μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{univ}, Set.countable_singleton _, ?_, ?_⟩
    · simpa using (algebra π).univ_mem
    · simp
  obtain ⟨t,ht,herr⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := μ) (algebra π).isSetRing hcover (generates π hπ) hs
    (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨u,hu,rfl⟩ := ht
  obtain ⟨I,S,hS,rfl⟩ := (mem_measurableCylinders u).mp hu
  refine ⟨I,S,hS,?_⟩
  simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using
    (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr herr

/-- Every finite measurable observation admits a finite-coordinate
approximation in measure. The output labels and their measurable meaning
are preserved; overlaps of the approximating atoms cause only the stated
symmetric-difference error. -/
theorem approximate_partition [∀ i, Fintype (A i)] [∀ i, MeasurableSingletonClass (A i)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hπ : ‹MeasurableSpace X› = MeasurableSpace.comap π MeasurableSpace.pi)
    {q : ℕ} {P : X → Fin (q+1)} (hP : Measurable P) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (J : Finset ι) (f : (∀ i : J, A i) → Fin (q+1)),
      Measurable (fun x => f (J.restrict (π x))) ∧
      μ.real {x | P x ≠ f (J.restrict (π x))} ≤ δ := by
  classical
  have hε : 0 < δ / (q+1) := div_pos hδ (by positivity)
  have ha (a : Fin (q+1)) := approximate_set π μ hπ
    ((measurableSet_singleton a).preimage hP) hε
  choose I S hS herr using ha
  let J := Finset.univ.biUnion I
  have hIJ (a : Fin (q+1)) : I a ⊆ J := fun i hi =>
    Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ a,hi⟩
  let R (a : Fin (q+1)) (z : ∀ i : J, A i) : Prop :=
    Finset.restrict₂ (hIJ a) z ∈ S a
  let f (z : ∀ i : J, A i) : Fin (q+1) :=
    if h : ∃ a, R a z then h.choose else 0
  have hmeasπ : Measurable π := by
    rw [Measurable, hπ]
    intro t ht
    exact ⟨t,ht,rfl⟩
  refine ⟨J,f,(measurable_of_finite f).comp (Finset.measurable_restrict J |>.comp hmeasπ),?_⟩
  let E (a : Fin (q+1)) := (π ⁻¹' cylinder (I a) (S a)) ∆ (P ⁻¹' {a})
  have hsub : {x | P x ≠ f (J.restrict (π x))} ⊆ ⋃ a, E a := by
    intro x hx
    by_contra hn
    have hnone (a : Fin (q+1)) : x ∉ E a := fun hm => hn (mem_iUnion.mpr ⟨a,hm⟩)
    have hiff (a : Fin (q+1)) : R a (J.restrict (π x)) ↔ P x = a := by
      have hh := hnone a
      simp only [E, mem_symmDiff, Set.mem_preimage, mem_singleton_iff,
        mem_cylinder, Finset.restrict_def] at hh
      change (fun i : I a => π x i) ∈ S a ↔ P x = a
      tauto
    have hex : ∃ a, R a (J.restrict (π x)) := ⟨P x,(hiff (P x)).mpr rfl⟩
    have hf : f (J.restrict (π x)) = P x := by
      dsimp only [f]
      rw [dite_eq_left hex]
      exact ((hiff hex.choose).mp hex.choose_spec).symm
    exact hx hf.symm
  calc
    _ ≤ μ.real (⋃ a, E a) := measureReal_mono hsub
    _ ≤ ∑ a, μ.real (E a) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _a : Fin (q+1), δ / (q+1) := Finset.sum_le_sum (fun a _ => (herr a).le)
    _ = δ := by simp; field_simp

end SmoothObstruction.CylinderApproximation

namespace SmoothObstruction.PhaseEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.PartitionEntropy
open scoped Topology

variable (A : Type) (m : ℕ → ℕ)
def Coordinate : ℤ ⊕ ℕ → Type
  | Sum.inl _ => A
  | Sum.inr i => ZMod (m i)
instance [Fintype A] [∀ i, NeZero (m i)] (i : ℤ ⊕ ℕ) : Fintype (Coordinate A m i) := by
  cases i <;> dsimp [Coordinate] <;> infer_instance
instance [Nonempty A] (i : ℤ ⊕ ℕ) : Nonempty (Coordinate A m i) := by
  cases i <;> dsimp [Coordinate] <;> infer_instance
instance [MeasurableSpace A] (i : ℤ ⊕ ℕ) : MeasurableSpace (Coordinate A m i) := by
  cases i <;> dsimp [Coordinate] <;> infer_instance
instance [MeasurableSpace A] [MeasurableSingletonClass A] (i : ℤ ⊕ ℕ) :
    MeasurableSingletonClass (Coordinate A m i) := by
  cases i <;> dsimp [Coordinate] <;> infer_instance

variable {A m} {X : Type*} [MeasurableSpace X]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [∀ i, NeZero (m i)]
  (s : X → ℤ → A) (p : X → ∀ i, ZMod (m i))

def coordinates (x : X) : ∀ i, Coordinate A m i
  | Sum.inl t => s x t
  | Sum.inr i => p x i

omit [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [∀ i, NeZero (m i)] [MeasurableSpace X] in
lemma symbol_iterate {T : X → X} (hs : ∀ x t, s (T x) t = s x (t+1)) (n : ℕ) (x : X) (t : ℤ) :
    s ((T^[n]) x) t = s x (t+n) := by
  induction n generalizing x t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', hs, ih]
    congr 1
    push_cast
    ring

omit [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [∀ i, NeZero (m i)] [MeasurableSpace X] in
lemma phase_iterate {T : X → X} (hp : ∀ x i, p (T x) i = p x i + 1)
    (n : ℕ) (x : X) (i : ℕ) : p ((T^[n]) x) i = p x i + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', hp, ih]; push_cast; ring

/-- Every genuine cylinder observation on symbols and phases has rate at most
log(card A). Initial phase data have finite cost and add zero entropy rate. -/
theorem cylinder_rate_bound (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ)
    (hcoord : Measurable (coordinates s p))
    (hs : ∀ x t, s (T x) t = s x (t+1)) (hp : ∀ x i, p (T x) i = p x i + 1)
    {q : ℕ} (J : Finset (ℤ ⊕ ℕ)) (f : (∀ i : J, Coordinate A m i) → Fin (q+1)) :
    ∃ h : ℝ, h ≤ Real.log (Fintype.card A) ∧
      Tendsto (fun n : ℕ => entropy μ (name T (fun x => f (J.restrict (coordinates s p x))) n) / n)
        atTop (𝓝 h) := by
  classical
  let Q := fun x => f (J.restrict (coordinates s p x))
  have hQ : Measurable Q := (measurable_of_finite f).comp ((Finset.measurable_restrict J).comp hcoord)
  obtain ⟨h,_,_,hh⟩ := exists_block_rate μ hT hQ
  let k := J.sup (Sum.elim Int.natAbs (fun _ => 0))
  have hbound (t : ℤ) (ht : Sum.inl t ∈ J) : -(k : ℤ) ≤ t ∧ t ≤ k := by
    have hk : t.natAbs ≤ k := Finset.le_sup (f := Sum.elim Int.natAbs (fun _ => 0)) ht
    have h₁ := Int.le_natAbs (a := t)
    have h₂ := Int.le_natAbs (a := -t)
    simp only [Int.natAbs_neg] at h₂
    omega
  let D := ∀ i : J, Coordinate A m i
  let O (n : ℕ) (x : X) : (Fin (n+2*k+1) → A) × D :=
    (fun a => s x ((a.val : ℤ)-k), J.restrict (coordinates s p x))
  have hO (n : ℕ) : Measurable (O n) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro a
      exact (measurable_pi_apply (Sum.inl ((a.val : ℤ)-k))).comp hcoord
    · exact (Finset.measurable_restrict J).comp hcoord
  have hindex (n : ℕ) (j : Fin n) (t : ℤ) (ht : Sum.inl t ∈ J) :
      (t+j.val+k).toNat < n+2*k+1 := by
    have hb := hbound t ht
    omega
  let decoder (n : ℕ) (d : (Fin (n+2*k+1) → A) × D) (j : Fin n) : D := fun i =>
    match i with
    | ⟨Sum.inl t, ht⟩ => d.1 ⟨(t+j.val+k).toNat, hindex n j t ht⟩
    | ⟨Sum.inr r, hr⟩ => (fun z : ZMod (m r) => z + (j.val : ZMod (m r))) (d.2 ⟨Sum.inr r,hr⟩)
  have hdecode (n : ℕ) (x : X) (j : Fin n) :
      decoder n (O n x) j = J.restrict (coordinates s p ((T^[j.val]) x)) := by
    funext ⟨i,hi⟩
    cases i with
    | inl t =>
      change s x (((t+j.val+k).toNat : ℤ)-k) = s ((T^[j.val]) x) t
      rw [symbol_iterate s hs]
      congr 1
      have hb := hbound t hi
      omega
    | inr r =>
      exact (phase_iterate p hp j.val x r).symm
  have hfactor (n : ℕ) : name T Q n = (fun d => fun j => f (decoder n d j)) ∘ O n := by
    funext x j
    rw [Function.comp_apply, hdecode]
    rfl
  have hcard (n : ℕ) : entropy μ (name T Q n) ≤
      ((n+2*k+1 : ℕ) : ℝ) * Real.log (Fintype.card A) + Real.log (Fintype.card D) := by
    rw [hfactor]
    have he := (entropy_comp_le μ (hO n) (fun d => fun j => f (decoder n d j))).trans
      (entropy_card_bound μ (hO n))
    simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_pow, Real.log_mul (by positivity : (Fintype.card A : ℝ) ^ (n+2*k+1) ≠ 0)
        (by positivity : (Fintype.card D : ℝ) ≠ 0), Real.log_pow] using he
  have hlim : Tendsto (fun n : ℕ => Real.log (Fintype.card A) +
      (((2*k+1 : ℕ) : ℝ) * Real.log (Fintype.card A) + Real.log (Fintype.card D)) / n)
      atTop (𝓝 (Real.log (Fintype.card A))) := by
    have ht : Tendsto (fun n : ℕ =>
        (((2*k+1 : ℕ) : ℝ) * Real.log (Fintype.card A) + Real.log (Fintype.card D)) / n)
        atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [add_zero] using
      (show Tendsto (fun _ : ℕ => Real.log (Fintype.card A)) atTop
        (𝓝 (Real.log (Fintype.card A))) from tendsto_const_nhds).add ht
  refine ⟨h,le_of_tendsto_of_tendsto hh hlim ?_,hh⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hb := div_le_div_of_nonneg_right (hcard n) (Nat.cast_nonneg n)
  convert hb using 1
  push_cast
  field_simp
  ring

/-- All finite measurable partitions on the actual coordinate subspace have
one finite entropy bound; the cylinder approximation is constructed in measure. -/
theorem all_partition_rates (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ)
    (hspace : ‹MeasurableSpace X› = MeasurableSpace.comap (coordinates s p) MeasurableSpace.pi)
    (hs : ∀ x t, s (T x) t = s x (t+1)) (hp : ∀ x i, p (T x) i = p x i + 1)
    {q : ℕ} {P : X → Fin (q+1)} (hP : Measurable P) :
    ∃ h : ℝ, 0 ≤ h ∧ h ≤ Real.log (Fintype.card A) + Real.log 2 + 1 ∧
      Tendsto (fun n : ℕ => entropy μ (name T P n) / n) atTop (𝓝 h) := by
  have hcoord : Measurable (coordinates s p) := by
    rw [Measurable, hspace]
    intro t ht
    exact ⟨t,ht,rfl⟩
  apply finite_rate_of_approximants μ hT hP
  intro δ hδ
  obtain ⟨J,f,hQ,herr⟩ := CylinderApproximation.approximate_partition
    (coordinates s p) μ hspace hP hδ
  exact ⟨_,hQ,herr,cylinder_rate_bound s p μ hT hcoord hs hp J f⟩

end SmoothObstruction.PhaseEntropy

namespace SmoothObstruction
open MeasureTheory Set Filter
open scoped Topology

/-- The entropy of the length-`n` join of the partition with labels in `Fin q`. -/
noncomputable def blockEntropy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) {q : ℕ} (P : X → Fin q) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin q,
    entropyTerm ((μ {x | ∀ j : Fin n, P ((T^[j.val]) x) = w j}).toReal)

/-- All finite-partition entropy rates exist and have one finite real upper
bound. This spells out `sup_P lim_n H(join_{j<n} T^{-j}P)/n < ∞` without
choosing a value for limits of nonconvergent sequences. Empty atoms are allowed. -/
def FiniteKSEntropy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) (P : X → Fin (q + 1)), Measurable P →
    ∃ h : ℝ, h ≤ C ∧
      Tendsto (fun n : ℕ => blockEntropy μ T P n / (n : ℝ)) atTop (𝓝 h)


lemma blockEntropy_eq_nats {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X → X) {q : ℕ} (P : X → Fin q) (n : ℕ) :
    blockEntropy μ T P n =
      PartitionEntropy.entropy μ (PartitionEntropy.name T P n) / Real.log 2 := by
  unfold blockEntropy PartitionEntropy.entropy FiniteEntropy.natEntropy
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  have he : {x | ∀ j : Fin n, P ((T^[j.val]) x) = w j} =
      PartitionEntropy.name T P n ⁻¹' {w} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
      funext_iff, PartitionEntropy.name]
  rw [he]
  simp only [entropyTerm, PartitionEntropy.mass, Measure.real, Real.negMulLog_def, neg_mul]

/-- The exact frozen finite-KS predicate for any finite-symbol cyclic phase
subspace with its genuine coordinate sigma field. -/
theorem PhaseEntropy.finiteKS {A : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    {m : ℕ → ℕ} [∀ i, NeZero (m i)] {X : Type*} [MeasurableSpace X]
    (s : X → ℤ → A) (p : X → ∀ i, ZMod (m i))
    (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ)
    (hspace : ‹MeasurableSpace X› = MeasurableSpace.comap (coordinates s p) MeasurableSpace.pi)
    (hs : ∀ x t, s (T x) t = s x (t+1)) (hp : ∀ x i, p (T x) i = p x i + 1) :
    FiniteKSEntropy μ T := by
  refine ⟨(Real.log (Fintype.card A) + Real.log 2 + 1) / Real.log 2, ?_⟩
  intro q P hP
  obtain ⟨h,_,hb,hl⟩ := all_partition_rates s p μ hT hspace hs hp hP
  refine ⟨h / Real.log 2,div_le_div_of_nonneg_right hb (Real.log_nonneg (by norm_num)),?_⟩
  have ht := hl.div_const (Real.log 2)
  convert ht using 1
  funext n
  rw [blockEntropy_eq_nats]
  ring
end SmoothObstruction

end

end OAI
