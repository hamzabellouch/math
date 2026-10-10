import OAI.Dynamics.SmoothObstruction.PhaseEntropy
import OAI.Dynamics.SmoothObstruction.InvariantMeasure
import OAI.Dynamics.SmoothObstruction.StandardProbability

namespace OAI

section

open MeasureTheory Set Filter Topology

namespace SmoothObstruction.PhaseDynamics

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
lemma iterate_phase {m : ℕ} (T : X → X) (a : X → ZMod m)
    (ha : ∀ x, a (T x) = a x + 1) (x : X) (n : ℕ) :
    a ((T^[n]) x) = a x + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ha, ih, Nat.cast_add, Nat.cast_one, add_assoc]

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- Uniform infinite cyclic factors rule out every periodic point. This
uses only the exact phase evolution, not recognition or word frequencies. -/
theorem no_periodic_points (T : X → X) (m : ℕ → ℕ) (a : ∀ i, X → ZMod (m i))
    (ha : ∀ i x, a i (T x) = a i x + 1) (hm : ∀ n, ∃ i, n < m i) :
    ∀ x n, 0 < n → (T^[n]) x ≠ x := by
  intro x n hn hx
  obtain ⟨i, hi⟩ := hm n
  have h := iterate_phase T (a i) (ha i) x n
  rw [hx] at h
  have hn0 : (n : ZMod (m i)) = 0 := by
    apply add_left_cancel (a := a i x)
    simpa using h.symm
  have hdiv := (ZMod.natCast_eq_zero_iff n (m i)).mp hn0
  exact (not_le.mpr hi) (Nat.le_of_dvd hn hdiv)

/-- The phase extension's nonatomicity: a positive singleton would return by
Poincare recurrence, contradicting its arbitrarily large cyclic factors. -/
theorem noAtoms_of_phases (μ : Measure X) [IsFiniteMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ) (m : ℕ → ℕ) (a : ∀ i, X → ZMod (m i))
    (ha : ∀ i x, a i (T x) = a i x + 1) (hm : ∀ n, ∃ i, n < m i) : NullSingletonClass μ := by
  refine ⟨fun x => ?_⟩
  by_contra hx
  obtain ⟨y, hy, n, hn, hny⟩ := hT.conservative.exists_mem_iterate_mem'
    (measurableSet_singleton x) hx
  have hyx : y = x := mem_singleton_iff.mp hy
  subst y
  exact no_periodic_points T m a ha hm x n (Nat.pos_of_ne_zero hn) (mem_singleton_iff.mp hny)

section Ambient
variable (A : Type*) [TopologicalSpace A] (m : ℕ → ℕ)

abbrev Space := (ℤ → A) × ∀ i, ZMod (m i)

/-- The source map: bilateral symbol shift and addition of one in every
phase. Its inverse subtracts one, with no modulo-null restriction. -/
def shift : Space A m ≃ₜ Space A m where
  toFun x := (fun t => x.1 (t + 1), fun i => x.2 i + 1)
  invFun x := (fun t => x.1 (t - 1), fun i => x.2 i - 1)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi (fun t => (continuous_apply (t + 1)).comp continuous_fst)
    · exact continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).add continuous_const)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_pi (fun t => (continuous_apply (t - 1)).comp continuous_fst)
    · exact continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).sub continuous_const)

@[simp] lemma shift_symbol (x : Space A m) (t : ℤ) : (shift A m x).1 t = x.1 (t + 1) := rfl
@[simp] lemma shift_phase (x : Space A m) (i : ℕ) : (shift A m x).2 i = x.2 i + 1 := rfl

end Ambient

section Words
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  (m : ℕ → ℕ) (hm : ∀ i, m i ∣ m (i + 1))
  (W : ∀ i, Set (Fin (m i) → A))

/-- Level-i symbols beginning at an integer time. -/
def wordAt (x : Space A m) (i : ℕ) (t : ℤ) : Fin (m i) → A :=
  fun j => x.1 (t + j.val)

/-- Exact compatibility of phases through the canonical cyclic quotient. -/
def Compatible (x : Space A m) (i : ℕ) : Prop :=
  ZMod.castHom (hm i) (ZMod (m i)) (x.2 (i + 1)) = x.2 i

/-- Every level boundary carries a legal word; the sign convention records
the index of the origin inside its word, exactly as in source section 6. -/
def Legal (x : Space A m) (i : ℕ) : Prop :=
  ∀ t : ℤ, (t : ZMod (m i)) = -x.2 i → wordAt m x i t ∈ W i

def extension : Set (Space A m) :=
  {x | ∀ i, Compatible m hm x i ∧ Legal m W x i}

omit [DiscreteTopology A] in
lemma continuous_wordAt (i : ℕ) (t : ℤ) : Continuous (fun x : Space A m => wordAt m x i t) :=
  continuous_pi (fun j => (continuous_apply (t + j.val)).comp continuous_fst)

omit [DiscreteTopology A] in
lemma compatible_closed (i : ℕ) : IsClosed {x : Space A m | Compatible m hm x i} := by
  apply isClosed_eq _ ((continuous_apply i).comp continuous_snd)
  exact (continuous_of_discreteTopology : Continuous (ZMod.castHom (hm i) (ZMod (m i)))).comp
    ((continuous_apply (i + 1)).comp continuous_snd)

lemma legal_closed (i : ℕ) : IsClosed {x : Space A m | Legal m W x i} := by
  have heq : {x : Space A m | Legal m W x i} =
      ⋂ t : ℤ, ({x : Space A m | (t : ZMod (m i)) ≠ -x.2 i} ∪
        (fun x : Space A m => wordAt m x i t) ⁻¹' W i) := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_preimage, Legal]
    simp only [imp_iff_not_or]
  rw [heq]
  apply isClosed_iInter
  intro t
  apply IsClosed.union _ ((isClosed_discrete (W i)).preimage (continuous_wordAt m i t))
  have hc : IsClosed {a : ZMod (m i) | (t : ZMod (m i)) ≠ -a} := isClosed_discrete _
  exact hc.preimage (show Continuous (fun x : Space A m => x.2 i) from
    (continuous_apply i).comp continuous_snd)

lemma extension_closed : IsClosed (extension m hm W) := by
  have heq : extension m hm W =
      ⋂ i, {x : Space A m | Compatible m hm x i} ∩ {x : Space A m | Legal m W x i} := by
    ext x; simp [extension]
  rw [heq]
  exact isClosed_iInter (fun i => (compatible_closed m hm i).inter (legal_closed m W i))

omit [DiscreteTopology A] in
lemma compatible_shift_iff (x : Space A m) (i : ℕ) :
    Compatible m hm (shift A m x) i ↔ Compatible m hm x i := by
  simp [Compatible, shift, map_add, map_one]

omit [DiscreteTopology A] in
lemma legal_shift_iff (x : Space A m) (i : ℕ) :
    Legal m W (shift A m x) i ↔ Legal m W x i := by
  constructor
  · intro h t ht
    have hb : ((t - 1 : ℤ) : ZMod (m i)) = -(shift A m x).2 i := by
      simp only [Int.cast_sub, Int.cast_one, shift_phase]
      rw [ht]
      ring
    have hw := h (t - 1) hb
    convert hw using 1
    ext j
    change x.1 (t + (j.val : ℤ)) = x.1 (t - 1 + (j.val : ℤ) + 1)
    exact congrArg x.1 (by ring)
  · intro h t ht
    have hb : ((t + 1 : ℤ) : ZMod (m i)) = -x.2 i := by
      simp only [Int.cast_add, Int.cast_one]
      rw [ht, shift_phase]
      ring
    have hw := h (t + 1) hb
    convert hw using 1
    ext j
    change x.1 (t + (j.val : ℤ) + 1) = x.1 (t + 1 + (j.val : ℤ))
    exact congrArg x.1 (by ring)

omit [DiscreteTopology A] in
lemma extension_shift_iff (x : Space A m) :
    shift A m x ∈ extension m hm W ↔ x ∈ extension m hm W := by
  simp only [extension, mem_ofPred_eq, compatible_shift_iff, legal_shift_iff]

omit [DiscreteTopology A] in
lemma extension_shift_symm (x : Space A m) (hx : x ∈ extension m hm W) :
    (shift A m).symm x ∈ extension m hm W := by
  apply (extension_shift_iff m hm W ((shift A m).symm x)).mp
  simpa using hx

/-- Restriction to the genuine closed phase extension, in both directions. -/
def extensionShift : extension m hm W ≃ₜ extension m hm W where
  toFun x := ⟨shift A m x.val, (extension_shift_iff m hm W x.val).mpr x.property⟩
  invFun x := ⟨(shift A m).symm x.val, extension_shift_symm m hm W x.val x.property⟩
  left_inv x := Subtype.ext ((shift A m).left_inv x.val)
  right_inv x := Subtype.ext ((shift A m).right_inv x.val)
  continuous_toFun := ((shift A m).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((shift A m).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- Compactness needs only finite-level admissible configurations. The actual
word hierarchy supplies these by periodically repeating a word at the largest
requested level; no invariant measure or frequency hypothesis enters. -/
theorem extension_nonempty [CompactSpace A] [∀ i, NeZero (m i)]
    (hfinite : ∀ n, ∃ x : Space A m, ∀ i ≤ n, Compatible m hm x i ∧ Legal m W x i) :
    (extension m hm W).Nonempty := by
  let E : ℕ → Set (Space A m) := fun n =>
    {x | ∀ i ≤ n, Compatible m hm x i ∧ Legal m W x i}
  have hcl (n : ℕ) : IsClosed (E n) := by
    have heq : E n = ⋂ i ∈ Set.Iic n,
        {x : Space A m | Compatible m hm x i} ∩ {x : Space A m | Legal m W x i} := by
      ext x; simp [E]
    rw [heq]
    exact isClosed_biInter (fun i _ => (compatible_closed m hm i).inter (legal_closed m W i))
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed E
    (fun n x hx i hi => hx i (by omega)) hfinite (hcl 0).isCompact hcl
  refine ⟨x, fun i => ?_⟩
  exact (mem_iInter.mp hx i) i le_rfl

end Words
end SmoothObstruction.PhaseDynamics

end

section

namespace SmoothObstruction.PhaseDynamics
open MeasureTheory Set Filter
open scoped Topology
variable {A : Type} [Fintype A] [Nonempty A] [TopologicalSpace A]
  [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
  (m : ℕ → ℕ) [∀ i, NeZero (m i)] (hm : ∀ i, m i ∣ m (i+1))
  (W : ∀ i, Set (Fin (m i) → A))

omit [Fintype A] [Nonempty A] [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [∀ i, NeZero (m i)] in
lemma extension_coordinate_space :
    (inferInstance : MeasurableSpace (extension m hm W)) = MeasurableSpace.comap
      (PhaseEntropy.coordinates (fun x : extension m hm W => x.val.1)
        (fun x : extension m hm W => x.val.2)) MeasurableSpace.pi := by
  let e := MeasurableEquiv.sumPiEquivProdPi (PhaseEntropy.Coordinate A m)
  have he := e.symm.measurableEmbedding.comap_eq
  have hc : PhaseEntropy.coordinates (fun x : extension m hm W => x.val.1)
      (fun x : extension m hm W => x.val.2) = e.symm ∘ Subtype.val := by
    funext x i
    cases i <;> rfl
  change MeasurableSpace.comap (Subtype.val : extension m hm W → Space A m)
    inferInstance = _
  exact (congrArg (MeasurableSpace.comap (Subtype.val : extension m hm W → Space A m)) he).symm.trans
    (MeasurableSpace.comap_comp.trans (congrArg (fun f => MeasurableSpace.comap f MeasurableSpace.pi) hc.symm))

/-- A genuine ergodic invertible standard nonatomic finite-KS system from
any nonempty finite admissible word hierarchy with unbounded lengths.
This is the measure-theoretic construction, not its graph obstruction. -/
theorem exists_system
    (hunbounded : ∀ n, ∃ i, n < m i)
    (hfinite : ∀ n, ∃ x : Space A m, ∀ i ≤ n, Compatible m hm x i ∧ Legal m W x i) :
    ∃ μ : ProbabilityMeasure (extension m hm W),
      StandardNonatomic (μ : Measure (extension m hm W)) ∧
      Ergodic (extensionShift m hm W) (μ : Measure (extension m hm W)) ∧
      FiniteKSEntropy (μ : Measure (extension m hm W)) (extensionShift m hm W) := by
  let : CompactSpace A := Finite.compactSpace
  let : Fact (IsClosed (extension m hm W)) := ⟨extension_closed m hm W⟩
  let : CompactSpace (extension m hm W) := isCompact_iff_compactSpace.mp (extension_closed m hm W).isCompact
  have hn := extension_nonempty m hm W hfinite
  let : Nonempty (extension m hm W) := hn.to_subtype
  let : StandardBorelSpace (extension m hm W) := (extension_closed m hm W).measurableSet.standardBorel
  obtain ⟨μ,hμ⟩ := CompactInvariant.exists_ergodic_probability
    (extensionShift m hm W) (extensionShift m hm W).continuous
  let : NullSingletonClass (μ : Measure (extension m hm W)) :=
    noAtoms_of_phases μ (extensionShift m hm W) hμ.toMeasurePreserving m
      (fun i x => x.val.2 i) (fun _ _ => rfl) hunbounded
  refine ⟨μ,standardNonatomic_of_standardBorel (μ : Measure (extension m hm W)),hμ,?_⟩
  exact PhaseEntropy.finiteKS (fun x : extension m hm W => x.val.1)
    (fun x : extension m hm W => x.val.2) μ hμ.toMeasurePreserving
    (extension_coordinate_space m hm W) (fun _ _ => rfl) (fun _ _ => rfl)
end SmoothObstruction.PhaseDynamics

end

end OAI
