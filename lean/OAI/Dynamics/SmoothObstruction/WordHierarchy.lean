import OAI.Dynamics.SmoothObstruction.PhaseDynamics
import OAI.Dynamics.SmoothObstruction.WordStep

namespace OAI

section

namespace SmoothObstruction.WordHierarchy
open WordParameters WordAlphabet WordStep FiniteLaw WordLaw
open scoped BigOperators

noncomputable abbrev S (i : ℕ) := sequence 40000 i
abbrev A (i : ℕ) := Alphabet (S i)
noncomputable abbrev size (i : ℕ) := Fintype.card (A i)
noncomputable abbrev groupLength (i : ℕ) := q (S i)*H (S i)
noncomputable abbrev Config (i : ℕ) := Fin (q (S i)) → Fin (H (S i)) → A i
noncomputable abbrev Labels (i : ℕ) := Fin (groupLength i) → A i
noncomputable abbrev goodDim (i : ℕ) : K (S i)+1 ≤ Module.finrank (ZMod 2) (WordAlphabet.Space (S i)) := by
  rw [finrank]
  exact dimension_budget (step_conditions initial_threshold i).1
noncomputable abbrev raw (i : ℕ) := rawLaw (form (S i)) (goodDim i) (H (S i)) (q (S i))

/-- The chosen family stores the actual conditioning event and its mass,
not merely the existence of enough labels. -/
structure Family (i : ℕ) where
  E : Finset (Config i)
  massE : 1/2 ≤ prob (raw i) E
  w : Fin (size (i+1)) → Labels i
  injective : Function.Injective w
  supported : ∀ a, WordFlatten.flattenEquiv.symm (w a) ∈ E
  relations : ∀ a b (r k : ℕ) (_hk : k<K (S i)) (_hk8 : k ≤ K (S i)/8) (hr : r+2^k<H (S i)),
    form (S i) (w a (finProdFinEquiv (b,⟨r,lt_trans (Nat.lt_add_of_pos_right (by positivity)) hr⟩))).val
      (w a (finProdFinEquiv (b,⟨r+2^k,hr⟩))).val = 0
  windowTV : ∀ t, WordFamily.empiricalTV
    (WordFlatten.flatLaw (form (S i)) (goodDim i) E massE)
    (window (S i) t) w ≤ 1/10000
  separated : ∀ a b c, ∀ t : Fin (groupLength i), t≠0 ∨ a≠c →
    ShiftComparisons.matchCount w a b c t < matchThreshold i (S i)

noncomputable def chooseFamily (i : ℕ) (E : Finset (Config i))
    (hE : 1/2 ≤ prob (raw i) E) : Family i := by
  classical
  have hx := exists_step (step_conditions initial_threshold i).1
    (step_conditions initial_threshold i).2 E hE
  let w := Classical.choose hx
  have hw := Classical.choose_spec hx
  exact ⟨E,hE,w,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2⟩

noncomputable def Family.word {i : ℕ} (F : Family i) (a : A (i+1)) : Labels i :=
  F.w ((Fintype.equivFin (A (i+1))) a)

lemma Family.word_injective {i : ℕ} (F : Family i) : Function.Injective F.word :=
  F.injective.comp (Fintype.equivFin (A (i+1))).injective

noncomputable def stage : (i : ℕ) → Family i
  | 0 => chooseFamily 0 Finset.univ (by norm_num [prob,FiniteLaw.Law.total])
  | i+1 => by
    classical
    let f := fun t a => window (S i) t ((stage i).word a)
    let E := Finset.univ.filter (fun w : Config (i+1) => ∀ t, tvFromUniformObservable (f t) w ≤ 1/10000)
    have hE : 1/2 ≤ prob (raw (i+1)) E :=
      approximation_mass (step_conditions initial_threshold i).1
        (step_conditions initial_threshold i).2 f
    exact chooseFamily (i+1) E hE

/-- Every stored successor word actually obeys the W4 event for every
nonwrapping lower-window offset. -/
lemma stage_approximates (i : ℕ) (a : A (i+2)) (t : Offsets (S i)) :
    tvFromUniformObservable (fun b => window (S i) t ((stage i).word b))
      (WordFlatten.flattenEquiv.symm ((stage (i+1)).word a)) ≤ 1/10000 := by
  classical
  have h := (stage (i+1)).supported ((Fintype.equivFin (A (i+2))) a)
  change _ ∈ Finset.univ.filter _ at h
  exact (Finset.mem_filter.mp h).2 t

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordConcatenation
variable {A B : Type*} {m N : ℕ}

def pack : Fin N × Fin m ≃ Fin (m*N) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm N m))

lemma pack_val (b : Fin N) (r : Fin m) : (pack (b,r)).val = b.val*m+r.val := by
  change r.val + m*b.val = b.val*m+r.val
  ac_rfl

def concat (u : B → Fin m → A) (w : Fin N → B) : Fin (m*N) → A :=
  fun j => u (w (pack.symm j).1) (pack.symm j).2

@[simp] lemma concat_pack (u : B → Fin m → A) (w : Fin N → B) (b : Fin N) (r : Fin m) :
    concat u w (pack (b,r)) = u (w b) r := by simp [concat]

lemma concat_injective (u : B → Fin m → A) (hu : Function.Injective u) :
    Function.Injective (concat (N:=N) u) := by
  intro w v hw
  funext b
  apply hu
  funext r
  have hh := congrFun hw (pack (b,r))
  simpa only [concat_pack] using hh

/-- Every aligned lower word in a concatenation is an actual constituent,
including near the last endpoint. -/
lemma slice_is_constituent (hm : 0 < m) (u : B → Fin m → A) (w : Fin N → B)
    (a : ℕ) (ha : m ∣ a) (hlen : a+m ≤ m*N) :
    ∃ b : Fin N, (fun r : Fin m => concat u w
      ⟨a+r.val,lt_of_lt_of_le (Nat.add_lt_add_left r.isLt a) hlen⟩) = u (w b) := by
  have hb : a/m < N := by
    apply (Nat.div_lt_iff_lt_mul hm).mpr
    rw [Nat.mul_comm N m]
    omega
  let b : Fin N := ⟨a/m,hb⟩
  have hab : b.val*m = a := Nat.div_mul_cancel ha
  refine ⟨b,?_⟩
  funext r
  have hi : (⟨a+r.val,lt_of_lt_of_le (Nat.add_lt_add_left r.isLt a) hlen⟩ : Fin (m*N)) =
      pack (b,r) := by
    apply Fin.ext
    simp only [pack_val,hab]
  rw [hi,concat_pack]
end SmoothObstruction.WordConcatenation

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation

noncomputable def children (i : ℕ) (a : A (i+1)) : Fin (N (S i)) → A i :=
  fun j => (stage i).word a ((finCongr (q_mul_H (S i))).symm j)

lemma children_injective (i : ℕ) : Function.Injective (children i) := by
  intro a b hab
  apply (stage i).word_injective
  funext j
  have hh := congrFun hab ((finCongr (q_mul_H (S i))) j)
  simpa only [children,Equiv.symm_apply_apply] using hh

/-- Source words have exactly the recursively prescribed lengths, over the
fixed initial alphabet. Reindexing is the fixed arbitrary labeling allowed
by the manuscript, not a new conditioning at any level. -/
noncomputable def word : (i : ℕ) → A i → Fin (length 40000 i) → A 0
  | 0,a,_ => a
  | i+1,a,j => concat (word i) (children i a) j

lemma word_injective (i : ℕ) : Function.Injective (word i) := by
  induction i with
  | zero =>
    intro a b hab
    exact congrFun hab ⟨0,by simp [length]⟩
  | succ i ih =>
    exact (concat_injective (word i) ih).comp (children_injective i)

noncomputable def words (i : ℕ) : Set (Fin (length 40000 i) → A 0) := Set.range (word i)

lemma alphabet_nonempty (i : ℕ) : Nonempty (A i) := by
  have hs := s_pos_of_Kpos (show 0<K (S i) by
    change 0<K (sequence 40000 i)
    have := (step_conditions initial_threshold i).1
    omega)
  have hp : (0 : ℝ) < Fintype.card (A i) := by
    rw [cardAlphabetReal]
    exact alphabetSize_pos hs
  exact Fintype.card_pos_iff.mp (by exact_mod_cast hp)

lemma words_nonempty (i : ℕ) : (words i).Nonempty := by
  let : Nonempty (A i) := alphabet_nonempty i
  exact Set.range_nonempty _

lemma words_card (i : ℕ) : (words i).ncard = size i := by
  rw [words,Set.ncard_range_of_injective (word_injective i),Nat.card_eq_fintype_card]

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.PhaseDynamics
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  (m : ℕ → ℕ) [∀ i, NeZero (m i)] (hm : ∀ i, m i ∣ m (i+1))
  (W : ∀ i, Set (Fin (m i) → A))

/-- The exact concatenation property of legal source words, expressed at
all aligned lower-word positions. -/
def SubwordClosed : Prop :=
  ∀ i (w : Fin (m (i+1)) → A), w ∈ W (i+1) → ∀ r : ℕ,
    m i ∣ r → ∀ hr : r+m i ≤ m (i+1),
    (fun j : Fin (m i) => w ⟨r+j.val,lt_of_lt_of_le (Nat.add_lt_add_left j.isLt r) hr⟩) ∈ W i

omit [TopologicalSpace A] [DiscreteTopology A] in
include hm in
lemma legal_of_succ (hW : SubwordClosed m W) (x : Space A m)
    (hx : ∀ i, x.2 i = 0) (i : ℕ) (hi : Legal m W x (i+1)) : Legal m W x i := by
  intro t ht
  have ht0 : (t : ZMod (m i)) = 0 := by simpa only [hx,neg_zero] using ht
  let r := (t : ZMod (m (i+1))).val
  have hr : r < m (i+1) := ZMod.val_lt _
  have hrmod : (r : ZMod (m (i+1))) = (t : ZMod (m (i+1))) := by
    exact ZMod.natCast_zmod_val _
  have hr0 : (r : ZMod (m i)) = 0 := by
    have hh := congrArg (ZMod.castHom (hm i) (ZMod (m i))) hrmod
    simpa only [map_natCast,map_intCast,ht0] using hh
  have hrdvd : m i ∣ r := (ZMod.natCast_eq_zero_iff r (m i)).mp hr0
  have hlen : r+m i ≤ m (i+1) := by
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt hr) (Nat.dvd_sub (hm i) hrdvd)
    omega
  have hstart : ((t-(r:ℤ) : ℤ) : ZMod (m (i+1))) = -x.2 (i+1) := by
    simp only [Int.cast_sub,Int.cast_natCast,hx,neg_zero,hrmod,sub_self]
  have hw := hW i (wordAt m x (i+1) (t-r)) (hi (t-r) hstart) r hrdvd hlen
  have heq : wordAt m x i t = fun j : Fin (m i) =>
      wordAt m x (i+1) (t-r) ⟨r+j.val,lt_of_lt_of_le (Nat.add_lt_add_left j.isLt r) hlen⟩ := by
    funext j
    change x.1 (t+(j.val:ℤ)) = x.1 (t-(r:ℤ)+((r+j.val:ℕ):ℤ))
    apply congrArg x.1
    push_cast
    ring
  simpa only [heq] using hw

/-- Periodic repetition is used solely as a finite-admissibility witness;
it is not the ergodic measure ultimately selected. -/
def repeatWord (n : ℕ) (w : Fin (m n) → A) : Space A m :=
  (fun t => w ⟨(t : ZMod (m n)).val,ZMod.val_lt _⟩,fun _ => 0)

omit [TopologicalSpace A] [DiscreteTopology A] in
lemma repeatWord_legal (n : ℕ) (w : Fin (m n) → A) (hw : w ∈ W n) :
    Legal m W (repeatWord m n w) n := by
  intro t ht
  have ht0 : (t : ZMod (m n)) = 0 := by simpa [repeatWord] using ht
  have heq : wordAt m (repeatWord m n w) n t = w := by
    funext j
    change w ⟨((t+j.val : ℤ) : ZMod (m n)).val,ZMod.val_lt _⟩ = w j
    congr 1
    apply Fin.ext
    simp only [Int.cast_add,Int.cast_natCast,ht0,zero_add,ZMod.val_natCast_of_lt j.isLt]
  simpa only [heq] using hw

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- Every nonempty concatenated word hierarchy has all the finite-level
configurations required by the compact phase construction. -/
theorem finite_configs (hW : SubwordClosed m W) (hne : ∀ i, (W i).Nonempty) :
    ∀ n, ∃ x : Space A m, ∀ i ≤ n, Compatible m hm x i ∧ Legal m W x i := by
  intro n
  obtain ⟨w,hw⟩ := hne n
  refine ⟨repeatWord m n w,fun i hi => ⟨?_,?_⟩⟩
  · simp [Compatible,repeatWord]
  · have htop := repeatWord_legal m W n w hw
    induction hi using Nat.decreasingInduction with
    | self => exact htop
    | of_succ i hi ih => exact legal_of_succ m hm W hW _ (fun _ => rfl) i ih
end SmoothObstruction.PhaseDynamics

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory

noncomputable instance lengthNeZero (i : ℕ) : NeZero (length 40000 i) :=
  ⟨(length_pos 40000 i).ne'⟩

lemma words_subwordClosed : PhaseDynamics.SubwordClosed (length 40000) words := by
  intro i w hw r hr hlen
  obtain ⟨a,rfl⟩ := hw
  obtain ⟨b,hb⟩ := slice_is_constituent (length_pos 40000 i) (word i) (children i a) r hr hlen
  change (fun j => concat (word i) (children i a) _) ∈ Set.range (word i)
  exact ⟨children i a b,hb.symm⟩

/-- The compact source extension is nonvacuous for the actual balanced,
shift-separated, symplectically constrained recursively selected hierarchy. -/
noncomputable abbrev Extension := PhaseDynamics.extension (length 40000) (length_dvd 40000) words

noncomputable instance initialNonempty : Nonempty (A 0) := alphabet_nonempty 0

/-- Here the finite-admissibility producers are discharged by the actual
words. The remaining main obstruction is not part of this theorem. -/
theorem actual_system : ∃ μ : ProbabilityMeasure Extension,
    StandardNonatomic (μ : Measure Extension) ∧
    Ergodic (PhaseDynamics.extensionShift (length 40000) (length_dvd 40000) words)
      (μ : Measure Extension) ∧
    FiniteKSEntropy (μ : Measure Extension)
      (PhaseDynamics.extensionShift (length 40000) (length_dvd 40000) words) := by
  exact PhaseDynamics.exists_system (length 40000) (length_dvd 40000) words
    (length_unbounded initial_threshold)
    (PhaseDynamics.finite_configs (length 40000) (length_dvd 40000) words
      words_subwordClosed words_nonempty)

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.PhaseDynamics
open MeasureTheory Set Finset
section Window
variable {A : Type*} [TopologicalSpace A] 
  [MeasurableSpace A] [MeasurableSingletonClass A] (m : ℕ → ℕ)
  [∀ i, NeZero (m i)]

/-- The actual symbol word containing the origin, not an independently
assigned label. Its starting time is minus the finite phase representative. -/
def containingWord (x : Space A m) (i : ℕ) : Fin (m i) → A :=
  wordAt m x i (-((x.2 i).val : ℤ))

omit [TopologicalSpace A] [MeasurableSingletonClass A] in
lemma measurable_containingWord (i : ℕ) : Measurable (fun x : Space A m => containingWord m x i) := by
  refine measurable_pi_iff.mpr (fun j => ?_)
  have he : Measurable (fun p : (ℤ → A) × ℤ => p.1 p.2) :=
    measurable_from_prod_countable_left (fun t => measurable_pi_apply t)
  have hi : Measurable (fun x : Space A m => -((x.2 i).val : ℤ)+(j.val : ℤ)) := by
    exact (measurable_of_countable (fun a : ZMod (m i) => -(a.val : ℤ)+(j.val : ℤ))).comp
      ((measurable_pi_apply i).comp measurable_snd)
  exact he.comp (measurable_fst.prodMk hi)

omit [MeasurableSpace A] [MeasurableSingletonClass A]  in
omit [∀ i, NeZero (m i)] in
lemma iterate_symbol (x : Space A m) (j : ℕ) (t : ℤ) :
    ((shift A m)^[j] x).1 t = x.1 (t+j) := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',shift_symbol,ih]
    apply congrArg x.1
    push_cast
    omega

omit [MeasurableSpace A] [MeasurableSingletonClass A]  in
omit [∀ i, NeZero (m i)] in
lemma shift_iterate_phase (x : Space A m) (i j : ℕ) :
    ((shift A m)^[j] x).2 i=x.2 i+j :=
  iterate_phase (shift A m) (fun x => x.2 i) (fun _ => rfl) x j

omit [MeasurableSpace A] [MeasurableSingletonClass A]  in
omit [∀ i, NeZero (m i)] in
lemma containingWord_tower (x : Space A m) (i : ℕ) (hc : x.2 i=0)
    (j : ℕ) (hj : j < m i) :
    containingWord m ((shift A m)^[j] x) i=containingWord m x i := by
  have hp : (((shift A m)^[j] x).2 i).val=j := by
    rw [shift_iterate_phase,hc,zero_add,ZMod.val_natCast,Nat.mod_eq_of_lt hj]
  funext r
  simp only [containingWord,wordAt,hp,hc,ZMod.val_zero,Nat.cast_zero,neg_zero,zero_add,iterate_symbol]
  apply congrArg x.1
  omega

/-- Every parent-word event has exactly the same unnormalized mass at each
phase. This is the invariance argument in source (parent-slot-law), before
normalizing either restriction. No uniform-parent assumption occurs. -/
theorem parent_phase_mass (μ : Measure (Space A m))
    (hT : MeasurePreserving (shift A m) μ μ) (i : ℕ) (v : Fin (m i) → A)
    (j : ℕ) (hj : j < m i) :
    μ {x | x.2 i=(j : ZMod (m i)) ∧ containingWord m x i=v} =
      μ {x | x.2 i=0 ∧ containingWord m x i=v} := by
  let E : Set (Space A m) := {x | x.2 i=(j : ZMod (m i)) ∧ containingWord m x i=v}
  have hc : Measurable (fun x : Space A m => x.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hE : MeasurableSet E := (hc (measurableSet_singleton _)).inter
    (measurable_containingWord m i (measurableSet_singleton v))
  have hpre : ((shift A m)^[j]) ⁻¹' E = {x | x.2 i=0 ∧ containingWord m x i=v} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,E,shift_iterate_phase]
    constructor
    · rintro ⟨hp,hv⟩
      have hz : x.2 i=0 := by
        apply add_right_cancel (b := (j : ZMod (m i)))
        simpa only [zero_add] using hp
      exact ⟨hz,(containingWord_tower m x i hz j hj) ▸ hv⟩
    · rintro ⟨hz,hv⟩
      exact ⟨by rw [hz,zero_add],by rwa [containingWord_tower m x i hz j hj]⟩
  rw [←(hT.iterate j).measure_preimage hE.nullMeasurableSet,hpre]

lemma parent_phase_mass_zmod (μ : Measure (Space A m))
    (hT : MeasurePreserving (shift A m) μ μ) (i : ℕ) (v : Fin (m i) → A)
    (j : ZMod (m i)) :
    μ {x | x.2 i=j ∧ containingWord m x i=v} =
      μ {x | x.2 i=0 ∧ containingWord m x i=v} := by
  simpa only [ZMod.natCast_zmod_val] using parent_phase_mass m μ hT i v j.val (ZMod.val_lt j)

omit [TopologicalSpace A] [MeasurableSingletonClass A] in
lemma sum_phase_parent (μ : Measure (Space A m)) [IsFiniteMeasure μ]
    (i : ℕ) (v : Fin (m i) → A) :
    (∑ j : ZMod (m i), μ.real {x | x.2 i=j ∧ containingWord m x i=v}) =
      μ.real {x | containingWord m x i=v} := by
  let E : Set (Space A m) := {x | containingWord m x i=v}
  have hc : Measurable (fun x : Space A m => x.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hs := sum_measureReal_preimage_singleton (μ:=μ.restrict E) univ
    (fun j _ => (measurableSet_singleton j).preimage hc)
  have hterm (j : ZMod (m i)) : (μ.restrict E).real ((fun x : Space A m => x.2 i) ⁻¹' {j}) =
      μ.real {x | x.2 i=j ∧ containingWord m x i=v} := by
    rw [measureReal_restrict_apply (hc (measurableSet_singleton j))]
    rfl
  change (∑ j, (μ.restrict E).real ((fun x : Space A m => x.2 i) ⁻¹' {j})) =
    (μ.restrict E).real ((fun x : Space A m => x.2 i) ⁻¹' (↑(univ : Finset (ZMod (m i))))) at hs
  simp only [hterm,coe_univ,Set.preimage_univ,measureReal_restrict_apply_univ] at hs
  exact hs

/-- Parent and containing slot are independent under the full stationary
law, although the parent distribution can be wholly nonuniform. -/
theorem parent_slot_independent (μ : Measure (Space A m)) [IsFiniteMeasure μ]
    (hT : MeasurePreserving (shift A m) μ μ) (i : ℕ) (v : Fin (m i) → A)
    (j : ZMod (m i)) :
    (m i : ℝ)*μ.real {x | x.2 i=j ∧ containingWord m x i=v} =
      μ.real {x | containingWord m x i=v} := by
  have hs := sum_phase_parent m μ i v
  have ht (u : ZMod (m i)) : μ.real {x | x.2 i=u ∧ containingWord m x i=v} =
      μ.real {x | x.2 i=j ∧ containingWord m x i=v} := by
    simp only [Measure.real,parent_phase_mass_zmod m μ hT i v]
  simp_rw [ht] at hs
  simpa only [sum_const,card_univ,ZMod.card,nsmul_eq_mul] using hs
end Window
end SmoothObstruction.PhaseDynamics

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set

noncomputable abbrev T : Extension ≃ₜ Extension :=
  PhaseDynamics.extensionShift (length 40000) (length_dvd 40000) words

lemma containingWord_legal (i : ℕ) (x : Extension) :
    PhaseDynamics.containingWord (length 40000) x.val i ∈ words i := by
  apply (x.property i).2
  simp only [Int.cast_neg,Int.cast_natCast,ZMod.natCast_zmod_val]

/-- The actual legal word containing the origin, read as its unique selected
level label. This is a function of the symbolic configuration, not added data. -/
noncomputable def label (i : ℕ) (x : Extension) : A i :=
  Classical.choose (containingWord_legal i x)

lemma word_label (i : ℕ) (x : Extension) :
    word i (label i x)=PhaseDynamics.containingWord (length 40000) x.val i :=
  Classical.choose_spec (containingWord_legal i x)

lemma label_eq_iff (i : ℕ) (x : Extension) (a : A i) :
    label i x=a ↔ PhaseDynamics.containingWord (length 40000) x.val i=word i a := by
  rw [←word_label, (word_injective i).eq_iff]

lemma measurable_label (i : ℕ) : Measurable (label i) := by
  let : Nonempty (A i) := alphabet_nonempty i
  have he : label i = (Function.invFun (word i)) ∘
      (fun x : Extension => PhaseDynamics.containingWord (length 40000) x.val i) := by
    funext x
    simp only [Function.comp_apply,←word_label]
    exact ((Function.leftInverse_invFun (word_injective i)) (label i x)).symm
  rw [he]
  exact (measurable_of_countable _).comp
    ((PhaseDynamics.measurable_containingWord (length 40000) i).comp measurable_subtype_coe)

lemma stationary_ambient (μ : Measure Extension) (hT : MeasurePreserving T μ μ) :
    MeasurePreserving (PhaseDynamics.shift (A 0) (length 40000))
      (μ.map Subtype.val) (μ.map Subtype.val) := by
  have hm : Measurable (PhaseDynamics.shift (A 0) (length 40000)) := by
    apply Measurable.prodMk
    · exact measurable_pi_iff.mpr (fun t => (measurable_pi_apply (t+1)).comp measurable_fst)
    · exact measurable_pi_iff.mpr (fun i => (measurable_of_countable (fun a : ZMod (length 40000 i) => a+1)).comp
        ((measurable_pi_apply i).comp measurable_snd))
  refine ⟨hm,?_⟩
  rw [Measure.map_map hm measurable_subtype_coe]
  have he : (PhaseDynamics.shift (A 0) (length 40000)) ∘ (Subtype.val : Extension → _) =
      (Subtype.val : Extension → _) ∘ T := rfl
  rw [he,←Measure.map_map measurable_subtype_coe hT.measurable,hT.map_eq]

/-- Actual selected parent labels are independent of the fine phase under
EVERY invariant finite measure on the extension. The parent law is arbitrary. -/
theorem label_phase_independent (μ : Measure Extension) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) (a : A i) (j : ZMod (length 40000 i)) :
    (length 40000 i : ℝ)*μ.real {x | x.val.2 i=j ∧ label i x=a} =
      μ.real {x | label i x=a} := by
  have hh := PhaseDynamics.parent_slot_independent (length 40000) (μ.map Subtype.val)
    (stationary_ambient μ hT) i (word i a) j
  have hp : Measurable (fun x : PhaseDynamics.Space (A 0) (length 40000) => x.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hw := PhaseDynamics.measurable_containingWord (A := A 0) (length 40000) i
  have hE : MeasurableSet {x : PhaseDynamics.Space (A 0) (length 40000) |
      x.2 i=j ∧ PhaseDynamics.containingWord (length 40000) x i=word i a} := by
    exact (measurableSet_eq_fun hp measurable_const).inter (measurableSet_eq_fun hw measurable_const)
  have hF : MeasurableSet {x : PhaseDynamics.Space (A 0) (length 40000) |
      PhaseDynamics.containingWord (length 40000) x i=word i a} := by
    exact measurableSet_eq_fun hw measurable_const
  simp only [Measure.real] at hh ⊢
  rw [Measure.map_apply (μ := μ) measurable_subtype_coe hE,
    Measure.map_apply (μ := μ) measurable_subtype_coe hF] at hh
  simpa only [Set.preimage_ofPred_eq,←label_eq_iff] using hh

/-- Compatibility determines the child offset by the parent residue. -/
lemma phase_mod (i : ℕ) (x : Extension) :
    (x.val.2 (i+1)).val % length 40000 i=(x.val.2 i).val := by
  have hc := (x.property i).1
  change ZMod.castHom (length_dvd 40000 i) (ZMod (length 40000 i)) (x.val.2 (i+1))=x.val.2 i at hc
  have hh := congrArg (fun a : ZMod (length 40000 i) => a.val) hc
  rw [←ZMod.natCast_zmod_val (x.val.2 (i+1)),map_natCast,ZMod.val_natCast] at hh
  exact hh


/-- The slot of the containing selected child inside the containing parent. -/
noncomputable def slot (i : ℕ) (x : Extension) : Fin (N (S i)) :=
  ⟨(x.val.2 (i+1)).val / length 40000 i,by
    apply (Nat.div_lt_iff_lt_mul (length_pos 40000 i)).mpr
    simpa only [length,N,S,Nat.mul_comm] using ZMod.val_lt (x.val.2 (i+1))⟩

lemma phase_decompose (i : ℕ) (x : Extension) :
    (x.val.2 (i+1)).val=(slot i x).val*length 40000 i+(x.val.2 i).val := by
  rw [←phase_mod i x]
  exact (Nat.div_add_mod' _ _).symm

/-- The observed child label is exactly the selected concatenation entry
indexed by the actual parent phase, with no exceptional configurations. -/
theorem label_child (i : ℕ) (x : Extension) :
    label i x=children i (label (i+1) x) (slot i x) := by
  apply word_injective i
  funext j
  have hh := congrFun (word_label (i+1) x) (pack (slot i x,j))
  change concat (word i) (children i (label (i+1) x)) (pack (slot i x,j)) = _ at hh
  rw [concat_pack] at hh
  rw [hh,congrFun (word_label i x) j]
  simp only [PhaseDynamics.containingWord,PhaseDynamics.wordAt]
  apply congrArg x.val.1
  change -((x.val.2 i).val : ℤ)+(j.val:ℤ) =
    -((x.val.2 (i+1)).val : ℤ)+((j.val+length 40000 i*(slot i x).val : ℕ):ℤ)
  have hp : ((x.val.2 (i+1)).val : ℤ)=(slot i x).val*(length 40000 i : ℤ)+(x.val.2 i).val := by
    exact_mod_cast phase_decompose i x
  push_cast
  rw [hp]
  ring

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.Alignment
open MeasureTheory Set Finset
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype Y] [MeasurableSingletonClass Y]

/-- Partition an arbitrary event by a finite measurable observation. -/
lemma sum_fibers (μ : Measure X) [IsFiniteMeasure μ] (E : Set X)
    {f : X → Y} (hf : Measurable f) :
    (∑ a : Y,μ.real {x | x∈E ∧ f x=a})=μ.real E := by
  have hh := sum_measureReal_preimage_singleton (μ:=μ.restrict E) univ
    (fun a _ => hf (measurableSet_singleton a))
  have he (a : Y) : (μ.restrict E).real (f ⁻¹' {a})=μ.real {x | x∈E ∧ f x=a} := by
    rw [measureReal_restrict_apply (hf (measurableSet_singleton a))]
    congr 1
    ext x
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq,and_comm]
  simp only [he,coe_univ,Set.preimage_univ,measureReal_restrict_apply_univ] at hh
  exact hh

section Cyclic
variable {m : ℕ} [NeZero m]
variable (T : X → X) (a : X → ZMod m)

def align (x : X) : X := (T^[(-a x).val]) x

omit [MeasurableSpace X] [NeZero m] in
lemma iterate_phase (ha : ∀ x,a (T x)=a x+1) (x : X) (j : ℕ) :
    a ((T^[j]) x)=a x+j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply',ha,ih,Nat.cast_add,Nat.cast_one,add_assoc]

lemma measurable_align (hT : Measurable T) (ha : Measurable a) : Measurable (align T a) := by
  have hf : Measurable (fun p : ℕ × X => (T^[p.1]) p.2) :=
    measurable_from_prod_countable_right (fun j => hT.iterate j)
  exact hf.comp (((measurable_of_countable (fun r : ZMod m => (-r).val)).comp ha).prodMk measurable_id)

omit [MeasurableSpace X] in
lemma align_phase (ha : ∀ x,a (T x)=a x+1) (x : X) : a (align T a x)=0 := by
  rw [align,iterate_phase T a ha,ZMod.natCast_zmod_val,add_neg_cancel]

/-- Each fixed phase piece maps to exactly the same boundary event; this
is an unnormalized identity using invariance, not a uniform-word assumption. -/
lemma phase_piece (μ : Measure X) (hT : MeasurePreserving T μ μ)
    (ha : Measurable a) (hevolve : ∀ x,a (T x)=a x+1)
    (E : Set X) (hE : MeasurableSet E) (j : ZMod m) :
    μ {x | x∈(align T a) ⁻¹' E ∧ a x=j}=μ (E∩{x | a x=0}) := by
  have hb : MeasurableSet (E∩{x | a x=0}) :=
    hE.inter (measurableSet_eq_fun ha measurable_const)
  rw [←(hT.iterate (-j).val).measure_preimage hb.nullMeasurableSet]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_inter_iff,iterate_phase T a hevolve,
    ZMod.natCast_zmod_val]
  constructor
  · rintro ⟨hx,hj⟩
    exact ⟨by simpa only [align,hj] using hx,by rw [hj,add_neg_cancel]⟩
  · rintro ⟨hx,hj⟩
    have hj' : a x=j := by exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hj)
    exact ⟨by simpa only [align,hj'] using hx,hj'⟩

/-- Exact forward-alignment law for every measurable event. -/
theorem align_real (μ : Measure X) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a)
    (hevolve : ∀ x,a (T x)=a x+1) (E : Set X) (hE : MeasurableSet E) :
    μ.real ((align T a) ⁻¹' E) = (m:ℝ)*μ.real (E∩{x | a x=0}) := by
  rw [←sum_fibers μ ((align T a) ⁻¹' E) ha]
  simp only [Measure.real,phase_piece T a μ hT ha hevolve E hE]
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul]

noncomputable def boundaryMeasure (μ : Measure X) : Measure X :=
  (m:ℝ≥0∞) • μ.restrict {x | a x=0}

omit [NeZero m] in
lemma boundary_real (μ : Measure X) (E : Set X) (hE : MeasurableSet E) :
    (boundaryMeasure a μ).real E=(m:ℝ)*μ.real (E∩{x | a x=0}) := by
  rw [boundaryMeasure,Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_natCast,Measure.restrict_apply hE]
  rfl

/-- The image of the original stationary law under first-boundary advance
is the normalized boundary restriction itself. -/
theorem align_map (μ : Measure X) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a)
    (hevolve : ∀ x,a (T x)=a x+1) :
    μ.map (align T a)=boundaryMeasure a μ := by
  have hm := measurable_align T a hT.measurable ha
  apply Measure.ext
  intro E hE
  apply ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by
    change ((m:ℝ≥0∞)*(μ.restrict {x | a x=0}) E)≠⊤
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) (measure_ne_top _ _)) |>.mp
  change (μ.map (align T a)).real E=(boundaryMeasure a μ).real E
  rw [boundary_real a μ E hE]
  simpa only [Measure.real,Measure.map_apply hm hE] using align_real T a μ hT ha hevolve E hE

/-- Its normalization is proved, including the literal source factor m. -/
theorem boundary_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a)
    (hevolve : ∀ x,a (T x)=a x+1) : IsProbabilityMeasure (boundaryMeasure a μ) := by
  rw [←align_map T a μ hT ha hevolve]
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_align T a hT.measurable ha).aemeasurable).2 inferInstance
end Cyclic
end SmoothObstruction.Alignment

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep MeasureTheory Set
open scoped ENNReal

abbrev phase (i : ℕ) (x : Extension) : ZMod (length 40000 i) := x.val.2 i
lemma measurable_phase (i : ℕ) : Measurable (phase i) :=
  ((measurable_pi_apply i).comp measurable_snd).comp measurable_subtype_coe

lemma iterate_coe (j : ℕ) (x : Extension) :
    ((T^[j]) x).val=(PhaseDynamics.shift (A 0) (length 40000))^[j] x.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    change PhaseDynamics.shift (A 0) (length 40000) (((T^[j]) x).val) = _
    exact congrArg (PhaseDynamics.shift (A 0) (length 40000)) ih

lemma phase_iterate (i j : ℕ) (x : Extension) : phase i ((T^[j]) x)=phase i x+j := by
  change (((T^[j]) x).val).2 i = _
  rw [iterate_coe,PhaseDynamics.shift_iterate_phase]

noncomputable def boundary (μ : Measure Extension) (i : ℕ) : Measure Extension :=
  Alignment.boundaryMeasure (phase i) μ

lemma boundary_isProbability (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) : IsProbabilityMeasure (boundary μ i) :=
  Alignment.boundary_probability T (phase i) μ hT (measurable_phase i) (fun _ => rfl)

noncomputable def advance (i : ℕ) : Extension → Extension := Alignment.align T (phase i)

/-- Literal forward-to-first-boundary law; µ_i is the source's factor-m_i
normalized restriction, not a newly chosen distribution. -/
theorem advance_map (μ : Measure Extension) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) : μ.map (advance i)=boundary μ i :=
  Alignment.align_map T (phase i) μ hT (measurable_phase i) (fun _ => rfl)

lemma phase_mod_two (i : ℕ) (x : Extension) :
    (phase (i+2) x).val % length 40000 i=(phase i x).val := by
  rw [←phase_mod i x,←phase_mod (i+1) x,Nat.mod_mod_of_dvd _ (length_dvd 40000 i)]

lemma length_two (i : ℕ) :
    length 40000 (i+2)=length 40000 i*(N (S i)*N (S (i+1))) := by
  simp only [length,N,S]
  ring

noncomputable def parentSlot (i : ℕ) (x : Extension) : Fin (N (S i)*N (S (i+1))) :=
  ⟨(phase (i+2) x).val / length 40000 i,by
    apply (Nat.div_lt_iff_lt_mul (length_pos 40000 i)).mpr
    simpa only [length_two,Nat.mul_comm] using ZMod.val_lt (phase (i+2) x)⟩

lemma measurable_parentSlot (i : ℕ) : Measurable (parentSlot i) := by
  have hh : parentSlot i = (fun a : ZMod (length 40000 (i+2)) =>
      (⟨a.val / length 40000 i,by
        apply (Nat.div_lt_iff_lt_mul (length_pos 40000 i)).mpr
        simpa only [length_two,Nat.mul_comm] using ZMod.val_lt a⟩ : Fin (N (S i)*N (S (i+1))))) ∘ phase (i+2) := rfl
  rw [hh]
  exact (measurable_of_countable _).comp (measurable_phase (i+2))

lemma parentSlot_decompose (i : ℕ) (x : Extension) :
    (phase (i+2) x).val=(parentSlot i x).val*length 40000 i+(phase i x).val := by
  rw [←phase_mod_two i x]
  exact (Nat.div_add_mod' _ _).symm

lemma parentSlot_site_lt (i : ℕ) (j : Fin (N (S i)*N (S (i+1)))) :
    j.val*length 40000 i < length 40000 (i+2) := by
  rw [length_two,Nat.mul_comm (length 40000 i)]
  exact Nat.mul_lt_mul_of_pos_right j.isLt (length_pos 40000 i)

lemma parentSlot_site (i : ℕ) (x : Extension) (j : Fin (N (S i)*N (S (i+1)))) :
    parentSlot i x=j ∧ phase i x=0 ↔
      phase (i+2) x=(j.val*length 40000 i : ℕ) := by
  constructor
  · rintro ⟨hj,hp⟩
    apply ZMod.val_injective
    rw [parentSlot_decompose,hj,hp,ZMod.val_zero,Nat.add_zero,ZMod.val_natCast,
      Nat.mod_eq_of_lt (parentSlot_site_lt i j)]
  · intro hp
    have hv : (phase (i+2) x).val=j.val*length 40000 i := by
      rw [hp,ZMod.val_natCast,Nat.mod_eq_of_lt (parentSlot_site_lt i j)]
    refine ⟨?_,?_⟩
    · apply Fin.ext
      change (phase (i+2) x).val / length 40000 i=j.val
      rw [hv,Nat.mul_div_left _ (length_pos 40000 i)]
    · apply ZMod.val_injective
      rw [ZMod.val_zero,←phase_mod_two i x,hv,Nat.mul_mod_left]

/-- Every genuine parent slot has the same mass with a fixed parent label.
The right-hand side is the arbitrary stationary parent law, not uniform. -/
theorem boundary_parentSlot_mass (μ : Measure Extension) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) (v : A (i+2))
    (j : Fin (N (S i)*N (S (i+1)))) :
    (N (S i)*N (S (i+1)) : ℕ)*(boundary μ i).real {x | parentSlot i x=j ∧ label (i+2) x=v} =
      μ.real {x | label (i+2) x=v} := by
  have hE : MeasurableSet {x | parentSlot i x=j ∧ label (i+2) x=v} :=
    (measurableSet_eq_fun (measurable_parentSlot i) measurable_const).inter
      (measurableSet_eq_fun (measurable_label (i+2)) measurable_const)
  change (N (S i)*N (S (i+1)) : ℕ)*
    (Alignment.boundaryMeasure (phase i) μ).real _ = _
  rw [Alignment.boundary_real (phase i) μ _ hE]
  have he : {x | parentSlot i x=j ∧ label (i+2) x=v} ∩ {x | phase i x=0} =
      {x | phase (i+2) x=(j.val*length 40000 i : ℕ) ∧ label (i+2) x=v} := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq]
    simpa only [and_assoc,and_left_comm,and_comm] using
      and_congr_left (fun _ : label (i+2) x=v => parentSlot_site i x j)
  rw [he]
  have hh := label_phase_independent μ hT (i+2) v (j.val*length 40000 i : ℕ)
  rw [show (length 40000 (i+2):ℝ)=(length 40000 i:ℝ)*(N (S i)*N (S (i+1)):ℕ) by
    exact_mod_cast length_two i] at hh
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set

lemma phase_val_nonwrap (i j : ℕ) (x : Extension)
    (hj : (phase i x).val+j < length 40000 i) :
    (phase i ((T^[j]) x)).val=(phase i x).val+j := by
  rw [phase_iterate,←ZMod.natCast_zmod_val (phase i x),←Nat.cast_add,
    ZMod.val_natCast,Nat.mod_eq_of_lt hj,ZMod.natCast_zmod_val]

lemma label_nonwrap (i j : ℕ) (x : Extension)
    (hj : (phase i x).val+j < length 40000 i) :
    label i ((T^[j]) x)=label i x := by
  apply word_injective i
  rw [word_label,word_label]
  funext r
  change (((T^[j]) x).val).1 (-(phase i ((T^[j]) x)).val+(r.val:ℤ)) =
    x.val.1 (-(phase i x).val+(r.val:ℤ))
  rw [phase_val_nonwrap i j x hj,iterate_coe,PhaseDynamics.iterate_symbol]
  apply congrArg x.val.1
  push_cast
  ring

lemma length_step (i : ℕ) : length 40000 (i+1)=length 40000 i*N (S i) := rfl

lemma slot_pair (i : ℕ) (x : Extension) :
    (parentSlot i x).val=(slot (i+1) x).val*N (S i)+(slot i x).val := by
  have h := parentSlot_decompose i x
  rw [phase_decompose (i+1) x,phase_decompose i x,length_step i] at h
  have he : ((parentSlot i x).val)*length 40000 i =
      ((slot (i+1) x).val*N (S i)+(slot i x).val)*length 40000 i := by
    nlinarith
  exact Nat.eq_of_mul_eq_mul_right (length_pos 40000 i) he

/-- Inside a parent, advancement by a child-word length advances its actual
slot by one. Alignment is the genuine phase-zero event. -/
lemma label_advance_child (i r : ℕ) (x : Extension) (hx : phase i x=0)
    (hr : (slot i x).val+r < N (S i)) :
    label i ((T^[r*length 40000 i]) x) =
      children i (label (i+1) x) ⟨(slot i x).val+r,hr⟩ := by
  have hp : (phase (i+1) x).val=(slot i x).val*length 40000 i := by
    change x.val.2 i=0 at hx
    rw [phase_decompose i x,hx,ZMod.val_zero,Nat.add_zero]
  have hj : (phase (i+1) x).val+r*length 40000 i < length 40000 (i+1) := by
    rw [hp,←Nat.add_mul,length_step,Nat.mul_comm (length 40000 i)]
    exact Nat.mul_lt_mul_of_pos_right hr (length_pos 40000 i)
  rw [label_child,label_nonwrap (i+1) _ x hj]
  apply congrArg (children i (label (i+1) x))
  apply Fin.ext
  change (phase (i+1) ((T^[r*length 40000 i]) x)).val / length 40000 i = _
  rw [phase_val_nonwrap (i+1) _ x hj,hp,←Nat.add_mul,
    Nat.mul_div_left _ (length_pos 40000 i)]

/-- The exact observed finite word-label list on the normalized boundary. -/
noncomputable def labelList (i r : ℕ) (x : Extension) : Fin r → A i :=
  fun j => label i ((T^[j.val*length 40000 i]) x)

lemma measurable_T : Measurable (T : Extension → Extension) := by
  apply Measurable.subtype_mk
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr (fun t =>
      ((measurable_pi_apply (t+1)).comp measurable_fst).comp measurable_subtype_coe)
  · exact measurable_pi_iff.mpr (fun i =>
      (measurable_of_countable (fun a : ZMod (length 40000 i) => a+1)).comp (measurable_phase i))

lemma measurable_labelList (i r : ℕ) : Measurable (labelList i r) := by
  exact measurable_pi_iff.mpr (fun j => (measurable_label i).comp
    (measurable_T.iterate (j.val*length 40000 i)))

/-- Uniform finite-window sampling is an exact identification of the actual
symbolic orbit, not a replacement process. No wrap occurs at admissible slots. -/
theorem labelList_inside (i r : ℕ) (x : Extension) (hx : phase i x=0)
    (hr : (slot i x).val+r ≤ N (S i)) :
    labelList i r x = fun j : Fin r =>
      children i (children (i+1) (label (i+2) x) (slot (i+1) x))
        ⟨(slot i x).val+j.val,by have := j.isLt; omega⟩ := by
  funext j
  rw [labelList,label_advance_child i j.val x hx (by have := j.isLt; omega),
    label_child (i+1) x]
end SmoothObstruction.WordHierarchy

end

end OAI
