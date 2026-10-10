import Mathlib
import OAI.Computability.MaxCut.Games.TranslationTarget
import OAI.Computability.MaxCut.Encoding.TableKeysCompleteness

namespace OAI

/-! Direct canonical-body addresses. The fixed list of canonical words is
interpreted in big-endian order, matching forward Horner steps `B*acc+digit`.
Unused addresses represent isolated vertices. These are semantic encoding and
polynomial-size results, not an assumed machine implementation. -/

namespace MaxCutGames.Reduction.CanonicalAddress

open CanonicalEncoding

/-- Most-significant-word first, with leading zero words retained in the
fixed-length domain. Mathlib's `ofDigits` uses the opposite list order. -/
def radix (B : Nat) (words : List Nat) : Nat := Nat.ofDigits B words.reverse

theorem radix_eq_foldl (B : Nat) (words : List Nat) :
    radix B words = words.foldl (fun acc digit => B * acc + digit) 0 := by
  unfold radix
  rw [Nat.ofDigits_eq_foldr, List.foldr_reverse]
  simp only [Nat.cast_id, Nat.add_comm]

@[simp] theorem radix_nil (B : Nat) : radix B [] = 0 := rfl

/-- This is precisely the arithmetic operation of `MachineRadixStep`. -/
theorem radix_append_word (B : Nat) (words : List Nat) (digit : Nat) :
    radix B (words ++ [digit]) = B * radix B words + digit := by
  simp only [radix_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem radix_lt_pow_length {B : Nat} (hB : 1 < B) (words : List Nat)
    (bounded : ∀ w ∈ words, w < B) : radix B words < B ^ words.length := by
  unfold radix
  simpa only [List.length_reverse] using
    Nat.ofDigits_lt_base_pow_length hB
      (fun w hw => bounded w (List.mem_reverse.mp hw))

/-- Fixed width makes leading zero words unambiguous. -/
theorem radix_injective_of_length_eq {B : Nat} (hB : 1 < B)
    {xs ys : List Nat} (sameLength : xs.length = ys.length)
    (xsBounded : ∀ w ∈ xs, w < B) (ysBounded : ∀ w ∈ ys, w < B)
    (sameAddress : radix B xs = radix B ys) : xs = ys := by
  have reversed : xs.reverse = ys.reverse :=
    Nat.ofDigits_inj_of_len_eq hB (by simpa only [List.length_reverse] using sameLength)
      (fun w hw => xsBounded w (List.mem_reverse.mp hw))
      (fun w hw => ysBounded w (List.mem_reverse.mp hw)) sameAddress
  have h := congrArg List.reverse reversed
  simpa only [List.reverse_reverse] using h

/-- One larger than the proved bound on every canonical word. -/
def base (n m s d : Nat) : Nat := wordBound n m s d + 1

@[simp] theorem base_eq (n m s d : Nat) :
    base n m s d = n + m + 2^s + 2^d + 4 := by
  simp [base, wordBound, Nat.add_assoc]

theorem one_lt_base (n m s d : Nat) : 1 < base n m s d := by
  have h : 3 ≤ wordBound n m s d := by
    unfold wordBound
    exact Nat.le_add_left 3 _
  unfold base
  omega

theorem bodyWords_lt_base {n m k s d : Nat} (body : Body n m k s d)
    (w : Nat) (hw : w ∈ bodyWords body) : w < base n m s d :=
  Nat.lt_succ_of_le (bodyWords_bounded body w hw)

def capacity (n m k s d : Nat) : Nat := (base n m s d) ^ (1 + 9*k)

theorem capacity_pos (n m k s d : Nat) : 0 < capacity n m k s d :=
  pow_pos (Nat.zero_lt_of_lt (one_lt_base n m s d)) _

def bodyAddress {n m k s d : Nat} (body : Body n m k s d) :
    Fin (capacity n m k s d) :=
  ⟨radix (base n m s d) (bodyWords body), by
    simpa only [capacity, bodyWords_length] using
      radix_lt_pow_length (one_lt_base n m s d) (bodyWords body) (bodyWords_lt_base body)⟩

@[simp] theorem bodyAddress_val {n m k s d : Nat} (body : Body n m k s d) :
    (bodyAddress body).val = radix (base n m s d) (bodyWords body) := rfl

theorem bodyAddress_injective {n m k s d : Nat} :
    Function.Injective (bodyAddress (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  apply bodyWords_injective
  exact radix_injective_of_length_eq (one_lt_base n m s d)
    (by simp only [bodyWords_length]) (bodyWords_lt_base x) (bodyWords_lt_base y)
    (congrArg Fin.val h)

@[simp] theorem bodyAddress_eq_iff {n m k s d : Nat} (x y : Body n m k s d) :
    bodyAddress x = bodyAddress y ↔ x = y := bodyAddress_injective.eq_iff

/-- For fixed k,s,d, the entire direct-address space is a polynomial in n+m. -/
noncomputable def capacityPolynomial (k s d : Nat) : Polynomial Nat :=
  (Polynomial.X + Polynomial.C (2^s + 2^d + 4)) ^ (1 + 9*k)

theorem capacityPolynomial_eval (n m k s d : Nat) :
    (capacityPolynomial k s d).eval (n + m) = capacity n m k s d := by
  simp [capacityPolynomial, capacity, base_eq, Nat.add_assoc]

end MaxCutGames.Reduction.CanonicalAddress

/-! Finite noise tables for the executable outer reduction. Positions, including
positions containing equal vectors, remain distinct sample outcomes. -/

namespace MaxCutGames.Integration.NoiseTables

open BinaryLinear MaxCutGames.Reduction.ActualSource

variable {s d : Nat}

/-- Reindexing changes the names of outcomes, retaining their uniform law. -/
def reindex (g : SplitGadget s d) {I : Type} [Fintype I] [Nonempty I]
    (e : I ≃ g.NoiseIndex) : SplitGadget s d where
  f := g.f
  equivariant := g.equivariant
  NoiseIndex := I
  noiseFintype := inferInstance
  noiseNonempty := inferInstance
  noise i := g.noise (e i)

theorem reindex_stabilityError (g : SplitGadget s d)
    {I : Type} [Fintype I] [Nonempty I] (e : I ≃ g.NoiseIndex) :
    (reindex g e).stabilityError = g.stabilityError := by
  apply Fintype.expect_equiv ((Equiv.refl (Ambient s d)).prodCongr e)
  intro x
  rfl

theorem reindex_kernelProbability (g : SplitGadget s d)
    {I : Type} [Fintype I] [Nonempty I] (e : I ≃ g.NoiseIndex)
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    SplitGadget.kernelProbability (reindex g e) S =
      SplitGadget.kernelProbability g S := by
  classical
  apply Fintype.expect_equiv e
  intro i
  rfl

/-- Only a nonempty finite list of binary vectors is required as static noise
data. The correcting function is a separate witness used in the proof. -/
structure Table (s d : Nat) where
  vectors : List (Ambient s d)
  nonempty : vectors ≠ []

namespace Table

def gadget (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : SplitGadget s d where
  f := f
  equivariant := hf
  NoiseIndex := Fin T.vectors.length
  noiseFintype := inferInstance
  noiseNonempty := ⟨⟨0, List.length_pos_iff.mpr T.nonempty⟩⟩
  noise := T.vectors.get

def ofEnumeration (g : SplitGadget s d) (en : NoiseEnumeration g) : Table s d where
  vectors := en.indices.map g.noise
  nonempty := by simpa using en.nonempty

@[simp] theorem ofEnumeration_length (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (ofEnumeration g en).vectors.length = en.indices.length := by
  simp [ofEnumeration]

/-- The inverse equivalence is used only to prove the probability identity;
the forward noise lookup is ordinary finite-list indexing. -/
noncomputable def positionEquiv (g : SplitGadget s d) (en : NoiseEnumeration g) :
    Fin (ofEnumeration g en).vectors.length ≃ g.NoiseIndex := by
  classical
  exact (finCongr (ofEnumeration_length g en)).trans
    (en.nodup.getEquivOfForallMemList en.indices en.complete)

theorem noise_positionEquiv (g : SplitGadget s d) (en : NoiseEnumeration g)
    (i : Fin (ofEnumeration g en).vectors.length) :
    ((ofEnumeration g en).gadget g.f g.equivariant).noise i =
      g.noise (positionEquiv g en i) := by
  change (en.indices.map g.noise)[i.val] = g.noise en.indices[i.val]
  exact List.getElem_map _

theorem stabilityError_ofEnumeration (g : SplitGadget s d) (en : NoiseEnumeration g) :
    ((ofEnumeration g en).gadget g.f g.equivariant).stabilityError =
      g.stabilityError := by
  apply Fintype.expect_equiv
    ((Equiv.refl (Ambient s d)).prodCongr (positionEquiv g en))
  intro x
  change (if g.f (x.1 + _) = g.f x.1 then (0 : ℚ) else 1) = _
  rw [noise_positionEquiv]
  rfl

theorem kernelProbability_ofEnumeration (g : SplitGadget s d)
    (en : NoiseEnumeration g) {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) :
    SplitGadget.kernelProbability ((ofEnumeration g en).gadget g.f g.equivariant) S =
      SplitGadget.kernelProbability g S := by
  classical
  apply Fintype.expect_equiv (positionEquiv g en)
  intro i
  rw [noise_positionEquiv]

/-- Exact table conversion retains both mathematical gadget guarantees. -/
theorem guarantees_ofEnumeration (g : SplitGadget s d) (en : NoiseEnumeration g)
    {ζ ν : ℚ} {r : Nat}
    (hstable : g.stabilityError ≤ ζ)
    (hdisp : ∀ (P : Type) [AddCommGroup P] [Module F2 P]
      (S : Ambient s d →ₗ[F2] P),
      r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
      SplitGadget.kernelProbability g S ≤ ν) :
    ((ofEnumeration g en).gadget g.f g.equivariant).stabilityError ≤ ζ ∧
      ∀ (P : Type) [AddCommGroup P] [Module F2 P]
        (S : Ambient s d →ₗ[F2] P),
        r ≤ Module.finrank F2 (S.comp (alphabetEmbedding s d)).range →
        SplitGadget.kernelProbability
          ((ofEnumeration g en).gadget g.f g.equivariant) S ≤ ν := by
  constructor
  · simpa only [stabilityError_ofEnumeration] using hstable
  · intro P _ _ S hS
    rw [kernelProbability_ofEnumeration]
    exact hdisp P S hS

end Table
end MaxCutGames.Integration.NoiseTables

namespace MaxCutGames.Integration.TableReduction

open BinaryLinear NoiseTables MaxCutGames.Reduction.ActualSource
open MaxCutGames.Reduction.ActualGame MaxCutGames.Foundations.Target

variable {s d : Nat}

def tableEnumeration (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : NoiseEnumeration (T.gadget f hf) where
  indices := List.finRange T.vectors.length
  nodup := List.nodup_finRange _
  complete i := List.mem_finRange i

/-- The projection is used only to fill an erased witness field. It is never
used when generating constraints or evaluating their permutation tables. -/
def tableSkeleton (T : Table s d) : SplitGadget s d :=
  T.gadget Prod.fst (fun _ _ => rfl)

/-- A total executable map with finite vector data and no nonlinear-map input. -/
def output (S : Source) (k : Nat) (T : Table s d) : Instance (2 ^ s) :=
  outputInstanceWithEnumeration S k (tableSkeleton T)
    (tableEnumeration T Prod.fst (fun _ _ => rfl))

/-- Every correcting-map witness generates exactly the same numbered instance,
including the ordered constraint list and all permutation entries. -/
theorem output_eq_with_witness (S : Source) (k : Nat) (T : Table s d)
    (f : Ambient s d → Alphabet s) (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    output S k T =
      outputInstanceWithEnumeration S k (T.gadget f hf) (tableEnumeration T f hf) := by
  rfl

theorem completeAt_output_iff (error : RationalError) (S : Source) (k : Nat)
    (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    CompleteAt error (output S k T) ↔
      CompleteAt error (outputInstance S k (T.gadget f hf)) := by
  rw [output_eq_with_witness S k T f hf]
  exact completeAt_outputInstanceWithEnumeration_iff _ _ _ _ _

theorem soundAt_output_iff (error : RationalError) (S : Source) (k : Nat)
    (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    SoundAt error (output S k T) ↔
      SoundAt error (outputInstance S k (T.gadget f hf)) := by
  rw [output_eq_with_witness S k T f hf]
  exact soundAt_outputInstanceWithEnumeration_iff _ _ _ _ _

theorem edge_ofEnumeration (S : Source) (k : Nat) (g : SplitGadget s d)
    (en : NoiseEnumeration g)
    (ω : Outcome S k ((Table.ofEnumeration g en).gadget g.f g.equivariant)) :
    edge S k ((Table.ofEnumeration g en).gadget g.f g.equivariant) ω =
      edge S k g (ω.1, Table.positionEquiv g en ω.2.1, ω.2.2) := by
  simp only [edge, leftQuery, rightQuery]
  erw [Table.noise_positionEquiv g en ω.2.1]

theorem acceptance_ofEnumeration (S : Source) (k : Nat) (g : SplitGadget s d)
    (en : NoiseEnumeration g) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) :
    acceptanceProbability S k ((Table.ofEnumeration g en).gadget g.f g.equivariant) label =
      acceptanceProbability S k g label := by
  apply Fintype.expect_equiv ((Equiv.refl (Query S k s d)).prodCongr
    ((Table.positionEquiv g en).prodCongr (Equiv.refl (Dual k))))
  intro ω
  exact congrArg
    (fun c : Constraint (vertexCount S k s d) (2 ^ s) =>
      if c.satisfied label then (1 : ℚ) else 0)
    (edge_ofEnumeration S k g en ω)

theorem rate_ofEnumeration (S : Source) (k : Nat) (g : SplitGadget s d)
    (en : NoiseEnumeration g) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) :
    GapSemantics.satisfactionRate
      (outputInstance S k ((Table.ofEnumeration g en).gadget g.f g.equivariant)) label =
      GapSemantics.satisfactionRate (outputInstance S k g) label := by
  exact (acceptanceProbability_eq_count S k _ label).symm.trans
    ((acceptance_ofEnumeration S k g en label).trans
      (acceptanceProbability_eq_count S k g label))

/-- Normalization to a concrete table preserves the original completeness
threshold exactly; there is no additional approximation loss. -/
theorem completeAt_ofEnumeration_iff (error : RationalError)
    (S : Source) (k : Nat) (g : SplitGadget s d) (en : NoiseEnumeration g) :
    CompleteAt error (output S k (Table.ofEnumeration g en)) ↔
      CompleteAt error (outputInstance S k g) := by
  rw [completeAt_output_iff error S k _ g.f g.equivariant]
  rw [GapSemantics.completeAt_iff, GapSemantics.completeAt_iff]
  constructor
  · rintro ⟨label, h⟩
    exact ⟨label, h.trans_eq (rate_ofEnumeration S k g en label)⟩
  · rintro ⟨label, h⟩
    exact ⟨label, h.trans_eq (rate_ofEnumeration S k g en label).symm⟩

theorem soundAt_ofEnumeration_iff (error : RationalError)
    (S : Source) (k : Nat) (g : SplitGadget s d) (en : NoiseEnumeration g) :
    SoundAt error (output S k (Table.ofEnumeration g en)) ↔
      SoundAt error (outputInstance S k g) := by
  rw [soundAt_output_iff error S k _ g.f g.equivariant]
  rw [GapSemantics.soundAt_iff, GapSemantics.soundAt_iff]
  constructor
  · intro h label
    exact (rate_ofEnumeration S k g en label).symm.trans_le (h label)
  · intro h label
    exact (rate_ofEnumeration S k g en label).trans_le (h label)

end MaxCutGames.Integration.TableReduction

/-! Injective vertex addresses may leave unused output vertices. The actual
instance is obtained by mapping endpoints in the original constraint list;
constraint order, multiplicity, and permutation tables are retained exactly. -/

namespace MaxCutGames.Integration.VertexEmbedding

open MaxCutGames.Foundations.Target
open GapSemantics TranslationTarget

def embedConstraint {n m q : Nat} (f : Fin n → Fin m) (c : Constraint n q) :
    Constraint m q where
  source := f c.source
  target := f c.target
  permutation := c.permutation

@[simp] theorem embedConstraint_satisfied {n m q : Nat} (f : Fin n → Fin m)
    (c : Constraint n q) (labeling : Fin m → Fin q) :
    (embedConstraint f c).satisfied labeling = c.satisfied (labeling ∘ f) := rfl

@[simp] theorem embedConstraint_permutation {n m q : Nat} (f : Fin n → Fin m)
    (c : Constraint n q) : (embedConstraint f c).permutation = c.permutation := rfl

theorem count_map {n m q : Nat} (f : Fin n → Fin m)
    (constraints : List (Constraint n q)) (labeling : Fin m → Fin q) :
    countSatisfied labeling (constraints.map (embedConstraint f)) =
      countSatisfied (labeling ∘ f) constraints := by
  induction constraints with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c.satisfied (labeling ∘ f) = true <;> simp [countSatisfied, ih, hc]

def embedInstance {q m : Nat} (g : Instance q) (f : Fin g.vertices → Fin m)
    (_hf : Function.Injective f) : Instance q where
  vertices := m
  constraints := g.constraints.map (embedConstraint f)
  nonempty h := g.nonempty (List.map_eq_nil_iff.mp h)

@[simp] theorem embedInstance_vertices {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    (embedInstance g f hf).vertices = m := rfl

theorem embedInstance_constraints {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    (embedInstance g f hf).constraints = g.constraints.map (embedConstraint f) := rfl

@[simp] theorem embedInstance_length {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    (embedInstance g f hf).constraints.length = g.constraints.length := List.length_map _

theorem count_embed {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f)
    (labeling : Fin m → Fin q) :
    countSatisfied labeling (embedInstance g f hf).constraints =
      countSatisfied (labeling ∘ f) g.constraints := count_map f g.constraints labeling

theorem satisfactionRate_embed {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f)
    (labeling : Fin m → Fin q) :
    satisfactionRate (embedInstance g f hf) labeling =
      satisfactionRate g (labeling ∘ f) := by
  unfold satisfactionRate
  simp only [embedInstance, count_map, List.length_map]

/-- The extension is only used as a semantic witness, not by the instance constructor. -/
noncomputable def extendLabeling {n m q : Nat} (f : Fin n → Fin m)
    (labeling : Fin n → Fin q) (defaultLabel : Fin q) (v : Fin m) : Fin q := by
  classical
  exact if h : ∃ u, f u = v then labeling (Classical.choose h) else defaultLabel

@[simp] theorem extendLabeling_apply {n m q : Nat} (f : Fin n → Fin m)
    (hf : Function.Injective f) (labeling : Fin n → Fin q)
    (defaultLabel : Fin q) (v : Fin n) :
    extendLabeling f labeling defaultLabel (f v) = labeling v := by
  classical
  have hx : ∃ u, f u = f v := ⟨v, rfl⟩
  rw [extendLabeling, dite_eq_left hx]
  exact congrArg labeling (hf (Classical.choose_spec hx))

theorem extendLabeling_comp {n m q : Nat} (f : Fin n → Fin m)
    (hf : Function.Injective f) (labeling : Fin n → Fin q) (defaultLabel : Fin q) :
    extendLabeling f labeling defaultLabel ∘ f = labeling := by
  funext v
  exact extendLabeling_apply f hf labeling defaultLabel v

theorem soundAt_embed {q m : Nat} (error : RationalError) (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f)
    (hg : SoundAt error g) : SoundAt error (embedInstance g f hf) := by
  intro labeling
  change (Fin m → Fin q) at labeling
  simp only [embedInstance, count_map, List.length_map]
  exact hg (labeling ∘ f)

theorem completeAt_embed {q m : Nat} (error : RationalError) (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) (hq : 0 < q)
    (hg : CompleteAt error g) : CompleteAt error (embedInstance g f hf) := by
  obtain ⟨labeling, hl⟩ := hg
  refine ⟨extendLabeling f labeling ⟨0, hq⟩, ?_⟩
  simp only [embedInstance, count_map, List.length_map, extendLabeling_comp f hf]
  exact hl

theorem completeAt_embed_iff {q m : Nat} (error : RationalError) (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) (hq : 0 < q) :
    CompleteAt error (embedInstance g f hf) ↔ CompleteAt error g := by
  constructor
  · rintro ⟨labeling, hl⟩
    change (Fin m → Fin q) at labeling
    refine ⟨labeling ∘ f, ?_⟩
    simpa only [embedInstance, count_map, List.length_map] using hl
  · exact completeAt_embed error g f hf hq

theorem soundAt_embed_iff {q m : Nat} (error : RationalError) (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) (hq : 0 < q) :
    SoundAt error (embedInstance g f hf) ↔ SoundAt error g := by
  constructor
  · intro hg labeling
    have hl := hg (extendLabeling f labeling ⟨0, hq⟩)
    simpa only [embedInstance, count_map, List.length_map, extendLabeling_comp f hf] using hl
  · exact soundAt_embed error g f hf

theorem isTranslationInstance_embed_iff {q s m : Nat}
    (coordinates : Fin q ≃ BinaryLinear.Vector s) (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    IsTranslationInstance coordinates (embedInstance g f hf) ↔
      IsTranslationInstance coordinates g := by
  constructor
  · intro hg c hc
    exact hg (embedConstraint f c) (List.mem_map.mpr ⟨c, hc, rfl⟩)
  · intro hg c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact hg d hd

end MaxCutGames.Integration.VertexEmbedding

end OAI
