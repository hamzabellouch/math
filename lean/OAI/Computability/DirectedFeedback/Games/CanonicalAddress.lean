import Mathlib
import OAI.Computability.DirectedFeedback.Games.ActualAdviceUpper

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.CanonicalAddress

open CanonicalEncoding

def radix (B : Nat) (words : List Nat) : Nat := Nat.ofDigits B words.reverse

theorem radix_eq_foldl (B : Nat) (words : List Nat) :
    radix B words = words.foldl (fun acc digit => B * acc + digit) 0 := by
  unfold radix
  rw [Nat.ofDigits_eq_foldr, List.foldr_reverse]
  simp only [Nat.cast_id, Nat.add_comm]

@[simp] theorem radix_nil (B : Nat) : radix B [] = 0 := rfl

theorem radix_append_word (B : Nat) (words : List Nat) (digit : Nat) :
    radix B (words ++ [digit]) = B * radix B words + digit := by
  simp only [radix_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem radix_lt_pow_length {B : Nat} (hB : 1 < B) (words : List Nat)
    (bounded : ∀ w ∈ words, w < B) : radix B words < B ^ words.length := by
  unfold radix
  simpa only [List.length_reverse] using
    Nat.ofDigits_lt_base_pow_length hB
      (fun w hw => bounded w (List.mem_reverse.mp hw))

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

noncomputable def capacityPolynomial (k s d : Nat) : Polynomial Nat :=
  (Polynomial.X + Polynomial.C (2^s + 2^d + 4)) ^ (1 + 9*k)

theorem capacityPolynomial_eval (n m k s d : Nat) :
    (capacityPolynomial k s d).eval (n + m) = capacity n m k s d := by
  simp [capacityPolynomial, capacity, base_eq, Nat.add_assoc]

end DFVSGames.Reduction.CanonicalAddress
end

section

namespace DFVSGames.Integration.NoiseTables

open BinaryLinear DFVSGames.Reduction.ActualSource

variable {s d : Nat}

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
end DFVSGames.Integration.NoiseTables
end

section

namespace DFVSGames.Integration.TableReduction

open BinaryLinear NoiseTables DFVSGames.Reduction.ActualSource
open DFVSGames.Reduction.ActualGame DFVSGames.Foundations.Target

variable {s d : Nat}

def tableEnumeration (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : NoiseEnumeration (T.gadget f hf) where
  indices := List.finRange T.vectors.length
  nodup := List.nodup_finRange _
  complete i := List.mem_finRange i

def tableSkeleton (T : Table s d) : SplitGadget s d :=
  T.gadget Prod.fst (fun _ _ => rfl)

def output (S : Source) (k : Nat) (T : Table s d) : Instance (2 ^ s) :=
  outputInstanceWithEnumeration S k (tableSkeleton T)
    (tableEnumeration T Prod.fst (fun _ _ => rfl))

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

end DFVSGames.Integration.TableReduction
end

section

namespace DFVSGames.Integration.VertexEmbedding

open DFVSGames.Foundations.Target
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

end DFVSGames.Integration.VertexEmbedding
end

section

namespace DFVSGames.Decoder.TableKeysAddressGame

open DFVSGames.Reduction
open ActualSource Foundations.Target
open Integration.VertexEmbedding

abbrev vertexCount (S : Source) (k s d : Nat) : Nat :=
  CanonicalAddress.capacity S.«variables» S.occurrences k s d

def vertexAddress (S : Source) (k s d : Nat) (v : TableKeysGame.Vertex S k s d) :
    Fin (vertexCount S k s d) := CanonicalAddress.bodyAddress v.val

theorem vertexAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (vertexAddress S k s d) := by
  intro v w h
  apply Subtype.ext
  exact CanonicalAddress.bodyAddress_injective h

def queryAddress (S : Source) (k s d : Nat) (q : TableKeysGame.Query S k s d) :
    Fin (vertexCount S k s d) :=
  CanonicalAddress.bodyAddress (ActualOrbit.body (TableKeysGame.canonical S k s d) q)

@[simp] theorem vertexAddress_query (S : Source) (k s d : Nat)
    (q : TableKeysGame.Query S k s d) :
    vertexAddress S k s d (TableKeysGame.vertex S k s d q) =
      queryAddress S k s d q := rfl

def explicitToAddress (S : Source) (k s d : Nat) :
    Fin (TableKeysGame.explicitVertexCount S k s d) → Fin (vertexCount S k s d) :=
  fun i => vertexAddress S k s d ((TableKeysGame.explicitVertexEncoding S k s d).symm i)

theorem explicitToAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (explicitToAddress S k s d) :=
  (vertexAddress_injective S k s d).comp
    (TableKeysGame.explicitVertexEncoding S k s d).symm.injective

@[simp] theorem explicitToAddress_apply (S : Source) (k s d : Nat)
    (v : TableKeysGame.Vertex S k s d) :
    explicitToAddress S k s d (TableKeysGame.explicitVertexEncoding S k s d v) =
      vertexAddress S k s d v := by
  simp only [explicitToAddress, Equiv.symm_apply_apply]

noncomputable def semanticToAddress (S : Source) (k s d : Nat) :
    Fin (TableKeysGame.vertexCount S k s d) → Fin (vertexCount S k s d) :=
  fun i => vertexAddress S k s d ((TableKeysGame.vertexEncoding S k s d).symm i)

theorem semanticToAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (semanticToAddress S k s d) :=
  (vertexAddress_injective S k s d).comp
    (TableKeysGame.vertexEncoding S k s d).symm.injective

@[simp] theorem semanticToAddress_apply (S : Source) (k s d : Nat)
    (v : TableKeysGame.Vertex S k s d) :
    semanticToAddress S k s d (TableKeysGame.vertexEncoding S k s d v) =
      vertexAddress S k s d v := by
  simp only [semanticToAddress, Equiv.symm_apply_apply]

def addressEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : TableKeysGame.Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := queryAddress S k s d (TableKeysGame.leftQuery S k g ω)
  target := queryAddress S k s d (TableKeysGame.rightQuery S k g ω)
  permutation := Encoding.translationTable
    (TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω))
    (TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω))

theorem addressEdge_eq_embed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : TableKeysGame.Outcome S k g) :
    addressEdge S k g ω = embedConstraint (explicitToAddress S k s d)
      (TableKeysGame.explicitEdge S k g ω) := by
  simp only [addressEdge, embedConstraint, TableKeysGame.explicitEdge,
    explicitToAddress_apply, vertexAddress_query]

theorem addressEdge_eq_semantic_embed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : TableKeysGame.Outcome S k g) :
    addressEdge S k g ω = embedConstraint (semanticToAddress S k s d)
      (TableKeysGame.edge S k g ω) := by
  simp only [addressEdge, embedConstraint, TableKeysGame.edge,
    semanticToAddress_apply, vertexAddress_query]

def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (en : NoiseEnumeration g) : Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (ActualGame.explicitOutcomes S k g en).map (addressEdge S k g)
  nonempty h := by
    have hempty := List.map_eq_nil_iff.mp h
    apply (TableKeysGame.outputInstanceWithEnumeration S k g en).nonempty
    change (ActualGame.explicitOutcomes S k g en).map (TableKeysGame.explicitEdge S k g) = []
    rw [hempty]
    rfl

theorem outputInstance_eq_embed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    outputInstance S k g en =
      embedInstance (TableKeysGame.outputInstanceWithEnumeration S k g en)
        (explicitToAddress S k s d) (explicitToAddress_injective S k s d) := by
  unfold outputInstance embedInstance TableKeysGame.outputInstanceWithEnumeration
  congr 1
  simp only [List.map_map, Function.comp_def, ← addressEdge_eq_embed]

@[simp] theorem outputInstance_length (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstance S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstance, List.length_map, ActualGame.explicitOutcomes,
    ActualEnumeration.length_indexedOutcomes]

theorem outputInstance_count (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    countSatisfied labeling (outputInstance S k g en).constraints =
      countSatisfied (labeling ∘ explicitToAddress S k s d)
        (TableKeysGame.outputInstanceWithEnumeration S k g en).constraints := by
  simpa only [outputInstance, TableKeysGame.outputInstanceWithEnumeration, List.map_map,
    Function.comp_def, ← addressEdge_eq_embed] using
    count_map (explicitToAddress S k s d)
      ((ActualGame.explicitOutcomes S k g en).map (TableKeysGame.explicitEdge S k g)) labeling

theorem completeAt_outputInstance_iff_explicit (error : RationalError)
    (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    CompleteAt error (outputInstance S k g en) ↔
      CompleteAt error (TableKeysGame.outputInstanceWithEnumeration S k g en) := by
  rw [outputInstance_eq_embed]
  exact completeAt_embed_iff error _ _ _ (by positivity)

theorem soundAt_outputInstance_iff_explicit (error : RationalError)
    (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    SoundAt error (outputInstance S k g en) ↔
      SoundAt error (TableKeysGame.outputInstanceWithEnumeration S k g en) := by
  rw [outputInstance_eq_embed]
  exact soundAt_embed_iff error _ _ _ (by positivity)

theorem completeAt_outputInstance_iff (error : RationalError)
    (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    CompleteAt error (outputInstance S k g en) ↔
      CompleteAt error (TableKeysGame.outputInstance S k g) :=
  (completeAt_outputInstance_iff_explicit error S k g en).trans
    (TableKeysGame.completeAt_outputInstanceWithEnumeration_iff error S k g en)

theorem soundAt_outputInstance_iff (error : RationalError)
    (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    SoundAt error (outputInstance S k g en) ↔
      SoundAt error (TableKeysGame.outputInstance S k g) :=
  (soundAt_outputInstance_iff_explicit error S k g en).trans
    (TableKeysGame.soundAt_outputInstanceWithEnumeration_iff error S k g en)

theorem outputInstance_translations (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm
      (outputInstance S k g en) := by
  intro constraint hconstraint
  obtain ⟨ω, _, rfl⟩ := List.mem_map.mp hconstraint
  refine ⟨TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω) +
    TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω), ?_⟩
  intro label
  have h := Encoding.translationTable_images
    (TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω))
    (TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω))
    ((Encoding.alphabetEquiv s).symm label)
  simpa only [addressEdge, Encoding.alphabetEquiv_apply_symm_apply,
    Encoding.alphabetEquiv_symm_apply_apply, add_assoc] using
    congrArg (Encoding.alphabetEquiv s).symm h

def tableOutput (S : Source) (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    Instance (2^s) :=
  outputInstance S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

theorem tableOutput_eq_with_witness (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    tableOutput S k T = outputInstance S k (T.gadget f hf)
      (Integration.TableReduction.tableEnumeration T f hf) := by
  rfl

theorem completeAt_tableOutput_iff (error : RationalError) (S : Source) (k : Nat)
    {s d : Nat} (T : Integration.NoiseTables.Table s d)
    (f : Ambient s d → Alphabet s) (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    CompleteAt error (tableOutput S k T) ↔
      CompleteAt error (TableKeysGame.outputInstance S k (T.gadget f hf)) := by
  rw [tableOutput_eq_with_witness S k T f hf]
  exact completeAt_outputInstance_iff error S k _ _

theorem soundAt_tableOutput_iff (error : RationalError) (S : Source) (k : Nat)
    {s d : Nat} (T : Integration.NoiseTables.Table s d)
    (f : Ambient s d → Alphabet s) (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    SoundAt error (tableOutput S k T) ↔
      SoundAt error (TableKeysGame.outputInstance S k (T.gadget f hf)) := by
  rw [tableOutput_eq_with_witness S k T f hf]
  exact soundAt_outputInstance_iff error S k _ _

theorem tableOutput_translations (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm
      (tableOutput S k T) := outputInstance_translations S k _ _

theorem vertexCount_eq_polynomial (S : Source) (k s d : Nat) :
    vertexCount S k s d = (CanonicalAddress.capacityPolynomial k s d).eval
      (S.«variables» + S.occurrences) := by
  rw [CanonicalAddress.capacityPolynomial_eval]

end DFVSGames.Decoder.TableKeysAddressGame
end

section

namespace DFVSGames.Decoder.MatrixGap

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Foundations.Target
open DFVSGames.Integration
open ActualSource

noncomputable section

theorem address_rate_eq_semantic_acceptance (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysAddressGame.vertexCount S k s d) → Fin (2 ^ s)) :
    GapSemantics.satisfactionRate (TableKeysAddressGame.outputInstance S k g en) labeling =
      TableKeysGame.acceptanceProbability S k g
        ((labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
          TableKeysGame.semanticToExplicitVertices S k s d) := by
  calc
    _ = GapSemantics.satisfactionRate
        (TableKeysGame.outputInstanceWithEnumeration S k g en)
        (labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) := by
      unfold GapSemantics.satisfactionRate
      exact congrArg₂ (fun a b : Nat => (a : ℚ) / b)
        (TableKeysAddressGame.outputInstance_count S k g en labeling)
        (by simp only [TableKeysAddressGame.outputInstance,
          TableKeysGame.outputInstanceWithEnumeration, List.length_map])
    _ = GapSemantics.satisfactionRate (TableKeysGame.outputInstance S k g)
        ((labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
          TableKeysGame.semanticToExplicitVertices S k s d) :=
      InstanceEquivalences.satisfactionRate_eq_of_rename_perm
        (TableKeysGame.outputInstance S k g)
        (TableKeysGame.outputInstanceWithEnumeration S k g en)
        (TableKeysGame.semanticToExplicitVertices S k s d)
        (TableKeysGame.explicitConstraints_perm_renamed S k g en) _
    _ = _ := (TableKeysGame.acceptanceProbability_eq_count S k g _).symm

theorem address_value_le_of_semantic_acceptance (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (h : ∀ labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s),
      TableKeysGame.acceptanceProbability S k (T.gadget f hf) labeling ≤ (99 : ℚ) / 100) :
    InstanceValue.value (TableKeysAddressGame.tableOutput S k T) ≤ (99 : ℝ) / 100 := by
  rw [TableKeysAddressGame.tableOutput_eq_with_witness S k T f hf]
  apply (InstanceValue.forall_rate_le_iff _ (by positivity) _).mp
  intro labeling
  change (Fin (TableKeysAddressGame.vertexCount S k s d) → Fin (2 ^ s)) at labeling
  have hrate : GapSemantics.satisfactionRate
      (TableKeysAddressGame.outputInstance S k (T.gadget f hf)
        (TableReduction.tableEnumeration T f hf)) labeling ≤ (99 : ℚ) / 100 := by
    rw [address_rate_eq_semantic_acceptance S k (T.gadget f hf)
      (TableReduction.tableEnumeration T f hf) labeling]
    exact h _
  have hreal := (Rat.cast_le (K := ℝ)
    (p := GapSemantics.satisfactionRate
      (TableKeysAddressGame.outputInstance S k (T.gadget f hf)
        (TableReduction.tableEnumeration T f hf)) labeling)
    (q := (99 : ℚ) / 100)).2 hrate
  simpa [GapSemantics.satisfactionRate] using hreal

end

end DFVSGames.Decoder.MatrixGap
end

section

namespace DFVSGames.Decoder.MatrixGap

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Foundations.Target
open DFVSGames.Integration
open ActualSource

noncomputable section

theorem semantic_acceptance_le_address_value (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) :
    (TableKeysGame.acceptanceProbability S k g labeling : ℝ) ≤
      InstanceValue.value (TableKeysAddressGame.outputInstance S k g en) := by
  let e := TableKeysGame.semanticToExplicitVertices S k s d
  let addressLabel := VertexEmbedding.extendLabeling
    (TableKeysAddressGame.explicitToAddress S k s d) (labeling ∘ e.symm)
      (⟨0, by positivity⟩ : Fin (2 ^ s))
  have hrestrict : addressLabel ∘ TableKeysAddressGame.explicitToAddress S k s d =
      labeling ∘ e.symm :=
    VertexEmbedding.extendLabeling_comp _
      (TableKeysAddressGame.explicitToAddress_injective S k s d) _ _
  have hpullback : (addressLabel ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
      TableKeysGame.semanticToExplicitVertices S k s d = labeling := by
    rw [hrestrict]
    funext v
    exact congrArg labeling (e.symm_apply_apply v)
  have hrate := address_rate_eq_semantic_acceptance S k g en addressLabel
  rw [hpullback] at hrate
  have hvalue := InstanceValue.satisfactionRate_le_value
    (TableKeysAddressGame.outputInstance S k g en) addressLabel
  rw [hrate] at hvalue
  exact hvalue

theorem address_value_ge_of_near_assignment (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (assignment : Fin S.«variables» → Bool) (ξ p : ℚ)
    (hfailure : S.failure assignment ≤ ξ)
    (hstable : (T.gadget f hf).stabilityError ≤ p) :
    (1 : ℝ) - ((k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      InstanceValue.value (TableKeysAddressGame.tableOutput S k T) := by
  let g := T.gadget f hf
  have hrat := TableKeysCompleteness.honest_acceptance_of_bounds S k g assignment
    ξ p ((k : ℚ) * ξ + p / 2) hfailure hstable (le_refl _)
  have hreal : (1 : ℝ) - ((k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      (TableKeysGame.acceptanceProbability S k g
        (TableKeysCompleteness.honestLabeling S k g assignment) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).2 hrat
    simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_add, Rat.cast_mul,
      Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] using h
  rw [TableKeysAddressGame.tableOutput_eq_with_witness S k T f hf]
  exact hreal.trans (semantic_acceptance_le_address_value S k g
    (TableReduction.tableEnumeration T f hf)
    (TableKeysCompleteness.honestLabeling S k g assignment))

end
end DFVSGames.Decoder.MatrixGap

end

section

namespace DFVSGames.Decoder.MatrixGap

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Foundations.Target
open DFVSGames.Foundations.Games
open DFVSGames.Integration
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

structure Parameters (p : ℚ) where
  k : Nat
  s : Nat
  d : Nat
  k_pos : 1 ≤ k
  s_pos : 1 ≤ s
  T : NoiseTables.Table s d
  f : Ambient s d → Alphabet s
  equivariant : ∀ x c, f (x + (c, 0)) = f x + c
  stability : (T.gadget f equivariant).stabilityError ≤ p
  sound : ∀ S : Source, S.DistinctNames →
    Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5 →
    InstanceValue.value (TableKeysAddressGame.tableOutput S k T) ≤ (99 : ℝ) / 100

theorem semantic_rate_le_address_value (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) :
    (GapSemantics.satisfactionRate (TableKeysGame.outputInstance S k g) labeling : ℝ) ≤
      InstanceValue.value (TableKeysAddressGame.outputInstance S k g en) := by
  have h := semantic_acceptance_le_address_value S k g en labeling
  rw [TableKeysGame.acceptanceProbability_eq_count] at h
  exact h

namespace Parameters

variable {p : ℚ}

def output (P : Parameters p) (S : Source) : Instance (2 ^ P.s) :=
  TableKeysAddressGame.tableOutput S P.k P.T

theorem completeness (P : Parameters p) (S : Source)
    (assignment : Fin S.«variables» → Bool) (ξ : ℚ)
    (hfailure : S.failure assignment ≤ ξ) :
    (1 : ℝ) - ((P.k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      InstanceValue.value (TableKeysAddressGame.tableOutput S P.k P.T) :=
  address_value_ge_of_near_assignment S P.k P.T P.f P.equivariant assignment
    ξ p hfailure P.stability

theorem output_translations (P : Parameters p) (S : Source) :
    TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv P.s).symm
      (P.output S) :=
  TableKeysAddressGame.tableOutput_translations S P.k P.T

end Parameters

end

end DFVSGames.Decoder.MatrixGap
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
