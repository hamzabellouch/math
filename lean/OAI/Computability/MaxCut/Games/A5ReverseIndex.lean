import Mathlib
import OAI.Computability.MaxCut.Games.A1Reduction

namespace OAI

namespace MaxCutGames.Appendix.A5ReverseIndex

open MaxCutGames.Integration.BinaryLinear
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]

/-- Earlier codomain constraints inside the final codomain constraint. -/
abbrev EarlierA (A' : Submodule F2 V) (i : ℕ) :=
  {A : Submodule F2 V // A ≤ A' ∧ Module.finrank F2 A = i}

/-- Earlier retained domains containing the final retained domain. -/
abbrev EarlierB (B' : Submodule F2 W) (j : ℕ) :=
  {B : Submodule F2 W // B' ≤ B ∧ Module.finrank F2 (W ⧸ B) = j}

/-- Natural frequency coordinates for an earlier pair inside a fixed final
pair. This is a change of domain and codomain separately. -/
def frequencyEquiv (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B) :
    (B' →ₗ[F2] (V ⧸ A')) ≃ₗ[F2]
      ((B'.comap B.subtype) →ₗ[F2] ((V ⧸ A) ⧸ A'.map A.mkQ)) :=
  LinearEquiv.arrowCongr
    (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩)
    (Submodule.quotientQuotientEquivQuotient A A' hA).symm

def relativeFrequency (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B) (Y : B' →ₗ[F2] (V ⧸ A')) :=
  frequencyEquiv A A' B' B hA hB Y

theorem relativeFrequency_rank (A A' : Submodule F2 V)
    (B' B : Submodule F2 W) (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) :
    Module.finrank F2 (relativeFrequency A A' B' B hA hB Y).range =
      Module.finrank F2 Y.range :=
  CoordinateTransport.finrank_range_transport
    (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩)
    (Submodule.quotientQuotientEquivQuotient A A' hA).symm Y

/-- The exact reverse fiber after the earlier dimensions are fixed. -/
abbrev Ancestor (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (i j : ℕ) :=
  Σ A : EarlierA A' i, Σ B : EarlierB B' j,
    AntecedentCount.Antecedent (B'.comap B.val.subtype) (A'.map A.val.mkQ)
      (relativeFrequency A.val A' B' B.val A.property.1 B.property.1 Y)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem relative_codomain_dimension (A A' : Submodule F2 V) (hA : A ≤ A') :
    Module.finrank F2 (A'.map A.mkQ) + Module.finrank F2 A =
      Module.finrank F2 A' := by
  have h₁ := (A'.map A.mkQ).finrank_quotient_add_finrank
  have h₂ := A.finrank_quotient_add_finrank
  have h₃ := A'.finrank_quotient_add_finrank
  have h₄ := (Submodule.quotientQuotientEquivQuotient A A' hA).finrank_eq
  omega

theorem relative_domain_codimension_le (B' B : Submodule F2 W) (hB : B' ≤ B) :
    Module.finrank F2 (B ⧸ B'.comap B.subtype) ≤
      Module.finrank F2 (W ⧸ B') := by
  have h₁ := (B'.comap B.subtype).finrank_quotient_add_finrank
  have h₂ := B'.finrank_quotient_add_finrank
  have h₃ := B.finrank_le
  have h₄ := (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).finrank_eq
  change Module.finrank F2 B' = Module.finrank F2 (B'.comap B.subtype) at h₄
  omega

/-- Each fixed earlier pair contributes at most two graph-parameter budgets. -/
theorem card_local_antecedent_le (A A' : Submodule F2 V)
    (B' B : Submodule F2 W) (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hAd : Module.finrank F2 A' ≤ d)
    (hBd : Module.finrank F2 (W ⧸ B') ≤ d) :
    Nat.card (AntecedentCount.Antecedent
      (B'.comap B.subtype) (A'.map A.mkQ)
      (relativeFrequency A A' B' B hA hB Y)) ≤ 2 ^ (2 * d * k) := by
  apply AntecedentCount.card_antecedent_le
  · simpa only [relativeFrequency_rank] using hY
  · have h := relative_codomain_dimension A A' hA
    omega
  · exact (relative_domain_codimension_le B' B hB).trans hBd

local instance quotientFinite {U : Type*} [AddCommGroup U] [Module F2 U]
    [Finite U] (P : Submodule F2 U) : Finite (U ⧸ P) :=
  Finite.of_surjective P.mkQ P.mkQ_surjective

local instance linearMapFinite {U Z : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup Z] [Module F2 Z] [Finite U] [Finite Z] :
    Finite (U →ₗ[F2] Z) :=
  Finite.of_injective (fun f : U →ₗ[F2] Z => (f : U → Z)) DFunLike.coe_injective

private theorem card_sigma_le_inline_A5ReverseIndex {I : Type*} [Fintype I]
    (fiber : I → Type*) [∀ i, Finite (fiber i)] (N : ℕ)
    (h : ∀ i, Nat.card (fiber i) ≤ N) :
    Nat.card (Σ i, fiber i) ≤ Nat.card I * N := by
  rw [Nat.card_sigma]
  calc
    (∑ i, Nat.card (fiber i)) ≤ ∑ _i : I, N := Finset.sum_le_sum (fun i _ => h i)
    _ = Nat.card I * N := by simp [Nat.card_eq_fintype_card]

variable [Finite V] [Finite W]
variable [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)]

/-- Sharp graph-based upper bound for the entire actual reverse fiber. -/
theorem card_ancestor_le (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d i j k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hA : Module.finrank F2 A' ≤ d)
    (hB : Module.finrank F2 (W ⧸ B') ≤ d) :
    Nat.card (Ancestor A' B' Y i j) ≤ 2 ^ (d * (i + j) + 2 * d * k) := by
  have hlocal (A : EarlierA A' i) (B : EarlierB B' j) :=
    card_local_antecedent_le A.val A' B' B.val A.property.1 B.property.1
      Y d k hY hA hB
  have hinner (A : EarlierA A' i) :
      Nat.card (Σ B : EarlierB B' j,
        AntecedentCount.Antecedent (B'.comap B.val.subtype) (A'.map A.val.mkQ)
          (relativeFrequency A.val A' B' B.val A.property.1 B.property.1 Y)) ≤
        Nat.card (EarlierB B' j) * 2 ^ (2 * d * k) :=
    card_sigma_le_inline_A5ReverseIndex _ _ (hlocal A)
  have htotal : Nat.card (Ancestor A' B' Y i j) ≤
      Nat.card (EarlierA A' i) * (Nat.card (EarlierB B' j) * 2 ^ (2 * d * k)) :=
    card_sigma_le_inline_A5ReverseIndex _ _ hinner
  calc
    Nat.card (Ancestor A' B' Y i j) ≤
        Nat.card (EarlierA A' i) * (Nat.card (EarlierB B' j) * 2 ^ (2 * d * k)) := htotal
    _ ≤ 2 ^ (d * i) * (2 ^ (d * j) * 2 ^ (2 * d * k)) :=
      Nat.mul_le_mul (BadConvolution.card_lower_rank_le A' d i hA)
        (Nat.mul_le_mul_right _ (BadConvolution.card_upper_codim_le B' d j hB))
    _ = 2 ^ (d * (i + j) + 2 * d * k) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring

theorem card_ancestor_le_source (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d i j k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hA : Module.finrank F2 A' ≤ d)
    (hB : Module.finrank F2 (W ⧸ B') ≤ d) (ht : i + j + k ≤ d) :
    Nat.card (Ancestor A' B' Y i j) ≤ 2 ^ (3 * (d * (i + j + k))) := by
  apply (card_ancestor_le A' B' Y d i j k hY hA hB).trans
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  have h := Induction.antecedent_exponent_budget d i j k (i + j + k) rfl ht
  calc
    d * (i + j) + 2 * d * k ≤ d * (i + j) + 2 * d * k + k * k :=
      Nat.le_add_right _ _
    _ ≤ 3 * (d * (i + j + k)) := by simpa only [Nat.mul_assoc] using h

end

end MaxCutGames.Appendix.A5ReverseIndex

/-! Pointwise identification of the natural frequency transport with the
relative frequency used by the actual reverse compression fibers. -/

noncomputable section
namespace MaxCutGames.Appendix.A5FrequencyTransport

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Appendix.LinearIdentities
open MaxCutGames.Appendix.NaturalTransport

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]

theorem quotient_relativeFrequency_apply
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) (b : B'.comap B.subtype) :
    Submodule.quotientQuotientEquivQuotient A A' hA
      (A5ReverseIndex.relativeFrequency A A' B' B hA hB Y b) =
    Y ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b) := by
  change Submodule.quotientQuotientEquivQuotient A A' hA
      ((Submodule.quotientQuotientEquivQuotient A A' hA).symm
        (Y ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b))) = _
  exact (Submodule.quotientQuotientEquivQuotient A A' hA).apply_symm_apply _

theorem quotient_compress_apply
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (X : B →ₗ[F2] (V ⧸ A)) (b : B'.comap B.subtype) :
    Submodule.quotientQuotientEquivQuotient A A' hA
      (compress X (A'.map A.mkQ) (B'.comap B.subtype) b) =
    Submodule.mapQ A A' LinearMap.id hA (X b.val) := rfl

/-- The relative compression equation follows from the concrete map to the
direct quotient on each element of the retained subspace. -/
theorem compression_eq_relativeFrequency_of_pointwise
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B)
    (X : B →ₗ[F2] (V ⧸ A)) (Y : B' →ₗ[F2] (V ⧸ A'))
    (hY : ∀ b : B', Submodule.mapQ A A' LinearMap.id hA
      (X ⟨b.val, hB b.property⟩) = Y b) :
    compress X (A'.map A.mkQ) (B'.comap B.subtype) =
      A5ReverseIndex.relativeFrequency A A' B' B hA hB Y := by
  ext b
  apply (Submodule.quotientQuotientEquivQuotient A A' hA).injective
  rw [quotient_compress_apply, quotient_relativeFrequency_apply]
  exact hY ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]
  [Finite V] [Finite W]

omit [FiniteDimensional F2 V] [Finite V] in
theorem quotientFactor_mapQ
    (A : Submodule F2 V) (C : Submodule F2 (V ⧸ A))
    (hA : A ≤ C.comap A.mkQ) (u : V ⧸ A) :
    quotientFactor A C
      (Submodule.mapQ A (C.comap A.mkQ) LinearMap.id hA u) = C.mkQ u := by
  obtain ⟨x, rfl⟩ := A.mkQ_surjective u
  change quotientFactor A C ((C.comap A.mkQ).mkQ x) = C.mkQ (A.mkQ x)
  exact quotientFactor_mkQ A C x

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
theorem dualFactor_quotient
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (Z : D →ₗ[F2] ((V ⧸ A) ⧸ C)) (b : D.map B.subtype) :
    quotientFactor A C (dualFactor A B C D Z b) =
      Z ((outputFactor B D).symm b) := by
  change quotientFactor A C ((quotientFactor A C).symm
    (Z ((outputFactor B D).symm b))) = _
  exact (quotientFactor A C).apply_symm_apply _

omit [FiniteDimensional F2 W] [Finite W] in
theorem outputFactor_symm_as_inclusion
    (B : Submodule F2 W) (D : Submodule F2 B)
    (hB : D.map B.subtype ≤ B) (b : D.map B.subtype) :
    (((outputFactor B D).symm b : D) : B) = ⟨b.val, hB b.property⟩ := by
  apply Subtype.ext
  have hh := outputFactor_val B D ((outputFactor B D).symm b)
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
/-- The naturally transported local compression belongs to the precise
relative-frequency fiber used in `A5ReverseIndex.Ancestor`. -/
theorem compression_eq_relativeFrequency_dualFactor
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (hA : A ≤ C.comap A.mkQ) (hB : D.map B.subtype ≤ B)
    (X : B →ₗ[F2] (V ⧸ A)) :
    compress X ((C.comap A.mkQ).map A.mkQ) ((D.map B.subtype).comap B.subtype) =
      A5ReverseIndex.relativeFrequency A (C.comap A.mkQ) (D.map B.subtype) B hA hB
        (dualFactor A B C D (compress X C D)) := by
  apply compression_eq_relativeFrequency_of_pointwise
  intro b
  apply (quotientFactor A C).injective
  rw [quotientFactor_mapQ, dualFactor_quotient]
  change C.mkQ (X ⟨b.val, hB b.property⟩) =
    C.mkQ (X (((outputFactor B D).symm b : D) : B))
  rw [outputFactor_symm_as_inclusion B D hB b]

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
/-- Package the actual naturally transported label into its counted
antecedent fiber, retaining the original map as the witness. -/
theorem isAntecedent_relativeFrequency_dualFactor
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (hA : A ≤ C.comap A.mkQ) (hB : D.map B.subtype ≤ B)
    (X : B →ₗ[F2] (V ⧸ A))
    (hdis : Disjoint X.range C) (hcover : D ⊔ X.ker = ⊤) :
    AntecedentCount.IsAntecedent ((D.map B.subtype).comap B.subtype)
      ((C.comap A.mkQ).map A.mkQ)
      (A5ReverseIndex.relativeFrequency A (C.comap A.mkQ) (D.map B.subtype) B hA hB
        (dualFactor A B C D (compress X C D))) X := by
  refine ⟨compression_eq_relativeFrequency_dualFactor A B C D hA hB X, ?_, ?_⟩
  · rw [Submodule.map_comap_eq_of_surjective A.mkQ_surjective C]
    exact hdis
  · rw [Submodule.comap_map_eq_of_injective (f := B.subtype) Subtype.val_injective D]
    exact hcover

end MaxCutGames.Appendix.A5FrequencyTransport

namespace MaxCutGames.Appendix.A5ForwardIndex

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier.MatrixRestrictions (order)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

abbrev Index (d : ℕ) :=
  Σ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
    A5Passage.Passage r.val.2.2 (d - A13Index.size r.val)

def descendant {d : ℕ} (a : Index (E := E) (F := F) d) :
    A13Index.Triple (E := E) (F := F) :=
  ⟨a.2.2.val.1.comap a.1.val.1.mkQ, a.2.2.val.2.map a.1.val.2.1.subtype,
    NaturalTransport.dualFactor a.1.val.1 a.1.val.2.1 a.2.2.val.1 a.2.2.val.2
      (LinearIdentities.compress a.1.val.2.2 a.2.2.val.1 a.2.2.val.2)⟩

def sourceI {d : ℕ} (a : Index (E := E) (F := F) d) : ℕ :=
  Module.finrank F2 a.1.val.1

def sourceJ {d : ℕ} (a : Index (E := E) (F := F) d) : ℕ :=
  Module.finrank F2 (F ⧸ a.1.val.2.1)

def targetRank (r : A13Index.Triple (E := E) (F := F)) : ℕ :=
  Module.finrank F2 r.2.2.range

omit [FiniteDimensional F2 E] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_rank {d : ℕ} (a : Index (E := E) (F := F) d) :
    targetRank (descendant a) = Module.finrank F2 a.1.val.2.2.range :=
  A5Passage.descendant_rank a.1.val.1 a.1.val.2.1 a.1.val.2.2 a.2

omit [FiniteDimensional F2 E] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem original_size {d : ℕ} (a : Index (E := E) (F := F) d) :
    sourceI a + sourceJ a + targetRank (descendant a) = A13Index.size a.1.val := by
  rw [descendant_rank]
  rfl

omit [FiniteDimensional F2 E] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem original_order_bounds {d : ℕ} (a : Index (E := E) (F := F) d) :
    1 ≤ sourceI a + sourceJ a + targetRank (descendant a) ∧
      sourceI a + sourceJ a + targetRank (descendant a) ≤ d := by
  rw [original_size]
  exact a.1.property

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_size_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    A13Index.size (descendant a) ≤ d :=
  A5Passage.effective_order_rank_le a.1.val.1 a.1.val.2.1 a.1.val.2.2 d
    a.1.property.2 a.2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierA_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    a.1.val.1 ≤ (descendant a).1 := by
  intro x hx
  change a.1.val.1.mkQ x ∈ a.2.2.val.1
  rw [show a.1.val.1.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hx]
  exact a.2.2.val.1.zero_mem

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierB_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    (descendant a).2.1 ≤ a.1.val.2.1 := by
  rintro x ⟨b, hb, rfl⟩
  exact b.property

abbrev Fiber (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :=
  {a : Index (E := E) (F := F) d //
    descendant a = r ∧ sourceI a = i ∧ sourceJ a = j}

/-- The encoder keeps the actual earlier pair and actual earlier map. -/
def encode (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ)
    (a : Fiber d r i j) : A5ReverseIndex.Ancestor r.1 r.2.1 r.2.2 i j := by
  rcases a with ⟨a, hr, hi, hj⟩
  cases hr
  refine ⟨⟨a.1.val.1, earlierA_le a, hi⟩,
    ⟨a.1.val.2.1, earlierB_le a, hj⟩, ⟨a.1.val.2.2, ?_⟩⟩
  exact A5FrequencyTransport.isAntecedent_relativeFrequency_dualFactor
    a.1.val.1 a.1.val.2.1 a.2.2.val.1 a.2.2.val.2
    (earlierA_le a) (earlierB_le a) a.1.val.2.2
    a.2.2.property.1.symm a.2.2.property.2.2.1

def earlierTriple {A' : Submodule F2 E} {B' : Submodule F2 F}
    {Y : B' →ₗ[F2] (E ⧸ A')} {i j : ℕ}
    (a : A5ReverseIndex.Ancestor A' B' Y i j) : A13Index.Triple (E := E) (F := F) :=
  ⟨a.1.val, a.2.1.val, a.2.2.val⟩

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierTriple_encode (d : ℕ)
    (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) (a : Fiber d r i j) :
    earlierTriple (encode d r i j a) = a.val.1.val := by
  rcases a with ⟨a, hr, hi, hj⟩
  cases hr
  rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Fixing the result and retained earlier data fixes both the complementary
pair and its outer hybrid index. No additional outer-index factor occurs. -/
theorem encode_injective (d : ℕ)
    (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :
    Function.Injective (encode d r i j) := by
  intro a b hab
  have hraw : a.val.1.val = b.val.1.val := by
    simpa only [earlierTriple_encode] using congrArg earlierTriple hab
  have hbase : a.val.1 = b.val.1 := Subtype.ext hraw
  have hresult : descendant a.val = descendant b.val := a.property.1.trans b.property.1.symm
  rcases a with ⟨⟨r₁, p⟩, ha⟩
  rcases b with ⟨⟨r₂, q⟩, hb⟩
  change r₁ = r₂ at hbase
  cases hbase
  have hA := congrArg (fun z : A13Index.Triple (E := E) (F := F) => z.1) hresult
  have hB := congrArg (fun z : A13Index.Triple (E := E) (F := F) => z.2.1) hresult
  change p.2.val.1.comap r₁.val.1.mkQ = q.2.val.1.comap r₁.val.1.mkQ at hA
  change p.2.val.2.map r₁.val.2.1.subtype = q.2.val.2.map r₁.val.2.1.subtype at hB
  have hpq : p = q := A5Passage.forget_injective r₁.val.2.2 _
    (Prod.ext (A5Passage.comap_mkQ_injective r₁.val.1 hA)
      (A5Passage.map_subtype_injective r₁.val.2.1 hB))
  cases hpq
  rfl

local instance indexFintype (d : ℕ) : Fintype (Index (E := E) (F := F) d) := by
  letI := A13Index.boundedPositiveTripleFintype (E := E) (F := F) d
  exact inferInstance

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Actual cardinality bound for every fiber used by the weighted reversal. -/
theorem card_fiber_le (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :
    Nat.card (Fiber d r i j) ≤ 2 ^ (3 * (d * (i + j + targetRank r))) := by
  by_cases hn : Nonempty (Fiber d r i j)
  · obtain ⟨a⟩ := hn
    have hsize : A13Index.size r ≤ d := by
      rw [← a.property.1]
      exact descendant_size_le a.val
    have hA : Module.finrank F2 r.1 ≤ d := by
      unfold A13Index.size order at hsize
      omega
    have hB : Module.finrank F2 (F ⧸ r.2.1) ≤ d := by
      unfold A13Index.size order at hsize
      omega
    have ht : i + j + targetRank r ≤ d := by
      have h := (original_order_bounds a.val).2
      rwa [a.property.1, a.property.2.1, a.property.2.2] at h
    have hcount := A5ReverseIndex.card_ancestor_le_source r.1 r.2.1 r.2.2
      d i j (targetRank r) (le_refl _) hA hB ht
    exact (Nat.card_le_card_of_injective (encode d r i j)
      (encode_injective d r i j)).trans hcount
  · have : IsEmpty (Fiber d r i j) := ⟨fun a => hn ⟨a⟩⟩
    simp

end MaxCutGames.Appendix.A5ForwardIndex

open scoped BigOperators

namespace MaxCutGames.Appendix.A5WeightedReindex

attribute [local instance] Classical.propDecidable

theorem exponent_weight_le (d t k : ℕ) (ht : t ≤ d) (hk : k ≤ t) :
    (2 : ℝ) ^ (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) ≤
      (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (63 * d * t + 4 * d * k) := by
  have he : (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) +
      (63 * d * t + 4 * d * k) ≤ 100 * d * d := by
    simpa only [pow_two, Nat.mul_assoc, Nat.add_assoc] using
      Induction.induction_exponent_budget d t k ht hk
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he
  rw [pow_add] at hp
  have hn : (2 : ℝ) ^ (63 * d * t + 4 * d * k) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hm := mul_le_mul_of_nonneg_right hp
    (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (63 * d * t + 4 * d * k)))
  rw [mul_assoc, mul_inv_cancel₀ hn, mul_one] at hm
  simpa only [inv_pow] using hm

theorem counted_weight_le (d t k c : ℕ) (ht : t ≤ d) (hk : k ≤ t)
    (hc : c ≤ 2 ^ (3 * d * t)) :
    (c : ℝ) * (2 : ℝ) ^ (100 * (d - t) ^ 2 + 24 * d * t + 6 * d * k) ≤
      (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (63 * d * t + 4 * d * k) := by
  have hc' : (c : ℝ) ≤ (2 : ℝ) ^ (3 * d * t) := by exact_mod_cast hc
  calc
    _ ≤ (2 : ℝ) ^ (3 * d * t) *
        (2 : ℝ) ^ (100 * (d - t) ^ 2 + 24 * d * t + 6 * d * k) :=
      mul_le_mul_of_nonneg_right hc' (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) := by
      rw [← pow_add]
      congr 1
      ring
    _ ≤ _ := exponent_weight_le d t k ht hk

variable {α β : Type*} [Fintype α] [Fintype β]

def fiber (result : α → β) (i j : α → ℕ) (b : β) (r s : ℕ) : Finset α :=
  Finset.univ.filter (fun a => result a = b ∧ i a = r ∧ j a = s)

/-- Exact finite grouping by the actual result and both dimension indices. -/
theorem sum_grouped (d : ℕ) (result : α → β) (i j : α → ℕ)
    (hbound : ∀ a, i a ≤ d ∧ j a ≤ d) (C : β → ℕ → ℕ → ℝ) :
    (∑ a, C (result a) (i a) (j a)) =
      ∑ b, ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
        ((fiber result i j b r s).card : ℝ) * C b r s := by
  classical
  let key : α → β × ℕ × ℕ := fun a => (result a, i a, j a)
  let target : Finset (β × ℕ × ℕ) :=
    Finset.univ ×ˢ (Finset.range (d + 1) ×ˢ Finset.range (d + 1))
  let G : β × ℕ × ℕ → ℝ := fun p => C p.1 p.2.1 p.2.2
  have hmap : ∀ a ∈ (Finset.univ : Finset α), key a ∈ target := by
    intro a _
    simp only [target, key, Finset.mem_product, Finset.mem_univ,
      Finset.mem_range, true_and]
    exact ⟨Nat.lt_succ_iff.mpr (hbound a).1, Nat.lt_succ_iff.mpr (hbound a).2⟩
  have h := Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := target)
    (g := key) hmap G
  simpa only [target, Finset.sum_product, G, key, Prod.mk.injEq,
    Finset.sum_const, nsmul_eq_mul, fiber] using h.symm

theorem weighted_reindex (d : ℕ) (hd : 1 ≤ d)
    (result : α → β) (i j : α → ℕ) (k : β → ℕ) (w : β → ℝ)
    (hw : ∀ b, 0 ≤ w b)
    (horder : ∀ a, 1 ≤ i a + j a + k (result a) ∧ i a + j a + k (result a) ≤ d)
    (hcard : ∀ b r s,
      Nat.card {a : α // result a = b ∧ i a = r ∧ j a = s} ≤
        2 ^ (3 * d * (r + s + k b))) :
    (∑ a, (2 : ℝ) ^ (100 * (d - (i a + j a + k (result a))) ^ 2 +
        24 * d * (i a + j a + k (result a)) + 6 * d * k (result a)) * w (result a)) ≤
      (2 : ℝ) ^ (100 * d * d) *
        ∑ b, ((2 : ℝ)⁻¹) ^ (31 * d * (k b + 1) + 4 * d * k b) * w b := by
  classical
  let C : β → ℕ → ℕ → ℝ := fun b r s =>
    (2 : ℝ) ^ (100 * (d - (r + s + k b)) ^ 2 +
      24 * d * (r + s + k b) + 6 * d * k b) * w b
  let envelope : β → ℝ := fun b =>
    (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (4 * d * k b) * w b
  have henvelope : ∀ b, 0 ≤ envelope b := by
    intro b
    exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
      (pow_nonneg (by norm_num) _)) (hw b)
  have hbound : ∀ a, i a ≤ d ∧ j a ≤ d := by
    intro a
    have h := (horder a).2
    omega
  have hfiber : ∀ b r s,
      ((fiber result i j b r s).card : ℝ) * C b r s ≤
        envelope b * (if 1 ≤ r + s + k b then
          ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
    intro b r s
    by_cases hne : (fiber result i j b r s).Nonempty
    · obtain ⟨a, ha⟩ := hne
      rcases Finset.mem_filter.mp ha with ⟨_, hr, hi, hj⟩
      have ht := horder a
      rw [hr, hi, hj] at ht
      have hc : (fiber result i j b r s).card ≤ 2 ^ (3 * d * (r + s + k b)) := by
        simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, fiber] using hcard b r s
      have hweight := counted_weight_le d (r + s + k b) (k b)
        (fiber result i j b r s).card ht.2 (by omega) hc
      rw [ite_eq_left ht.1]
      calc
        _ = (((fiber result i j b r s).card : ℝ) *
            (2 : ℝ) ^ (100 * (d - (r + s + k b)) ^ 2 +
              24 * d * (r + s + k b) + 6 * d * k b)) * w b := by
          dsimp only [C]
          ring
        _ ≤ ((2 : ℝ) ^ (100 * d * d) *
            ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b) + 4 * d * k b)) * w b :=
          mul_le_mul_of_nonneg_right hweight (hw b)
        _ = envelope b * ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) := by
          dsimp only [envelope]
          rw [pow_add]
          ring
    · have hz : (fiber result i j b r s).card = 0 := by
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
      rw [hz, Nat.cast_zero, zero_mul]
      apply mul_nonneg (henvelope b)
      split_ifs <;> positivity
  change (∑ a, C (result a) (i a) (j a)) ≤ _
  rw [sum_grouped d result i j hbound C]
  calc
    _ ≤ ∑ b, ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
        envelope b * (if 1 ≤ r + s + k b then
          ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro r _
      exact Finset.sum_le_sum (fun s _ => hfiber b r s)
    _ = ∑ b, envelope b *
        (∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
          if 1 ≤ r + s + k b then ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ b, envelope b * ((2 : ℝ)⁻¹) ^ (31 * d * (k b + 1)) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (A5Scalar.a16_original_range d (k b) hd) (henvelope b)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [envelope]
      rw [pow_add]
      ring

end MaxCutGames.Appendix.A5WeightedReindex
end

/-!
# The actual weighted reversal in Appendix A.5

The forward index records an original positive triple and an actual A.5
passage. Its checked reverse-fiber bound permits finite weighted grouping.
The resulting weights are the moments of the actual transported derivatives.
No degree hypothesis or analytic induction hypothesis is used here.
-/

noncomputable section
namespace MaxCutGames.Appendix.A5ReverseSum

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier.MatrixRestrictions (order)
open Derivatives
open A5ForwardIndex

attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def actualMoment (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : ℝ :=
  𝔼 T, (𝔼 N, mapDerivative r.2.2 (hybridDerivative r.1 r.2.1 T f) N ^ 2) ^ 2

def targetWeight (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : ℝ :=
  if order r.1 r.2.1 ≤ d then actualMoment f r else 0

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem targetWeight_nonneg (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : 0 ≤ targetWeight d f r := by
  unfold targetWeight
  split_ifs
  · exact Finset.expect_nonneg fun _ _ => sq_nonneg _
  · exact le_refl _

theorem targetWeight_descendant (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (a : Index (E := E) (F := F) d) :
    targetWeight d f (descendant a) = actualMoment f (descendant a) := by
  have h := descendant_size_le a
  have ho : order (descendant a).1 (descendant a).2.1 ≤ d := by
    unfold A13Index.size at h
    omega
  exact ite_eq_left ho

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- The target cutoff is exactly the actual finite hybrid index. -/
theorem sum_triples_cutoff (d : ℕ)
    (H : ∀ (A : Submodule F2 E) (B : Submodule F2 F),
      (B →ₗ[F2] (E ⧸ A)) → ℝ) :
    (∑ r : A13Index.Triple (E := E) (F := F),
      if order r.1 r.2.1 ≤ d then H r.1 r.2.1 r.2.2 else 0) =
    ∑ s : HybridIndex (E := E) (F := F) d,
      ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1), H s.val.1 s.val.2 Y := by
  classical
  let G : Submodule F2 E × Submodule F2 F → ℝ :=
    fun p => ∑ Y : p.2 →ₗ[F2] (E ⧸ p.1), H p.1 p.2 Y
  have hh : (∑ s : HybridIndex (E := E) (F := F) d, G s.val) =
      ∑ p : Submodule F2 E × Submodule F2 F,
        if order p.1 p.2 ≤ d then G p else 0 := by
    calc
      _ = ∑ p ∈ Finset.univ.filter (fun p : Submodule F2 E × Submodule F2 F =>
            order p.1 p.2 ≤ d), G p := by
        exact (Finset.sum_subtype _ (by simp) G).symm
      _ = _ := Finset.sum_filter _ _
  change _ = ∑ s : HybridIndex (E := E) (F := F) d, G s.val
  rw [hh, Fintype.sum_prod_type]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro A _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : order A B ≤ d
  · simp only [h, ite_true, G]
  · simp only [h, ite_false, Finset.sum_const_zero]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem target_sum_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ r : A13Index.Triple (E := E) (F := F),
      ((2 : ℝ)⁻¹) ^ (31 * d * (targetRank r + 1) + 4 * d * targetRank r) *
        targetWeight d f r) =
    ∑ s : HybridIndex (E := E) (F := F) d,
      𝔼 T, ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1),
        ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
          4 * d * Module.finrank F2 Y.range) *
          (𝔼 N, mapDerivative Y (hybridDerivative s.val.1 s.val.2 T f) N ^ 2) ^ 2 := by
  let H : ∀ (A : Submodule F2 E) (B : Submodule F2 F),
      (B →ₗ[F2] (E ⧸ A)) → ℝ := fun A B Y =>
    ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
      4 * d * Module.finrank F2 Y.range) * actualMoment f ⟨A, B, Y⟩
  calc
    _ = ∑ r : A13Index.Triple (E := E) (F := F),
        if order r.1 r.2.1 ≤ d then H r.1 r.2.1 r.2.2 else 0 := by
      apply Finset.sum_congr rfl
      rintro ⟨A, B, Y⟩ _
      simp only [targetWeight, targetRank, H, mul_ite, mul_zero]
    _ = ∑ s : HybridIndex (E := E) (F := F) d,
        ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1), H s.val.1 s.val.2 Y :=
      sum_triples_cutoff d H
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  rw [← Finset.mul_expect]
  rfl

theorem source_summand_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (a : Index (E := E) (F := F) d) :
    (2 : ℝ) ^ (100 * (d - (sourceI a + sourceJ a + targetRank (descendant a))) ^ 2 +
      24 * d * (sourceI a + sourceJ a + targetRank (descendant a)) +
      6 * d * targetRank (descendant a)) * targetWeight d f (descendant a) =
    (2 : ℝ) ^ (100 * (d - A13Index.size a.1.val) ^ 2 +
      24 * d * A13Index.size a.1.val + 6 * d * Module.finrank F2 a.1.val.2.2.range) *
        actualMoment f (descendant a) := by
  rw [original_size, descendant_rank, targetWeight_descendant]

theorem source_sum_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ a : Index (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - (sourceI a + sourceJ a + targetRank (descendant a))) ^ 2 +
        24 * d * (sourceI a + sourceJ a + targetRank (descendant a)) +
        6 * d * targetRank (descendant a)) * targetWeight d f (descendant a)) =
    ∑ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - A13Index.size r.val) ^ 2 + 24 * d * A13Index.size r.val +
        6 * d * Module.finrank F2 r.val.2.2.range) *
        A5Passage.descendantSum r.val.1 r.val.2.1 r.val.2.2
          (d - A13Index.size r.val) f := by
  simp_rw [source_summand_eq]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [A5Passage.descendantSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rfl

/-- The weighted sum of actual A.5 descendants is bounded by damped actual
map-derivative moments over all hybrid restrictions of order at most `d`. -/
theorem weighted_descendantSum_le (d : ℕ) (hd : 1 ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) :
    (∑ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - A13Index.size r.val) ^ 2 + 24 * d * A13Index.size r.val +
        6 * d * Module.finrank F2 r.val.2.2.range) *
        A5Passage.descendantSum r.val.1 r.val.2.1 r.val.2.2
          (d - A13Index.size r.val) f) ≤
    (2 : ℝ) ^ (100 * d * d) *
      ∑ s : HybridIndex (E := E) (F := F) d,
        𝔼 T, ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1),
          ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
            4 * d * Module.finrank F2 Y.range) *
            (𝔼 N, mapDerivative Y (hybridDerivative s.val.1 s.val.2 T f) N ^ 2) ^ 2 := by
  have h := A5WeightedReindex.weighted_reindex d hd
    (descendant (E := E) (F := F) (d := d)) sourceI sourceJ targetRank
    (targetWeight d f) (targetWeight_nonneg d f) original_order_bounds
    (fun r i j => by simpa only [Nat.mul_assoc] using card_fiber_le d r i j)
  rwa [source_sum_eq, target_sum_eq] at h

end MaxCutGames.Appendix.A5ReverseSum
end

end OAI
