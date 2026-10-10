import Mathlib
import OAI.Computability.MaxCut.Encoding.BinaryCoordinates

namespace OAI

namespace MaxCutGames.Fourier.Deletion

universe u v w

/-- The number of entries on which a Boolean function is true. -/
def trueCount {Ω : Type u} (f : Ω → Bool) : List Ω → Nat
  | [] => 0
  | x :: xs => (if f x then 1 else 0) + trueCount f xs

theorem trueCount_mono {Ω : Type u} (f g : Ω → Bool)
    (h : ∀ x, f x = true → g x = true) (xs : List Ω) :
    trueCount f xs ≤ trueCount g xs := by
  induction xs with
  | nil => simp [trueCount]
  | cons x xs ih =>
    have hx : (if f x then 1 else 0 : Nat) ≤ (if g x then 1 else 0) := by
      cases hf : f x with
      | false => simp
      | true => simp [h x hf]
    exact Nat.add_le_add hx ih

theorem trueCount_eq_zero {Ω : Type u} (f : Ω → Bool) (xs : List Ω)
    (h : ∀ x, x ∈ xs → f x = false) : trueCount f xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : f x = false := h x (by simp)
    have ht : trueCount f xs = 0 := ih (fun y hy => h y (by simp [hy]))
    simp [trueCount, hx, ht]

/-- A family of admissible restrictions and their containing rows. Rows may
overlap, and there is no requirement that different restrictions share the
same ancillary data. -/
structure RestrictionSystem (Ω : Type u) (Row : Type v) (Witness : Type w) where
  samples : Witness → List Ω
  samples_nonempty : ∀ t, samples t ≠ []
  admissible : Witness → Prop
  row : Row → Ω → Prop
  containingRow : Witness → Row
  contained : ∀ t x, x ∈ samples t → row (containingRow t) x

variable {Ω : Type u} {Row : Type v} {Witness : Type w}

/-- Strict density above the rational threshold `p / q` when `q > 0`. -/
def Dense (S : RestrictionSystem Ω Row Witness) (H : Ω → Bool)
    (p q : Nat) (t : Witness) : Prop :=
  p * (S.samples t).length < q * trueCount H (S.samples t)

/-- A row is bad when it contains a dense admissible restriction. -/
def BadRow (S : RestrictionSystem Ω Row Witness) (H : Ω → Bool)
    (p q : Nat) (r : Row) : Prop :=
  ∃ t, S.admissible t ∧ S.containingRow t = r ∧ Dense S H p q t

/-- All points of every bad row are removed. -/
def DeletedSet (S : RestrictionSystem Ω Row Witness) (H : Ω → Bool)
    (p q : Nat) (x : Ω) : Prop :=
  ∃ r, BadRow S H p q r ∧ S.row r x

/-- The Boolean remainder after deleting the union of bad rows. -/
noncomputable def remainder (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (x : Ω) : Bool := by
  classical
  exact if DeletedSet S H p q x then false else H x

/-- The Boolean part removed from the original function. -/
noncomputable def removed (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (x : Ω) : Bool := by
  classical
  exact if DeletedSet S H p q x then H x else false

theorem remainder_le_original (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (x : Ω)
    (h : remainder S H p q x = true) : H x = true := by
  classical
  unfold remainder at h
  split at h
  · contradiction
  · exact h

/-- A dense restriction makes its whole row bad, including points that were
not sampled by the restriction. -/
theorem dense_deletes_whole_row (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (t : Witness)
    (ha : S.admissible t) (hd : Dense S H p q t)
    (x : Ω) (hx : S.row (S.containingRow t) x) :
    remainder S H p q x = false := by
  classical
  have hdel : DeletedSet S H p q x :=
    ⟨S.containingRow t, ⟨t, ha, rfl, hd⟩, hx⟩
  simp [remainder, hdel]

theorem dense_restriction_remainder_zero
    (S : RestrictionSystem Ω Row Witness) (H : Ω → Bool) (p q : Nat)
    (t : Witness) (ha : S.admissible t) (hd : Dense S H p q t) :
    trueCount (remainder S H p q) (S.samples t) = 0 := by
  apply trueCount_eq_zero
  intro x hx
  exact dense_deletes_whole_row S H p q t ha hd x (S.contained t x hx)

/-- Rational restriction globality of a Boolean function. -/
def RestrictionGlobal (S : RestrictionSystem Ω Row Witness) (G : Ω → Bool)
    (p q : Nat) : Prop :=
  ∀ t, S.admissible t → q * trueCount G (S.samples t) ≤ p * (S.samples t).length

/-- Whole-row deletion establishes every admissible restriction bound. This
is the first assertion of Lemma 5.2, before applying Fourier estimates. -/
theorem remainder_restrictionGlobal
    (S : RestrictionSystem Ω Row Witness) (H : Ω → Bool) (p q : Nat) :
    RestrictionGlobal S (remainder S H p q) p q := by
  classical
  intro t ha
  by_cases hd : Dense S H p q t
  · rw [dense_restriction_remainder_zero S H p q t ha hd]
    simp
  · have hn : q * trueCount H (S.samples t) ≤ p * (S.samples t).length :=
      Nat.le_of_not_gt hd
    exact Nat.le_trans
      (Nat.mul_le_mul_left q
        (trueCount_mono (remainder S H p q) H
          (remainder_le_original S H p q) (S.samples t))) hn

/-- Retained and removed contributions form a disjoint Boolean partition. -/
theorem boolean_partition (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (x : Ω) :
    (remainder S H p q x || removed S H p q x) = H x ∧
    (remainder S H p q x && removed S H p q x) = false := by
  classical
  by_cases hd : DeletedSet S H p q x <;> simp [remainder, removed, hd]

/-- Exact conservation of retained and removed mass on any sampling list. -/
theorem trueCount_partition (S : RestrictionSystem Ω Row Witness)
    (H : Ω → Bool) (p q : Nat) (xs : List Ω) :
    trueCount H xs = trueCount (remainder S H p q) xs +
      trueCount (removed S H p q) xs := by
  classical
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hd : DeletedSet S H p q x
    · simp only [trueCount, remainder, removed, ite_eq_left hd, Bool.false_eq_true,
        ↓reduceIte, Nat.zero_add]
      omega
    · simp only [trueCount, remainder, removed, ite_eq_right hd, Bool.false_eq_true,
        ↓reduceIte, Nat.zero_add]
      omega

end MaxCutGames.Fourier.Deletion

namespace MaxCutGames.Fourier.MatrixRestrictions

open MaxCutGames.Integration.BinaryLinear
open scoped BigOperators

abbrev Ambient (m n : Nat) := Vector m →ₗ[F2] Vector n
variable {E C : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C]

abbrev Parameter (W : Submodule F2 E)
    (C' : Submodule F2 C) := (E ⧸ W) →ₗ[F2] C'

/-- The canonical inclusion of `L(E/W,C')` into `L(E,C)`. -/
def embed (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') : (E →ₗ[F2] C) :=
  C'.subtype.comp (A.comp W.mkQ)

@[simp] theorem embed_apply (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') (x : E) :
    embed W C' A x = (A (W.mkQ x) : C) := rfl

theorem embed_injective (W : Submodule F2 E)
    (C' : Submodule F2 C) : Function.Injective (embed W C') := by
  intro A B h
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := W.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : (E →ₗ[F2] C) => f y) h

theorem embed_vanishes (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') :
    W ≤ LinearMap.ker (embed W C' A) := by
  intro x hx
  change (A (W.mkQ x) : C) = 0
  have hzero : W.mkQ x = 0 := by simpa using hx
  simp [hzero]

theorem embed_range (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') :
    LinearMap.range (embed W C' A) ≤ C' := by
  rintro x ⟨y, rfl⟩
  exact (A (W.mkQ y)).property

/-- These are exactly the maps vanishing on `W` with image in `C'`. -/
theorem exists_embed_iff (W : Submodule F2 E)
    (C' : Submodule F2 C) (B : (E →ₗ[F2] C)) :
    (∃ A : Parameter W C', embed W C' A = B) ↔
      W ≤ LinearMap.ker B ∧ LinearMap.range B ≤ C' := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨embed_vanishes W C' A, embed_range W C' A⟩
  · rintro ⟨hW, hC⟩
    let B' : E →ₗ[F2] C' :=
      B.codRestrict C' (fun x => hC ⟨x, rfl⟩)
    have hker : W ≤ LinearMap.ker B' := by
      intro x hx
      apply Subtype.ext
      exact hW hx
    refine ⟨W.liftQ B' hker, ?_⟩
    apply LinearMap.ext
    intro x
    rfl

/-- Quotient rows are unchanged by every admissible restriction perturbation. -/
theorem quotient_embed_zero (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') :
    C'.mkQ.comp (embed W C' A) = 0 := by
  apply LinearMap.ext
  intro x
  change C'.mkQ (embed W C' A x) = 0
  exact (Submodule.Quotient.mk_eq_zero C').mpr (A (W.mkQ x)).property

def translate (W : Submodule F2 E)
    (C' : Submodule F2 C) (X : (E →ₗ[F2] C))
    (A : Parameter W C') : (E →ₗ[F2] C) := X + embed W C' A

theorem translate_injective (W : Submodule F2 E)
    (C' : Submodule F2 C) (X : (E →ₗ[F2] C)) :
    Function.Injective (translate W C' X) := by
  intro A B h
  exact embed_injective W C' (add_left_cancel h)

theorem quotient_translate (W : Submodule F2 E)
    (C' : Submodule F2 C) (X : (E →ₗ[F2] C))
    (A : Parameter W C') :
    C'.mkQ.comp (translate W C' X A) = C'.mkQ.comp X := by
  apply LinearMap.ext
  intro x
  change C'.mkQ (X x + embed W C' A x) = C'.mkQ (X x)
  rw [map_add]
  have h : C'.mkQ (embed W C' A x) = 0 :=
    congrArg (fun f : E →ₗ[F2] (C ⧸ C') => f x)
    (quotient_embed_zero W C' A)
  rw [h, add_zero]

/-- The perturbation inclusion is itself a binary linear map. -/
def embedding (W : Submodule F2 E) (C' : Submodule F2 C) :
    Parameter W C' →ₗ[F2] (E →ₗ[F2] C) where
  toFun := embed W C'
  map_add' A B := by
    apply LinearMap.ext
    intro x
    rfl
  map_smul' a A := by
    apply LinearMap.ext
    intro x
    rfl

noncomputable def order (W : Submodule F2 E) (C' : Submodule F2 C) : Nat :=
  Module.finrank F2 W + Module.finrank F2 (C ⧸ C')

/-- Restrict a real observable to the actual affine quotient-map domain. -/
def restrict (f : (E →ₗ[F2] C) → ℝ) (W : Submodule F2 E)
    (C' : Submodule F2 C) (X : E →ₗ[F2] C) : Parameter W C' → ℝ :=
  fun A => f (translate W C' X A)

noncomputable instance parameterFintype [Finite E] [Finite C]
    (W : Submodule F2 E) (C' : Submodule F2 C) : Fintype (Parameter W C') := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype C' := Fintype.ofFinite C'
  exact Fintype.ofInjective (fun A : Parameter W C' => (A : (E ⧸ W) → C'))
    DFunLike.coe_injective

/-- Every actual restriction domain has at least its zero map. -/
theorem parameter_card_pos [Finite E] [Finite C]
    (W : Submodule F2 E) (C' : Submodule F2 C) :
    0 < Fintype.card (Parameter W C') := Fintype.card_pos

/-- An actual row includes its target subspace as part of its index. -/
structure Row (E C : Type*) [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C] where
  target : Submodule F2 C
  value : E →ₗ[F2] (C ⧸ target)

structure Witness (E C : Type*) [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C] where
  vanishing : Submodule F2 E
  target : Submodule F2 C
  base : E →ₗ[F2] C

noncomputable def samples [Finite E] [Finite C] (t : Witness E C) :
    List (E →ₗ[F2] C) :=
  (Finset.univ : Finset (Parameter t.vanishing t.target)).toList.map
    (translate t.vanishing t.target t.base)

theorem samples_length [Finite E] [Finite C] (t : Witness E C) :
    (samples t).length = Fintype.card (Parameter t.vanishing t.target) := by
  simp [samples]

theorem samples_nonempty [Finite E] [Finite C] (t : Witness E C) :
    samples t ≠ [] := by
  intro h
  have hp := parameter_card_pos t.vanishing t.target
  rw [← samples_length t, h] at hp
  exact Nat.not_lt_zero 0 hp

theorem mem_samples_iff [Finite E] [Finite C] (t : Witness E C)
    (X : E →ₗ[F2] C) : X ∈ samples t ↔
      ∃ A : Parameter t.vanishing t.target,
        translate t.vanishing t.target t.base A = X := by
  classical
  simp [samples]

theorem samples_nodup [Finite E] [Finite C] (t : Witness E C) :
    (samples t).Nodup := by
  classical
  exact List.Nodup.map (translate_injective t.vanishing t.target t.base)
    (Finset.nodup_toList _)

/-- Actual affine matrix restrictions instantiate the generic deletion interface. -/
noncomputable def system [Finite E] [Finite C] (r : Nat) :
    Deletion.RestrictionSystem (E →ₗ[F2] C) (Row E C) (Witness E C) where
  samples := samples
  samples_nonempty := samples_nonempty
  admissible t := order t.vanishing t.target ≤ r
  row t X := t.target.mkQ.comp X = t.value
  containingRow t := ⟨t.target, t.target.mkQ.comp t.base⟩
  contained t X hX := by
    obtain ⟨A, rfl⟩ := (mem_samples_iff t X).mp hX
    exact quotient_translate t.vanishing t.target t.base A

/-- Every actual affine restriction of order at most `r` obeys the residual
count bound after whole-row deletion. No linear containment assumption remains. -/
theorem remainder_restriction_count [Finite E] [Finite C]
    (H : (E →ₗ[F2] C) → Bool) (r p q : Nat) (t : Witness E C)
    (ht : order t.vanishing t.target ≤ r) :
    q * Deletion.trueCount (Deletion.remainder (system r) H p q) (samples t) ≤
      p * Fintype.card (Parameter t.vanishing t.target) := by
  rw [← samples_length t]
  exact Deletion.remainder_restrictionGlobal (system r) H p q t ht

private theorem trueCount_eq_countP_inline_MatrixRestrictions {α : Type*} (H : α → Bool) (xs : List α) :
    Deletion.trueCount H xs = xs.countP H := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : H x <;> simp [Deletion.trueCount, ih, hx, Nat.add_comm]

/-- Exact numerator for uniform sampling of the actual affine restriction. -/
theorem samples_trueCount [Finite E] [Finite C] (H : (E →ₗ[F2] C) → Bool)
    (t : Witness E C) :
    Deletion.trueCount H (samples t) =
      (Finset.univ.filter fun A : Parameter t.vanishing t.target =>
        H (translate t.vanishing t.target t.base A) = true).card := by
  classical
  rw [trueCount_eq_countP_inline_MatrixRestrictions]
  simp only [samples, List.countP_map]
  symm
  simpa [Function.comp_def] using (Finset.nodup_toList
    (Finset.univ : Finset (Parameter t.vanishing t.target))).card_eq_countP
      (P := fun A => H (translate t.vanishing t.target t.base A) = true)

noncomputable def density [Finite E] [Finite C]
    (H : (E →ₗ[F2] C) → Bool) (t : Witness E C) : ℝ :=
  𝔼 A : Parameter t.vanishing t.target,
    if H (translate t.vanishing t.target t.base A) then (1 : ℝ) else 0

theorem density_eq_count_div [Finite E] [Finite C]
    (H : (E →ₗ[F2] C) → Bool) (t : Witness E C) :
    density H t = (Deletion.trueCount H (samples t) : ℝ) /
      Fintype.card (Parameter t.vanishing t.target) := by
  classical
  rw [density, Finset.expect_eq_sum_div_card, samples_trueCount]
  simp

theorem dense_iff_lt_density [Finite E] [Finite C]
    (H : (E →ₗ[F2] C) → Bool) (r p q : Nat) (hq : 0 < q)
    (t : Witness E C) :
    Deletion.Dense (system r) H p q t ↔ (p : ℝ) / q < density H t := by
  rw [density_eq_count_div]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard : (0 : ℝ) < Fintype.card (Parameter t.vanishing t.target) := by
    exact_mod_cast parameter_card_pos t.vanishing t.target
  rw [div_lt_div_iff₀ hq' hcard]
  rw [mul_comm (Deletion.trueCount H (samples t) : ℝ) (q : ℝ)]
  change p * (samples t).length < q * Deletion.trueCount H (samples t) ↔ _
  rw [samples_length]
  constructor <;> intro h <;> exact_mod_cast h

/-- Whole-row deletion gives the normalized real restriction bound on every
actual affine restriction of the permitted dimension and codimension. -/
theorem remainder_restriction_density [Finite E] [Finite C]
    (H : (E →ₗ[F2] C) → Bool) (r p q : Nat) (hq : 0 < q)
    (t : Witness E C) (ht : order t.vanishing t.target ≤ r) :
    density (Deletion.remainder (system r) H p q) t ≤ (p : ℝ) / q := by
  rw [density_eq_count_div]
  have hcard : (0 : ℝ) < Fintype.card (Parameter t.vanishing t.target) := by
    exact_mod_cast parameter_card_pos t.vanishing t.target
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  apply (div_le_div_iff₀ hcard hq').mpr
  have h := remainder_restriction_count H r p q t ht
  have hc : (q : ℝ) * Deletion.trueCount (Deletion.remainder (system r) H p q)
      (samples t) ≤ (p : ℝ) * Fintype.card (Parameter t.vanishing t.target) := by
    exact_mod_cast h
  simpa [mul_comm] using hc

/-- The same bound expressed as the squared normalized real `L²` norm.
This is the restriction-global hypothesis used by the Fourier level theorem. -/
theorem remainder_restriction_sq_expect [Finite E] [Finite C]
    (H : (E →ₗ[F2] C) → Bool) (r p q : Nat) (hq : 0 < q)
    (W : Submodule F2 E) (C' : Submodule F2 C)
    (horder : order W C' ≤ r) (X : E →ₗ[F2] C) :
    (𝔼 A : Parameter W C',
      (restrict (fun Y => if Deletion.remainder (system r) H p q Y
        then (1 : ℝ) else 0) W C' X A) ^ 2) ≤ (p : ℝ) / q := by
  have heq : (𝔼 A : Parameter W C',
      (restrict (fun Y => if Deletion.remainder (system r) H p q Y
        then (1 : ℝ) else 0) W C' X A) ^ 2) =
      density (Deletion.remainder (system r) H p q) ⟨W, C', X⟩ := by
    apply Finset.expect_congr rfl
    intro A _
    simp only [restrict]
    split <;> norm_num
  rw [heq]
  exact remainder_restriction_density H r p q hq ⟨W, C', X⟩ horder

/-- A dual map killed by the quotient has a unique factor with values in `W`.
This is the exact finite object counted in the parity argument of Lemma 5.3. -/
def quotientKernelEquiv (W : Submodule F2 E) :
    {T : C →ₗ[F2] E // W.mkQ.comp T = 0} ≃ (C →ₗ[F2] W) where
  toFun T := T.val.codRestrict W (fun x => by
    apply (Submodule.Quotient.mk_eq_zero W).mp
    exact congrArg (fun f : C →ₗ[F2] (E ⧸ W) => f x) T.property)
  invFun T := ⟨W.subtype.comp T, by
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero W).mpr (T x).property⟩
  left_inv T := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rfl
  right_inv T := by
    apply LinearMap.ext
    intro x
    rfl

theorem quotientKernel_card (W : Submodule F2 E)
    [Fintype {T : C →ₗ[F2] E // W.mkQ.comp T = 0}]
    [Fintype (C →ₗ[F2] W)] :
    Fintype.card {T : C →ₗ[F2] E // W.mkQ.comp T = 0} =
      Fintype.card (C →ₗ[F2] W) :=
  Fintype.card_congr (quotientKernelEquiv W)

open scoped Classical in
theorem quotientKernel_filter_card (W : Submodule F2 E)
    [Fintype (C →ₗ[F2] E)] [Fintype (C →ₗ[F2] W)] :
    (Finset.univ.filter fun T : C →ₗ[F2] E => W.mkQ.comp T = 0).card =
      Fintype.card (C →ₗ[F2] W) := by
  classical
  rw [← Fintype.card_subtype]
  exact quotientKernel_card W

/-- Every deleted point determines its row once the target subspace is fixed.
Thus the union bound ranges over target subspaces, not over row values. -/
theorem deletedSet_iff_exists_target [Finite E] [Finite C]
    (H : (E →ₗ[F2] C) → Bool) (r p q : Nat) (X : E →ₗ[F2] C) :
    Deletion.DeletedSet (system r) H p q X ↔
      ∃ C' : Submodule F2 C,
        Deletion.BadRow (system r) H p q ⟨C', C'.mkQ.comp X⟩ := by
  constructor
  · rintro ⟨⟨C', Z⟩, hbad, hX⟩
    change C'.mkQ.comp X = Z at hX
    subst Z
    exact ⟨C', hbad⟩
  · rintro ⟨C', hbad⟩
    exact ⟨⟨C', C'.mkQ.comp X⟩, hbad, rfl⟩

theorem badRow_codim_le [Finite E] [Finite C]
    (H : (E →ₗ[F2] C) → Bool) (r p q : Nat) (row : Row E C)
    (hbad : Deletion.BadRow (system r) H p q row) :
    Module.finrank F2 (C ⧸ row.target) ≤ r := by
  rcases hbad with ⟨t, ht, heq, _⟩
  have ht' : Module.finrank F2 t.vanishing +
      Module.finrank F2 (C ⧸ t.target) ≤ r := ht
  have htarget : t.target = row.target := congrArg Row.target heq
  rw [← htarget]
  omega

theorem deletedSet_iff_exists_admissible_target [Finite E] [Finite C]
    (H : (E →ₗ[F2] C) → Bool) (r p q : Nat) (X : E →ₗ[F2] C) :
    Deletion.DeletedSet (system r) H p q X ↔
      ∃ C' : Submodule F2 C, Module.finrank F2 (C ⧸ C') ≤ r ∧
        Deletion.BadRow (system r) H p q ⟨C', C'.mkQ.comp X⟩ := by
  rw [deletedSet_iff_exists_target]
  constructor
  · rintro ⟨C', hb⟩
    exact ⟨C', badRow_codim_le H r p q ⟨C', C'.mkQ.comp X⟩ hb, hb⟩
  · rintro ⟨C', _, hb⟩
    exact ⟨C', hb⟩

end MaxCutGames.Fourier.MatrixRestrictions

end OAI
