import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Disjoint
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum
import OAI.Computability.PerfectCompleteness.Algebra.BilinearGramCompressionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaces
import OAI.Computability.UniqueGames.Analysis.MatrixCharactersLemmas
import OAI.Computability.UniqueGames.Foundations.FiniteTrialsLemmas
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.RecursiveSpaceEquiv

open PointwiseSpaces RecursiveSpaces

universe u v w

variable {𝕜 : Type w} [Field 𝕜] {branch : Nat → Nat} {n : Nat}
  {A : Slots branch n → Type u} {B : Slots branch n → Type v}

def assignmentEquiv (e : ∀ s, A s ≃ B s) : Assignment A ≃ Assignment B where
  toFun := project (fun s => e s)
  invFun := project (fun s => (e s).symm)
  left_inv x := by
    funext s
    exact (e s).symm_apply_apply (x s)
  right_inv x := by
    funext s
    exact (e s).apply_symm_apply (x s)

def spaceEquiv (e : ∀ s, A s ≃ B s) :
    space 𝕜 branch n B ≃ₗ[𝕜] space 𝕜 branch n A where
  toLinearMap := spacePullback A B (fun s => e s)
  invFun := spacePullback B A (fun s => (e s).symm)
  left_inv f := by
    apply Subtype.ext
    funext x
    change f.val (project (fun s => e s) (project (fun s => (e s).symm) x)) = f.val x
    apply congrArg f.val
    funext s
    exact (e s).apply_symm_apply (x s)
  right_inv f := by
    apply Subtype.ext
    funext x
    change f.val (project (fun s => (e s).symm) (project (fun s => e s) x)) = f.val x
    apply congrArg f.val
    funext s
    exact (e s).symm_apply_apply (x s)

@[simp] theorem spaceEquiv_apply (e : ∀ s, A s ≃ B s)
    (f : space 𝕜 branch n B) (x : Assignment A) :
    (spaceEquiv e f).val x = f.val (project (fun s => e s) x) := rfl

def squarePullback (e : ∀ s, A s → B s) :
    squareSpace (space 𝕜 branch n B) →ₗ[𝕜] squareSpace (space 𝕜 branch n A) where
  toFun f := ⟨pullback 𝕜 (project e) f.val,
    squareSpace_project_le A B e (Submodule.mem_map_of_mem f.property)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

def squareEquiv (e : ∀ s, A s ≃ B s) :
    squareSpace (space 𝕜 branch n B) ≃ₗ[𝕜] squareSpace (space 𝕜 branch n A) where
  toLinearMap := squarePullback (fun s => e s)
  invFun := squarePullback (fun s => (e s).symm)
  left_inv f := by
    apply Subtype.ext
    funext x
    change f.val (project (fun s => e s) (project (fun s => (e s).symm) x)) = f.val x
    apply congrArg f.val
    funext s
    exact (e s).apply_symm_apply (x s)
  right_inv f := by
    apply Subtype.ext
    funext x
    change f.val (project (fun s => (e s).symm) (project (fun s => e s) x)) = f.val x
    apply congrArg f.val
    funext s
    exact (e s).symm_apply_apply (x s)

@[simp] theorem squareEquiv_apply (e : ∀ s, A s ≃ B s)
    (f : squareSpace (space 𝕜 branch n B)) (x : Assignment A) :
    (squareEquiv e f).val x = f.val (project (fun s => e s) x) := rfl

theorem space_natCard_eq (e : ∀ s, A s ≃ B s) :
    Nat.card (space 𝕜 branch n A) = Nat.card (space 𝕜 branch n B) :=
  Nat.card_congr (spaceEquiv (𝕜 := 𝕜) e).symm.toEquiv

theorem square_natCard_eq (e : ∀ s, A s ≃ B s) :
    Nat.card (squareSpace (space 𝕜 branch n A)) =
      Nat.card (squareSpace (space 𝕜 branch n B)) :=
  Nat.card_congr (squareEquiv (𝕜 := 𝕜) e).symm.toEquiv

theorem space_card_eq [Fintype (space 𝕜 branch n A)] [Fintype (space 𝕜 branch n B)]
    (e : ∀ s, A s ≃ B s) :
    Fintype.card (space 𝕜 branch n A) = Fintype.card (space 𝕜 branch n B) :=
  Fintype.card_congr (spaceEquiv (𝕜 := 𝕜) e).symm.toEquiv

theorem square_card_eq [Fintype (squareSpace (space 𝕜 branch n A))]
    [Fintype (squareSpace (space 𝕜 branch n B))] (e : ∀ s, A s ≃ B s) :
    Fintype.card (squareSpace (space 𝕜 branch n A)) =
      Fintype.card (squareSpace (space 𝕜 branch n B)) :=
  Fintype.card_congr (squareEquiv (𝕜 := 𝕜) e).symm.toEquiv

end PerfectCompleteness.RecursiveSpaceEquiv

end

section

namespace PerfectCompleteness.ReducedPartition

variable {X W R Y : Type*}

def ConstantOnFibers (r : X → R) (f : X → Y) : Prop :=
  ∀ x x', r x = r x' → f x = f x'

def fiber (r : X → R) (f : X → Y) (x : X) : Set R :=
  {v | ∃ z, r z = v ∧ f z = f x}

def parts (r : X → R) (f : X → Y) : Set (Set R) :=
  Set.range (fiber r f)

theorem self_mem_fiber (r : X → R) (f : X → Y) (x : X) :
    r x ∈ fiber r f x :=
  ⟨x, rfl, rfl⟩

theorem fiber_nonempty (r : X → R) (f : X → Y) (x : X) :
    (fiber r f x).Nonempty :=
  ⟨r x, self_mem_fiber r f x⟩

theorem fiber_subset_range (r : X → R) (f : X → Y) (x : X) :
    fiber r f x ⊆ Set.range r := by
  rintro v ⟨z, hz, _⟩
  exact ⟨z, hz⟩

theorem mem_fiber_iff (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) (z x : X) :
    r z ∈ fiber r f x ↔ f z = f x := by
  constructor
  · rintro ⟨w, hw, hfw⟩
    exact (hf w z hw).symm.trans hfw
  · intro h
    exact ⟨z, rfl, h⟩

theorem fiber_eq_of_output_eq (r : X → R) (f : X → Y) {x x' : X}
    (h : f x = f x') : fiber r f x = fiber r f x' := by
  ext v
  constructor
  · rintro ⟨z, hz, hfz⟩
    exact ⟨z, hz, hfz.trans h⟩
  · rintro ⟨z, hz, hfz⟩
    exact ⟨z, hz, hfz.trans h.symm⟩

theorem fiber_eq_iff (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) (x x' : X) :
    fiber r f x = fiber r f x' ↔ f x = f x' := by
  constructor
  · intro h
    apply (mem_fiber_iff r f hf x x').1
    rw [← h]
    exact self_mem_fiber r f x
  · exact fiber_eq_of_output_eq r f

theorem output_eq_of_common_mem (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) {x x' : X} {v : R}
    (hx : v ∈ fiber r f x) (hx' : v ∈ fiber r f x') : f x = f x' := by
  obtain ⟨z, hz, hfz⟩ := hx
  obtain ⟨z', hz', hfz'⟩ := hx'
  exact hfz.symm.trans ((hf z z' (hz.trans hz'.symm)).trans hfz')

theorem fiber_disjoint_of_output_ne (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) {x x' : X} (h : f x ≠ f x') :
    Disjoint (fiber r f x) (fiber r f x') := by
  apply Set.disjoint_left.2
  intro v hv hv'
  exact h (output_eq_of_common_mem r f hf hv hv')

theorem fiber_eq_or_disjoint (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) (x x' : X) :
    fiber r f x = fiber r f x' ∨ Disjoint (fiber r f x) (fiber r f x') := by
  classical
  by_cases h : f x = f x'
  · exact Or.inl (fiber_eq_of_output_eq r f h)
  · exact Or.inr (fiber_disjoint_of_output_ne r f hf h)

theorem covered_iff_mem_range (r : X → R) (f : X → Y) (v : R) :
    (∃ P ∈ parts r f, v ∈ P) ↔ v ∈ Set.range r := by
  constructor
  · rintro ⟨P, ⟨x, hx⟩, hv⟩
    apply fiber_subset_range r f x
    rw [hx]
    exact hv
  · rintro ⟨x, hx⟩
    refine ⟨fiber r f x, ⟨x, rfl⟩, ?_⟩
    exact ⟨x, hx, rfl⟩

abbrev Part (r : X → R) (f : X → Y) := ↥(parts r f)

def label (r : X → R) (f : X → Y) (x : X) : Part r f :=
  ⟨fiber r f x, ⟨x, rfl⟩⟩

instance [Nonempty X] (r : X → R) (f : X → Y) : Nonempty (Part r f) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨label r f x⟩

noncomputable def representative (r : X → R) (f : X → Y) (P : Part r f) : X :=
  P.property.choose

theorem representative_spec (r : X → R) (f : X → Y) (P : Part r f) :
    fiber r f (representative r f P) = P.val :=
  P.property.choose_spec

theorem representative_mem (r : X → R) (f : X → Y) (P : Part r f) :
    r (representative r f P) ∈ P.val := by
  rw [← representative_spec r f P]
  exact self_mem_fiber r f _

theorem part_nonempty (r : X → R) (f : X → Y) (P : Part r f) :
    P.val.Nonempty :=
  ⟨r (representative r f P), representative_mem r f P⟩

noncomputable def output (r : X → R) (f : X → Y) (P : Part r f) : Y :=
  f (representative r f P)

theorem output_mem_range (r : X → R) (f : X → Y) (P : Part r f) :
    output r f P ∈ Set.range f :=
  ⟨representative r f P, rfl⟩

theorem mem_iff (r : X → R) (f : X → Y) (hf : ConstantOnFibers r f)
    (P : Part r f) (x : X) : r x ∈ P.val ↔ f x = output r f P := by
  rw [← representative_spec r f P]
  exact mem_fiber_iff r f hf x (representative r f P)

@[simp] theorem output_label (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) (x : X) : output r f (label r f x) = f x :=
  ((mem_iff r f hf (label r f x) x).1 (self_mem_fiber r f x)).symm

theorem output_injective (r : X → R) (f : X → Y) :
    Function.Injective (output r f) := by
  intro P Q h
  apply Subtype.ext
  calc
    P.val = fiber r f (representative r f P) := (representative_spec r f P).symm
    _ = fiber r f (representative r f Q) := fiber_eq_of_output_eq r f h
    _ = Q.val := representative_spec r f Q

@[simp] theorem label_representative (r : X → R) (f : X → Y) (P : Part r f) :
    label r f (representative r f P) = P := by
  apply Subtype.ext
  exact representative_spec r f P

theorem label_surjective (r : X → R) (f : X → Y) :
    Function.Surjective (label r f) := by
  intro P
  exact ⟨representative r f P, label_representative r f P⟩

instance [Finite X] (r : X → R) (f : X → Y) : Finite (Part r f) :=
  Finite.of_surjective (label r f) (label_surjective r f)

theorem card_parts_le [Finite X] (r : X → R) (f : X → Y) :
    Nat.card (Part r f) ≤ Nat.card X :=
  Nat.card_le_card_of_surjective (label r f) (label_surjective r f)

theorem restoration_bijective (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) :
    Function.Bijective
      (fun P : Part r f => (⟨output r f P, output_mem_range r f P⟩ : Set.range f)) := by
  constructor
  · intro P Q h
    exact output_injective r f (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨label r f x, ?_⟩
    apply Subtype.ext
    exact (output_label r f hf x).trans hx

def rangeMap (r : X → R) (x : X) : Set.range r :=
  ⟨r x, ⟨x, rfl⟩⟩

noncomputable def preimage (r : X → R) (v : Set.range r) : X :=
  v.property.choose

theorem preimage_spec (r : X → R) (v : Set.range r) : r (preimage r v) = v.val :=
  v.property.choose_spec

theorem rangeMap_preimage (r : X → R) (v : Set.range r) :
    rangeMap r (preimage r v) = v :=
  Subtype.ext (preimage_spec r v)

theorem rangeMap_surjective (r : X → R) : Function.Surjective (rangeMap r) := by
  intro v
  exact ⟨preimage r v, rangeMap_preimage r v⟩

noncomputable def induced (r : X → R) (f : X → Y) (v : Set.range r) : Y :=
  f (preimage r v)

@[simp] theorem induced_rangeMap (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) (x : X) : induced r f (rangeMap r x) = f x :=
  hf _ x (preimage_spec r (rangeMap r x))

theorem induced_factorization (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) : f = induced r f ∘ rangeMap r := by
  funext x
  exact (induced_rangeMap r f hf x).symm

theorem induced_unique (r : X → R) (f : X → Y) (g : Set.range r → Y)
    (hg : ∀ x, g (rangeMap r x) = f x) : g = induced r f := by
  funext v
  calc
    g v = g (rangeMap r (preimage r v)) := congrArg g (rangeMap_preimage r v).symm
    _ = f (preimage r v) := hg (preimage r v)
    _ = induced r f v := rfl

theorem mem_fiber_iff_induced (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) (v : Set.range r) (x : X) :
    v.val ∈ fiber r f x ↔ induced r f v = f x := by
  have h := mem_fiber_iff r f hf (preimage r v) x
  simpa only [preimage_spec, induced] using h

theorem fiber_eq_of_pullback
    (π : X → W) (hπ : Function.Surjective π)
    (rX : X → R) (rW : W → R) (fX : X → Y) (fW : W → Y)
    (hr : ∀ x, rX x = rW (π x)) (hf : ∀ x, fX x = fW (π x)) (x : X) :
    fiber rX fX x = fiber rW fW (π x) := by
  ext v
  constructor
  · rintro ⟨z, hz, hfz⟩
    exact ⟨π z, (hr z).symm.trans hz, (hf z).symm.trans (hfz.trans (hf x))⟩
  · rintro ⟨w, hw, hfw⟩
    obtain ⟨z, hz⟩ := hπ w
    refine ⟨z, (hr z).trans ((congrArg rW hz).trans hw), ?_⟩
    exact (hf z).trans ((congrArg fW hz).trans (hfw.trans (hf x).symm))

theorem parts_eq_of_pullback
    (π : X → W) (hπ : Function.Surjective π)
    (rX : X → R) (rW : W → R) (fX : X → Y) (fW : W → Y)
    (hr : ∀ x, rX x = rW (π x)) (hf : ∀ x, fX x = fW (π x)) :
    parts rX fX = parts rW fW := by
  apply Set.ext
  intro P
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨π x, (fiber_eq_of_pullback π hπ rX rW fX fW hr hf x).symm.trans hx⟩
  · rintro ⟨w, hw⟩
    obtain ⟨x, hx⟩ := hπ w
    refine ⟨x, ?_⟩
    calc
      fiber rX fX x = fiber rW fW (π x) :=
        fiber_eq_of_pullback π hπ rX rW fX fW hr hf x
      _ = fiber rW fW w := congrArg (fiber rW fW) hx
      _ = P := hw

theorem output_eq_of_shared_part
    (π : X → W) (rX : X → R) (rW : W → R) (fX : X → Y) (fW : W → Y)
    (hr : ∀ x, rX x = rW (π x)) (hf : ∀ x, fX x = fW (π x))
    (hW : ConstantOnFibers rW fW)
    (P : Part rX fX) (Q : Part rW fW) (hPQ : P.val = Q.val) :
    output rX fX P = output rW fW Q := by
  let x := representative rX fX P
  have hx : rX x ∈ P.val := representative_mem rX fX P
  have hmem : rW (π x) ∈ Q.val := by
    rw [← hr x, ← hPQ]
    exact hx
  change fX x = output rW fW Q
  exact (hf x).trans ((mem_iff rW fW hW Q (π x)).1 hmem)

end PerfectCompleteness.ReducedPartition

end

section

namespace PerfectCompleteness.RowAdvice

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

def pad {d r : Nat} (_h : d ≤ r) : (Fin d → F2) →ₗ[F2] (Fin r → F2) where
  toFun v i := if hi : i.val < d then v ⟨i.val, hi⟩ else 0
  map_add' v w := by
    funext i
    by_cases hi : i.val < d <;> simp [hi]
  map_smul' a v := by
    funext i
    by_cases hi : i.val < d <;> simp [hi]

@[simp] theorem pad_low {d r : Nat} (h : d ≤ r) (v : Fin d → F2) (i : Fin d) :
    pad h v ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩ = v i := by
  simp [pad, i.isLt]

theorem pad_high {d r : Nat} (h : d ≤ r) (v : Fin d → F2)
    (i : Fin r) (hi : d ≤ i.val) : pad h v i = 0 := by
  simp [pad, Nat.not_lt.mpr hi]

theorem pad_injective {d r : Nat} (h : d ≤ r) : Function.Injective (pad h) := by
  intro v w hvw
  funext i
  have hi := congrFun hvw (⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩ : Fin r)
  simpa only [pad_low] using hi

variable {E C R : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem apply_eq_iff_ker_mkQ_eq (A : C →ₗ[F2] R) (x y : C) :
    A x = A y ↔ (LinearMap.ker A).mkQ x = (LinearMap.ker A).mkQ y := by
  calc
    A x = A y ↔ A (x - y) = 0 := by rw [map_sub, sub_eq_zero]
    _ ↔ (LinearMap.ker A).mkQ (x - y) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.ker A)).symm
    _ ↔ _ := by rw [map_sub, sub_eq_zero]

theorem comp_eq_iff_ker_quotient (A : C →ₗ[F2] R) (X T : E →ₗ[F2] C) :
    A.comp X = A.comp T ↔
      (LinearMap.ker A).mkQ.comp X = (LinearMap.ker A).mkQ.comp T := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    exact (apply_eq_iff_ker_mkQ_eq A (X x) (T x)).mp (LinearMap.congr_fun h x)
  · intro h
    apply LinearMap.ext
    intro x
    exact (apply_eq_iff_ker_mkQ_eq A (X x) (T x)).mpr (LinearMap.congr_fun h x)

theorem slice_row_eq (W : Submodule F2 E) (A : C →ₗ[F2] R)
    (T : E →ₗ[F2] C) (X : MatrixSlice.Slice W (LinearMap.ker A) T) :
    A.comp X.val = A.comp T :=
  (comp_eq_iff_ker_quotient A X.val T).mpr X.property.2

def paddedRowMap [FiniteDimensional F2 C] (r : Nat) (C' : Submodule F2 C)
    (h : Module.finrank F2 (C ⧸ C') ≤ r) : C →ₗ[F2] (Fin r → F2) :=
  (pad h).comp (MatrixSlice.rowMap C')

theorem paddedRowMap_apply_eq_iff [FiniteDimensional F2 C]
    (r : Nat) (C' : Submodule F2 C) (h : Module.finrank F2 (C ⧸ C') ≤ r)
    (x y : C) :
    paddedRowMap r C' h x = paddedRowMap r C' h y ↔ C'.mkQ x = C'.mkQ y := by
  constructor
  · intro hxy
    apply (Module.finBasis F2 (C ⧸ C')).equivFun.injective
    exact pad_injective h hxy
  · intro hxy
    change pad h ((Module.finBasis F2 (C ⧸ C')).equivFun (C'.mkQ x)) =
      pad h ((Module.finBasis F2 (C ⧸ C')).equivFun (C'.mkQ y))
    rw [hxy]

theorem ker_paddedRowMap [FiniteDimensional F2 C]
    (r : Nat) (C' : Submodule F2 C) (h : Module.finrank F2 (C ⧸ C') ≤ r) :
    LinearMap.ker (paddedRowMap r C' h) = C' := by
  ext x
  change paddedRowMap r C' h x = 0 ↔ x ∈ C'
  calc
    paddedRowMap r C' h x = 0 ↔
        paddedRowMap r C' h x = paddedRowMap r C' h 0 := by rw [map_zero]
    _ ↔ C'.mkQ x = C'.mkQ 0 := paddedRowMap_apply_eq_iff r C' h x 0
    _ ↔ x ∈ C' := by
      rw [map_zero]
      exact Submodule.Quotient.mk_eq_zero C'

theorem paddedRowMap_comp_eq_iff [FiniteDimensional F2 C]
    (r : Nat) (C' : Submodule F2 C) (h : Module.finrank F2 (C ⧸ C') ≤ r)
    (X T : E →ₗ[F2] C) :
    (paddedRowMap r C' h).comp X = (paddedRowMap r C' h).comp T ↔
      C'.mkQ.comp X = C'.mkQ.comp T := by
  rw [comp_eq_iff_ker_quotient, ker_paddedRowMap]

theorem codimension_le_of_order_le (W : Submodule F2 E) (C' : Submodule F2 C)
    {r : Nat} (h : UniqueGamesTheorem.Fourier.MatrixRestrictions.order W C' ≤ r) :
    Module.finrank F2 (C ⧸ C') ≤ r :=
  (MatrixSlice.row_count_le_order W C').trans h

theorem card_rowMaps [FiniteDimensional F2 C] (r : Nat)
    [Fintype (C →ₗ[F2] (Fin r → F2))] :
    Fintype.card (C →ₗ[F2] (Fin r → F2)) = 2 ^ (r * Module.finrank F2 C) := by
  simpa only [Module.finrank_fin_fun, Nat.mul_comm] using
    (UniqueGamesTheorem.Fourier.MatrixParity.card_linearMaps (C := C) (E := Fin r → F2))

theorem card_rowMaps_le [FiniteDimensional F2 C] (r s : Nat)
    [Fintype (C →ₗ[F2] (Fin r → F2))] (hC : Module.finrank F2 C ≤ s) :
    Fintype.card (C →ₗ[F2] (Fin r → F2)) ≤ 2 ^ (r * s) := by
  rw [card_rowMaps]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_left r hC)

end
end PerfectCompleteness.RowAdvice

end

section

namespace PerfectCompleteness.SliceMass

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions (Parameter)
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.MatrixSlice

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

def columnEventEquivSlice (W : Submodule F2 E) (C' : Submodule F2 C)
    (T : E →ₗ[F2] C) :
    {X : Slice (⊥ : Submodule F2 E) C' T //
      X.val.domRestrict W = T.domRestrict W} ≃ Slice W C' T where
  toFun X := ⟨X.val.val, X.property, X.val.property.2⟩
  invFun X := ⟨⟨X.val, by
    apply LinearMap.ext
    intro x
    have hx : (x : E) = 0 := (Submodule.mem_bot F2).mp x.property
    simp [hx], X.property.2⟩, X.property.1⟩
  left_inv X := by apply Subtype.ext; rfl
  right_inv X := by apply Subtype.ext; rfl

section Finite

variable [Finite E] [Finite C]
  [FiniteDimensional F2 E] [FiniteDimensional F2 C]

theorem card_slice (W : Submodule F2 E) (C' : Submodule F2 C)
    (T : E →ₗ[F2] C) :
    Fintype.card (Slice W C' T) =
      2 ^ (Module.finrank F2 (E ⧸ W) * Module.finrank F2 C') := by
  rw [← Fintype.card_congr (parameterEquivSlice W C' T)]
  rw [Module.card_eq_pow_finrank (K := F2) (V := Parameter W C')]
  rw [show Fintype.card F2 = 2 by decide]
  change 2 ^ Module.finrank F2 ((E ⧸ W) →ₗ[F2] C') = _
  rw [Module.finrank_linearMap]

theorem card_rowFiber (C' : Submodule F2 C) (T : E →ₗ[F2] C) :
    Fintype.card (Slice (⊥ : Submodule F2 E) C' T) =
      2 ^ (Module.finrank F2 E * Module.finrank F2 C') := by
  rw [card_slice]
  have hdim := (⊥ : Submodule F2 E).finrank_quotient_add_finrank
  simp only [finrank_bot, add_zero] at hdim
  rw [hdim]

theorem card_rowFiber_eq_card_slice_mul (W : Submodule F2 E)
    (C' : Submodule F2 C) (T : E →ₗ[F2] C) :
    Fintype.card (Slice (⊥ : Submodule F2 E) C' T) =
      Fintype.card (Slice W C' T) *
        2 ^ (Module.finrank F2 W * Module.finrank F2 C') := by
  rw [card_rowFiber, card_slice, ← pow_add, ← Nat.add_mul,
    W.finrank_quotient_add_finrank]

theorem card_ratio (W : Submodule F2 E) (C' : Submodule F2 C)
    (T : E →ₗ[F2] C) :
    (Fintype.card (Slice W C' T) : ℝ) /
        Fintype.card (Slice (⊥ : Submodule F2 E) C' T) =
      1 / (2 : ℝ) ^ (Module.finrank F2 W * Module.finrank F2 C') := by
  rw [card_rowFiber_eq_card_slice_mul W C' T, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  have hcard : (Fintype.card (Slice W C' T) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [div_mul_eq_div_div, div_self hcard]

theorem probability_columnConstraint (W : Submodule F2 E)
    (C' : Submodule F2 C) (T : E →ₗ[F2] C) :
    (FiniteDistribution.uniform (Slice (⊥ : Submodule F2 E) C' T)).probability
        (fun X => decide (X.val.domRestrict W = T.domRestrict W)) =
      1 / (2 : ℝ) ^ (Module.finrank F2 W * Module.finrank F2 C') := by
  let event : Slice (⊥ : Submodule F2 E) C' T → Prop :=
    fun X => X.val.domRestrict W = T.domRestrict W
  calc
    _ = (FiniteDistribution.uniform (Slice (⊥ : Submodule F2 E) C' T)).expectation
        (fun X => if event X then (1 : ℝ) else 0) := by
      unfold FiniteDistribution.probability FiniteDistribution.expectation
      apply Finset.sum_congr rfl
      intro X _
      by_cases hX : event X <;> simp [event] at hX ⊢
    _ = (∑ X, if event X then (1 : ℝ) else 0) /
        (Fintype.card (Slice (⊥ : Submodule F2 E) C' T) : ℝ) :=
      FiniteDistribution.expectation_uniform _
    _ = (Fintype.card {X // event X} : ℝ) /
        (Fintype.card (Slice (⊥ : Submodule F2 E) C' T) : ℝ) := by
      simp only [Fintype.card_subtype, Finset.sum_boole]
    _ = (Fintype.card (Slice W C' T) : ℝ) /
        (Fintype.card (Slice (⊥ : Submodule F2 E) C' T) : ℝ) := by
      rw [Fintype.card_congr (columnEventEquivSlice W C' T)]
    _ = _ := card_ratio W C' T

theorem probability_columnConstraint_ge (W : Submodule F2 E)
    (C' : Submodule F2 C) (T : E →ₗ[F2] C) :
    1 / (2 : ℝ) ^ (Module.finrank F2 W * Module.finrank F2 C) ≤
      (FiniteDistribution.uniform (Slice (⊥ : Submodule F2 E) C' T)).probability
        (fun X => decide (X.val.domRestrict W = T.domRestrict W)) := by
  rw [probability_columnConstraint]
  apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
  exact pow_le_pow_right₀ (by norm_num)
    (Nat.mul_le_mul_left _ C'.finrank_le)

theorem probability_columnConstraint_ge_of_finrank_le
    (W : Submodule F2 E) (C' : Submodule F2 C) (T : E →ₗ[F2] C)
    (r : Nat) (hW : Module.finrank F2 W ≤ r) :
    1 / (2 : ℝ) ^ (r * Module.finrank F2 C) ≤
      (FiniteDistribution.uniform (Slice (⊥ : Submodule F2 E) C' T)).probability
        (fun X => decide (X.val.domRestrict W = T.domRestrict W)) := by
  apply le_trans _ (probability_columnConstraint_ge W C' T)
  apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
  exact pow_le_pow_right₀ (by norm_num)
    (Nat.mul_le_mul_right _ hW)

end Finite
end
end PerfectCompleteness.SliceMass

end

section

namespace PerfectCompleteness.SmallBias

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Foundations.Information

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem expectation_mono (μ : FiniteDistribution Ω) {a b : Ω → ℝ}
    (h : ∀ x, a x ≤ b x) : μ.expectation a ≤ μ.expectation b := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

@[simp] theorem expectation_const (μ : FiniteDistribution Ω) (c : ℝ) :
    μ.expectation (fun _ => c) = c := by
  simp only [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized, one_mul]

@[simp] theorem expectation_neg (μ : FiniteDistribution Ω) (a : Ω → ℝ) :
    μ.expectation (fun x => -a x) = -μ.expectation a := by
  simp only [FiniteDistribution.expectation, mul_neg, Finset.sum_neg_distrib]

theorem expectation_sum (μ : FiniteDistribution Ω) (a : I → Ω → ℝ) :
    μ.expectation (fun x => ∑ i, a i x) = ∑ i, μ.expectation (a i) := by
  simp only [FiniteDistribution.expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem bounded_target_cauchySchwarz (μ : FiniteDistribution Ω)
    (g a : Ω → ℝ) (hg : ∀ x, g x ^ 2 ≤ 1) :
    μ.expectation (fun x => g x * a x) ^ 2 ≤
      μ.expectation (fun x => a x ^ 2) := by
  have hcs := weighted_sum_sq_le μ.weight (fun x => g x * a x)
    ⟨μ.nonnegative, μ.normalized⟩
  change μ.expectation (fun x => g x * a x) ^ 2 ≤
    μ.expectation (fun x => (g x * a x) ^ 2) at hcs
  apply hcs.trans
  apply expectation_mono
  intro x
  calc
    (g x * a x) ^ 2 = g x ^ 2 * a x ^ 2 := mul_pow _ _ _
    _ ≤ 1 * a x ^ 2 := mul_le_mul_of_nonneg_right (hg x) (sq_nonneg _)
    _ = a x ^ 2 := one_mul _

theorem gram_energy_bound (μ : FiniteDistribution Ω) (f : I → Ω → ℝ)
    (biasBound : ℝ) (hf : ∀ i x, f i x ^ 2 ≤ 1)
    (hpair : ∀ i j, i ≠ j → μ.expectation (fun x => f i x * f j x) ≤ biasBound) :
    μ.expectation (fun x => (∑ i, f i x) ^ 2) ≤
      (Fintype.card I : ℝ) * (1 + ((Fintype.card I : ℝ) - 1) * biasBound) := by
  classical
  have hentry : ∀ i j, μ.expectation (fun x => f i x * f j x) ≤
      biasBound + if i = j then 1 - biasBound else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hdiag : μ.expectation (fun x => f i x * f i x) ≤ 1 := by
        calc
          _ ≤ μ.expectation (fun _ => 1) := expectation_mono μ (fun x => by
            simpa only [pow_two] using hf i x)
          _ = 1 := expectation_const μ 1
      simp only [ite_true]
      linarith
    · simpa only [ite_eq_right hij, add_zero] using hpair i j hij
  have hrow : ∀ i, (∑ j, μ.expectation (fun x => f i x * f j x)) ≤
      (Fintype.card I : ℝ) * biasBound + (1 - biasBound) := by
    intro i
    calc
      _ ≤ ∑ j, (biasBound + if i = j then 1 - biasBound else 0) :=
        Finset.sum_le_sum (fun j _ => hentry i j)
      _ = _ := by simp [Finset.sum_add_distrib]
  calc
    _ = ∑ i, ∑ j, μ.expectation (fun x => f i x * f j x) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, expectation_sum]
      exact Finset.sum_comm
    _ ≤ ∑ _i : I, ((Fintype.card I : ℝ) * biasBound + (1 - biasBound)) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem aligned_heavy_energy (μ : FiniteDistribution Ω) (f : I → Ω → ℝ)
    (g : Ω → ℝ) (τ biasBound : ℝ) (hτ : 0 ≤ τ)
    (hg : ∀ x, g x ^ 2 ≤ 1) (hf : ∀ i x, f i x ^ 2 ≤ 1)
    (hpair : ∀ i j, i ≠ j → μ.expectation (fun x => f i x * f j x) ≤ biasBound)
    (hheavy : ∀ i, τ ≤ μ.expectation (fun x => g x * f i x)) :
    ((Fintype.card I : ℝ) * τ) ^ 2 ≤
      (Fintype.card I : ℝ) * (1 + ((Fintype.card I : ℝ) - 1) * biasBound) := by
  have hlower : (Fintype.card I : ℝ) * τ ≤
      μ.expectation (fun x => g x * ∑ i, f i x) := by
    calc
      _ = ∑ _i : I, τ := by simp
      _ ≤ ∑ i, μ.expectation (fun x => g x * f i x) :=
        Finset.sum_le_sum (fun i _ => hheavy i)
      _ = _ := by simp only [Finset.mul_sum, expectation_sum]
  calc
    _ ≤ μ.expectation (fun x => g x * ∑ i, f i x) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hτ) hlower 2
    _ ≤ μ.expectation (fun x => (∑ i, f i x) ^ 2) :=
      bounded_target_cauchySchwarz μ g _ hg
    _ ≤ _ := gram_energy_bound μ f biasBound hf hpair

def align (μ : FiniteDistribution Ω) (g : Ω → ℝ) (f : I → Ω → ℝ)
    (i : I) (x : Ω) : ℝ :=
  if 0 ≤ μ.expectation (fun y => g y * f i y) then f i x else -f i x

omit [Fintype I] in
theorem align_sq (μ : FiniteDistribution Ω) (g : Ω → ℝ)
    (f : I → Ω → ℝ) (i : I) (x : Ω) :
    align μ g f i x ^ 2 = f i x ^ 2 := by
  unfold align
  split <;> simp

omit [Fintype I] in
theorem align_correlation (μ : FiniteDistribution Ω) (g : Ω → ℝ)
    (f : I → Ω → ℝ) (i : I) :
    μ.expectation (fun x => g x * align μ g f i x) =
      |μ.expectation (fun x => g x * f i x)| := by
  by_cases hi : 0 ≤ μ.expectation (fun x => g x * f i x)
  · simp only [align, ite_eq_left hi, abs_of_nonneg hi]
  · simp only [align, ite_eq_right hi, mul_neg, expectation_neg,
      abs_of_neg (lt_of_not_ge hi)]

omit [Fintype I] in
theorem align_pair_bound (μ : FiniteDistribution Ω) (g : Ω → ℝ)
    (f : I → Ω → ℝ) (biasBound : ℝ)
    (hpair : ∀ i j, i ≠ j → |μ.expectation (fun x => f i x * f j x)| ≤ biasBound) :
    ∀ i j, i ≠ j → μ.expectation (fun x => align μ g f i x * align μ g f j x) ≤ biasBound := by
  intro i j hij
  have hpos := (abs_le.mp (hpair i j hij)).2
  have hneg : -μ.expectation (fun x => f i x * f j x) ≤ biasBound := by
    linarith [(abs_le.mp (hpair i j hij)).1]
  by_cases hi : 0 ≤ μ.expectation (fun x => g x * f i x) <;>
    by_cases hj : 0 ≤ μ.expectation (fun x => g x * f j x)
  · simpa [align, hi, hj] using hpos
  · simpa [align, hi, hj, mul_neg, expectation_neg] using hneg
  · simpa [align, hi, hj, neg_mul, expectation_neg] using hneg
  · simpa [align, hi, hj] using hpos

theorem heavy_list_card_le (μ : FiniteDistribution Ω) (f : I → Ω → ℝ)
    (g : Ω → ℝ) (τ biasBound : ℝ) (hτ : 0 < τ) (hbiasBound : 0 ≤ biasBound)
    (hsmall : biasBound ≤ τ ^ 2 / 2)
    (hg : ∀ x, g x ^ 2 ≤ 1) (hf : ∀ i x, f i x ^ 2 ≤ 1)
    (hpair : ∀ i j, i ≠ j → |μ.expectation (fun x => f i x * f j x)| ≤ biasBound)
    (hheavy : ∀ i, τ ≤ |μ.expectation (fun x => g x * f i x)|) :
    (Fintype.card I : ℝ) ≤ 2 / τ ^ 2 := by
  have he := aligned_heavy_energy μ (align μ g f) g τ biasBound hτ.le hg
    (fun i x => (align_sq μ g f i x).trans_le (hf i x))
    (align_pair_bound μ g f biasBound hpair)
    (fun i => (hheavy i).trans_eq (align_correlation μ g f i).symm)
  have hm : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hτsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  apply (le_div_iff₀ hτsq).2
  by_cases hmzero : (Fintype.card I : ℝ) = 0
  · simp [hmzero]
  · have hmpos : (0 : ℝ) < Fintype.card I := lt_of_le_of_ne hm (Ne.symm hmzero)
    have hscale := mul_le_mul_of_nonneg_left hsmall (sq_nonneg (Fintype.card I : ℝ))
    have hmulbiasBound := mul_nonneg hm hbiasBound
    have hbound : (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) * τ ^ 2) ≤
        (Fintype.card I : ℝ) * 2 := by nlinarith
    exact le_of_mul_le_mul_left hbound hmpos

def heavySet (μ : FiniteDistribution Ω) (f : I → Ω → ℝ)
    (g : Ω → ℝ) (τ : ℝ) : Finset I :=
  Finset.univ.filter (fun i => τ ≤ |μ.expectation (fun x => g x * f i x)|)

theorem heavySet_card_le (μ : FiniteDistribution Ω) (f : I → Ω → ℝ)
    (g : Ω → ℝ) (τ biasBound : ℝ) (hτ : 0 < τ) (hbias : 0 ≤ biasBound)
    (hsmall : biasBound ≤ τ ^ 2 / 2)
    (hg : ∀ x, g x ^ 2 ≤ 1) (hf : ∀ i x, f i x ^ 2 ≤ 1)
    (hpair : ∀ i j, i ≠ j →
      |μ.expectation (fun x => f i x * f j x)| ≤ biasBound) :
    ((heavySet μ f g τ).card : ℝ) ≤ 2 / τ ^ 2 := by
  classical
  let s := heavySet μ f g τ
  have hs := heavy_list_card_le (I := ↥s) μ (fun i => f i.val) g τ biasBound
    hτ hbias hsmall hg (fun i x => hf i.val x)
    (fun i j hij => hpair i.val j.val (fun heq => hij (Subtype.ext heq)))
    (fun i => (Finset.mem_filter.mp i.property).2)
  simpa only [Fintype.card_coe] using hs

end

end PerfectCompleteness.SmallBias

end

end OAI
