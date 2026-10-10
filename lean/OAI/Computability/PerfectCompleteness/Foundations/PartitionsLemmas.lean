import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import OAI.Computability.UniqueGames.Reduction.BinaryLinear

namespace OAI

section

namespace PerfectCompleteness.CanonicalPartition

variable {X Y Z W : Type*}

def fiber (f : X → Y) (y : Y) : Set X := {x | f x = y}

def parts (f : X → Y) : Set (Set X) :=
  Set.range fun x => fiber f (f x)

abbrev Part (f : X → Y) := ↥(parts f)

def label (f : X → Y) (x : X) : Part f :=
  ⟨fiber f (f x), ⟨x, rfl⟩⟩

instance [Nonempty X] (f : X → Y) : Nonempty (Part f) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨label f x⟩

instance [Finite X] (f : X → Y) : Finite (Part f) := by
  dsimp [Part]
  infer_instance

noncomputable def representative (f : X → Y) (P : Part f) : X :=
  P.property.choose

theorem representative_spec (f : X → Y) (P : Part f) :
    fiber f (f (representative f P)) = P.val :=
  P.property.choose_spec

noncomputable def output (f : X → Y) (P : Part f) : Y :=
  f (representative f P)

theorem part_eq_fiber (f : X → Y) (P : Part f) :
    P.val = fiber f (output f P) :=
  (representative_spec f P).symm

theorem mem_iff (f : X → Y) (P : Part f) (x : X) :
    x ∈ P.val ↔ f x = output f P := by
  rw [part_eq_fiber f P]
  rfl

theorem part_nonempty (f : X → Y) (P : Part f) : P.val.Nonempty := by
  refine ⟨representative f P, ?_⟩
  exact (mem_iff f P _).2 rfl

theorem output_mem_range (f : X → Y) (P : Part f) :
    output f P ∈ Set.range f :=
  ⟨representative f P, rfl⟩

@[simp] theorem output_label (f : X → Y) (x : X) :
    output f (label f x) = f x := by
  have hx : x ∈ (label f x).val := rfl
  exact ((mem_iff f (label f x) x).1 hx).symm

theorem output_injective (f : X → Y) : Function.Injective (output f) := by
  intro P Q h
  apply Subtype.ext
  rw [part_eq_fiber f P, part_eq_fiber f Q, h]

@[simp] theorem label_representative (f : X → Y) (P : Part f) :
    label f (representative f P) = P := by
  apply Subtype.ext
  exact representative_spec f P

theorem label_surjective (f : X → Y) : Function.Surjective (label f) := by
  intro P
  exact ⟨representative f P, label_representative f P⟩

theorem card_parts_le [Finite X] (f : X → Y) :
    Nat.card (Part f) ≤ Nat.card X :=
  Nat.card_le_card_of_surjective (label f) (label_surjective f)

theorem restoration_bijective (f : X → Y) :
    Function.Bijective
      (fun P : Part f => (⟨output f P, output_mem_range f P⟩ : Set.range f)) := by
  constructor
  · intro P Q h
    exact output_injective f (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨label f x, ?_⟩
    apply Subtype.ext
    exact (output_label f x).trans hx

theorem parts_eq_of_kernel_eq (f : X → Y) (g : X → Z)
    (h : ∀ x x', f x = f x' ↔ g x = g x') : parts f = parts g := by
  have hfiber : ∀ x, fiber f (f x) = fiber g (g x) := by
    intro x
    ext x'
    exact h x' x
  apply Set.ext
  intro P
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (hfiber x).symm.trans hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (hfiber x).trans hx⟩

theorem kernel_le_of_parts_subset (f : X → Y) (g : X → Z)
    (h : parts f ⊆ parts g) {x x' : X} (hxx' : f x = f x') :
    g x = g x' := by
  obtain ⟨z, hz⟩ := h (show fiber f (f x') ∈ parts f from ⟨x', rfl⟩)
  change fiber g (g z) = fiber f (f x') at hz
  have hx : x ∈ fiber g (g z) := by
    rw [hz]
    exact hxx'
  have hx' : x' ∈ fiber g (g z) := by
    rw [hz]
    rfl
  exact hx.trans hx'.symm

theorem parts_eq_iff_kernel_eq (f : X → Y) (g : X → Z) :
    parts f = parts g ↔ ∀ x x', f x = f x' ↔ g x = g x' := by
  constructor
  · intro h x x'
    exact ⟨kernel_le_of_parts_subset f g (fun _ hP => h ▸ hP),
      kernel_le_of_parts_subset g f (fun _ hP => h.symm ▸ hP)⟩
  · exact parts_eq_of_kernel_eq f g

theorem label_val_eq_of_parts_eq (f : X → Y) (g : X → Z)
    (h : parts f = parts g) (x : X) :
    (label f x).val = (label g x).val := by
  ext x'
  exact (parts_eq_iff_kernel_eq f g).1 h x' x

theorem parts_postcomp_injective (f : X → Y) (p : Y → Z)
    (hp : Function.Injective p) : parts (p ∘ f) = parts f := by
  apply parts_eq_of_kernel_eq
  intro x x'
  exact ⟨fun h => hp h, fun h => congrArg p h⟩

noncomputable def coarsen (f : X → Y) (p : Y → Z) (P : Part f) :
    Part (p ∘ f) :=
  label (p ∘ f) (representative f P)

@[simp] theorem output_coarsen (f : X → Y) (p : Y → Z) (P : Part f) :
    output (p ∘ f) (coarsen f p P) = p (output f P) :=
  output_label (p ∘ f) (representative f P)

theorem coarsen_eq_iff (f : X → Y) (p : Y → Z)
    (P : Part f) (Q : Part (p ∘ f)) :
    coarsen f p P = Q ↔ p (output f P) = output (p ∘ f) Q := by
  constructor
  · intro h
    rw [← output_coarsen f p P, h]
  · intro h
    apply output_injective (p ∘ f)
    exact (output_coarsen f p P).trans h

theorem subset_coarsen (f : X → Y) (p : Y → Z) (P : Part f) :
    P.val ⊆ (coarsen f p P).val := by
  intro x hx
  apply (mem_iff (p ∘ f) (coarsen f p P) x).2
  rw [output_coarsen]
  exact congrArg p ((mem_iff f P x).1 hx)

@[simp] theorem coarsen_label (f : X → Y) (p : Y → Z) (x : X) :
    coarsen f p (label f x) = label (p ∘ f) x := by
  apply (coarsen_eq_iff f p _ _).2
  rw [output_label, output_label]
  rfl

theorem coarsen_surjective (f : X → Y) (p : Y → Z) :
    Function.Surjective (coarsen f p) := by
  intro Q
  refine ⟨label f (representative (p ∘ f) Q), ?_⟩
  rw [coarsen_label, label_representative]

theorem card_coarsen_fiber_le [Finite Y] (f : X → Y) (p : Y → Z)
    (Q : Part (p ∘ f)) :
    Nat.card {P : Part f // coarsen f p P = Q} ≤
      Nat.card {y : Y // p y = output (p ∘ f) Q} := by
  let restoreFiber : {P : Part f // coarsen f p P = Q} →
      {y : Y // p y = output (p ∘ f) Q} :=
    fun P => ⟨output f P.val, (coarsen_eq_iff f p P.val Q).1 P.property⟩
  apply Nat.card_le_card_of_injective restoreFiber
  intro P P' h
  apply Subtype.ext
  apply output_injective f
  exact congrArg Subtype.val h

theorem coarsen_at_most_two [Finite Y] (f : X → Y) (p : Y → Z)
    (hp : ∀ z : Z, Nat.card {y : Y // p y = z} ≤ 2)
    (Q : Part (p ∘ f)) :
    Nat.card {P : Part f // coarsen f p P = Q} ≤ 2 :=
  (card_coarsen_fiber_le f p Q).trans (hp (output (p ∘ f) Q))

def binaryDeletionFiberEquiv (y : Y) :
    {v : Bool × Y // v.2 = y} ≃ Bool where
  toFun v := v.val.1
  invFun b := ⟨(b, y), rfl⟩
  left_inv v := by
    apply Subtype.ext
    exact Prod.ext rfl v.property.symm
  right_inv _ := rfl

theorem card_binaryDeletion_fiber (y : Y) :
    Nat.card {v : Bool × Y // v.2 = y} = 2 := by
  rw [Nat.card_congr (binaryDeletionFiberEquiv y), Nat.card_eq_fintype_card]
  exact Fintype.card_bool

theorem binaryDeletion_at_most_two [Finite Y] (f : X → Bool × Y)
    (Q : Part (Prod.snd ∘ f)) :
    Nat.card {P : Part f // coarsen f Prod.snd P = Q} ≤ 2 := by
  apply coarsen_at_most_two f Prod.snd
  intro y
  exact (card_binaryDeletion_fiber y).le

theorem evaluation_consistent_and_satisfying (x : X) :
    (∀ (f : X → Y) (g : X → Z), parts f = parts g →
      (label f x).val = (label g x).val) ∧
    (∀ (f : X → Y) (p : Y → Z),
      coarsen f p (label f x) = label (p ∘ f) x) := by
  exact ⟨fun f g h => label_val_eq_of_parts_eq f g h x,
    fun f p => coarsen_label f p x⟩

end PerfectCompleteness.CanonicalPartition

end

section

namespace PerfectCompleteness.PointwiseSpaces

variable {X Y Z : Type*}

def pullback (𝕜 : Type*) [Field 𝕜] (r : X → Y) :
    (Y → 𝕜) →ₗ[𝕜] (X → 𝕜) where
  toFun f := fun x => f (r x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {𝕜 : Type*} [Field 𝕜]

@[simp] theorem pullback_apply (r : X → Y) (f : Y → 𝕜) (x : X) :
    pullback 𝕜 r f x = f (r x) := rfl

@[simp] theorem pullback_one (r : X → Y) :
    pullback 𝕜 r (1 : Y → 𝕜) = (1 : X → 𝕜) := rfl

@[simp] theorem pullback_mul (r : X → Y) (f g : Y → 𝕜) :
    pullback 𝕜 r (f * g) = pullback 𝕜 r f * pullback 𝕜 r g := rfl

theorem pullback_comp (r : X → Y) (s : Y → Z) :
    (pullback 𝕜 r).comp (pullback 𝕜 s) = pullback 𝕜 (s ∘ r) := by
  ext f x
  rfl

theorem pullback_injective (r : X → Y) (hr : Function.Surjective r) :
    Function.Injective (pullback 𝕜 r) := by
  intro f g h
  funext y
  obtain ⟨x, rfl⟩ := hr y
  exact congrFun h x

def squareSpace (H : Submodule 𝕜 (X → 𝕜)) : Submodule 𝕜 (X → 𝕜) :=
  Submodule.span 𝕜 {u | ∃ f ∈ H, ∃ g ∈ H, f * g = u}

theorem mul_mem_squareSpace (H : Submodule 𝕜 (X → 𝕜))
    {f g : X → 𝕜} (hf : f ∈ H) (hg : g ∈ H) :
    f * g ∈ squareSpace H :=
  Submodule.subset_span ⟨f, hf, g, hg, rfl⟩

theorem squareSpace_mono {H K : Submodule 𝕜 (X → 𝕜)} (h : H ≤ K) :
    squareSpace H ≤ squareSpace K := by
  apply Submodule.span_mono
  rintro u ⟨f, hf, g, hg, rfl⟩
  exact ⟨f, h hf, g, h hg, rfl⟩

theorem le_squareSpace (H : Submodule 𝕜 (X → 𝕜)) (hone : (1 : X → 𝕜) ∈ H) :
    H ≤ squareSpace H := by
  intro f hf
  simpa only [mul_one] using mul_mem_squareSpace H hf hone

theorem one_mem_squareSpace (H : Submodule 𝕜 (X → 𝕜))
    (hone : (1 : X → 𝕜) ∈ H) : (1 : X → 𝕜) ∈ squareSpace H :=
  le_squareSpace H hone hone

theorem squareSpace_pullback_le (r : X → Y)
    (H : Submodule 𝕜 (Y → 𝕜)) (K : Submodule 𝕜 (X → 𝕜))
    (h : H.map (pullback 𝕜 r) ≤ K) :
    (squareSpace H).map (pullback 𝕜 r) ≤ squareSpace K := by
  apply (Submodule.map_span_le _ _ _).2
  rintro u ⟨f, hf, g, hg, rfl⟩
  simpa only [pullback_mul] using mul_mem_squareSpace K
    (h (Submodule.mem_map_of_mem hf)) (h (Submodule.mem_map_of_mem hg))

theorem squareSpace_map_pullback (r : X → Y) (H : Submodule 𝕜 (Y → 𝕜)) :
    (squareSpace H).map (pullback 𝕜 r) = squareSpace (H.map (pullback 𝕜 r)) := by
  apply le_antisymm
  · exact squareSpace_pullback_le r H _ le_rfl
  · apply Submodule.span_le.mpr
    rintro u ⟨f, hf, g, hg, rfl⟩
    obtain ⟨f', hf', rfl⟩ := Submodule.mem_map.mp hf
    obtain ⟨g', hg', rfl⟩ := Submodule.mem_map.mp hg
    exact Submodule.mem_map.mpr ⟨f' * g', mul_mem_squareSpace H hf' hg', rfl⟩

section Children

variable {J : Type*} {D E : J → Type*}

def childSpace (r : ∀ i, X → D i) (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) :
    Submodule 𝕜 (X → 𝕜) :=
  ⨆ i, (squareSpace (H i)).map (pullback 𝕜 (r i))

theorem child_square_le (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) (i : J) :
    (squareSpace (H i)).map (pullback 𝕜 (r i)) ≤ childSpace r H :=
  le_iSup (fun j => (squareSpace (H j)).map (pullback 𝕜 (r j))) i

theorem child_le (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) (i : J)
    (hone : (1 : D i → 𝕜) ∈ H i) :
    (H i).map (pullback 𝕜 (r i)) ≤ childSpace r H := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  exact child_square_le r H i
    (Submodule.mem_map_of_mem (le_squareSpace (H i) hone hg))

theorem one_mem_childSpace_of_child (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) (i : J)
    (hone : (1 : D i → 𝕜) ∈ H i) : (1 : X → 𝕜) ∈ childSpace r H := by
  have h : pullback 𝕜 (r i) (1 : D i → 𝕜) ∈ childSpace r H :=
    child_square_le r H i
      (Submodule.mem_map_of_mem (one_mem_squareSpace (H i) hone))
  simpa only [pullback_one] using h

theorem one_mem_childSpace [Nonempty J] (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜))
    (hone : ∀ i, (1 : D i → 𝕜) ∈ H i) : (1 : X → 𝕜) ∈ childSpace r H := by
  obtain ⟨i⟩ := ‹Nonempty J›
  exact one_mem_childSpace_of_child r H i (hone i)

theorem childSpace_mono (r : ∀ i, X → D i)
    (H K : ∀ i, Submodule 𝕜 (D i → 𝕜)) (h : ∀ i, H i ≤ K i) :
    childSpace r H ≤ childSpace r K := by
  exact iSup_mono (fun i => Submodule.map_mono (squareSpace_mono (h i)))

theorem childSpace_pullback_le (p : X → Y)
    (rY : ∀ i, Y → D i) (rX : ∀ i, X → E i) (q : ∀ i, E i → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) (K : ∀ i, Submodule 𝕜 (E i → 𝕜))
    (hcomm : ∀ i x, q i (rX i x) = rY i (p x))
    (hchild : ∀ i, (H i).map (pullback 𝕜 (q i)) ≤ K i) :
    (childSpace rY H).map (pullback 𝕜 p) ≤ childSpace rX K := by
  simp only [childSpace, Submodule.map_iSup]
  apply iSup_mono
  intro i
  have hcomp : (pullback 𝕜 p).comp (pullback 𝕜 (rY i)) =
      (pullback 𝕜 (rX i)).comp (pullback 𝕜 (q i)) := by
    ext f x
    exact congrArg f (hcomm i x).symm
  calc
    ((squareSpace (H i)).map (pullback 𝕜 (rY i))).map (pullback 𝕜 p) =
        ((squareSpace (H i)).map (pullback 𝕜 (q i))).map (pullback 𝕜 (rX i)) := by
      rw [← Submodule.map_comp, ← Submodule.map_comp, hcomp]
    _ ≤ (squareSpace (K i)).map (pullback 𝕜 (rX i)) :=
      Submodule.map_mono (squareSpace_pullback_le (q i) (H i) (K i) (hchild i))

end Children

end PerfectCompleteness.PointwiseSpaces

end

section

namespace PerfectCompleteness.ProductReduction

variable {I : Type*} {X R W : I → Type*} {Y : Type*}

def productMap (r : ∀ i, X i → R i) (x : ∀ i, X i) : ∀ i, R i :=
  fun i => r i (x i)

@[simp] theorem productMap_apply (r : ∀ i, X i → R i)
    (x : ∀ i, X i) (i : I) : productMap r x i = r i (x i) := rfl

theorem productMap_surjective (r : ∀ i, X i → R i)
    (hr : ∀ i, Function.Surjective (r i)) :
    Function.Surjective (productMap r) := by
  intro z
  refine ⟨fun i => (hr i (z i)).choose, ?_⟩
  funext i
  exact (hr i (z i)).choose_spec

def CoordinateInvariant (r : ∀ i, X i → R i) (f : (∀ i, X i) → Y) : Prop :=
  ∀ (i : I) (x x' : ∀ i, X i),
    (∀ j, j ≠ i → x j = x' j) →
    r i (x i) = r i (x' i) → f x = f x'

theorem coordinateInvariant_of_update [DecidableEq I]
    (r : ∀ i, X i → R i) (f : (∀ i, X i) → Y)
    (hf : ∀ (i : I) (x : ∀ i, X i) (u : X i),
      r i (x i) = r i u → f x = f (Function.update x i u)) :
    CoordinateInvariant r f := by
  intro i x x' hfixed hr
  have hupdate : Function.update x i (x' i) = x' :=
    Function.update_eq_iff.2 ⟨rfl, hfixed⟩
  exact (hf i x (x' i) hr).trans (congrArg f hupdate)

theorem CoordinateInvariant.update [DecidableEq I]
    {r : ∀ i, X i → R i} {f : (∀ i, X i) → Y}
    (hf : CoordinateInvariant r f) (i : I) (x : ∀ i, X i) (u : X i)
    (hr : r i (x i) = r i u) : f x = f (Function.update x i u) := by
  apply hf i x (Function.update x i u)
  · intro j hji
    exact (Function.update_of_ne hji u x).symm
  · simpa only [Function.update_self] using hr

theorem constant_on_product_fibers [Finite I]
    (r : ∀ i, X i → R i) (f : (∀ i, X i) → Y)
    (hf : CoordinateInvariant r f) {x x' : ∀ i, X i}
    (h : productMap r x = productMap r x') : f x = f x' := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hreplace : ∀ s : Finset I, f (s.piecewise x' x) = f x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.piecewise_empty]
    | @insert i s hi ih =>
      have hstep : f ((insert i s).piecewise x' x) = f (s.piecewise x' x) := by
        apply hf i
        · intro j hji
          exact Finset.piecewise_insert_of_ne s x' x hji
        · simp only [Finset.piecewise_insert_self,
            Finset.piecewise_eq_of_notMem s x' x hi]
          exact (congrFun h i).symm
      exact hstep.trans ih
  simpa only [Finset.piecewise_univ] using (hreplace Finset.univ).symm

noncomputable def preimage (r : ∀ i, X i → R i)
    (hr : ∀ i, Function.Surjective (r i)) (z : ∀ i, R i) : ∀ i, X i :=
  (productMap_surjective r hr z).choose

@[simp] theorem productMap_preimage (r : ∀ i, X i → R i)
    (hr : ∀ i, Function.Surjective (r i)) (z : ∀ i, R i) :
    productMap r (preimage r hr z) = z :=
  (productMap_surjective r hr z).choose_spec

noncomputable def induced (r : ∀ i, X i → R i)
    (hr : ∀ i, Function.Surjective (r i)) (f : (∀ i, X i) → Y) :
    (∀ i, R i) → Y :=
  fun z => f (preimage r hr z)

@[simp] theorem induced_productMap [Finite I]
    (r : ∀ i, X i → R i) (hr : ∀ i, Function.Surjective (r i))
    (f : (∀ i, X i) → Y) (hf : CoordinateInvariant r f) (x : ∀ i, X i) :
    induced r hr f (productMap r x) = f x := by
  apply constant_on_product_fibers r f hf
  exact productMap_preimage r hr (productMap r x)

theorem induced_factorization [Finite I]
    (r : ∀ i, X i → R i) (hr : ∀ i, Function.Surjective (r i))
    (f : (∀ i, X i) → Y) (hf : CoordinateInvariant r f) :
    f = induced r hr f ∘ productMap r := by
  funext x
  exact (induced_productMap r hr f hf x).symm

theorem induced_unique (r : ∀ i, X i → R i)
    (hr : ∀ i, Function.Surjective (r i)) (f : (∀ i, X i) → Y)
    (g : (∀ i, R i) → Y) (hg : ∀ x, g (productMap r x) = f x) :
    g = induced r hr f := by
  funext z
  calc
    g z = g (productMap r (preimage r hr z)) :=
      congrArg g (productMap_preimage r hr z).symm
    _ = f (preimage r hr z) := hg (preimage r hr z)
    _ = induced r hr f z := rfl

theorem coordinateInvariant_pullback
    (p : ∀ i, X i → W i) (r : ∀ i, W i → R i)
    (g : (∀ i, W i) → Y) (hg : CoordinateInvariant r g) :
    CoordinateInvariant (fun i => r i ∘ p i) (g ∘ productMap p) := by
  intro i x x' hfixed hr
  apply hg i (productMap p x) (productMap p x')
  · intro j hji
    exact congrArg (p j) (hfixed j hji)
  · exact hr

theorem induced_eq_of_pullback [Finite I]
    (p : ∀ i, X i → W i)
    (rX : ∀ i, X i → R i) (rW : ∀ i, W i → R i)
    (hrX : ∀ i, Function.Surjective (rX i))
    (hrW : ∀ i, Function.Surjective (rW i))
    (hcomm : ∀ i x, rX i x = rW i (p i x))
    (f : (∀ i, X i) → Y) (g : (∀ i, W i) → Y)
    (hg : CoordinateInvariant rW g)
    (hfg : ∀ x, f x = g (productMap p x)) :
    induced rX hrX f = induced rW hrW g := by
  symm
  apply induced_unique rX hrX f
  intro x
  have hmap : productMap rX x = productMap rW (productMap p x) := by
    funext i
    exact hcomm i (x i)
  rw [hmap, induced_productMap rW hrW g hg]
  exact (hfg x).symm

end PerfectCompleteness.ProductReduction

end

section

namespace PerfectCompleteness.ProjectedColumnSlice

noncomputable section

variable {𝕜 H H' W : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup H'] [Module 𝕜 H']
  [AddCommGroup W] [Module 𝕜 W]
  (i : H' →ₗ[𝕜] H) (Z : Submodule 𝕜 (Module.Dual 𝕜 H))

def projectedColumns : Submodule 𝕜 (Module.Dual 𝕜 H') := Z.map i.dualMap

def restrictionZ : Z →ₗ[𝕜] projectedColumns i Z :=
  (i.dualMap.comp Z.subtype).codRestrict (projectedColumns i Z) (by
    intro z
    exact Submodule.mem_map.mpr ⟨z.val, z.property, rfl⟩)

@[simp] theorem restrictionZ_val (z : Z) :
    (restrictionZ i Z z : Module.Dual 𝕜 H') = i.dualMap z := rfl

@[simp] theorem restrictionZ_apply (z : Z) (h : H') :
    (restrictionZ i Z z : Module.Dual 𝕜 H') h = z.val (i h) := rfl

theorem restrictionZ_surjective : Function.Surjective (restrictionZ i Z) := by
  intro q
  obtain ⟨z, hz, heq⟩ := Submodule.mem_map.mp q.property
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  exact heq

theorem finrank_projectedColumns_le [FiniteDimensional 𝕜 Z] :
    Module.finrank 𝕜 (projectedColumns i Z) ≤ Module.finrank 𝕜 Z :=
  Submodule.finrank_map_le i.dualMap Z

def Compatible (v : Z →ₗ[𝕜] W) (X : Module.Dual 𝕜 H' →ₗ[𝕜] W) : Prop :=
  ∀ z : Z, X (i.dualMap z) = v z

def targetQ (X₀ : Module.Dual 𝕜 H' →ₗ[𝕜] W) : projectedColumns i Z →ₗ[𝕜] W :=
  X₀.domRestrict (projectedColumns i Z)

@[simp] theorem targetQ_apply (X₀ : Module.Dual 𝕜 H' →ₗ[𝕜] W)
    (q : projectedColumns i Z) : targetQ i Z X₀ q = X₀ q.val := rfl

theorem targetQ_comp_restrictionZ (v : Z →ₗ[𝕜] W)
    (X₀ : Module.Dual 𝕜 H' →ₗ[𝕜] W) (h₀ : Compatible i Z v X₀) :
    (targetQ i Z X₀).comp (restrictionZ i Z) = v := by
  apply LinearMap.ext
  exact h₀

theorem targetQ_independent (v : Z →ₗ[𝕜] W)
    (X₀ X₁ : Module.Dual 𝕜 H' →ₗ[𝕜] W)
    (h₀ : Compatible i Z v X₀) (h₁ : Compatible i Z v X₁) :
    targetQ i Z X₀ = targetQ i Z X₁ := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := restrictionZ_surjective i Z q
  exact (h₀ z).trans (h₁ z).symm

theorem compatible_iff_domRestrict (v : Z →ₗ[𝕜] W)
    (X₀ : Module.Dual 𝕜 H' →ₗ[𝕜] W) (h₀ : Compatible i Z v X₀)
    (X : Module.Dual 𝕜 H' →ₗ[𝕜] W) :
    Compatible i Z v X ↔ X.domRestrict (projectedColumns i Z) = targetQ i Z X₀ := by
  constructor
  · intro hX
    exact targetQ_independent i Z v X X₀ hX h₀
  · intro hX z
    have hz := LinearMap.congr_fun hX (restrictionZ i Z z)
    exact hz.trans (h₀ z)

theorem target_unique (v : Z →ₗ[𝕜] W)
    (t₀ t₁ : projectedColumns i Z →ₗ[𝕜] W)
    (h₀ : t₀.comp (restrictionZ i Z) = v)
    (h₁ : t₁.comp (restrictionZ i Z) = v) : t₀ = t₁ := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := restrictionZ_surjective i Z q
  exact (LinearMap.congr_fun h₀ z).trans (LinearMap.congr_fun h₁ z).symm

def inducedTarget (v : Z →ₗ[𝕜] W)
    (hne : ∃ X : Module.Dual 𝕜 H' →ₗ[𝕜] W, Compatible i Z v X) :
    projectedColumns i Z →ₗ[𝕜] W :=
  targetQ i Z (Classical.choose hne)

theorem inducedTarget_comp_restrictionZ (v : Z →ₗ[𝕜] W)
    (hne : ∃ X : Module.Dual 𝕜 H' →ₗ[𝕜] W, Compatible i Z v X) :
    (inducedTarget i Z v hne).comp (restrictionZ i Z) = v :=
  targetQ_comp_restrictionZ i Z v (Classical.choose hne) (Classical.choose_spec hne)

theorem inducedTarget_eq_targetQ (v : Z →ₗ[𝕜] W)
    (hne : ∃ X : Module.Dual 𝕜 H' →ₗ[𝕜] W, Compatible i Z v X)
    (X₀ : Module.Dual 𝕜 H' →ₗ[𝕜] W) (h₀ : Compatible i Z v X₀) :
    inducedTarget i Z v hne = targetQ i Z X₀ :=
  targetQ_independent i Z v (Classical.choose hne) X₀ (Classical.choose_spec hne) h₀

theorem compatible_iff_inducedTarget (v : Z →ₗ[𝕜] W)
    (hne : ∃ X : Module.Dual 𝕜 H' →ₗ[𝕜] W, Compatible i Z v X)
    (X : Module.Dual 𝕜 H' →ₗ[𝕜] W) :
    Compatible i Z v X ↔
      X.domRestrict (projectedColumns i Z) = inducedTarget i Z v hne :=
  compatible_iff_domRestrict i Z v (Classical.choose hne) (Classical.choose_spec hne) X

def sliceEquiv (v : Z →ₗ[𝕜] W)
    (hne : ∃ X : Module.Dual 𝕜 H' →ₗ[𝕜] W, Compatible i Z v X) :
    {X : Module.Dual 𝕜 H' →ₗ[𝕜] W // Compatible i Z v X} ≃
      {X : Module.Dual 𝕜 H' →ₗ[𝕜] W //
        X.domRestrict (projectedColumns i Z) = inducedTarget i Z v hne} where
  toFun X := ⟨X.val, (compatible_iff_inducedTarget i Z v hne X.val).mp X.property⟩
  invFun X := ⟨X.val, (compatible_iff_inducedTarget i Z v hne X.val).mpr X.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end PerfectCompleteness.ProjectedColumnSlice

end

section

namespace PerfectCompleteness.PulledColumnSpace

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {H : Type*} [AddCommGroup H] [Module F2 H]

def pulled (W : Submodule F2 H) (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) :
    Submodule F2 (Module.Dual F2 H) :=
  C.map W.mkQ.dualMap

theorem quotientDual_injective (W : Submodule F2 H) :
    Function.Injective W.mkQ.dualMap :=
  LinearMap.dualMap_injective_of_surjective W.mkQ_surjective

def pulledEquiv (W : Submodule F2 H) (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) :
    C ≃ₗ[F2] pulled W C :=
  Submodule.equivMapOfInjective W.mkQ.dualMap (quotientDual_injective W) C

@[simp] theorem pulledEquiv_val (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (q : C) :
    (pulledEquiv W C q : Module.Dual F2 H) = q.val.comp W.mkQ := rfl

theorem pulled_le_annihilator (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) :
    pulled W C ≤ W.dualAnnihilator := by
  rintro q ⟨p, hp, rfl⟩
  apply (Submodule.mem_dualAnnihilator (W := W) _).mpr
  intro w hw
  change p (W.mkQ w) = 0
  have hwzero : W.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hw
  rw [hwzero, map_zero]

theorem finrank_pulled (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) :
    Module.finrank F2 (pulled W C) = Module.finrank F2 C :=
  (pulledEquiv W C).finrank_eq.symm

theorem finrank_pulled_le (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) {r : Nat}
    (hC : Module.finrank F2 C ≤ r) : Module.finrank F2 (pulled W C) ≤ r := by
  rw [finrank_pulled]
  exact hC

def Candidates (W : Submodule F2 H) (C : Submodule F2 (Module.Dual F2 (H ⧸ W)))
    (center : Module.Dual F2 H) :=
  {q : Module.Dual F2 H // q - center ∈ pulled W C}

instance candidatesNonempty (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H) :
    Nonempty (Candidates W C center) := ⟨⟨center, by
      rw [sub_self]
      exact (pulled W C).zero_mem⟩⟩

def candidateEquiv (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H) :
    pulled W C ≃ Candidates W C center where
  toFun q := ⟨center + q.val, by
    have he : center + q.val - center = q.val := by abel
    rw [he]
    exact q.property⟩
  invFun q := ⟨q.val - center, q.property⟩
  left_inv q := by
    apply Subtype.ext
    change center + q.val - center = q.val
    abel
  right_inv q := by
    apply Subtype.ext
    change center + (q.val - center) = q.val
    abel

@[simp] theorem candidateEquiv_val (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H)
    (q : pulled W C) :
    (candidateEquiv W C center q).val = center + q.val := rfl

theorem candidate_apply_known (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H)
    (q : Candidates W C center) (w : W) : q.val w = center w := by
  have hq := (Submodule.mem_dualAnnihilator (W := W) (q.val - center)).mp
    (pulled_le_annihilator W C q.property) w w.property
  change q.val w - center w = 0 at hq
  exact sub_eq_zero.mp hq

variable [FiniteDimensional F2 H]

theorem card_pulled (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) :
    Nat.card (pulled W C) = 2 ^ Module.finrank F2 C := by
  rw [Module.natCard_eq_pow_finrank (K := F2), finrank_pulled]
  rw [show Nat.card F2 = 2 from Nat.card_zmod 2]

theorem card_pulled_le (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) {r : Nat}
    (hC : Module.finrank F2 C ≤ r) : Nat.card (pulled W C) ≤ 2 ^ r := by
  rw [card_pulled]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hC

def candidatesEquivCoordinates (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H) :
    Candidates W C center ≃ (Fin (Module.finrank F2 C) → F2) := by
  let : Module.Free F2 C := Module.Free.of_divisionRing F2 C
  exact (candidateEquiv W C center).symm.trans
    ((pulledEquiv W C).symm.toEquiv.trans (Module.finBasis F2 C).equivFun.toEquiv)

instance candidatesFintype (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H) :
    Fintype (Candidates W C center) :=
  Fintype.ofEquiv (Fin (Module.finrank F2 C) → F2)
    (candidatesEquivCoordinates W C center).symm

theorem card_candidates (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H) :
    Nat.card (Candidates W C center) = 2 ^ Module.finrank F2 C :=
  (Nat.card_congr (candidateEquiv W C center)).symm.trans (card_pulled W C)

theorem card_candidates_le (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H)
    {r : Nat} (hC : Module.finrank F2 C ≤ r) :
    Nat.card (Candidates W C center) ≤ 2 ^ r := by
  rw [card_candidates]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hC

theorem fintype_card_candidates (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H) :
    Fintype.card (Candidates W C center) = 2 ^ Module.finrank F2 C := by
  rw [← Nat.card_eq_fintype_card]
  exact card_candidates W C center

end
end PerfectCompleteness.PulledColumnSpace

end

end OAI
