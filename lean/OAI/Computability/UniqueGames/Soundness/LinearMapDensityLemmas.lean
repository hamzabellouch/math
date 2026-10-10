import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Std
import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas
import OAI.Computability.UniqueGames.Soundness.ExpectationComparisonLemmas

namespace OAI

section

/-!
The exact combined-map density formula of Lemma 6.3 for genuine finite-dimensional
binary linear maps. Subspaces are supplied as kernels; their annihilator counts
and all normalized first and second moments are proved, not assumed.
-/

namespace UniqueGamesTheorem.Soundness.LinearMapDensity

open scoped BigOperators

universe u v w

variable {E : Type u} {R : Type v}
variable [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
variable [AddCommGroup R] [Module (ZMod 2) R] [FiniteDimensional (ZMod 2) R]

noncomputable def uniformMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  Finset.expect Finset.univ f

theorem uniformMean_eq_sum_div_card {α : Type*} [Fintype α] (f : α → ℝ) :
    uniformMean f = (∑ a, f a) / (Fintype.card α : ℝ) := by
  simp [uniformMean, Finset.expect_eq_sum_div_card]

theorem uniformMean_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) :=
  Finset.expect_comm _ _ _

theorem uniformMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f :=
  (Finset.mul_expect _ _ _).symm

theorem uniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c :=
  Fintype.expect_const _

omit [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) R] in
theorem restriction_surjective (K : Submodule (ZMod 2) E) :
    Function.Surjective (LinearMap.domRestrict' (M₂ := R) K) := by
  intro f
  obtain ⟨g, hg⟩ := f.exists_extend
  exact ⟨g, hg⟩

omit [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) R] in
theorem restriction_zero_iff (K : Submodule (ZMod 2) E) (M : E →ₗ[ZMod 2] R) :
    LinearMap.domRestrict' K M = 0 ↔ K ≤ M.ker := by
  constructor
  · intro h x hx
    have := LinearMap.congr_fun h (⟨x, hx⟩ : K)
    exact this
  · intro h
    ext x
    exact h x.property

/-- Pulling back a map along a projection produces a map annihilating its kernel. -/
def pullbackMap {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (π : E →ₗ[ZMod 2] V) (B : V →ₗ[ZMod 2] R) :
    {M : E →ₗ[ZMod 2] R // π.ker ≤ M.ker} :=
  ⟨B.comp π, by
    intro x hx
    change B (π x) = 0
    change π x = 0 at hx
    rw [hx, map_zero]⟩

omit [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) R] in
/-- The pullback map is a bijection onto the genuine kernel-annihilator event.
This connects the density calculation to uniform maps on the partner space. -/
theorem pullbackMap_bijective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (π : E →ₗ[ZMod 2] V) (hπ : Function.Surjective π) :
    Function.Bijective (pullbackMap (R := R) π) := by
  constructor
  · intro B C h
    ext y
    obtain ⟨x, rfl⟩ := hπ y
    exact LinearMap.congr_fun (congrArg Subtype.val h) x
  · intro M
    obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
    refine ⟨M.val.comp s, ?_⟩
    apply Subtype.ext
    ext x
    change M.val (s (π x)) = M.val x
    have hx : x - s (π x) ∈ π.ker := by
      have hsx := LinearMap.congr_fun hs (π x)
      change π (s (π x)) = π x at hsx
      change π (x - s (π x)) = 0
      rw [map_sub, hsx, sub_self]
    have hz : M.val (x - s (π x)) = 0 := M.property hx
    rw [map_sub] at hz
    exact (sub_eq_zero.mp hz).symm

theorem annihilator_count [Fintype (E →ₗ[ZMod 2] R)] (K : Submodule (ZMod 2) E) :
    Nat.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} *
      2 ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) =
        Fintype.card (E →ₗ[ZMod 2] R) := by
  classical
  let restriction := LinearMap.domRestrict' (M₂ := R) K
  have h := Gadget.LinearKernelCount.zero_event_card_mul_pow_rank restriction
  have hrange : restriction.range = ⊤ :=
    LinearMap.range_eq_top.mpr (restriction_surjective K)
  have hcard : Nat.card {M : E →ₗ[ZMod 2] R // restriction M = 0} =
      Nat.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} :=
    Nat.card_congr (Equiv.subtypeEquivRight (restriction_zero_iff K))
  rw [hcard, hrange, finrank_top, Module.finrank_linearMap] at h
  simpa only [Nat.card_eq_fintype_card, Nat.mul_comm] using h

noncomputable def kernelDensity (K : Submodule (ZMod 2) E)
    (M : E →ₗ[ZMod 2] R) : ℝ := by
  classical
  exact if K ≤ M.ker then (2 : ℝ) ^
    (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) else 0

theorem kernelDensity_mean [Fintype (E →ₗ[ZMod 2] R)]
    (K : Submodule (ZMod 2) E) : uniformMean (kernelDensity (R := R) K) = 1 := by
  classical
  have hc := annihilator_count (R := R) K
  have hreal : (Nat.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} : ℝ) *
      (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) =
        Fintype.card (E →ₗ[ZMod 2] R) := by exact_mod_cast hc
  rw [uniformMean_eq_sum_div_card]
  have hsum : (∑ M : E →ₗ[ZMod 2] R, kernelDensity K M) =
      (Nat.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} : ℝ) *
        (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) := by
    simp [kernelDensity, Nat.card_eq_fintype_card, Fintype.card_subtype,
      ← Finset.sum_filter]
  rw [hsum, hreal]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

omit [FiniteDimensional (ZMod 2) R] in
/-- Pointwise overlap formula, using the actual dimension formula for subspaces. -/
theorem kernelDensity_product (K L : Submodule (ZMod 2) E)
    (M : E →ₗ[ZMod 2] R) :
    kernelDensity K M * kernelDensity L M =
      (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊓ L : Submodule (ZMod 2) E)) *
        kernelDensity (K ⊔ L) M := by
  classical
  have hd := K.finrank_sup_add_finrank_inf_eq L
  have hexp :
      Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K +
        Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) L =
      Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊓ L : Submodule (ZMod 2) E) +
        Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊔ L : Submodule (ZMod 2) E) := by
    have hm := congrArg (fun n => Module.finrank (ZMod 2) R * n) hd.symm
    simpa [Nat.mul_add, Nat.add_comm] using hm
  have hp :
      (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) *
        2 ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) L) =
      (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊓ L : Submodule (ZMod 2) E)) *
        2 ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊔ L : Submodule (ZMod 2) E)) := by
    rw [← pow_add, ← pow_add, hexp]
  by_cases hK : K ≤ M.ker <;> by_cases hL : L ≤ M.ker <;>
    simp [kernelDensity, sup_le_iff, hK, hL, hp]

/-- The two-kernel second-moment identity for the uniform law on all genuine
linear maps E→R. No annihilator probability is a hypothesis. -/
theorem kernelDensity_pair_mean [Fintype (E →ₗ[ZMod 2] R)]
    (K L : Submodule (ZMod 2) E) :
    uniformMean (fun M : E →ₗ[ZMod 2] R => kernelDensity K M * kernelDensity L M) =
      (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊓ L : Submodule (ZMod 2) E)) := by
  simp_rw [kernelDensity_product]
  rw [uniformMean_const_mul, kernelDensity_mean, mul_one]

noncomputable def mixtureDensity {Partner : Type w} [Fintype Partner]
    (kernels : Partner → Submodule (ZMod 2) E) (M : E →ₗ[ZMod 2] R) : ℝ :=
  uniformMean (fun p => kernelDensity (kernels p) M)

theorem mixtureDensity_mean {Partner : Type w} [Fintype Partner] [Nonempty Partner]
    [Fintype (E →ₗ[ZMod 2] R)] (kernels : Partner → Submodule (ZMod 2) E) :
    uniformMean (mixtureDensity (R := R) kernels) = 1 := by
  unfold mixtureDensity
  rw [uniformMean_comm]
  simp_rw [kernelDensity_mean]
  exact uniformMean_const 1

/-- Lemma 6.3's exact second-moment identity for an arbitrary finite uniform
list of genuine kernel subspaces. The two partner indices are independent
because the right side is an iterated uniform expectation. -/
theorem mixtureDensity_second_moment {Partner : Type w} [Fintype Partner]
    [Fintype (E →ₗ[ZMod 2] R)] (kernels : Partner → Submodule (ZMod 2) E) :
    uniformMean (fun M : E →ₗ[ZMod 2] R => (mixtureDensity kernels M) ^ 2) =
      uniformMean (fun p => uniformMean (fun q => (2 : ℝ) ^
        (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(kernels p ⊓ kernels q : Submodule (ZMod 2) E)))) := by
  have hexpand (M : E →ₗ[ZMod 2] R) :
      (mixtureDensity kernels M) ^ 2 =
        uniformMean (fun p => uniformMean (fun q =>
          kernelDensity (kernels p) M * kernelDensity (kernels q) M)) := by
    simpa [mixtureDensity, uniformMean, pow_two] using
      (Fintype.expect_mul_expect (fun p => kernelDensity (kernels p) M)
        (fun q => kernelDensity (kernels q) M))
  simp_rw [hexpand]
  rw [uniformMean_comm]
  congr 1
  funext p
  rw [uniformMean_comm]
  simp_rw [kernelDensity_pair_mean]

theorem kernelDensity_weighted_mean [Fintype (E →ₗ[ZMod 2] R)]
    (K : Submodule (ZMod 2) E)
    [Fintype {M : E →ₗ[ZMod 2] R // K ≤ M.ker}]
    (H : (E →ₗ[ZMod 2] R) → ℝ) :
    uniformMean (fun M => kernelDensity K M * H M) =
      uniformMean (fun M : {M : E →ₗ[ZMod 2] R // K ≤ M.ker} => H M.val) := by
  classical
  let c : ℝ := (2 : ℝ) ^
    (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K)
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hcount :
      Fintype.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} *
        2 ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) =
      Fintype.card (E →ₗ[ZMod 2] R) := by
    simpa only [Nat.card_eq_fintype_card] using annihilator_count (R := R) K
  have hr : (Fintype.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} : ℝ) * c =
      (Fintype.card (E →ₗ[ZMod 2] R) : ℝ) := by
    dsimp [c]
    exact_mod_cast hcount
  have hdenom : (Fintype.card (E →ₗ[ZMod 2] R) : ℝ) =
      c * (Fintype.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} : ℝ) := by
    simpa only [mul_comm] using hr.symm
  have hsum : (∑ M : E →ₗ[ZMod 2] R, kernelDensity K M * H M) =
      c * ∑ M : {M : E →ₗ[ZMod 2] R // K ≤ M.ker}, H M.val := by
    simp only [kernelDensity, ite_mul, zero_mul]
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_subtype _ (fun M => by simp) H
  rw [uniformMean_eq_sum_div_card, uniformMean_eq_sum_div_card, hsum, hdenom]
  exact mul_div_mul_left _ _ hc

theorem pullback_uniformMean {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype (E →ₗ[ZMod 2] R)] [Fintype (V →ₗ[ZMod 2] R)]
    (π : E →ₗ[ZMod 2] V) (hπ : Function.Surjective π)
    (H : (E →ₗ[ZMod 2] R) → ℝ) :
    uniformMean (fun B : V →ₗ[ZMod 2] R => H (B.comp π)) =
      uniformMean (fun M => kernelDensity π.ker M * H M) := by
  classical
  rw [kernelDensity_weighted_mean]
  exact Fintype.expect_bijective (pullbackMap (R := R) π)
    (pullbackMap_bijective (R := R) π hπ) _ _ (fun _ => rfl)

theorem mixture_pullback_uniformMean {Partner : Type*} [Fintype Partner]
    {V : Partner → Type*} [∀ p, AddCommGroup (V p)] [∀ p, Module (ZMod 2) (V p)]
    [Fintype (E →ₗ[ZMod 2] R)] [∀ p, Fintype (V p →ₗ[ZMod 2] R)]
    (π : ∀ p, E →ₗ[ZMod 2] V p) (hπ : ∀ p, Function.Surjective (π p))
    (H : (E →ₗ[ZMod 2] R) → ℝ) :
    uniformMean (fun p => uniformMean (fun B : V p →ₗ[ZMod 2] R => H (B.comp (π p)))) =
    uniformMean (fun M => mixtureDensity (fun p => (π p).ker) M * H M) := by
  have hp (p : Partner) :
      uniformMean (fun B : V p →ₗ[ZMod 2] R => H (B.comp (π p))) =
      uniformMean (fun M : E →ₗ[ZMod 2] R => kernelDensity (π p).ker M * H M) :=
    pullback_uniformMean (π p) (hπ p) H
  simp_rw [hp]
  rw [uniformMean_comm]
  congr 1
  funext M
  exact (Finset.expect_mul Finset.univ (fun p => kernelDensity (π p).ker M) (H M)).symm

end UniqueGamesTheorem.Soundness.LinearMapDensity

end

section

namespace UniqueGamesTheorem.Soundness.PartnerProjection

inductive Slot where
  | first | second | third
  deriving DecidableEq, Repr

structure Triple where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq, Repr

def zeroTriple : Triple := ⟨false, false, false⟩

def parity (x : Triple) : Bool := (x.first.xor x.second).xor x.third

def addTriple (x y : Triple) : Triple :=
  ⟨x.first.xor y.first, x.second.xor y.second, x.third.xor y.third⟩

theorem parity_add (x y : Triple) :
    parity (addTriple x y) = (parity x).xor (parity y) := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem and_xor (b h h' : Bool) :
    (b && h).xor (b && h') = (b && h.xor h') := by
  cases b <;> cases h <;> cases h' <;> decide

def retained (s : Slot) (x : Triple) : Bool :=
  match s with
  | .first => x.first
  | .second => x.second
  | .third => x.third

def freeBit (s : Slot) (x : Triple) : Bool :=
  match s with
  | .first => x.second
  | .second => x.first
  | .third => x.first

theorem retained_add (s : Slot) (x y : Triple) :
    retained s (addTriple x y) = (retained s x).xor (retained s y) := by
  cases s <;> rfl

theorem freeBit_add (s : Slot) (x y : Triple) :
    freeBit s (addTriple x y) = (freeBit s x).xor (freeBit s y) := by
  cases s <;> rfl

/-- Reconstruct a parity-constrained triple from its retained bit and one free bit. -/
def complete (s : Slot) (p r f : Bool) : Triple :=
  match s with
  | .first => ⟨r, f, (p.xor r).xor f⟩
  | .second => ⟨f, r, (p.xor r).xor f⟩
  | .third => ⟨f, (p.xor r).xor f, r⟩

theorem parity_complete (s : Slot) (p r f : Bool) :
    parity (complete s p r f) = p := by
  cases s <;> cases p <;> cases r <;> cases f <;> decide

theorem retained_complete (s : Slot) (p r f : Bool) :
    retained s (complete s p r f) = r := by
  cases s <;> rfl

theorem freeBit_complete (s : Slot) (p r f : Bool) :
    freeBit s (complete s p r f) = f := by
  cases s <;> rfl

theorem complete_coordinates (s : Slot) (x : Triple) :
    complete s (parity x) (retained s x) (freeBit s x) = x := by
  rcases x with ⟨a, b, c⟩
  cases s <;> cases a <;> cases b <;> cases c <;> decide

theorem retained_zero (s : Slot) : retained s zeroTriple = false := by
  cases s <;> rfl

theorem freeBit_zero (s : Slot) : freeBit s zeroTriple = false := by
  cases s <;> rfl

theorem complete_zero (s : Slot) : complete s false false false = zeroTriple := by
  cases s <;> rfl

theorem complete_kernel_add (s : Slot) (a b : Bool) :
    complete s false false (a.xor b) =
      addTriple (complete s false false a) (complete s false false b) := by
  cases s <;> cases a <;> cases b <;> decide

variable {Position : Type} (rhs active : Position → Bool) (slot : Position → Slot)

structure SourcePoint where
  homogeneous : Bool
  coordinates : Position → Triple
  valid : ∀ j, parity (coordinates j) = (rhs j && homogeneous)

structure PartnerPoint where
  homogeneous : Bool
  full : Position → Triple
  single : Position → Bool
  full_zero : ∀ j, active j = true → full j = zeroTriple
  full_valid : ∀ j, active j = false → parity (full j) = (rhs j && homogeneous)
  single_zero : ∀ j, active j = false → single j = false

theorem source_ext {x y : SourcePoint rhs}
    (hh : x.homogeneous = y.homogeneous) (hx : x.coordinates = y.coordinates) : x = y := by
  cases x
  cases y
  cases hh
  cases hx
  rfl

theorem partner_ext {x y : PartnerPoint rhs active}
    (hh : x.homogeneous = y.homogeneous) (hf : x.full = y.full)
    (hs : x.single = y.single) : x = y := by
  cases x
  cases y
  cases hh
  cases hf
  cases hs
  rfl

def project (x : SourcePoint rhs) : PartnerPoint rhs active where
  homogeneous := x.homogeneous
  full := fun j => if active j then zeroTriple else x.coordinates j
  single := fun j => if active j then retained (slot j) (x.coordinates j) else false
  full_zero := by intro j hj; simp [hj]
  full_valid := by intro j hj; simpa [hj] using x.valid j
  single_zero := by intro j hj; simp [hj]

/-- The constructive preimage used in Lemma 6.1: choose the free bit to be zero. -/
def lift (y : PartnerPoint rhs active) : SourcePoint rhs where
  homogeneous := y.homogeneous
  coordinates := fun j =>
    if active j then complete (slot j) (rhs j && y.homogeneous) (y.single j) false
    else y.full j
  valid := by
    intro j
    cases hj : active j with
    | false => simpa [hj] using y.full_valid j hj
    | true => simp [parity_complete]

theorem project_lift (y : PartnerPoint rhs active) :
    project rhs active slot (lift rhs active slot y) = y := by
  apply partner_ext
  · rfl
  · funext j
    cases hj : active j with
    | false => simp [project, lift, hj]
    | true => simpa [project, hj] using (y.full_zero j hj).symm
  · funext j
    cases hj : active j with
    | false => simpa [project, hj] using (y.single_zero j hj).symm
    | true => simp [project, lift, hj, retained_complete]

theorem project_surjective :
    ∀ y : PartnerPoint rhs active, ∃ x : SourcePoint rhs, project rhs active slot x = y := by
  intro y
  exact ⟨lift rhs active slot y, project_lift rhs active slot y⟩

theorem homogeneous_preserved (x : SourcePoint rhs) :
    (project rhs active slot x).homogeneous = x.homogeneous := rfl

def zeroSource : SourcePoint rhs where
  homogeneous := false
  coordinates := fun _ => zeroTriple
  valid := by intro j; simp [parity, zeroTriple]

def zeroPartner : PartnerPoint rhs active where
  homogeneous := false
  full := fun _ => zeroTriple
  single := fun _ => false
  full_zero := by intros; rfl
  full_valid := by intros; simp [parity, zeroTriple]
  single_zero := by intros; rfl

def addSource (x y : SourcePoint rhs) : SourcePoint rhs where
  homogeneous := x.homogeneous.xor y.homogeneous
  coordinates := fun j => addTriple (x.coordinates j) (y.coordinates j)
  valid := by
    intro j
    rw [parity_add, x.valid, y.valid, and_xor]

def addPartner (x y : PartnerPoint rhs active) : PartnerPoint rhs active where
  homogeneous := x.homogeneous.xor y.homogeneous
  full := fun j => addTriple (x.full j) (y.full j)
  single := fun j => (x.single j).xor (y.single j)
  full_zero := by
    intro j hj
    rw [x.full_zero j hj, y.full_zero j hj]
    rfl
  full_valid := by
    intro j hj
    rw [parity_add, x.full_valid j hj, y.full_valid j hj, and_xor]
  single_zero := by
    intro j hj
    rw [x.single_zero j hj, y.single_zero j hj]
    rfl

/-- The projection preserves F₂ addition, as well as zero. -/
theorem project_add (x y : SourcePoint rhs) :
    project rhs active slot (addSource rhs x y) =
      addPartner rhs active (project rhs active slot x) (project rhs active slot y) := by
  apply partner_ext
  · rfl
  · funext j
    cases hj : active j <;> simp [project, addSource, addPartner, hj, addTriple, zeroTriple]
  · funext j
    cases hj : active j <;> simp [project, addSource, addPartner, hj, retained_add]

theorem project_zero :
    project rhs active slot (zeroSource rhs) = zeroPartner rhs active := by
  apply partner_ext
  · rfl
  · funext j
    cases active j <;> simp [project, zeroSource, zeroPartner]
  · funext j
    cases active j <;> simp [project, zeroSource, zeroPartner, retained_zero]

def InKernel (x : SourcePoint rhs) : Prop :=
  project rhs active slot x = zeroPartner rhs active

theorem kernel_characterization (x : SourcePoint rhs) :
    InKernel rhs active slot x ↔
      x.homogeneous = false ∧
      (∀ j, active j = false → x.coordinates j = zeroTriple) ∧
      (∀ j, active j = true → retained (slot j) (x.coordinates j) = false) := by
  constructor
  · intro hx
    refine ⟨congrArg PartnerPoint.homogeneous hx, ?_, ?_⟩
    · intro j hj
      have h := congrArg (fun y : PartnerPoint rhs active => y.full j) hx
      simpa [project, zeroPartner, hj] using h
    · intro j hj
      have h := congrArg (fun y : PartnerPoint rhs active => y.single j) hx
      simpa [project, zeroPartner, hj] using h
  · rintro ⟨hh, hf, hs⟩
    apply partner_ext
    · exact hh
    · funext j
      cases hj : active j with
      | false => simpa [project, zeroPartner, hj] using hf j hj
      | true => simp [project, zeroPartner, hj]
    · funext j
      cases hj : active j with
      | false => simp [project, zeroPartner, hj]
      | true => simpa [project, zeroPartner, hj] using hs j hj

/-- One coefficient bit at every active position; all other coefficients vanish. -/
structure ActiveBits where
  coefficient : Position → Bool
  inactive_zero : ∀ j, active j = false → coefficient j = false

theorem activeBits_ext {a b : ActiveBits active}
    (h : a.coefficient = b.coefficient) : a = b := by
  cases a
  cases b
  cases h
  rfl

def addActiveBits (a b : ActiveBits active) : ActiveBits active where
  coefficient := fun j => (a.coefficient j).xor (b.coefficient j)
  inactive_zero := by
    intro j hj
    rw [a.inactive_zero j hj, b.inactive_zero j hj]
    rfl

def kernelPoint (a : ActiveBits active) : SourcePoint rhs where
  homogeneous := false
  coordinates := fun j => complete (slot j) false false (a.coefficient j)
  valid := by intro j; simp [parity_complete]

theorem kernelPoint_add (a b : ActiveBits active) :
    kernelPoint rhs active slot (addActiveBits active a b) =
      addSource rhs (kernelPoint rhs active slot a) (kernelPoint rhs active slot b) := by
  apply source_ext
  · rfl
  · funext j
    exact complete_kernel_add _ _ _

theorem kernelPoint_mem (a : ActiveBits active) :
    InKernel rhs active slot (kernelPoint rhs active slot a) := by
  apply (kernel_characterization rhs active slot _).2
  refine ⟨rfl, ?_, ?_⟩
  · intro j hj
    simp [kernelPoint, a.inactive_zero j hj, complete_zero]
  · intro j _
    exact retained_complete _ _ _ _

def kernelCoefficients (x : SourcePoint rhs) (hx : InKernel rhs active slot x) :
    ActiveBits active where
  coefficient := fun j => freeBit (slot j) (x.coordinates j)
  inactive_zero := by
    intro j hj
    have hf := (kernel_characterization rhs active slot x).1 hx |>.2.1 j hj
    rw [hf, freeBit_zero]

theorem kernelPoint_coefficients (x : SourcePoint rhs) (hx : InKernel rhs active slot x) :
    kernelPoint rhs active slot (kernelCoefficients rhs active slot x hx) = x := by
  have hc := (kernel_characterization rhs active slot x).1 hx
  apply source_ext
  · exact hc.1.symm
  · funext j
    have hp : parity (x.coordinates j) = false := by
      rw [x.valid j, hc.1]
      simp
    have hr : retained (slot j) (x.coordinates j) = false := by
      cases hj : active j with
      | false => rw [hc.2.1 j hj, retained_zero]
      | true => exact hc.2.2 j hj
    simpa [kernelPoint, kernelCoefficients, hp, hr] using
      complete_coordinates (slot j) (x.coordinates j)

theorem coefficients_kernelPoint (a : ActiveBits active) :
    kernelCoefficients rhs active slot (kernelPoint rhs active slot a)
      (kernelPoint_mem rhs active slot a) = a := by
  apply activeBits_ext active
  funext j
  exact freeBit_complete _ _ _ _

theorem kernelPoint_injective (a b : ActiveBits active)
    (h : kernelPoint rhs active slot a = kernelPoint rhs active slot b) : a = b := by
  have hc : a.coefficient = b.coefficient := by
    funext j
    have he := congrArg (fun x : SourcePoint rhs => freeBit (slot j) (x.coordinates j)) h
    simpa [kernelPoint, freeBit_complete] using he
  cases a
  cases b
  cases hc
  rfl

/-- Every kernel vector is uniquely determined by one bit per active position. -/
theorem kernel_unique_coefficients (x : SourcePoint rhs) (hx : InKernel rhs active slot x) :
    ∃ a : ActiveBits active, kernelPoint rhs active slot a = x ∧
      ∀ b : ActiveBits active, kernelPoint rhs active slot b = x → b = a := by
  refine ⟨kernelCoefficients rhs active slot x hx,
    kernelPoint_coefficients rhs active slot x hx, ?_⟩
  intro b hb
  apply kernelPoint_injective rhs active slot
  exact hb.trans (kernelPoint_coefficients rhs active slot x hx).symm

/-- Extend an arbitrary function on the active positions by zero. -/
def extendActive (f : {j : Position // active j = true} → Bool) : ActiveBits active where
  coefficient := fun j => if hj : active j = true then f ⟨j, hj⟩ else false
  inactive_zero := by intro j hj; simp [hj]

theorem kernel_realizes_active
    (f : {j : Position // active j = true} → Bool) :
    ∃ x : SourcePoint rhs, InKernel rhs active slot x ∧
      ∀ j (hj : active j = true), freeBit (slot j) (x.coordinates j) = f ⟨j, hj⟩ := by
  refine ⟨kernelPoint rhs active slot (extendActive active f),
    kernelPoint_mem rhs active slot _, ?_⟩
  intro j hj
  simp [kernelPoint, freeBit_complete, extendActive, hj]

theorem kernel_determined_by_active
    (x y : SourcePoint rhs)
    (hx : InKernel rhs active slot x) (hy : InKernel rhs active slot y)
    (hfree : ∀ j, active j = true →
      freeBit (slot j) (x.coordinates j) = freeBit (slot j) (y.coordinates j)) : x = y := by
  have hc : kernelCoefficients rhs active slot x hx = kernelCoefficients rhs active slot y hy := by
    apply activeBits_ext active
    funext j
    cases hj : active j with
    | false =>
      simp [kernelCoefficients,
        (kernel_characterization rhs active slot x).1 hx |>.2.1 j hj,
        (kernel_characterization rhs active slot y).1 hy |>.2.1 j hj]
    | true => exact hfree j hj
  have hp := congrArg (kernelPoint rhs active slot) hc
  simpa only [kernelPoint_coefficients] using hp

/-- The final assertion of Lemma 6.1, including arbitrary retained indices. -/
theorem disjoint_kernels_intersection_zero
    (active' : Position → Bool) (slot' : Position → Slot)
    (hdisjoint : ∀ j, active j = true → active' j = false)
    (x : SourcePoint rhs)
    (hx : InKernel rhs active slot x)
    (hx' : InKernel rhs active' slot' x) : x = zeroSource rhs := by
  have h := (kernel_characterization rhs active slot x).1 hx
  have h' := (kernel_characterization rhs active' slot' x).1 hx'
  apply source_ext
  · exact h.1
  · funext j
    cases hj : active j with
    | false => exact h.2.1 j hj
    | true => exact h'.2.1 j (hdisjoint j hj)

end UniqueGamesTheorem.Soundness.PartnerProjection

end

section

/-!
This bridge connects the concrete partner projection to the actual equation/name
predicate of the incidence game. It uses no probabilistic or analytic hypotheses.
-/

namespace UniqueGamesTheorem.Soundness.ConcreteExtraction

open PartnerProjection IncidenceExtraction

def slotIndex : PartnerProjection.Slot → Fin 3
  | .first => 0
  | .second => 1
  | .third => 2

def tripleCoordinates (x : PartnerProjection.Triple) : IncidenceExtraction.Triple :=
  fun i => if i = 0 then x.first else if i = 1 then x.second else x.third

theorem parity_coordinates (x : PartnerProjection.Triple) :
    IncidenceExtraction.xorTriple (tripleCoordinates x) = PartnerProjection.parity x := rfl

theorem retained_coordinates (x : PartnerProjection.Triple) (i : PartnerProjection.Slot) :
    tripleCoordinates x (slotIndex i) = PartnerProjection.retained i x := by
  cases i <;> rfl

def fullPoint {P : Type} {rhs : P → Bool}
    (x : PartnerProjection.SourcePoint rhs) : IncidenceExtraction.FullPoint P :=
  ⟨x.homogeneous, fun j => tripleCoordinates (x.coordinates j)⟩

def partnerPoint {P : Type} {rhs active : P → Bool}
    (x : PartnerProjection.PartnerPoint rhs active) : IncidenceExtraction.PartnerPoint P :=
  ⟨x.homogeneous, x.single⟩

/-- Concrete projection acceptance implies the coordinate-level acceptance
    relation used to extract a repeated incidence strategy. -/
theorem actual_projection_accepts
    {P O N : Type} (g : IncidenceExtraction.Incidence O N) (u : P → O)
    (active : P → Bool) (slot : P → PartnerProjection.Slot)
    (x : PartnerProjection.SourcePoint (fun j => g.rhs (u j)))
    (y : PartnerProjection.PartnerPoint (fun j => g.rhs (u j)) active)
    (hone : x.homogeneous = true)
    (hproject : PartnerProjection.project (fun j => g.rhs (u j)) active slot x = y) :
    IncidenceExtraction.AugmentedAccepts g u (fun j => active j = true)
      (fun j => slotIndex (slot j)) (fullPoint x) (partnerPoint y) := by
  subst y
  constructor
  · intro j
    exact x.valid j
  constructor
  · exact hone
  constructor
  · exact hone
  intro j hj
  change tripleCoordinates (x.coordinates j) (slotIndex (slot j)) =
    (if active j then PartnerProjection.retained (slot j) (x.coordinates j) else false)
  rw [hj]
  exact retained_coordinates _ _

theorem actual_projection_implies_named_repetition
    {P R O N : Type} (g : IncidenceExtraction.Incidence O N) (u : P → O)
    (active : P → Bool) (slot : P → PartnerProjection.Slot) (embed : R → P)
    (x : PartnerProjection.SourcePoint (fun j => g.rhs (u j)))
    (y : PartnerProjection.PartnerPoint (fun j => g.rhs (u j)) active)
    (hinside : ∀ r, active (embed r) = true)
    (hone : x.homogeneous = true)
    (hproject : PartnerProjection.project (fun j => g.rhs (u j)) active slot x = y) :
    ∀ r, g.namedAccepts (u (embed r))
      (g.name (u (embed r)) (slotIndex (slot (embed r))))
      (tripleCoordinates (x.coordinates (embed r))) (y.single (embed r)) := by
  exact IncidenceExtraction.augmented_accepts_implies_named_repeated_accepts g u
    (fun j => active j = true) (fun j => slotIndex (slot j)) embed
    (fullPoint x) (partnerPoint y) hinside
    (actual_projection_accepts g u active slot x y hone hproject)

end UniqueGamesTheorem.Soundness.ConcreteExtraction

end

section

/-!
Finite cardinality of the concrete projection kernel. This packages the explicit
bit parametrization of Lemma 6.1 as a genuine equivalence, then counts its points.
No vector-space dimension formula is assumed.
-/

namespace UniqueGamesTheorem.Soundness.KernelCardinality

open PartnerProjection

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

abbrev Kernel := {x : SourcePoint rhs // InKernel rhs active slot x}

/-- Exactly one freely chosen bit per active position parametrizes the kernel. -/
def kernelEquiv : Kernel rhs active slot ≃ ({j : P // active j = true} → Bool) where
  toFun x j := freeBit (slot j.val) (x.val.coordinates j.val)
  invFun f := ⟨kernelPoint rhs active slot (extendActive active f),
    kernelPoint_mem rhs active slot _⟩
  left_inv x := by
    apply Subtype.ext
    apply kernel_determined_by_active rhs active slot
    · exact kernelPoint_mem rhs active slot _
    · exact x.property
    · intro j hj
      simp [kernelPoint, freeBit_complete, extendActive, hj]
  right_inv f := by
    funext j
    simp [kernelPoint, freeBit_complete, extendActive, j.property]

noncomputable instance kernelFintype [Fintype P] : Fintype (Kernel rhs active slot) := by
  classical
  exact Fintype.ofEquiv ({j : P // active j = true} → Bool) (kernelEquiv rhs active slot).symm

/-- The actual kernel has `2^t` points when there are `t` active positions. -/
theorem kernel_card [Fintype P] :
    Fintype.card (Kernel rhs active slot) = 2 ^ Fintype.card {j : P // active j = true} := by
  classical
  calc
    Fintype.card (Kernel rhs active slot) =
        Fintype.card ({j : P // active j = true} → Bool) :=
      Fintype.card_congr (kernelEquiv rhs active slot)
    _ = _ := by simp

theorem kernel_card_of_active_card [Fintype P] (t : Nat)
    (h : Fintype.card {j : P // active j = true} = t) :
    Fintype.card (Kernel rhs active slot) = 2 ^ t := by
  rw [kernel_card, h]

end UniqueGamesTheorem.Soundness.KernelCardinality

end

end OAI
