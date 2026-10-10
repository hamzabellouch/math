import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel
import OAI.Computability.UniqueGames.Gadgets.ConcatenationLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Gadget.AdaptivePaths

open Harmonic

universe u

/-- A finite sequence represented as successive products, in reveal order. -/
def Path (C : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Path C n × C

variable {C : Type*}

instance pathFintype [Fintype C] (n : ℕ) : Fintype (Path C n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (Path C n × C))

instance pathNonempty [Nonempty C] (n : ℕ) : Nonempty (Path C n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty PUnit)
  | succ n ih => exact inferInstanceAs (Nonempty (Path C n × C))

/-- A deterministic state update applied to the revealed choices. -/
def run {S : Type*} (step : S → C → S) (s₀ : S) : (n : ℕ) → Path C n → S
  | 0, _ => s₀
  | n + 1, (p, c) => step (run step s₀ n p) c

variable [Fintype C] [Nonempty C]

omit [Nonempty C] in
theorem average_run_succ {S : Type*} (step : S → C → S) (s₀ : S)
    (n : ℕ) (f : S → ℚ) :
    average (fun p : Path C (n + 1) => f (run step s₀ (n + 1) p)) =
      average (fun p : Path C n => average (fun c => f (step (run step s₀ n p) c))) := by
  unfold average
  change Finset.univ.expect (fun p : Path C n × C => f (step (run step s₀ n p.1) p.2)) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]

theorem probability_bad_succ {S : Type*} (step : S → C → S) (s₀ : S)
    (bad : S → Prop) [DecidablePred bad] (ε : ℚ)
    (hfresh : ∀ s, probability (fun c => bad (step s c)) ≤ ε) (n : ℕ) :
    probability (fun p : Path C (n + 1) => bad (run step s₀ (n + 1) p)) ≤ ε := by
  unfold probability
  change average (fun p : Path C (n + 1) =>
    (fun s : S => if bad s then (1 : ℚ) else 0) (run step s₀ (n + 1) p)) ≤ ε
  rw [average_run_succ step s₀ n (fun s => if bad s then (1 : ℚ) else 0)]
  calc
    _ ≤ average (fun _ : Path C n => ε) := average_mono (fun p => hfresh _)
    _ = ε := average_const _

/-- No measurability or independence premise about the state's lift is needed:
the finite product itself supplies the conditioning identity. -/
theorem expected_drop_le {S : Type*} (step : S → C → S) (s₀ : S)
    (potential : S → ℚ) (bad : S → Prop) [DecidablePred bad]
    (A θ ε : ℚ) (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hε : 0 ≤ ε)
    (hsmall : A * ε ≤ 1) (hinitial : ¬ bad s₀)
    (hfresh : ∀ s, probability (fun c => bad (step s c)) ≤ ε)
    (hstep : ∀ s, average (fun c => potential s - potential (step s c)) ≤
      3 * θ + A * θ * if bad s then 1 else 0) (n : ℕ) :
    average (fun p : Path C n => potential (run step s₀ n p)) -
      average (fun p : Path C (n + 1) => potential (run step s₀ (n + 1) p)) ≤
      4 * θ := by
  have hbad : probability (fun p : Path C n => bad (run step s₀ n p)) ≤ ε := by
    cases n with
    | zero => simpa [run, probability, hinitial] using hε
    | succ n => exact probability_bad_succ step s₀ bad ε hfresh n
  have hmean :
      average (fun p : Path C n => potential (run step s₀ n p)) -
        average (fun p : Path C (n + 1) => potential (run step s₀ (n + 1) p)) =
      average (fun p : Path C n =>
        average (fun c => potential (run step s₀ n p) - potential (step (run step s₀ n p) c))) := by
    rw [average_run_succ, ← average_sub]
    apply Finset.expect_congr rfl
    intro p hp
    rw [average_sub, average_const]
  rw [hmean]
  exact expected_drop_le_four_theta _ _ A θ ε hA hθ
    (fun p => hstep _) hbad hsmall

/-- Harmonic loss bound on the actual adaptive path sample space. -/
theorem expected_total_drop_le {S : Type*} (step : S → C → S) (s₀ : S)
    (potential : S → ℚ) (bad : S → Prop) [DecidablePred bad]
    (A θ ε : ℚ) (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hε : 0 ≤ ε)
    (hsmall : A * ε ≤ 1) (hinitial : ¬ bad s₀)
    (hfresh : ∀ s, probability (fun c => bad (step s c)) ≤ ε)
    (hstep : ∀ s, average (fun c => potential s - potential (step s c)) ≤
      3 * θ + A * θ * if bad s then 1 else 0) (n : ℕ) :
    potential s₀ - average (fun p : Path C n => potential (run step s₀ n p)) ≤
      4 * n * θ := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hd := expected_drop_le step s₀ potential bad A θ ε hA hθ hε hsmall
      hinitial hfresh hstep n
    push_cast
    linarith

end UniqueGamesTheorem.Gadget.AdaptivePaths

end

section

/-!
# From full character lifts to linear-map detection

If a target linear map is injective on the logical alphabet, a linear left
inverse of that restriction turns all logical characters into a full lift.
Detection by this lift implies that the target map does not annihilate the
noise. The left inverse is proved to exist by the vector-space splitting
theorem; it is not an additional premise.
-/

namespace UniqueGamesTheorem.Gadget.DetectionBridge

open Harmonic

variable {K B V E Ω : Type*} [Field K]
variable [AddCommGroup B] [Module K B] [AddCommGroup V] [Module K V]
variable [AddCommGroup E] [Module K E] [Fintype Ω]

/-- Every logical character is extended to the ambient input space. -/
def IsFullLift (ι : B →ₗ[K] V)
    (ψ : Module.Dual K B →ₗ[K] Module.Dual K V) : Prop :=
  ∀ (z : Module.Dual K B) (b : B), ψ z (ι b) = z b

/-- Detection by any member of a character family. Classical decidability
only selects an event indicator on the finite noise sample space. -/
noncomputable def characterDetection (noise : Ω → V)
    (ψ : Module.Dual K B →ₗ[K] Module.Dual K V) : ℚ := by
  classical
  exact probability (fun ω => ∃ z : Module.Dual K B, ψ z (noise ω) ≠ 0)

theorem exists_leftInverse_of_logical_injective (ι : B →ₗ[K] V)
    (T : V →ₗ[K] E) (hinjective : Function.Injective (T.comp ι)) :
    ∃ l : E →ₗ[K] B, l.comp (T.comp ι) = LinearMap.id :=
  (T.comp ι).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinjective)

/-- The left inverse supplies an actual full character lift through `T`. -/
theorem fullLift_of_leftInverse (ι : B →ₗ[K] V) (T : V →ₗ[K] E)
    (l : E →ₗ[K] B) (hleft : l.comp (T.comp ι) = LinearMap.id) :
    IsFullLift ι (l.comp T).dualMap := by
  intro z b
  change z (l (T (ι b))) = z b
  have hb : l (T (ι b)) = b := LinearMap.congr_fun hleft b
  rw [hb]

/-- A full-lift detection guarantee transfers to every target map injective
on the logical alphabet. -/
theorem target_detection_of_full_lift_bound [DecidableEq E]
    (noise : Ω → V) (ι : B →ₗ[K] V) (T : V →ₗ[K] E) (q : ℚ)
    (hfull : ∀ ψ : Module.Dual K B →ₗ[K] Module.Dual K V,
      IsFullLift ι ψ → q ≤ characterDetection noise ψ)
    (hinjective : Function.Injective (T.comp ι)) :
    q ≤ probability (fun ω => T (noise ω) ≠ 0) := by
  classical
  obtain ⟨l, hl⟩ := exists_leftInverse_of_logical_injective ι T hinjective
  calc
    q ≤ characterDetection noise (l.comp T).dualMap :=
      hfull _ (fullLift_of_leftInverse ι T l hl)
    _ ≤ probability (fun ω => T (noise ω) ≠ 0) := by
      unfold characterDetection
      apply probability_mono
      rintro ω ⟨z, hz⟩ hzero
      apply hz
      change z (l (T (noise ω))) = 0
      simp [hzero]

/-- Equivalent useful interface when the recursive calculation already gives
detection of every vector-valued linear retraction of the logical inclusion. -/
theorem target_detection_of_retraction_bound [DecidableEq B] [DecidableEq E]
    (noise : Ω → V) (ι : B →ₗ[K] V) (T : V →ₗ[K] E) (q : ℚ)
    (hretract : ∀ L : V →ₗ[K] B, L.comp ι = LinearMap.id →
      q ≤ probability (fun ω => L (noise ω) ≠ 0))
    (hinjective : Function.Injective (T.comp ι)) :
    q ≤ probability (fun ω => T (noise ω) ≠ 0) := by
  obtain ⟨l, hl⟩ := exists_leftInverse_of_logical_injective ι T hinjective
  have hcomp : (l.comp T).comp ι = LinearMap.id := by
    simpa only [LinearMap.comp_assoc] using hl
  calc
    q ≤ probability (fun ω => (l.comp T) (noise ω) ≠ 0) := hretract _ hcomp
    _ ≤ probability (fun ω => T (noise ω) ≠ 0) := by
      apply probability_mono
      intro ω h hzero
      apply h
      simp [hzero]

end UniqueGamesTheorem.Gadget.DetectionBridge

end

section

/-!
# Common-parent factorization before fresh orientation

This is the linear algebra in the lift-factorization lemma of v2 Section 2.
The map `gamma` is obtained from the whole parent family and the first
aggregate coordinate. It is chosen once, before any child is selected.
No rank, genericity, or independence assumption is needed for this step.
-/

namespace UniqueGamesTheorem.Gadget

section Factorization

variable {k S T X B : Type*} [Field k]
variable [AddCommGroup S] [Module k S]
variable [AddCommGroup T] [Module k T]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]

/-- A linear family vanishing on the kernel of a surjection factors as one
linear family on the target. In particular the factor is linear in its
character parameter, rather than a separate arbitrary choice for each one. -/
theorem family_factors_of_ker
    (f : T →ₗ[k] X) (hf : Function.Surjective f)
    (ψ : S →ₗ[k] (T →ₗ[k] k))
    (hker : ∀ z t, f t = 0 → ψ z t = 0) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ z t, ψ z t = γ z (f t) := by
  obtain ⟨σ, hσ⟩ := f.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf)
  have hσ_apply (x : X) : f (σ x) = x := congrArg (fun g : X →ₗ[k] X => g x) hσ
  let γ : S →ₗ[k] (X →ₗ[k] k) :=
    { toFun := fun z => (ψ z).comp σ
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  refine ⟨γ, fun z t => ?_⟩
  have hz := hker z (t - σ (f t)) (by rw [map_sub, hσ_apply, sub_self])
  have heq : ψ z t - ψ z (σ (f t)) = 0 := by simpa only [map_sub] using hz
  exact sub_eq_zero.mp heq

/-- The common first-coordinate character of a parent lift. `ψ z` is the
parent character on child shifts, `ζ z` its prescribed logical character,
and `(a,b)` the aggregate. A parent shift is exactly a tuple with `a=0`.
The conclusion quantifies one `γ` before all tuples and all later children. -/
theorem common_parent_factorization
    (a : T →ₗ[k] X) (b : T →ₗ[k] B) (ha : Function.Surjective a)
    (ψ : S →ₗ[k] (T →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z t, a t = 0 → ψ z t = ζ z (b t)) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k),
      ∀ z t, ψ z t = γ z (a t) + ζ z (b t) := by
  let η : S →ₗ[k] (T →ₗ[k] k) :=
    { toFun := fun z => ψ z - (ζ z).comp b
      map_add' := by intros; ext; simp; abel
      map_smul' := by intros; ext; simp [smul_sub] }
  obtain ⟨γ, hγ⟩ := family_factors_of_ker a ha η (by
    intro z t ht
    change ψ z t - ζ z (b t) = 0
    rw [hlift z t ht, sub_self])
  refine ⟨γ, fun z t => ?_⟩
  have h := hγ z t
  change ψ z t - ζ z (b t) = γ z (a t) at h
  exact (sub_eq_iff_eq_add).mp h

/-- Evaluating the single parent factor on any child embedding gives the
child restriction formula. The same `γ` works for every child, so its choice
cannot depend on the fresh orientation subsequently sampled at that child. -/
theorem common_child_factorization
    {ι P : Type*} [AddCommGroup P] [Module k P]
    (a : T →ₗ[k] X) (b : T →ₗ[k] B) (ha : Function.Surjective a)
    (ψ : S →ₗ[k] (T →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z t, a t = 0 → ψ z t = ζ z (b t))
    (child : ι → P →ₗ[k] T) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k),
      ∀ i z p, ψ z (child i p) = γ z (a (child i p)) + ζ z (b (child i p)) := by
  obtain ⟨γ, hγ⟩ := common_parent_factorization a b ha ψ ζ hlift
  exact ⟨γ, fun i z p => hγ z (child i p)⟩

/-- For a surjective aggregate, its first coordinate is surjective. -/
theorem aggregate_fst_surjective (A : T →ₗ[k] X × B)
    (hA : Function.Surjective A) :
    Function.Surjective ((LinearMap.fst k X B).comp A) := by
  intro x
  obtain ⟨t, ht⟩ := hA (x, 0)
  exact ⟨t, congrArg Prod.fst ht⟩

end Factorization

end UniqueGamesTheorem.Gadget

end

section

/-!
# Every parent lift has one common map before the child is selected

This specializes the kernel factorization to the actual product construction.
It derives the child logical characters from a parent lift; it does not assume
independence of the lift and an incoming orientation.
-/

namespace UniqueGamesTheorem.Gadget

open scoped BigOperators

variable {k I P R X B S : Type*} [Field k] [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]
variable [AddCommGroup S] [Module k S]

/-- Inclusion of all child shifts before imposing the parent kernel condition. -/
def tupleEmbed (e : R →ₗ[k] P) : (I → R) →ₗ[k] (I → P) where
  toFun h i := e (h i)
  map_add' u v := by ext; simp
  map_smul' c v := by ext; simp

omit [Fintype I] in
theorem tupleEmbed_single (e : R →ₗ[k] P) (i : I) (h : R) :
    tupleEmbed e (Pi.single i h) = Pi.single i (e h) := by
  ext j
  by_cases hij : i = j
  · subst j; simp [tupleEmbed]
  · simp [tupleEmbed, hij]

theorem shiftAggregate_single (J : I → B →ₗ[k] X × B)
    (lam : R →ₗ[k] B) (i : I) (h : R) :
    shiftAggregate J lam (Pi.single i h) = J i (lam h) := by
  classical
  simp [shiftAggregate, aggregate, Pi.single_apply, apply_ite, map_zero]

/-- Actual parent lifts factor through the same aggregate first-coordinate
family on all child shifts. The existential `γ` occurs before both `i` and `h`.
This is the common-parent requirement used before revealing fresh orientation. -/
theorem parent_lift_common_child
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (ψ : S →ₗ[k] ((I → P) →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z (h : parentShifts J lam),
      ψ z (parentEmbed J lam e h) = ζ z (parentLogical J lam h)) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ i z h,
      ψ z (Pi.single i (e h)) =
        γ z (J i (lam h)).1 + ζ z (J i (lam h)).2 := by
  let a := (LinearMap.fst k X B).comp (shiftAggregate J lam)
  let b := (LinearMap.snd k X B).comp (shiftAggregate J lam)
  let Ψ : S →ₗ[k] ((I → R) →ₗ[k] k) :=
    { toFun := fun z => (ψ z).comp (tupleEmbed e)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have ha : Function.Surjective a :=
    aggregate_fst_surjective _ (shiftAggregate_surjective J hJ lam hlam)
  obtain ⟨γ, hγ⟩ := common_parent_factorization a b ha Ψ ζ (by
    intro z h hh
    exact hlift z ⟨h, hh⟩)
  refine ⟨γ, fun i z h => ?_⟩
  have heq := hγ z (Pi.single i h)
  change ψ z (tupleEmbed e (Pi.single i h)) =
    γ z (shiftAggregate J lam (Pi.single i h)).1 +
      ζ z (shiftAggregate J lam (Pi.single i h)).2 at heq
  simpa only [tupleEmbed_single, shiftAggregate_single] using heq

/-- In particular, every child restriction annihilates the child's logical
kernel. This proves that a child logical character exists for every lift. -/
theorem parent_lift_child_kernel
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (ψ : S →ₗ[k] ((I → P) →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z (h : parentShifts J lam),
      ψ z (parentEmbed J lam e h) = ζ z (parentLogical J lam h))
    (i : I) (z : S) (h : R) (hh : lam h = 0) :
    ψ z (Pi.single i (e h)) = 0 := by
  obtain ⟨γ, hγ⟩ := parent_lift_common_child J hJ e lam hlam ψ ζ hlift
  simpa [hh] using hγ i z h

end UniqueGamesTheorem.Gadget

end

section

/-!
# Exact kernel counts for binary linear maps

The last paragraph of Theorem 3.4 uses the fact that a uniform vector in a
binary vector space lands in the kernel of a rank-k map with probability
2⁻ᵏ. These theorems prove its exact integer-count form from mathlib's
rank-nullity and finite-vector-space cardinality theorems. The target space
does not have to be finite, and no injectivity of any factor map is assumed.
-/

namespace UniqueGamesTheorem.Gadget.LinearKernelCount

universe u v

variable {V : Type u} {P : Type v}
variable [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable [AddCommGroup P] [Module (ZMod 2) P]

/-- A finite-dimensional binary vector space has `2^dimension` vectors. -/
theorem card_binary_space : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp

/-- Exact cross-multiplied uniform kernel probability: `|ker f| * 2^rank f = |V|`. -/
theorem kernel_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card f.ker * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V := by
  rw [card_binary_space (V := f.ker), card_binary_space (V := V), ← pow_add]
  congr 1
  rw [Nat.add_comm]
  exact f.finrank_range_add_finrank_ker

/-- The denominator of the uniform vector experiment is positive. -/
theorem card_source_pos : 0 < Nat.card V := by
  rw [card_binary_space]
  exact Nat.pow_pos (by decide)

/-- The kernel size itself is the familiar power of the nullity. -/
theorem kernel_card_eq_pow_sub_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card f.ker =
      2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) f.range) := by
  rw [card_binary_space (V := f.ker)]
  congr 1
  have h := f.finrank_range_add_finrank_ker
  omega

/-- The kernel formula expressed directly as the cardinality of the zero event. -/
theorem zero_event_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card {x : V // f x = 0} * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V :=
  kernel_card_mul_pow_rank f

/-- A rank threshold gives the exact cleared-denominator bound used on a good leaf. -/
theorem zero_event_card_mul_pow_le (f : V →ₗ[ZMod 2] P) (r : Nat)
    (hr : r ≤ Module.finrank (ZMod 2) f.range) :
    Nat.card {x : V // f x = 0} * 2 ^ r ≤ Nat.card V := by
  calc
    Nat.card {x : V // f x = 0} * 2 ^ r ≤
        Nat.card {x : V // f x = 0} * 2 ^ Module.finrank (ZMod 2) f.range :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hr)
    _ = Nat.card V := zero_event_card_mul_pow_rank f

/-- The same exact probability identity for a direct count over a finite universe. -/
theorem zero_event_finset_count_mul_pow_rank [Fintype V] [DecidableEq P]
    (f : V →ₗ[ZMod 2] P) :
    (Finset.univ.filter (fun x : V => f x = 0)).card *
      2 ^ Module.finrank (ZMod 2) f.range = Fintype.card V := by
  have h := zero_event_card_mul_pow_rank f
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

/-- A rank-r lower bound yields a `2⁻ʳ` bound on the actual finite zero-event count. -/
theorem zero_event_finset_count_mul_pow_le [Fintype V] [DecidableEq P]
    (f : V →ₗ[ZMod 2] P) (r : Nat)
    (hr : r ≤ Module.finrank (ZMod 2) f.range) :
    (Finset.univ.filter (fun x : V => f x = 0)).card * 2 ^ r ≤ Fintype.card V := by
  have h := zero_event_card_mul_pow_le f r hr
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

end UniqueGamesTheorem.Gadget.LinearKernelCount

end

section

/-!
# Fresh finite orientations

The rank is fixed before the fresh isomorphism is sampled.  The finite
counting identities below do not require the subsequent lift to be independent
of that isomorphism.  In particular, an event concerning the oriented subspace
may be tested after arbitrary earlier choices have been fixed.
-/

noncomputable section

open scoped BigOperators
open Module

namespace UniqueGamesTheorem.Gadget.Orientation

section FiniteAction

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]

omit [Fintype X] in
/-- Right translation of the uniform group element changes the starting point,
but leaves the complete sample sum unchanged. -/
theorem sum_action_eq (x y : X) (h : ∃ a : G, a • x = y) (f : X → ℚ) :
    (∑ g : G, f (g • x)) = ∑ g : G, f (g • y) := by
  obtain ⟨a, rfl⟩ := h
  symm
  exact Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun g => by simp [mul_smul])

/-- Cross-multiplied uniform-pushforward identity for a transitive finite action.
This form also handles empty event sets without additional cases. -/
theorem card_mul_sum_action (x : X)
    (transitive : ∀ y : X, ∃ a : G, a • x = y) (f : X → ℚ) :
    (Fintype.card X : ℚ) * (∑ g : G, f (g • x)) =
      (Fintype.card G : ℚ) * (∑ y : X, f y) := by
  calc
    (Fintype.card X : ℚ) * (∑ g : G, f (g • x)) =
        ∑ y : X, ∑ g : G, f (g • x) := by simp
    _ = ∑ y : X, ∑ g : G, f (g • y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact sum_action_eq x y (transitive y) f
    _ = ∑ g : G, ∑ y : X, f (g • y) := Finset.sum_comm
    _ = ∑ _g : G, ∑ y : X, f y := by
      apply Finset.sum_congr rfl
      intro g _
      exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
    _ = (Fintype.card G : ℚ) * (∑ y : X, f y) := by simp

/-- A uniform group element sends a fixed point to the uniform distribution on
the entire transitive space.  Apply to indicator functions for event bounds. -/
theorem mean_action (x : X)
    (transitive : ∀ y : X, ∃ a : G, a • x = y) (f : X → ℚ) :
    (∑ g : G, f (g • x)) / Fintype.card G =
      (∑ y : X, f y) / Fintype.card X := by
  have : Nonempty X := ⟨x⟩
  have hG : (Fintype.card G : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hX : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (div_eq_div_iff hG hX).2
  simpa [mul_comm] using card_mul_sum_action x transitive f

end FiniteAction

section LinearOrientation

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

/-- Every two equal-dimensional subspaces are related by an automorphism of
the ambient space.  This supplies actual transitivity, rather than assuming
the desired distribution on the Grassmannian. -/
theorem exists_map_eq_of_finrank_eq (E F : Submodule K V)
    (h : finrank K E = finrank K F) :
    ∃ a : V ≃ₗ[K] V, E.map a.toLinearMap = F := by
  let e : E ≃ₗ[K] F := LinearEquiv.ofFinrankEq E F h
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨a, ?_⟩
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (ha ⟨u, hu⟩) ▸ (e ⟨u, hu⟩).property
  · intro hv
    obtain ⟨u, hu⟩ := e.surjective ⟨v, hv⟩
    refine ⟨u, u.property, ?_⟩
    exact (ha u).symm.trans (congrArg Subtype.val hu)

omit [FiniteDimensional K V] in
/-- Rank does not depend on the fresh orientation. -/
theorem rank_map (E : Submodule K V) (a : V ≃ₗ[K] V) :
    finrank K (E.map a.toLinearMap) = finrank K E :=
  a.finrank_map_eq E

/-- The finite Grassmannian at a rank chosen before orientation. -/
def RankSpace (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (r : ℕ) :=
  {E : Submodule K V // finrank K E = r}

instance rankSpaceAction (r : ℕ) : MulAction (V ≃ₗ[K] V) (RankSpace K V r) where
  smul a E := ⟨E.val.map a.toLinearMap, (a.finrank_map_eq E.val).trans E.property⟩
  one_smul E := by
    apply Subtype.ext
    exact E.val.map_id
  mul_smul a b E := by
    apply Subtype.ext
    exact E.val.map_comp b.toLinearMap a.toLinearMap

/-- Equal-rank transitivity specialized to the rank-indexed sampling space. -/
theorem rankSpace_transitive {r : ℕ} (E F : RankSpace K V r) :
    ∃ a : V ≃ₗ[K] V, a • E = F := by
  obtain ⟨a, ha⟩ := exists_map_eq_of_finrank_eq E.val F.val
    (E.property.trans F.property.symm)
  exact ⟨a, Subtype.ext ha⟩

/-- The exact uniform law of a fixed-rank subspace under a fresh uniform
linear orientation, with no genericity or independence premise. -/
theorem mean_oriented_subspace {r : ℕ} [Fintype (V ≃ₗ[K] V)]
    [Fintype (RankSpace K V r)] (E : RankSpace K V r) (f : RankSpace K V r → ℚ) :
    (∑ a : V ≃ₗ[K] V, f (a • E)) / Fintype.card (V ≃ₗ[K] V) =
      (∑ F : RankSpace K V r, f F) / Fintype.card (RankSpace K V r) :=
  mean_action E (rankSpace_transitive E) f

variable {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U]

/-- Pullback of a fixed character space by an isomorphism preserves rank.
The character space is an argument preceding the newly chosen orientation. -/
theorem rank_dual_pullback (E : Submodule K (Module.Dual K U)) (J : B ≃ₗ[K] U) :
    finrank K (E.map J.dualMap.toLinearMap) = finrank K E :=
  J.dualMap.finrank_map_eq E

/-- Choosing a reference isomorphism identifies all orientations with the
automorphism group of the target. -/
def orientationEquiv (J₀ : B ≃ₗ[K] U) : (B ≃ₗ[K] U) ≃ (U ≃ₗ[K] U) where
  toFun J := J₀.symm.trans J
  invFun a := J₀.trans a
  left_inv J := by ext x; simp
  right_inv a := by ext x; simp

/-- Uniform orientations between two spaces send a fixed character subspace
to the uniform distribution on all subspaces of the same dimension. -/
theorem mean_map_equiv [FiniteDimensional K U] (E : Submodule K B) (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)] [Fintype (U ≃ₗ[K] U)]
    [Fintype (RankSpace K U (finrank K E))]
    (f : RankSpace K U (finrank K E) → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ F : RankSpace K U (finrank K E), f F) /
        Fintype.card (RankSpace K U (finrank K E)) := by
  let E₀ : RankSpace K U (finrank K E) :=
    ⟨E.map J₀.toLinearMap, J₀.finrank_map_eq E⟩
  have hsum : (∑ J : B ≃ₗ[K] U, f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) =
      ∑ a : U ≃ₗ[K] U, f (a • E₀) := by
    apply Fintype.sum_equiv (orientationEquiv J₀)
    intro J
    congr 1
    apply Subtype.ext
    change E.map J.toLinearMap =
      (E.map J₀.toLinearMap).map (J₀.symm.trans J).toLinearMap
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp
  rw [hsum, Fintype.card_congr (orientationEquiv J₀)]
  exact mean_oriented_subspace E₀ f

/-- Dualization is a bijection on finite-dimensional isomorphisms.  This
connects uniform primal orientations to uniform character-space orientations. -/
def dualOrientationEquiv [FiniteDimensional K B] [FiniteDimensional K U] :
    (B ≃ₗ[K] U) ≃ (Module.Dual K U ≃ₗ[K] Module.Dual K B) where
  toFun J := J.dualMap
  invFun e := ((Module.evalEquiv K B).trans e.dualMap).trans (Module.evalEquiv K U).symm
  left_inv J := by
    ext b
    apply (Module.evalEquiv K U).injective
    ext φ
    simp
  right_inv e := by
    ext φ b
    simp

theorem mean_dual_pullback [FiniteDimensional K B] [FiniteDimensional K U]
    (E : Submodule K (Module.Dual K U)) (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)]
    [Fintype (Module.Dual K U ≃ₗ[K] Module.Dual K B)]
    [Fintype (Module.Dual K B ≃ₗ[K] Module.Dual K B)]
    [Fintype (RankSpace K (Module.Dual K B) (finrank K E))]
    (f : RankSpace K (Module.Dual K B) (finrank K E) → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨E.map J.dualMap.toLinearMap, J.dualMap.finrank_map_eq E⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ F : RankSpace K (Module.Dual K B) (finrank K E), f F) /
        Fintype.card (RankSpace K (Module.Dual K B) (finrank K E)) := by
  let e := dualOrientationEquiv (K := K) (B := B) (U := U)
  have hsum := Fintype.sum_equiv e
    (fun J : B ≃ₗ[K] U => f ⟨E.map J.dualMap.toLinearMap, J.dualMap.finrank_map_eq E⟩)
    (fun J : Module.Dual K U ≃ₗ[K] Module.Dual K B =>
      f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) (fun _ => rfl)
  rw [hsum, Fintype.card_congr e]
  exact mean_map_equiv E J₀.dualMap f

end LinearOrientation

end UniqueGamesTheorem.Gadget.Orientation

end

end

section

/-!
# Fresh orientations of nonzero perturbations

This is the nonzero-symbol uniformity step in the latent-noise recurrence.
The perturbation is fixed before the orientation, and zero is excluded from
both sample spaces explicitly.
-/

noncomputable section

open scoped BigOperators

namespace UniqueGamesTheorem.Gadget.OrientationVectors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Extend the isomorphism taking one specified nonzero vector to another. -/
theorem exists_equiv_map_nonzero (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : V ≃ₗ[K] V, e x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton K V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton K V y hy
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨e, ?_⟩
  have h := (he (ex 1)).symm
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h

theorem equiv_apply_ne_zero {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (J : B ≃ₗ[K] U) {b : B} (hb : b ≠ 0) :
    J b ≠ 0 := by
  intro h
  apply hb
  exact J.injective (h.trans (map_zero J).symm)

instance nonzeroAction : MulAction (V ≃ₗ[K] V) {x : V // x ≠ 0} where
  smul a x := ⟨a x.val, equiv_apply_ne_zero a x.property⟩
  one_smul x := by apply Subtype.ext; rfl
  mul_smul a b x := by apply Subtype.ext; rfl

theorem nonzero_transitive (x y : {v : V // v ≠ 0}) :
    ∃ a : V ≃ₗ[K] V, a • x = y := by
  obtain ⟨a, ha⟩ := exists_equiv_map_nonzero (K := K) x.val y.val x.property y.property
  exact ⟨a, Subtype.ext ha⟩

/-- A uniform ambient automorphism sends a fixed nonzero symbol uniformly
onto all nonzero symbols. -/
theorem mean_oriented_nonzero [Fintype (V ≃ₗ[K] V)]
    [Fintype {x : V // x ≠ 0}] (x : {v : V // v ≠ 0})
    (f : {v : V // v ≠ 0} → ℚ) :
    (∑ a : V ≃ₗ[K] V, f (a • x)) / Fintype.card (V ≃ₗ[K] V) =
      (∑ y : {v : V // v ≠ 0}, f y) / Fintype.card {v : V // v ≠ 0} :=
  Orientation.mean_action x (nonzero_transitive x) f

/-- The exact law used after fixing a child line and its nonzero output
difference: averaging over all `J : B ≃ₗ[K] U` is uniform on `U \ {0}`. -/
theorem mean_iso_nonzero {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)] [Fintype (U ≃ₗ[K] U)]
    [Fintype {u : U // u ≠ 0}] (b : B) (hb : b ≠ 0)
    (f : {u : U // u ≠ 0} → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨J b, equiv_apply_ne_zero J hb⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ u : {u : U // u ≠ 0}, f u) / Fintype.card {u : U // u ≠ 0} := by
  let x : {u : U // u ≠ 0} := ⟨J₀ b, equiv_apply_ne_zero J₀ hb⟩
  have hsum : (∑ J : B ≃ₗ[K] U, f ⟨J b, equiv_apply_ne_zero J hb⟩) =
      ∑ a : U ≃ₗ[K] U, f (a • x) := by
    apply Fintype.sum_equiv (Orientation.orientationEquiv J₀)
    intro J
    congr 1
    apply Subtype.ext
    change J b = (J₀.symm.trans J) (J₀ b)
    simp
  rw [hsum, Fintype.card_congr (Orientation.orientationEquiv J₀)]
  exact mean_oriented_nonzero x f

end UniqueGamesTheorem.Gadget.OrientationVectors

end

end

section

namespace UniqueGamesTheorem.Gadget.Parameters

open Harmonic
open scoped BigOperators

/-- Every block from `n+1` through `2n` adds at least one half. -/
theorem harmonic_double (n : ℕ) (hn : 0 < n) :
    harmonic n + 1 / 2 ≤ harmonic (2 * n) := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hsplit : harmonic (2 * n) = harmonic n +
      ∑ i ∈ Finset.range n, (↑(n + i + 1) : ℚ)⁻¹ := by
    rw [harmonic_eq_sum, show 2 * n = n + n by omega, Finset.sum_range_add]
    rw [← harmonic_eq_sum n]
  have hs : (∑ _i ∈ Finset.range n, (2 * (n : ℚ))⁻¹) ≤
      ∑ i ∈ Finset.range n, (↑(n + i + 1) : ℚ)⁻¹ := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    apply inv_anti₀ (by positivity)
    exact_mod_cast (show n + i + 1 ≤ 2 * n by omega)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have he : (n : ℚ) * (2 * (n : ℚ))⁻¹ = 1 / 2 := by
    field_simp [ne_of_gt hnq]
  rw [he] at hs
  rw [hsplit]
  linarith

theorem harmonic_pow_two (k : ℕ) : (k : ℚ) / 2 ≤ harmonic (2 ^ k) := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_div, pow_zero] using harmonic_nonneg 1
  | succ k ih =>
    have hd := harmonic_double (2 ^ k) (pow_pos (by decide) _)
    rw [pow_succ, Nat.mul_comm]
    push_cast
    linarith

/-- Computable rank exceeding any prescribed rational harmonic level. -/
def rankFor (level : ℚ) : ℕ := 2 ^ ⌈2 * level⌉₊

theorem rankFor_pos (level : ℚ) : 0 < rankFor level := by
  unfold rankFor
  positivity

theorem le_harmonic_rankFor (level : ℚ) : level ≤ harmonic (rankFor level) := by
  have hc := Nat.le_ceil (2 * level)
  have hh := harmonic_pow_two ⌈2 * level⌉₊
  change level ≤ harmonic (2 ^ ⌈2 * level⌉₊)
  linarith

theorem harmonic_unbounded (level : ℚ) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ level ≤ harmonic r₀ :=
  ⟨rankFor level, rankFor_pos level, le_harmonic_rankFor level⟩

/-- Strictly positive genericity error meeting the harmonic bad-rank budget. -/
def genericityError (r₀ : ℕ) : ℚ := 1 / (2 * (badRankCoefficient r₀ + 1))

theorem genericityError_pos (r₀ : ℕ) : 0 < genericityError r₀ := by
  unfold genericityError
  have := badRankCoefficient_nonneg r₀
  positivity

theorem genericityError_lt_one (r₀ : ℕ) : genericityError r₀ < 1 := by
  have hc := badRankCoefficient_nonneg r₀
  unfold genericityError
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem genericityError_budget (r₀ : ℕ) :
    badRankCoefficient r₀ * genericityError r₀ ≤ 1 := by
  have hc := badRankCoefficient_nonneg r₀
  unfold genericityError
  rw [← mul_div_assoc, mul_one]
  apply (div_le_one (by positivity)).mpr
  linarith

/-- The geometric decay has an elementary reciprocal upper bound. -/
theorem geometric_reciprocal_bound (θ : ℚ) (_hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (n : ℕ) : (1 - θ) ^ n * (1 + (n : ℚ) * θ) ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 0 ≤ (1 - θ) ^ n := pow_nonneg (sub_nonneg.mpr hθone) _
    have hn : (0 : ℚ) ≤ n := by positivity
    have hstep : (1 - θ) * (1 + ((n + 1 : ℕ) : ℚ) * θ) ≤
        1 + (n : ℚ) * θ := by
      push_cast
      nlinarith [sq_nonneg θ, mul_nonneg hn (sq_nonneg θ)]
    calc
      (1 - θ) ^ (n + 1) * (1 + ((n + 1 : ℕ) : ℚ) * θ) =
          (1 - θ) ^ n * ((1 - θ) * (1 + ((n + 1 : ℕ) : ℚ) * θ)) := by
        rw [pow_succ]
        ring
      _ ≤ (1 - θ) ^ n * (1 + (n : ℚ) * θ) :=
        mul_le_mul_of_nonneg_left hstep hp
      _ ≤ 1 := ih

/-- The chosen harmonic depth works uniformly for every subsequent
`0 < θ ≤ 1`. Thus the rank can be selected before the field/noise parameter. -/
theorem geometric_at_depth_le (p θ : ℚ) (r₀ : ℕ) (hp : 0 < p)
    (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hlarge : 8 * (p⁻¹ + 1) ≤ harmonic r₀) :
    (1 - θ) ^ depth r₀ θ ≤ p := by
  have hden : (0 : ℚ) < 8 * θ := by positivity
  have hf := Nat.lt_floor_add_one (harmonic r₀ / (8 * θ))
  have hf' := (div_lt_iff₀ hden).mp hf
  change harmonic r₀ < ((depth r₀ θ : ℚ) + 1) * (8 * θ) at hf'
  have hnθ : p⁻¹ ≤ (depth r₀ θ : ℚ) * θ := by nlinarith
  have hpne : p ≠ 0 := ne_of_gt hp
  have hm := mul_le_mul_of_nonneg_left hnθ (le_of_lt hp)
  simp only [mul_inv_cancel₀ hpne] at hm
  have hr := geometric_reciprocal_bound θ (le_of_lt hθ) hθone (depth r₀ θ)
  have hb : 1 ≤ p * (1 + (depth r₀ θ : ℚ) * θ) := by nlinarith
  have hpositive : 0 < 1 + (depth r₀ θ : ℚ) * θ := by positivity
  exact (mul_le_mul_iff_left₀ hpositive).mp (by simpa only [mul_comm] using hr.trans hb)

/-- Explicit threshold depending only on the requested nonlinear error. -/
def initialRank (p : ℚ) : ℕ := rankFor (8 * (p⁻¹ + 1))

theorem initialRank_pos (p : ℚ) : 0 < initialRank p := rankFor_pos _

theorem initialRank_large (p : ℚ) :
    8 * (p⁻¹ + 1) ≤ harmonic (initialRank p) := le_harmonic_rankFor _

/-- All scalar choices needed before the field dimension is selected. -/
theorem effective_parameters (p : ℚ) (hp : 0 < p) :
    ∃ r₀ : ℕ, ∃ ε : ℚ,
      0 < r₀ ∧ 0 < ε ∧ ε < 1 ∧ badRankCoefficient r₀ * ε ≤ 1 ∧
      ∀ θ : ℚ, 0 < θ → θ ≤ 1 → (1 - θ) ^ depth r₀ θ ≤ p := by
  refine ⟨initialRank p, genericityError (initialRank p), initialRank_pos p,
    genericityError_pos _, genericityError_lt_one _, genericityError_budget _, ?_⟩
  intro θ hθ hθone
  exact geometric_at_depth_le p θ (initialRank p) hp hθ hθone (initialRank_large p)

end UniqueGamesTheorem.Gadget.Parameters

end

end OAI
