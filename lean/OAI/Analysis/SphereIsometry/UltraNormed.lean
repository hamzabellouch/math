import OAI.Analysis.SphereIsometry.UltraRealLimit
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Group.SeparationQuotient

namespace OAI

/-!
# Bounded sequences with the ultralimit seminorm

The carrier below is a fresh wrapper, not the bounded submodule with its
inherited product topology. Only algebra is transported to the wrapper. Its
topology is then constructed from the ultralimit seminorm. The separation
quotient therefore identifies zero ultradistance, not eventual equality.
-/

noncomputable section

namespace Tingley

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The algebraic submodule of uniformly bounded sequences. -/
def boundedSequenceSubmodule : Submodule ℝ (ℕ → X) where
  carrier := {a | ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖a n‖ ≤ B}
  zero_mem' := ⟨0, le_rfl, by simp⟩
  add_mem' := by
    rintro a b ⟨A, hA, ha⟩ ⟨B, hB, hb⟩
    refine ⟨A + B, add_nonneg hA hB, fun n => ?_⟩
    exact (norm_add_le (a n) (b n)).trans (add_le_add (ha n) (hb n))
  smul_mem' := by
    rintro r a ⟨A, hA, ha⟩
    refine ⟨‖r‖ * A, mul_nonneg (norm_nonneg r) hA, fun n => ?_⟩
    simpa only [Pi.smul_apply, norm_smul] using
      mul_le_mul_of_nonneg_left (ha n) (norm_nonneg r)

/-- A fresh carrier on which only the ultralimit topology will be installed. -/
structure UltraSequence (U : Ultrafilter ℕ) (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X] where
  val : boundedSequenceSubmodule X

namespace UltraSequence

variable (U : Ultrafilter ℕ)

/-- Algebraic identification; it transports no topology. -/
def algebraEquiv : UltraSequence U X ≃ boundedSequenceSubmodule X where
  toFun := UltraSequence.val
  invFun := UltraSequence.mk
  left_inv a := by cases a; rfl
  right_inv a := rfl

instance instAddCommGroup : AddCommGroup (UltraSequence U X) :=
  (algebraEquiv X U).addCommGroup

instance instModule : Module ℝ (UltraSequence U X) :=
  ({ algebraEquiv X U with map_add' := fun _ _ => rfl } :
    UltraSequence U X ≃+ boundedSequenceSubmodule X).module ℝ

instance instCoeFun : CoeFun (UltraSequence U X) (fun _ => ℕ → X) :=
  ⟨fun a => a.val.val⟩

variable {X U}

@[ext] theorem ext {a b : UltraSequence U X} (h : ∀ n, a n = b n) : a = b := by
  have hv : a.val = b.val := Subtype.ext (funext h)
  cases a
  cases b
  cases hv
  rfl

/-- Construct a sequence from an actual uniform norm bound. -/
def ofBounded (U : Ultrafilter ℕ) (a : ℕ → X)
    (ha : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖a n‖ ≤ B) : UltraSequence U X :=
  ⟨⟨a, ha⟩⟩

@[simp] theorem ofBounded_apply (U : Ultrafilter ℕ) (a : ℕ → X)
    (ha : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖a n‖ ≤ B) (n : ℕ) :
    ofBounded U a ha n = a n := rfl

@[simp] theorem zero_apply (n : ℕ) : (0 : UltraSequence U X) n = 0 := rfl

@[simp] theorem add_apply (a b : UltraSequence U X) (n : ℕ) :
    (a + b) n = a n + b n := rfl

@[simp] theorem neg_apply (a : UltraSequence U X) (n : ℕ) : (-a) n = -a n := rfl

@[simp] theorem sub_apply (a b : UltraSequence U X) (n : ℕ) :
    (a - b) n = a n - b n := rfl

@[simp] theorem smul_apply (r : ℝ) (a : UltraSequence U X) (n : ℕ) :
    (r • a) n = r • a n := rfl

theorem bounded (a : UltraSequence U X) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖a n‖ ≤ B := a.val.property

theorem norm_bounded (a : UltraSequence U X) : RealSeqBounded (fun n => ‖a n‖) := by
  obtain ⟨B, _, hB⟩ := a.bounded
  exact ⟨B, fun n => by simpa only [abs_norm] using hB n⟩

/-- The actual ultralimit of coordinate norms. -/
def ultranorm (a : UltraSequence U X) : ℝ := realULim U (fun n => ‖a n‖)

theorem ultranorm_add_le (a b : UltraSequence U X) :
    ultranorm (a + b) ≤ ultranorm a + ultranorm b := by
  have h := realULim_le_realULim U (a + b).norm_bounded
    (a.norm_bounded.add b.norm_bounded)
    (Filter.Eventually.of_forall (fun n => norm_add_le (a n) (b n)))
  simpa only [ultranorm, add_apply, realULim_add U a.norm_bounded b.norm_bounded] using h

theorem ultranorm_smul (r : ℝ) (a : UltraSequence U X) :
    ultranorm (r • a) = ‖r‖ * ultranorm a := by
  simp only [ultranorm, smul_apply, norm_smul]
  exact realULim_const_mul U ‖r‖ a.norm_bounded

variable (X U)

/-- The proved seminorm; no bounded-vector convergence is asserted. -/
def seminorm : Seminorm ℝ (UltraSequence U X) :=
  Seminorm.of ultranorm ultranorm_add_le ultranorm_smul

instance instSeminormedAddCommGroup : SeminormedAddCommGroup (UltraSequence U X) :=
  (seminorm X U).toAddGroupSeminorm.toSeminormedAddCommGroup

instance instNormedSpace : NormedSpace ℝ (UltraSequence U X) where
  norm_smul_le r a := (ultranorm_smul r a).le

variable {X U}

theorem norm_eq_realULim (a : UltraSequence U X) :
    ‖a‖ = realULim U (fun n => ‖a n‖) := rfl

/-- Constant bounded sequences. -/
def constant (U : Ultrafilter ℕ) (x : X) : UltraSequence U X :=
  ofBounded U (fun _ => x) ⟨‖x‖, norm_nonneg x, fun _ => le_rfl⟩

@[simp] theorem constant_apply (U : Ultrafilter ℕ) (x : X) (n : ℕ) :
    constant U x n = x := rfl

end UltraSequence

/-- The normed space obtained by identifying sequences at zero ultradistance. -/
abbrev UltraQuotient (U : Ultrafilter ℕ) (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  SeparationQuotient (UltraSequence U X)

variable {X} (U : Ultrafilter ℕ)

/-- Projection to the zero-ultranorm quotient. -/
def classOf (a : UltraSequence U X) : UltraQuotient U X := SeparationQuotient.mk a

theorem classOf_surjective (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    Function.Surjective (classOf U (X := X)) :=
  SeparationQuotient.surjective_mk

@[simp] theorem classOf_zero : classOf U (0 : UltraSequence U X) = 0 := rfl

@[simp] theorem classOf_add (a b : UltraSequence U X) :
    classOf U (a + b) = classOf U a + classOf U b := rfl

@[simp] theorem classOf_neg (a : UltraSequence U X) : classOf U (-a) = -classOf U a := rfl

@[simp] theorem classOf_sub (a b : UltraSequence U X) :
    classOf U (a - b) = classOf U a - classOf U b := rfl

@[simp] theorem classOf_smul (r : ℝ) (a : UltraSequence U X) :
    classOf U (r • a) = r • classOf U a := rfl

theorem norm_classOf (a : UltraSequence U X) :
    ‖classOf U a‖ = realULim U (fun n => ‖a n‖) := rfl

theorem norm_sub_classOf (a b : UltraSequence U X) :
    ‖classOf U a - classOf U b‖ = realULim U (fun n => ‖a n - b n‖) := by
  rw [← classOf_sub, norm_classOf]
  rfl

theorem classOf_eq_iff (a b : UltraSequence U X) :
    classOf U a = classOf U b ↔ realULim U (fun n => ‖a n - b n‖) = 0 := by
  rw [← norm_sub_classOf, norm_eq_zero, sub_eq_zero]

/-- Constant sequences embed the original space isometrically and linearly. -/
def constantEmbedding : X →ₗᵢ[ℝ] UltraQuotient U X where
  toFun x := classOf U (UltraSequence.constant U x)
  map_add' x y := by
    rw [← classOf_add]
    congr 1
  map_smul' r x := by
    rw [← classOf_smul]
    congr 1
  norm_map' x := by
    change ‖classOf U (UltraSequence.constant U x)‖ = ‖x‖
    rw [norm_classOf]
    exact realULim_const U ‖x‖

@[simp] theorem constantEmbedding_apply (x : X) :
    constantEmbedding U x = classOf U (UltraSequence.constant U x) := rfl

instance ultraQuotient_nontrivial [Nontrivial X] : Nontrivial (UltraQuotient U X) :=
  (constantEmbedding U (X := X)).injective.nontrivial

/-- The actual Banach completion of the normed ultralimit quotient. -/
abbrev UltraCompletion (U : Ultrafilter ℕ) (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  UniformSpace.Completion (UltraQuotient U X)

instance ultraCompletion_nontrivial [Nontrivial X] : Nontrivial (UltraCompletion U X) :=
  (UniformSpace.Completion.toComplₗᵢ : UltraQuotient U X →ₗᵢ[ℝ]
    UltraCompletion U X).injective.nontrivial

end Tingley

end

end OAI
