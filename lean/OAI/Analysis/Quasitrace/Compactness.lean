import OAI.Analysis.Quasitrace.Extension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! Closed quasitrace constraints and compactness of normalized two-quasitraces. -/

section

noncomputable section
open scoped ComplexOrder
namespace Kaplansky
variable (A : Type*) [CStarAlgebra A]

inductive QuasitraceConstraint where
  | positive (x : A)
  | swap (x : A)
  | realImag (h k : A) (hh : IsSelfAdjoint h) (hk : IsSelfAdjoint k)
  | add (S : NonUnitalStarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
      (hc : ∀ x y : S, x * y = y * x) (x y : S)
  | smul (S : NonUnitalStarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
      (hc : ∀ x y : S, x * y = y * x) (c : ℂ) (x : S)

variable {A}

def QuasitraceConstraint.Holds : QuasitraceConstraint A → (A → ℂ) → Prop
  | .positive x, f => 0 ≤ f (star x * x)
  | .swap x, f => f (star x * x) = f (x * star x)
  | .realImag h k _ _, f => f (h + Complex.I • k) = f h + Complex.I * f k
  | .add _ _ _ x y, f => f (x + y) = f x + f y
  | .smul _ _ _ c x, f => f (c • x) = c * f x

/-- All coordinate requirements reconstruct the original bundled object,
including complex linearity on each closed nonunital abelian algebra. -/
def oneQuasitraceOfConstraints (f : A → ℂ)
    (hf : ∀ q : QuasitraceConstraint A, q.Holds f) : OneQuasitrace A where
  toFun := f
  square_nonneg x := hf (.positive x)
  square_swap x := hf (.swap x)
  real_imag h k hh hk := hf (.realImag h k hh hk)
  abelian_linear S hS hc := ⟨{
    toFun := fun x => f x
    map_add' := fun x y => hf (.add S hS hc x y)
    map_smul' := fun c x => hf (.smul S hS hc c x)
  }, fun _ => rfl⟩

theorem OneQuasitrace.satisfies_constraint (τ : OneQuasitrace A)
    (q : QuasitraceConstraint A) : q.Holds τ := by
  cases q with
  | positive x => exact τ.square_nonneg x
  | swap x => exact τ.square_swap x
  | realImag h k hh hk => exact τ.real_imag h k hh hk
  | add S hS hc x y =>
      obtain ⟨f, hf⟩ := τ.abelian_linear S hS hc
      exact (hf (x+y)).symm.trans ((f.map_add x y).trans (congrArg₂ (· + ·) (hf x) (hf y)))
  | smul S hS hc c x =>
      obtain ⟨f, hf⟩ := τ.abelian_linear S hS hc
      exact (hf (c • x)).symm.trans ((f.map_smul c x).trans (congrArg (c * ·) (hf x)))

/-- Each requirement is closed in the topology of pointwise convergence. -/
theorem QuasitraceConstraint.isClosed (q : QuasitraceConstraint A) :
    IsClosed {f : A → ℂ | q.Holds f} := by
  cases q with
  | positive x => exact isClosed_le continuous_const (continuous_apply _)
  | swap x => exact isClosed_eq (continuous_apply _) (continuous_apply _)
  | realImag h k hh hk =>
      exact isClosed_eq (continuous_apply _)
        ((continuous_apply h).add (continuous_const.mul (continuous_apply k)))
  | add S hS hc x y =>
      exact isClosed_eq (continuous_apply _) ((continuous_apply (x : A)).add (continuous_apply (y : A)))
  | smul S hS hc c x =>
      exact isClosed_eq (continuous_apply _) (continuous_const.mul (continuous_apply _))

end Kaplansky

end
end

section

noncomputable section
open scoped ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable (A : Type*) [CStarAlgebra A]

abbrev QuasitraceCandidate := (A → ℂ) × (CStarMatrix (Fin 2) (Fin 2) A → ℂ)

/-- Requirements on a function and its actual M₂ corner extension. The
extension is deliberately not required to have unit value one. -/
inductive TwoQuasitraceConstraint where
  | base (q : QuasitraceConstraint A)
  | matrix (q : QuasitraceConstraint (CStarMatrix (Fin 2) (Fin 2) A))
  | normalized
  | corner (a : A)

variable {A}

def TwoQuasitraceConstraint.Holds : TwoQuasitraceConstraint A → QuasitraceCandidate A → Prop
  | .base q, f => q.Holds f.1
  | .matrix q, f => q.Holds f.2
  | .normalized, f => f.1 1 = 1
  | .corner a, f => f.2 (upperLeft a) = f.1 a

theorem TwoQuasitraceConstraint.isClosed (q : TwoQuasitraceConstraint A) :
    IsClosed {f : QuasitraceCandidate A | q.Holds f} := by
  cases q with
  | base q => exact q.isClosed.preimage continuous_fst
  | matrix q => exact q.isClosed.preimage continuous_snd
  | normalized => exact isClosed_eq ((continuous_apply 1).comp continuous_fst) continuous_const
  | corner a =>
      exact isClosed_eq ((continuous_apply (upperLeft a)).comp continuous_snd)
        ((continuous_apply a).comp continuous_fst)

/-- Compact pointwise disks. The factor four for the extension follows
from its unit value two, not an additional assumption. -/
def quasitraceCandidateBox (A : Type*) [CStarAlgebra A] : Set (QuasitraceCandidate A) :=
  (Set.pi Set.univ fun a : A => Metric.closedBall (0 : ℂ) (2 * ‖a‖)) ×ˢ
    (Set.pi Set.univ fun a : CStarMatrix (Fin 2) (Fin 2) A =>
      Metric.closedBall (0 : ℂ) (4 * ‖a‖))

theorem mem_quasitraceCandidateBox (f : QuasitraceCandidate A) :
    f ∈ quasitraceCandidateBox A ↔
      (∀ a, ‖f.1 a‖ ≤ 2 * ‖a‖) ∧ (∀ a, ‖f.2 a‖ ≤ 4 * ‖a‖) := by
  simp [quasitraceCandidateBox, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]

theorem isCompact_quasitraceCandidateBox : IsCompact (quasitraceCandidateBox A) :=
  (isCompact_univ_pi fun _ => isCompact_closedBall _ _).prod
    (isCompact_univ_pi fun _ => isCompact_closedBall _ _)

theorem quasitrace_pair_mem_box (τ : OneQuasitrace A) (hτ : τ.Normalized)
    (σ : OneQuasitrace (CStarMatrix (Fin 2) (Fin 2) A))
    (hc : ∀ a, σ (upperLeft a) = τ a) :
    (τ.toFun, σ.toFun) ∈ quasitraceCandidateBox A := by
  refine (mem_quasitraceCandidateBox _).mpr ⟨τ.normalized_norm_le hτ, ?_⟩
  intro a
  have hu := extension_value_two τ hτ σ hc
  have hb := σ.norm_le_twice a
  rw [hu] at hb
  norm_num only [Complex.re_ofNat] at hb
  nlinarith

/-- Compactness assembles all three whole-algebra axioms and the genuine
matrix extension from bounded finite satisfiability. This is a conditional
construction; finite satisfiability is not deduced from stable finiteness. -/
theorem normalizedTwoQuasitrace_of_finite_constraints
    (hf : ∀ qs : Finset (TwoQuasitraceConstraint A),
      ∃ f ∈ quasitraceCandidateBox A, ∀ q ∈ qs, q.Holds f) :
    ∃ τ : OneQuasitrace A, τ.Normalized ∧ τ.IsTwo := by
  have hn := isCompact_quasitraceCandidateBox (A := A) |>.inter_iInter_nonempty
    (fun q : TwoQuasitraceConstraint A => {f | q.Holds f})
    (fun q => q.isClosed) (fun qs => by
      obtain ⟨f, hb, hf⟩ := hf qs
      exact ⟨f, hb, by simpa only [Set.mem_iInter, Set.mem_ofPred_eq] using hf⟩)
  obtain ⟨f, _, hall⟩ := hn
  have hq : ∀ q : TwoQuasitraceConstraint A, q.Holds f := by
    simpa only [Set.mem_iInter, Set.mem_ofPred_eq] using hall
  let τ := oneQuasitraceOfConstraints f.1 (fun q => hq (.base q))
  let σ := oneQuasitraceOfConstraints f.2 (fun q => hq (.matrix q))
  exact ⟨τ, hq .normalized, σ, fun a => hq (.corner a)⟩

/-- Exact equivalence: the bounded finite condition neither weakens the
quasitrace axioms nor strengthens the required matrix normalization. -/
theorem normalizedTwoQuasitrace_iff_finite_constraints :
    (∃ τ : OneQuasitrace A, τ.Normalized ∧ τ.IsTwo) ↔
      ∀ qs : Finset (TwoQuasitraceConstraint A),
        ∃ f ∈ quasitraceCandidateBox A, ∀ q ∈ qs, q.Holds f := by
  constructor
  · rintro ⟨τ, hτ, σ, hc⟩ qs
    refine ⟨(τ.toFun, σ.toFun), quasitrace_pair_mem_box τ hτ σ hc, ?_⟩
    intro q _
    cases q with
    | base q => exact τ.satisfies_constraint q
    | matrix q => exact σ.satisfies_constraint q
    | normalized => exact hτ
    | corner a => exact hc a
  · exact normalizedTwoQuasitrace_of_finite_constraints

end Kaplansky

end
end

end OAI
