import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.MetricSpace.ProperSpace
import OAI.Analysis.FactorGeneration.GroupTrace

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem operator_norm_one_le : ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro x; simp)

/-- Operator-norm bounded sequences, as an actual star subalgebra of pointwise sequences. -/
def boundedSequences (M : VonNeumannAlgebra H) : StarSubalgebra ℂ (ℕ → M.toStarSubalgebra) where
  carrier := {a | ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖a n‖ ≤ C}
  zero_mem' := ⟨0, le_rfl, by simp⟩
  one_mem' := ⟨1, by norm_num, fun n => operator_norm_one_le⟩
  add_mem' := by
    rintro a b ⟨C,hC,ha⟩ ⟨D,hD,hb⟩
    exact ⟨C+D, add_nonneg hC hD, fun n =>
      (norm_add_le _ _).trans (add_le_add (ha n) (hb n))⟩
  mul_mem' := by
    rintro a b ⟨C,hC,ha⟩ ⟨D,hD,hb⟩
    exact ⟨C*D, mul_nonneg hC hD, fun n =>
      (norm_mul_le _ _).trans (mul_le_mul (ha n) (hb n) (norm_nonneg _) hC)⟩
  algebraMap_mem' c := by
    refine ⟨‖c‖, norm_nonneg _, fun n => ?_⟩
    change ‖algebraMap ℂ M.toStarSubalgebra c‖ ≤ ‖c‖
    rw [Algebra.algebraMap_eq_smul_one, norm_smul]
    exact (mul_le_mul_of_nonneg_left operator_norm_one_le (norm_nonneg c)).trans_eq (mul_one _)
  star_mem' := by
    rintro a ⟨C,hC,ha⟩
    refine ⟨C,hC,fun n => ?_⟩
    change ‖star (a n : H →L[ℂ] H)‖ ≤ C
    simpa [ContinuousLinearMap.star_eq_adjoint] using ha n

abbrev Bounded (M : VonNeumannAlgebra H) := boundedSequences M

variable (τ : TracialRepresentation M) (l : Filter ℕ)
/-- The trace-null equivalence relation, before descending algebra operations. -/
def TraceRel (a b : Bounded M) : Prop :=
  Tendsto (fun n => τ.norm₂ (a.val n-b.val n)) l (𝓝 0)

theorem traceRel_refl (a : Bounded M) : TraceRel τ l a a := by
  simp only [TraceRel, sub_self, τ.norm₂_zero]
  exact tendsto_const_nhds

theorem traceRel_symm {a b : Bounded M} (h : TraceRel τ l a b) : TraceRel τ l b a := by
  simpa only [TraceRel, τ.norm₂_sub, norm_sub_rev] using h

theorem traceRel_trans {a b c : Bounded M}
    (hab : TraceRel τ l a b) (hbc : TraceRel τ l b c) : TraceRel τ l a c := by
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using hab.add hbc)
  have he : a.val n-c.val n = (a.val n-b.val n)+(b.val n-c.val n) := by abel
  rw [he]
  exact τ.norm₂_add_le _ _

theorem traceRel_add {a b c d : Bounded M}
    (hab : TraceRel τ l a b) (hcd : TraceRel τ l c d) : TraceRel τ l (a+c) (b+d) := by
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using hab.add hcd)
  change τ.norm₂ ((a.val n+c.val n)-(b.val n+d.val n)) ≤ _
  have he : (a.val n+c.val n)-(b.val n+d.val n) =
      (a.val n-b.val n)+(c.val n-d.val n) := by abel
  rw [he]
  exact τ.norm₂_add_le _ _

theorem traceRel_mul {a b c d : Bounded M}
    (hab : TraceRel τ l a b) (hcd : TraceRel τ l c d) : TraceRel τ l (a*c) (b*d) := by
  obtain ⟨C,hC,hc⟩ := c.property
  obtain ⟨B,hB,hb⟩ := b.property
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using (hab.mul_const C).add (hcd.const_mul B))
  change τ.norm₂ (a.val n*c.val n-b.val n*d.val n) ≤ _
  have he : a.val n*c.val n-b.val n*d.val n =
      (a.val n-b.val n)*c.val n+b.val n*(c.val n-d.val n) := by noncomm_ring
  rw [he]
  exact (τ.norm₂_add_le _ _).trans (add_le_add
    ((τ.norm₂_mul_le_right _ _).trans (mul_le_mul_of_nonneg_left (hc n) (norm_nonneg _)))
    ((τ.norm₂_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))))

theorem traceRel_star {a b : Bounded M} (hab : TraceRel τ l a b) :
    TraceRel τ l (star a) (star b) := by
  change Tendsto (fun n => τ.norm₂ (star (a.val n)-star (b.val n))) l (𝓝 0)
  simpa only [TraceRel, ← star_sub, τ.norm₂_star] using hab

/-- Algebra congruence proved from actual trace-norm estimates. -/
def traceCongruence : RingCon (Bounded M) where
  r := TraceRel τ l
  iseqv := ⟨traceRel_refl τ l, traceRel_symm τ l, traceRel_trans τ l⟩
  add' := traceRel_add τ l
  mul' := traceRel_mul τ l

/-- Underlying ring of the tracial ultrapower when l is a free ultrafilter. -/
abbrev TracialQuotient := (traceCongruence τ l).Quotient

def quotientMap : Bounded M →+* TracialQuotient τ l := (traceCongruence τ l).mk'

end

section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

theorem quotientMap_eq_iff (a b : Bounded M) :
    quotientMap τ l a = quotientMap τ l b ↔ TraceRel τ l a b := Quotient.eq

theorem quotientMap_surjective : Function.Surjective (quotientMap τ l) := Quotient.mk_surjective

instance : Star (TracialQuotient τ l) :=
  ⟨Quotient.map' star (fun _ _ h => traceRel_star τ l h)⟩

@[simp] theorem quotientMap_star (a : Bounded M) :
    quotientMap τ l (star a) = star (quotientMap τ l a) := rfl

instance : StarRing (TracialQuotient τ l) where
  star_involutive a := Quotient.inductionOn a (fun a => by
    change quotientMap τ l (star (star a)) = quotientMap τ l a
    rw [star_star])
  star_mul a b := Quotient.inductionOn₂ a b (fun a b => by
    change quotientMap τ l (star (a*b)) = quotientMap τ l (star b*star a)
    rw [star_mul])
  star_add a b := Quotient.inductionOn₂ a b (fun a b => by
    change quotientMap τ l (star (a+b)) = quotientMap τ l (star a+star b)
    rw [star_add])

@[simp] theorem quotientMap_smul (c : ℂ) (a : Bounded M) :
    quotientMap τ l (c • a) = c • quotientMap τ l a := rfl

instance : StarModule ℂ (TracialQuotient τ l) where
  star_smul c a := Quotient.inductionOn a (fun a =>
    congrArg (quotientMap τ l) (star_smul c a))

def quotientStarAlgHom : Bounded M →⋆ₐ[ℂ] TracialQuotient τ l where
  __ := quotientMap τ l
  commutes' _ := rfl
  map_star' := quotientMap_star τ l

end

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem TracialRepresentation.trace_sub (a b : M.toStarSubalgebra) :
    τ.trace (a-b) = τ.trace a-τ.trace b := inner_sub_right _ _ _

@[simp] theorem TracialRepresentation.trace_add (a b : M.toStarSubalgebra) :
    τ.trace (a+b) = τ.trace a+τ.trace b := inner_add_right _ _ _

@[simp] theorem TracialRepresentation.trace_smul (c : ℂ) (a : M.toStarSubalgebra) :
    τ.trace (c • a) = c*τ.trace a := inner_smul_right _ _ _

def traceRep (a : Bounded M) : ℂ := limUnder (ω : Filter ℕ) (fun n => τ.trace (a.val n))

theorem traceRep_tendsto (a : Bounded M) :
    Tendsto (fun n => τ.trace (a.val n)) (ω : Filter ℕ) (𝓝 (traceRep τ ω a)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨C,_,ha⟩ := a.property
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) C).ultrafilter_le_nhds
    (ω.map (fun n => τ.trace (a.val n))) (by
      apply le_principal_iff.mpr
      change {n | τ.trace (a.val n) ∈ Metric.closedBall 0 C} ∈ (ω : Filter ℕ)
      exact Filter.Eventually.of_forall (fun n => by
        simpa using ((τ.norm_trace_le_norm₂ _).trans (τ.norm₂_le_norm _)).trans (ha n)))
  exact ⟨z,hz⟩

theorem traceRep_eq_of_rel {a b : Bounded M} (h : TraceRel τ (ω : Filter ℕ) a b) :
    traceRep τ ω a = traceRep τ ω b := by
  have hz : Tendsto (fun n => ‖τ.trace (a.val n)-τ.trace (b.val n)‖)
      (ω : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h
    rw [← τ.trace_sub]
    exact τ.norm_trace_le_norm₂ _
  have hnorm := ((traceRep_tendsto τ ω a).sub (traceRep_tendsto τ ω b)).norm
  exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique hnorm hz))

/-- The actual ultralimit trace on the operator-algebra quotient. -/
def quotientTrace : TracialQuotient τ (ω : Filter ℕ) → ℂ :=
  Quotient.lift (traceRep τ ω) (fun _ _ h => traceRep_eq_of_rel τ ω h)

@[simp] theorem quotientTrace_mk (a : Bounded M) :
    quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) a) = traceRep τ ω a := rfl

@[simp] theorem quotientTrace_one : quotientTrace τ ω 1 = 1 := by
  apply tendsto_nhds_unique (traceRep_tendsto τ ω 1)
  simp

theorem quotientTrace_mul_comm (a b : TracialQuotient τ (ω : Filter ℕ)) :
    quotientTrace τ ω (a*b) = quotientTrace τ ω (b*a) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      change traceRep τ ω (a*b) = traceRep τ ω (b*a)
      apply tendsto_nhds_unique (traceRep_tendsto τ ω (a*b))
      have ht := traceRep_tendsto τ ω (b*a)
      change Tendsto (fun n => τ.trace (b.val n*a.val n)) _ _ at ht
      change Tendsto (fun n => τ.trace (a.val n*b.val n)) _ _
      simpa only [τ.trace_mul_comm] using ht

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology
namespace Generator.Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

/-- Unitary norm bound without requiring a separate nontriviality instance. -/
theorem unitary_norm_le (w : M.toStarSubalgebra) (hw : star w*w = 1) : ‖w‖ ≤ 1 := by
  have h : ‖star w*w‖ = ‖w‖*‖w‖ := CStarRing.norm_star_mul_self
  rw [hw] at h
  have hone : ‖(1 : M.toStarSubalgebra)‖ ≤ 1 := operator_norm_one_le
  nlinarith [norm_nonneg w]

/-- A quotient commutant condition controls all coordinate unitaries uniformly.
The filter need not be ultra for this diagonal-selection step. -/
theorem uniform_commutator_decay
    (P : StarSubalgebra ℂ M.toStarSubalgebra) (b : Bounded M)
    (hcomm : ∀ w : Bounded M, (∀ n, w.val n ∈ P) →
      quotientMap τ l w * quotientMap τ l b = quotientMap τ l b * quotientMap τ l w)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in l, ∀ w : M.toStarSubalgebra, w ∈ P → star w*w = 1 → w*star w = 1 →
      τ.norm₂ (w*b.val n-b.val n*w) < ε := by
  classical
  let bad (n : ℕ) := ∃ w : M.toStarSubalgebra,
    w ∈ P ∧ star w*w = 1 ∧ w*star w = 1 ∧ ε ≤ τ.norm₂ (w*b.val n-b.val n*w)
  let w (n : ℕ) : M.toStarSubalgebra := if h : bad n then h.choose else 1
  have hw (n : ℕ) : w n ∈ P ∧ star (w n)*w n = 1 ∧ w n*star (w n) = 1 := by
    dsimp [w]
    split_ifs with h
    · exact ⟨h.choose_spec.1,h.choose_spec.2.1,h.choose_spec.2.2.1⟩
    · simp
  let W : Bounded M := ⟨w, ⟨1, zero_le_one, fun n => unitary_norm_le (w n) (hw n).2.1⟩⟩
  have hc := hcomm W (fun n => (hw n).1)
  rw [← map_mul, ← map_mul, quotientMap_eq_iff] at hc
  have ht : ∀ᶠ n in l, τ.norm₂ (w n*b.val n-b.val n*w n) < ε :=
    hc (Iio_mem_nhds hε)
  filter_upwards [ht] with n hn v hv hv₁ hv₂
  by_contra hnot
  have hb : bad n := ⟨v,hv,hv₁,hv₂,le_of_not_gt hnot⟩
  have he : w n = hb.choose := dite_eq_left hb
  rw [he] at hn
  exact (not_lt_of_ge hb.choose_spec.2.2.2) hn

end Generator.Tracial

end

end OAI
