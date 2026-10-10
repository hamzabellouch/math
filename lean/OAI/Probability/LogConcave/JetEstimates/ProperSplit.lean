import Mathlib
import OAI.Probability.LogConcave.JetEstimates.AllSplitBound

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators Classical Matrix.Norms.L2Operator

variable {I J : Type*} [Fintype I] [Fintype J]

lemma bound_norm (A : Matrix I J ℝ) : Bound A (‖A‖^2) := by
  intro v
  have h := A.l2_opNorm_mulVec (WithLp.toLp 2 v)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  change ‖(WithLp.toLp 2 (fun i => ∑j,A i j*v j) : EuclideanSpace ℝ I)‖^2 ≤
    (‖A‖*‖(WithLp.toLp 2 v : EuclideanSpace ℝ J)‖)^2 at hs
  simpa only [mul_pow,EuclideanSpace.real_norm_sq_eq] using hs

lemma Bound.norm_le {A : Matrix I J ℝ} {M : ℝ} (hM : 0≤M) (h : Bound A (M^2)) :
    ‖A‖≤M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg v))).mp
  change ‖(WithLp.toLp 2 (fun i => ∑j,A i j*(WithLp.ofLp v) j) : EuclideanSpace ℝ I)‖^2 ≤
    (M*‖v‖)^2
  simpa only [mul_pow,EuclideanSpace.real_norm_sq_eq] using h (WithLp.ofLp v)

lemma bound_iff_norm_le {A : Matrix I J ℝ} {M : ℝ} (hM : 0≤M) :
    Bound A (M^2) ↔ ‖A‖≤M := by
  refine ⟨Bound.norm_le hM,fun h => ?_⟩
  intro v
  exact (bound_norm A v).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) h 2) (energy_nonneg v))

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators Classical Matrix.Norms.L2Operator

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

def ProperSplit (S : Type u) :=
  {p : S → Bool // (∃s,p s=true) ∧ (∃s,p s=false)}
instance : Fintype (ProperSplit S) := inferInstanceAs (Fintype {_p : S → Bool // _})

def InSlots (p : ProperSplit S) := {s : S // p.val s=true}
def OutSlots (p : ProperSplit S) := {s : S // ¬p.val s=true}
instance (p : ProperSplit S) : Fintype (InSlots p) := inferInstanceAs (Fintype {_s : S // _})
instance (p : ProperSplit S) : Fintype (OutSlots p) := inferInstanceAs (Fintype {_s : S // _})
instance (p : ProperSplit S) : Nonempty (InSlots p) := by
  obtain ⟨s,hs⟩ := p.property.1
  exact ⟨s,hs⟩
instance (p : ProperSplit S) : Nonempty (OutSlots p) := by
  obtain ⟨s,hs⟩ := p.property.2
  exact ⟨s,by simp [hs]⟩

def splitEquiv (p : ProperSplit S) : S ≃ InSlots p ⊕ OutSlots p :=
  (Equiv.sumCompl (fun s => p.val s=true)).symm

def splitMatrix (T : (S → Fin d) → ℝ) (p : ProperSplit S) :
    Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ :=
  fun o i => T (fun s => Sum.elim i o (splitEquiv p s))

def splitEnvelope (T : (S → Fin d) → ℝ) : ℝ :=
  ∑p : ProperSplit S, ‖splitMatrix T p‖

lemma splitEnvelope_nonneg (T : (S → Fin d) → ℝ) : 0 ≤ splitEnvelope T :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma splitMatrix_norm_le (T : (S → Fin d) → ℝ) (p : ProperSplit S) :
    ‖splitMatrix T p‖ ≤ splitEnvelope T :=
  Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ p)

section arbitrary
variable {I O : Type u} [Fintype I] [Fintype O] [Nonempty I] [Nonempty O]

def properOfEquiv (e : S ≃ I ⊕ O) : ProperSplit S :=
  ⟨fun s => (e s).isLeft, by
    constructor
    · obtain ⟨i⟩ := ‹Nonempty I›
      exact ⟨e.symm (Sum.inl i),by simp⟩
    · obtain ⟨o⟩ := ‹Nonempty O›
      exact ⟨e.symm (Sum.inr o),by simp⟩⟩

def leftOfEquiv (e : S ≃ I ⊕ O) : I ≃ InSlots (properOfEquiv e) where
  toFun i := ⟨e.symm (Sum.inl i),by simp [properOfEquiv]⟩
  invFun s := (e s.val).getLeft s.property
  left_inv i := by simp
  right_inv s := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inl_getLeft _ _

def rightOfEquiv (e : S ≃ I ⊕ O) : O ≃ OutSlots (properOfEquiv e) where
  toFun o := ⟨e.symm (Sum.inr o),by simp [properOfEquiv]⟩
  invFun s := (e s.val).getRight (by simpa [properOfEquiv] using s.property)
  left_inv o := by simp
  right_inv s := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inr_getRight _ _

omit [Fintype S] [Fintype I] [Fintype O] in
lemma splitEquiv_ofEquiv (e : S ≃ I ⊕ O) (s : S) :
    splitEquiv (properOfEquiv e) s =
      Sum.map (leftOfEquiv e) (rightOfEquiv e) (e s) := by
  apply (splitEquiv (properOfEquiv e)).symm.injective
  simp only [Equiv.symm_apply_apply]
  cases h : e s with
  | inl i =>
    have he : e.symm (Sum.inl i)=s := e.symm_apply_eq.mpr h.symm
    change s=e.symm (Sum.inl i)
    exact he.symm
  | inr o =>
    have he : e.symm (Sum.inr o)=s := e.symm_apply_eq.mpr h.symm
    change s=e.symm (Sum.inr o)
    exact he.symm

end arbitrary

lemma allSplitBound_envelope (T : (S → Fin d) → ℝ) :
    AllSplitBound T (splitEnvelope T) := by
  intro I O _ _ _ _ _ _ e
  have h := (bound_norm (splitMatrix T (properOfEquiv e))).mono
    (pow_le_pow_left₀ (norm_nonneg _) (splitMatrix_norm_le T (properOfEquiv e)) 2)
  have h' := h.reindex (Equiv.arrowCongr (rightOfEquiv e) (Equiv.refl (Fin d)))
    (Equiv.arrowCongr (leftOfEquiv e) (Equiv.refl (Fin d)))
  convert h' using 1
  ext o i
  unfold splitMatrix
  congr 1
  funext s
  rw [splitEquiv_ofEquiv]
  cases e s <;> simp

lemma splitEnvelope_le {T : (S → Fin d) → ℝ} {M : ℝ}
    (hM : 0≤M) (h : AllSplitBound T M) :
    splitEnvelope T ≤ Fintype.card (ProperSplit S)*M := by
  calc
    _ ≤ ∑p : ProperSplit S,M := Finset.sum_le_sum (fun p _ =>
      Bound.norm_le hM (h _ _ (splitEquiv p)))
    _ = _ := by simp

lemma measurable_splitEnvelope {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → (S → Fin d) → ℝ) (hT : ∀c,Measurable (fun x => T x c)) :
    Measurable (fun x => splitEnvelope (T x)) := by
  apply Finset.measurable_sum
  intro p _
  let : MeasurableSpace (Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ) :=
    inferInstanceAs (MeasurableSpace ((OutSlots p → Fin d) → (InSlots p → Fin d) → ℝ))
  have : BorelSpace (Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ) :=
    inferInstanceAs (BorelSpace ((OutSlots p → Fin d) → (InSlots p → Fin d) → ℝ))
  apply Measurable.norm
  exact Measurable.of_eval (fun _ => Measurable.of_eval (fun _ => hT _))

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
