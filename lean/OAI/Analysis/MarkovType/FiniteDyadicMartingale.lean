import OAI.Analysis.MarkovType.FiniteDyadicProbability
import OAI.Analysis.MarkovType.FiniteMartingaleBasic
import OAI.Analysis.MarkovType.FiniteMarcinkiewicz
import Mathlib.Tactic.Module

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

abbrev DyadicAtom (N : ℕ) := Unit ⊕ (Σ j : Fin N, DyadicWord j.val)

def dyadicInputWeight {N : ℕ} : DyadicAtom N → ℝ
  | .inl _ => 1
  | .inr ⟨j, α⟩ => (dyadicLaw j.val).mass α

theorem dyadicInputWeight_nonneg {N : ℕ} (a : DyadicAtom N) :
    0 ≤ dyadicInputWeight a := by
  cases a with
  | inl u => exact zero_le_one
  | inr a => exact (dyadicLaw a.1.val).mass_nonneg a.2

def dyadicRoot {N : ℕ} (φ : DyadicAtom N → E) : E := φ (.inl ())

def dyadicCoefficient {N : ℕ} (φ : DyadicAtom N → E) (j : Fin N)
    (α : DyadicWord j.val) : E := φ (.inr ⟨j, α⟩)

def dyadicSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem dyadicSign_not (b : Bool) : dyadicSign (!b) = -dyadicSign b := by
  cases b <;> norm_num [dyadicSign]

def dyadicIncrement {N : ℕ} (φ : DyadicAtom N → E) (j : Fin N)
    (ω : DyadicWord N) : E :=
  dyadicSign (ω j) • dyadicCoefficient φ j
    (dyadicPrefix ω j.val (Nat.le_of_lt j.is_lt))

@[simp] theorem norm_dyadicIncrement {N : ℕ} (φ : DyadicAtom N → E)
    (j : Fin N) (ω : DyadicWord N) :
    ‖dyadicIncrement φ j ω‖ =
      ‖dyadicCoefficient φ j (dyadicPrefix ω j.val (Nat.le_of_lt j.is_lt))‖ := by
  cases h : ω j <;> simp [dyadicIncrement, dyadicSign, h]

theorem dyadicIncrement_norm_predictable {N : ℕ} (φ : DyadicAtom N → E) (j : Fin N) :
    (dyadicFiltration N).AdaptedAt j.val (fun ω => ‖dyadicIncrement φ j ω‖) := by
  intro ω η h
  change ‖dyadicIncrement φ j ω‖ = ‖dyadicIncrement φ j η‖
  rw [norm_dyadicIncrement, norm_dyadicIncrement,
    dyadicPrefix_eq_of_rel (Nat.le_of_lt j.is_lt) h]

theorem dyadicIncrement_adapted {N : ℕ} (φ : DyadicAtom N → E) (j : Fin N) :
    (dyadicFiltration N).AdaptedAt (j.val + 1) (dyadicIncrement φ j) := by
  intro ω η h
  have hprefix := dyadicPrefix_eq_of_rel (Nat.le_of_lt j.is_lt)
    ((dyadicFiltration N).refines (Nat.le_succ j.val) h)
  have hbit : ω j = η j := h j (Nat.lt_succ_self j.val)
  simp only [dyadicIncrement, hprefix, hbit]

@[simp] theorem dyadicIncrement_flip {N : ℕ} (φ : DyadicAtom N → E)
    (j : Fin N) (ω : DyadicWord N) :
    dyadicIncrement φ j (dyadicFlip j ω) = -dyadicIncrement φ j ω := by
  simp only [dyadicIncrement, dyadicFlip_at, dyadicSign_not, dyadicFlip_prefix, neg_smul]

theorem dyadicIncrement_zero_conditional {N : ℕ} (φ : DyadicAtom N → E) (j : Fin N) :
    HasZeroConditionalSum (dyadicLaw N) ((dyadicFiltration N).part j.val)
      (dyadicIncrement φ j) := by
  classical
  intro a
  let f : DyadicWord N → E := fun ω =>
    if ((dyadicFiltration N).part j.val).r ω a then
      (dyadicLaw N).mass ω • dyadicIncrement φ j ω else 0
  have hflip (ω : DyadicWord N) : f (dyadicFlip j ω) = -f ω := by
    have hrel := dyadicFlip_rel j ω
    have hevent : ((dyadicFiltration N).part j.val).r (dyadicFlip j ω) a ↔
        ((dyadicFiltration N).part j.val).r ω a :=
      ⟨fun h => ((dyadicFiltration N).part j.val).trans'
          (((dyadicFiltration N).part j.val).symm' hrel) h,
        fun h => ((dyadicFiltration N).part j.val).trans' hrel h⟩
    simp only [f, hevent, dyadicLaw_mass, dyadicIncrement_flip, smul_neg]
    split_ifs <;> simp
  have hsum : (∑ ω, f ω) = -(∑ ω, f ω) := by
    calc
      _ = ∑ ω, f (dyadicFlip j ω) := ((dyadicFlipEquiv j).sum_comp f).symm
      _ = ∑ ω, -f ω := Finset.sum_congr rfl (fun ω _ => hflip ω)
      _ = -(∑ ω, f ω) := by rw [Finset.sum_neg_distrib]
  have hadd : (∑ ω, f ω) + (∑ ω, f ω) = 0 := add_eq_zero_iff_eq_neg.mpr hsum
  change (∑ ω, f ω) = 0
  calc
    _ = (2 : ℝ)⁻¹ • ((∑ ω, f ω) + (∑ ω, f ω)) := by module
    _ = 0 := by rw [hadd, smul_zero]

def dyadicProcess {N : ℕ} (φ : DyadicAtom N → E) : ℕ → DyadicWord N → E
  | 0 => fun _ => dyadicRoot φ
  | n + 1 => fun ω => dyadicProcess φ n ω +
      if hn : n < N then dyadicIncrement φ ⟨n, hn⟩ ω else 0

@[simp] theorem dyadicProcess_zero {N : ℕ} (φ : DyadicAtom N → E) (ω : DyadicWord N) :
    dyadicProcess φ 0 ω = dyadicRoot φ := rfl

theorem dyadicProcess_difference_succ {N : ℕ} (φ : DyadicAtom N → E)
    (n : ℕ) (ω : DyadicWord N) :
    finiteDifference (dyadicProcess φ) (n + 1) ω =
      if hn : n < N then dyadicIncrement φ ⟨n, hn⟩ ω else 0 := by
  rw [finiteDifference_succ]
  simp only [dyadicProcess, add_sub_cancel_left]

theorem dyadicProcess_adapted {N : ℕ} (φ : DyadicAtom N → E) (n : ℕ) :
    (dyadicFiltration N).AdaptedAt n (dyadicProcess φ n) := by
  induction n with
  | zero => intro ω η h; rfl
  | succ n ih =>
      intro ω η h
      have hprev := ih ((dyadicFiltration N).refines (Nat.le_succ n) h)
      by_cases hn : n < N
      · have hinc := dyadicIncrement_adapted φ (⟨n, hn⟩ : Fin N) h
        simp only [dyadicProcess, dite_eq_left hn, hprev, hinc]
      · simp only [dyadicProcess, dite_eq_right hn, hprev]

theorem dyadicProcess_isMartingale {N : ℕ} (φ : DyadicAtom N → E) (K : ℕ) :
    (dyadicFiltration N).IsMartingaleUpTo (dyadicLaw N) (dyadicProcess φ) K := by
  refine ⟨fun n _ => dyadicProcess_adapted φ n, ?_⟩
  intro n hn hnK
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      by_cases hnN : n < N
      · have hd : finiteDifference (dyadicProcess φ) (n + 1) =
            dyadicIncrement φ (⟨n, hnN⟩ : Fin N) := by
          funext ω
          rw [dyadicProcess_difference_succ, dite_eq_left hnN]
        simpa only [Nat.add_sub_cancel, hd] using
          dyadicIncrement_zero_conditional φ (⟨n, hnN⟩ : Fin N)
      · have hd : finiteDifference (dyadicProcess φ) (n + 1) = fun _ => (0 : E) := by
          funext ω
          rw [dyadicProcess_difference_succ, dite_eq_right hnN]
        simpa only [Nat.add_sub_cancel, hd] using
          hasZeroConditionalSum_zero (dyadicLaw N) ((dyadicFiltration N).part n)

theorem dyadicProcess_add {N : ℕ} (φ ψ : DyadicAtom N → E) (n : ℕ) (ω : DyadicWord N) :
    dyadicProcess (φ + ψ) n ω = dyadicProcess φ n ω + dyadicProcess ψ n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hn : n < N
      · simp only [dyadicProcess, dite_eq_left hn, ih, dyadicIncrement, dyadicCoefficient,
          Pi.add_apply, smul_add]
        abel
      · simp only [dyadicProcess, dite_eq_right hn, ih, add_zero]

theorem dyadicProcess_smul {N : ℕ} (c : ℝ) (φ : DyadicAtom N → E)
    (n : ℕ) (ω : DyadicWord N) :
    dyadicProcess (c • φ) n ω = c • dyadicProcess φ n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hn : n < N
      · simp only [dyadicProcess, dite_eq_left hn, ih, dyadicIncrement, dyadicCoefficient,
          Pi.smul_apply]
        module
      · simp only [dyadicProcess, dite_eq_right hn, ih, add_zero]

def dyadicSynthesis (N : ℕ) : (DyadicAtom N → E) →ₗ[ℝ] (DyadicWord N → E) where
  toFun φ := dyadicProcess φ N
  map_add' φ ψ := funext (dyadicProcess_add φ ψ N)
  map_smul' c φ := funext (dyadicProcess_smul c φ N)

theorem dyadicIncrement_moment {N : ℕ} (φ : DyadicAtom N → E) (p : ℝ) (j : Fin N) :
    finiteMoment (dyadicLaw N).mass p (dyadicIncrement φ j) =
      (dyadicLaw j.val).expect (fun α => ‖dyadicCoefficient φ j α‖ ^ p) := by
  change (dyadicLaw N).expect (fun ω => ‖dyadicIncrement φ j ω‖ ^ p) = _
  simp_rw [norm_dyadicIncrement]
  exact dyadicLaw_expect_prefix (Nat.le_of_lt j.is_lt)
    (fun α => ‖dyadicCoefficient φ j α‖ ^ p)

omit sectionNormedSpaceℝE in
theorem dyadicInputMoment_prefixes [NormedSpace ℝ E] {N : ℕ} (φ : DyadicAtom N → E) (p : ℝ) :
    finiteMoment dyadicInputWeight p φ = ‖dyadicRoot φ‖ ^ p +
      ∑ j : Fin N, (dyadicLaw j.val).expect (fun α => ‖dyadicCoefficient φ j α‖ ^ p) := by
  classical
  simp only [finiteMoment, Fintype.sum_sum_type, Fintype.sum_sigma,
    dyadicInputWeight, dyadicRoot, dyadicCoefficient, FiniteLaw.expect]
  simp

theorem dyadicInputMoment {N : ℕ} (φ : DyadicAtom N → E) (p : ℝ) :
    finiteMoment dyadicInputWeight p φ = ‖dyadicRoot φ‖ ^ p +
      ∑ j : Fin N, finiteMoment (dyadicLaw N).mass p (dyadicIncrement φ j) := by
  simp_rw [dyadicIncrement_moment]
  exact dyadicInputMoment_prefixes φ p

end MarkovSuperreflexivity

end

end OAI
