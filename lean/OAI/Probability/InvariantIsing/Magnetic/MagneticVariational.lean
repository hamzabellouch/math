import OAI.Probability.InvariantIsing.Magnetic.MagneticL1
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldParameter

namespace OAI

/-! The prescribed-magnetization variational expression in (7.3)--(7.4).
One common covariance path is used for every field group. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def magneticGroupValue {A : Type*} [Fintype A] (γ m : A → ℝ) (h : FieldStep) : ℝ :=
  ∑ a, γ a * constrainedFieldValue h (m a)

def magneticEntropyFunctional {A : Type*} [Fintype A] (γ m : A → ℝ)
    (p : OverlapPath) : EReal :=
  ⨆ h : FieldStep, ((magneticGroupValue γ m h + fieldPairing p h / 2 : ℝ) : EReal)

def magneticVariationalFunctional {A : Type*} [Fintype A] (R : ℝ → ℝ) (γ m : A → ℝ) : EReal :=
  ⨅ p : OverlapPath, magneticEntropyFunctional γ m p + (spectralFunctional R p : EReal)

def RationalMagnetization (A : Type*) := {m : A → ℚ // ∀ a, |(m a : ℝ)| < 1}

instance {A : Type*} : Inhabited (RationalMagnetization A) :=
  ⟨⟨fun _ => 0, by intro a; norm_num⟩⟩

def finiteMagneticFunctional {A : Type*} [Fintype A] (R : ℝ → ℝ) (γ c : A → ℝ) : EReal :=
  ⨆ m : RationalMagnetization A,
    ((∑ a, γ a * c a * (m.val a : ℝ) : ℝ) : EReal) +
      magneticVariationalFunctional R γ (fun a => (m.val a : ℝ))

lemma magneticGroupValue_zero {A : Type*} [Fintype A] (γ : A → ℝ)
    (hγ : ∑ a, γ a = 1) (h : FieldStep) :
    magneticGroupValue γ (fun _ => 0) h = fieldValue h 0 := by
  simp only [magneticGroupValue, constrainedFieldValue_zero_magnetization,
    ← Finset.sum_mul, hγ, one_mul]

lemma magneticGroupValue_le {A : Type*} [Fintype A] (γ m : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hm : ∀ a, |m a| ≤ 1) (h : FieldStep) :
    magneticGroupValue γ m h ≤ fieldValue h 0 := by
  calc
    _ ≤ ∑ a, γ a * fieldValue h 0 := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (by
        simpa only [zero_mul, sub_zero] using constrainedFieldValue_le_trial h (hm a) 0) (hγ a))
    _ = _ := by rw [← Finset.sum_mul, hγsum, one_mul]

lemma magneticEntropyFunctional_le {A : Type*} [Fintype A] (γ m : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1) (hm : ∀ a, |m a| ≤ 1)
    (p : OverlapPath) : magneticEntropyFunctional γ m p ≤ entropyFunctional p := by
  apply iSup_le
  intro h
  apply (show ((magneticGroupValue γ m h + fieldPairing p h / 2 : ℝ) : EReal) ≤
    ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal) from
    EReal.coe_le_coe (add_le_add (magneticGroupValue_le γ m hγ hγsum hm h) le_rfl)).trans
  exact le_iSup (fun h : FieldStep => ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)) h

lemma magneticEntropyFunctional_zero {A : Type*} [Fintype A] (γ : A → ℝ)
    (hγ : ∑ a, γ a = 1) (p : OverlapPath) :
    magneticEntropyFunctional γ (fun _ => 0) p = entropyFunctional p := by
  simp only [magneticEntropyFunctional, magneticGroupValue_zero γ hγ, entropyFunctional]

lemma magneticVariationalFunctional_zero {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ : A → ℝ) (hγ : ∑ a, γ a = 1) :
    magneticVariationalFunctional R γ (fun _ => 0) = variationalFunctional R := by
  simp only [magneticVariationalFunctional, magneticEntropyFunctional_zero γ hγ,
    variationalFunctional]

lemma magneticVariationalFunctional_le {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ m : A → ℝ) (hγ : ∀ a, 0 ≤ γ a)
    (hγsum : ∑ a, γ a = 1) (hm : ∀ a, |m a| ≤ 1) :
    magneticVariationalFunctional R γ m ≤ variationalFunctional R := by
  apply iInf_mono
  intro p
  exact add_le_add (magneticEntropyFunctional_le γ m hγ hγsum hm p) le_rfl

lemma finiteMagneticFunctional_lower {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ c : A → ℝ) (hγ : ∑ a, γ a = 1) :
    variationalFunctional R ≤ finiteMagneticFunctional R γ c := by
  have hh := le_iSup (fun m : RationalMagnetization A =>
    ((∑ a, γ a * c a * (m.val a : ℝ) : ℝ) : EReal) +
      magneticVariationalFunctional R γ (fun a => (m.val a : ℝ)))
    (⟨fun _ => 0, by intro a; norm_num⟩ : RationalMagnetization A)
  simpa only [Rat.cast_zero, mul_zero, Finset.sum_const_zero, EReal.coe_zero, zero_add,
    magneticVariationalFunctional_zero R γ hγ, finiteMagneticFunctional] using hh

lemma finiteMagneticFunctional_upper {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ c : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1) :
    finiteMagneticFunctional R γ c ≤ variationalFunctional R +
      ((∑ a, γ a * |c a| : ℝ) : EReal) := by
  apply iSup_le
  intro m
  have hcm : (∑ a, γ a * c a * (m.val a : ℝ)) ≤ ∑ a, γ a * |c a| := by
    apply Finset.sum_le_sum
    intro a _
    calc
      γ a * c a * (m.val a : ℝ) = γ a * (c a * (m.val a : ℝ)) := by ring
      _ ≤ γ a * |c a * (m.val a : ℝ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (hγ a)
      _ ≤ γ a * |c a| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_right (abs_nonneg _) (m.property a).le) (hγ a)
  have hv := magneticVariationalFunctional_le R γ (fun a => (m.val a : ℝ))
    hγ hγsum (fun a => (m.property a).le)
  exact (add_le_add (EReal.coe_le_coe hcm) hv).trans_eq (add_comm _ _)

end InvariantIsing

end

end OAI
