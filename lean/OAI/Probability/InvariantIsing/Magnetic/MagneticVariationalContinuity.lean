import OAI.Probability.InvariantIsing.Magnetic.MagneticVariational

namespace OAI

/-! Field-alphabet stability of the magnetic variational formula. These
bounds are uniform over all rational interior magnetizations. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma magnetic_field_term_difference {A : Type*} [Fintype A] (γ c d m : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hm : ∀ a, |m a| ≤ 1) :
    |(∑ a, γ a * c a * m a) - ∑ a, γ a * d a * m a| ≤
      ∑ a, γ a * |c a - d a| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, |γ a * c a * m a - γ a * d a * m a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a _
      have he : γ a * c a * m a - γ a * d a * m a = γ a * (c a - d a) * m a := by ring
      rw [he, abs_mul, abs_mul, abs_of_nonneg (hγ a)]
      exact mul_le_of_le_one_right (mul_nonneg (hγ a) (abs_nonneg _)) (hm a)

lemma finiteMagneticFunctional_le_add {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ c d : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) :
    finiteMagneticFunctional R γ c ≤ finiteMagneticFunctional R γ d +
      ((∑ a, γ a * |c a - d a| : ℝ) : EReal) := by
  apply iSup_le
  intro m
  have hb := (abs_le.mp (magnetic_field_term_difference γ c d
    (fun a => (m.val a : ℝ)) hγ (fun a => (m.property a).le))).2
  have hc : ((∑ a, γ a * c a * (m.val a : ℝ) : ℝ) : EReal) ≤
      ((∑ a, γ a * d a * (m.val a : ℝ) : ℝ) : EReal) +
        ((∑ a, γ a * |c a - d a| : ℝ) : EReal) := by
    rw [← EReal.coe_add]
    exact EReal.coe_le_coe (by linarith)
  have hi := le_iSup (fun m : RationalMagnetization A =>
    ((∑ a, γ a * d a * (m.val a : ℝ) : ℝ) : EReal) +
      magneticVariationalFunctional R γ (fun a => (m.val a : ℝ))) m
  calc
    _ ≤ (((∑ a, γ a * d a * (m.val a : ℝ) : ℝ) : EReal) +
        ((∑ a, γ a * |c a - d a| : ℝ) : EReal)) +
          magneticVariationalFunctional R γ (fun a => (m.val a : ℝ)) := add_le_add hc le_rfl
    _ = (((∑ a, γ a * d a * (m.val a : ℝ) : ℝ) : EReal) +
        magneticVariationalFunctional R γ (fun a => (m.val a : ℝ))) +
          ((∑ a, γ a * |c a - d a| : ℝ) : EReal) := by ac_rfl
    _ ≤ _ := add_le_add hi le_rfl

lemma finiteMagneticFunctional_ne_top_bot {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ c : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hRtop : variationalFunctional R ≠ ⊤) (hRbot : variationalFunctional R ≠ ⊥) :
    finiteMagneticFunctional R γ c ≠ ⊤ ∧ finiteMagneticFunctional R γ c ≠ ⊥ := by
  constructor
  · exact ne_top_of_le_ne_top (EReal.add_ne_top hRtop (EReal.coe_ne_top _))
      (finiteMagneticFunctional_upper R γ c hγ hγsum)
  · exact ne_bot_of_le_ne_bot hRbot (finiteMagneticFunctional_lower R γ c hγsum)

theorem abs_finiteMagneticFunctional_sub_le {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ c d : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hRtop : variationalFunctional R ≠ ⊤) (hRbot : variationalFunctional R ≠ ⊥) :
    |(finiteMagneticFunctional R γ c).toReal - (finiteMagneticFunctional R γ d).toReal| ≤
      ∑ a, γ a * |c a - d a| := by
  have hc := finiteMagneticFunctional_ne_top_bot R γ c hγ hγsum hRtop hRbot
  have hd := finiteMagneticFunctional_ne_top_bot R γ d hγ hγsum hRtop hRbot
  have hcd := finiteMagneticFunctional_le_add R γ c d hγ
  have hdc := finiteMagneticFunctional_le_add R γ d c hγ
  rw [← EReal.coe_toReal hc.1 hc.2, ← EReal.coe_toReal hd.1 hd.2, ← EReal.coe_add] at hcd
  rw [← EReal.coe_toReal hd.1 hd.2, ← EReal.coe_toReal hc.1 hc.2, ← EReal.coe_add] at hdc
  have hcd' := EReal.coe_le_coe_iff.mp hcd
  have hdc' := EReal.coe_le_coe_iff.mp hdc
  simp_rw [abs_sub_comm (d _)] at hdc'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end InvariantIsing

end

end OAI
