import OAI.Analysis.KadisonKastler.Basic

namespace OAI

/-! # Finite averages of unitary conjugations -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {G : Type*} [Fintype G] [Nonempty G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Uniform average over a nonempty finite set. -/
def finiteAverage (f : G → V) : V := (Fintype.card G : ℂ)⁻¹ • ∑ g, f g

@[simp]
theorem finiteAverage_const (v : V) : finiteAverage (fun _ : G => v) = v := by
  simp [finiteAverage, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Fintype.card_ne_zero]

omit [Nonempty G] in
theorem finiteAverage_sub (f g : G → V) :
    finiteAverage (fun a => f a - g a) = finiteAverage f - finiteAverage g := by
  simp [finiteAverage, Finset.sum_sub_distrib, smul_sub]

theorem norm_finiteAverage_le (f : G → V) {C : ℝ} (hf : ∀ g, ‖f g‖ ≤ C) :
    ‖finiteAverage f‖ ≤ C := by
  have hn : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  calc
    _ = (Fintype.card G : ℝ)⁻¹ * ‖∑ g, f g‖ := by
      simp [finiteAverage, norm_smul, norm_inv]
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖f g‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _ : G, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun g _ => hf g)) (inv_nonneg.mpr hn.le)
    _ = C := by simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Average over the image of a finite unitary representation. -/
def finiteUnitaryAverage (π : G → unitary (H →L[ℂ] H)) (h : H →L[ℂ] H) : H →L[ℂ] H :=
  finiteAverage (fun g => unitaryConj (π g) h)

omit [Nonempty G] in
theorem finiteUnitaryAverage_star (π : G → unitary (H →L[ℂ] H)) (h : H →L[ℂ] H) :
    star (finiteUnitaryAverage π h) = finiteUnitaryAverage π (star h) := by
  simp [finiteUnitaryAverage, finiteAverage, unitaryConj, star_mul, mul_assoc]

omit [Nonempty G] in
theorem finiteUnitaryAverage_selfAdjoint (π : G → unitary (H →L[ℂ] H))
    {h : H →L[ℂ] H} (hh : IsSelfAdjoint h) : IsSelfAdjoint (finiteUnitaryAverage π h) := by
  change star (finiteUnitaryAverage π h) = finiteUnitaryAverage π h
  rw [finiteUnitaryAverage_star, hh.star_eq]

variable [Group G]

omit [Nonempty G] in
theorem finiteUnitaryAverage_invariant (π : G →* unitary (H →L[ℂ] H))
    (h : H →L[ℂ] H) (g : G) :
    unitaryConj (π g) (finiteUnitaryAverage π h) = finiteUnitaryAverage π h := by
  have he : (∑ k : G, unitaryConj (π (g * k)) h) = ∑ k : G, unitaryConj (π k) h :=
    Equiv.sum_comp (Equiv.mulLeft g) (fun k => unitaryConj (π k) h)
  simp only [map_mul, unitaryConj_mul] at he
  unfold finiteUnitaryAverage finiteAverage
  simp only [unitaryConj, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1

omit [Nonempty G] in
theorem finiteUnitaryAverage_commutes (π : G →* unitary (H →L[ℂ] H))
    (h : H →L[ℂ] H) (g : G) :
    Commute (π g : H →L[ℂ] H) (finiteUnitaryAverage π h) := by
  have hh := congrArg (fun a : H →L[ℂ] H => a * (π g : H →L[ℂ] H))
    (finiteUnitaryAverage_invariant π h g)
  have hs := Unitary.star_mul_self_of_mem (π g).property
  change (π g : H →L[ℂ] H) * finiteUnitaryAverage π h =
    finiteUnitaryAverage π h * (π g : H →L[ℂ] H)
  simpa only [unitaryConj, mul_assoc, hs, mul_one] using hh


omit [Group G] in
theorem norm_sub_finiteUnitaryAverage_le (π : G → unitary (H →L[ℂ] H))
    (h : H →L[ℂ] H) {δ : ℝ}
    (hb : ∀ g, ‖h * (π g : H →L[ℂ] H) - (π g : H →L[ℂ] H) * h‖ ≤ δ) :
    ‖h - finiteUnitaryAverage π h‖ ≤ δ := by
  have he : finiteAverage (fun g => h - unitaryConj (π g) h) =
      h - finiteUnitaryAverage π h := by
    rw [finiteAverage_sub, finiteAverage_const]
    rfl
  rw [← he]
  apply norm_finiteAverage_le
  intro g
  have he : h - unitaryConj (π g) h =
      (h * (π g : H →L[ℂ] H) - (π g : H →L[ℂ] H) * h) * star (π g : H →L[ℂ] H) := by
    have hu := Unitary.mul_star_self_of_mem (π g).property
    simp only [sub_mul, mul_assoc, hu, mul_one, unitaryConj]
  rw [he, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
  exact hb g

/-- Conjugating a commutator conjugates its argument in the opposite direction. -/
theorem commutator_unitaryConj (u : unitary (H →L[ℂ] H)) (h a : H →L[ℂ] H) :
    unitaryConj u h * a - a * unitaryConj u h =
      unitaryConj u (h * unitaryConj (star u) a - unitaryConj (star u) a * h) := by
  have hu := Unitary.mul_star_self_of_mem u.property
  simp only [unitaryConj, Unitary.coe_star, star_star, mul_sub, sub_mul, mul_assoc, hu, mul_one]
  rw [← mul_assoc (u : H →L[ℂ] H) (star (u : H →L[ℂ] H)), hu, one_mul]

omit [Group G] in
theorem finiteUnitaryAverage_derivation_le
    (M : VonNeumannAlgebra H) (π : G → unitary (H →L[ℂ] H))
    (hπ : ∀ g, (π g : H →L[ℂ] H) ∈ M) (h : H →L[ℂ] H) {δ : ℝ}
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) :
    ∀ a ∈ M, ‖finiteUnitaryAverage π h * a - a * finiteUnitaryAverage π h‖ ≤ δ * ‖a‖ := by
  intro a ha
  have he : finiteUnitaryAverage π h * a - a * finiteUnitaryAverage π h =
      finiteAverage (fun g => unitaryConj (π g) h * a - a * unitaryConj (π g) h) := by
    simp [finiteUnitaryAverage, finiteAverage,
      Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib, smul_sub]
  rw [he]
  apply norm_finiteAverage_le
  intro g
  rw [commutator_unitaryConj, norm_unitaryConj]
  have hm : unitaryConj (star (π g)) a ∈ M := by
    simp only [unitaryConj, Unitary.coe_star, star_star]
    exact M.mul_mem (M.mul_mem ((show star (π g : H →L[ℂ] H) ∈ M from
      M.toStarSubalgebra.star_mem' (hπ g))) ha) (hπ g)
  simpa only [norm_unitaryConj] using hb _ hm

end

end KadisonKastler

end OAI
