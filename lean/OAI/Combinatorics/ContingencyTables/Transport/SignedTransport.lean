import OAI.Combinatorics.ContingencyTables.Transport.QuadraticTransport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

/-!
# Signed transport at a leaf and at a paired split

The signed-clique inequality, local potential increment and future quadratic
conservation give the counting paper's fixed-degree transport estimate.
Positivity of weights at unrelated degrees is unnecessary.
-/

namespace ContingencyTables.SignedTransport

open scoped BigOperators
open LinearMap (BilinForm)

section Clique

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The unordered complete exchange energy, expressed as half the ordered
sum, with the manuscript's minimum-endpoint conductance. -/
noncomputable def cliqueEnergy (m W H : I → ℝ) : ℝ :=
  (∑ i, ∑ j, min (W i * m i) (W j * m j) * (H i - H j) ^ 2) / 2

/-- A star uses each unordered edge once, so its energy is at most the
complete unordered exchange energy. -/
lemma star_energy_le (E : I → I → ℝ)
    (hE : ∀ i j, 0 ≤ E i j) (hsymm : ∀ i j, E i j = E j i)
    (hdiag : ∀ i, E i i = 0) (hub : I) :
    ∑ i, E i hub ≤ (∑ i, ∑ j, E i j) / 2 := by
  have hrest : (∑ i ∈ Finset.univ.erase hub, E i hub) ≤
      ∑ i ∈ Finset.univ.erase hub, ∑ j, E i j := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun j _ => hE i j) (Finset.mem_univ hub)
  rw [Finset.sum_erase (f := fun i => E i hub) _ (hdiag hub)] at hrest
  have htotal := Finset.sum_erase_add Finset.univ (fun i => ∑ j, E i j)
    (Finset.mem_univ hub)
  have hrow : (∑ j, E hub j) = ∑ j, E j hub := by simp_rw [hsymm hub]
  rw [hrow] at htotal
  linarith

/-- A balanced signed demand on the leaf clique has energy controlled by
its potential. This proves the squared inequality directly by weighted
Cauchy--Schwarz and the hub construction. -/
theorem leaf_signed_transport [Nonempty I] (m W h H : I → ℝ)
    (hm : ∀ i, 0 < m i) (hW : ∀ i, 0 < W i)
    (hbalance : ∑ i, m i * h i = 0) :
    (∑ i, m i * h i * H i) ^ 2 ≤
      (∑ i, m i * h i ^ 2 / W i) * cliqueEnergy m W H := by
  obtain ⟨hub, _, hhub⟩ := Finset.exists_max_image Finset.univ
    (fun i => W i * m i) Finset.univ_nonempty
  have hdemand : (∑ i, m i * h i * (H i - H hub)) = ∑ i, m i * h i * H i := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hbalance,
      zero_mul, sub_zero]
  have hcs : (∑ i, m i * h i * (H i - H hub)) ^ 2 ≤
      (∑ i, m i * h i ^ 2 / W i) *
        ∑ i, W i * m i * (H i - H hub) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    · intro i _
      exact div_nonneg (mul_nonneg (hm i).le (sq_nonneg _)) (hW i).le
    · intro i _
      exact mul_nonneg (mul_pos (hW i) (hm i)).le (sq_nonneg _)
    · intro i _
      have hw : W i ≠ 0 := ne_of_gt (hW i)
      apply le_of_eq
      field_simp
  have hstar : (∑ i, W i * m i * (H i - H hub) ^ 2) ≤ cliqueEnergy m W H := by
    have he := star_energy_le
      (fun i j => min (W i * m i) (W j * m j) * (H i - H j) ^ 2)
      (fun i j => mul_nonneg
        (le_min (mul_pos (hW i) (hm i)).le (mul_pos (hW j) (hm j)).le) (sq_nonneg _))
      (by intro i j; rw [min_comm]; ring) (by intro i; simp) hub
    simp_rw [min_eq_left (hhub _ (Finset.mem_univ _))] at he
    exact he
  rw [hdemand] at hcs
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left hstar
  exact Finset.sum_nonneg fun i _ =>
    div_nonneg (mul_nonneg (hm i).le (sq_nonneg _)) (hW i).le

end Clique

section Split

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The exact Schur inequality for a paired binary split. The fresh
coordinates have zero diagonals and positive mixed entry. -/
theorem split_signed_cost (B : BilinForm ℝ V)
    (hsymm : ∀ x y, B x y = B y x) (hsig : OnePositiveDirection B)
    (h ea eb : V) (u X : ℝ) (hu : 0 < u)
    (haa : B ea ea = 0) (hbb : B eb eb = 0) (hab : B ea eb = u)
    (hha : B h ea = -X) (hhb : B h eb = X) :
    2 * X ^ 2 / u ≤ -B h h := by
  have hleft : B h ea = u * (-X / u) - 0 * 0 := by
    rw [hha]
    field_simp
    ring
  have hright : B h eb = 0 * 0 - u * (-X / u) := by
    rw [hhb]
    field_simp
    ring
  have hh := pair_step_of_signature B hsymm hsig h ea eb 0 u 0 0 (-X / u) 0
    haa hbb hab hleft hright (by rfl) (by rfl) (Or.inr (Or.inr ⟨rfl, rfl, hu⟩))
  have heq : 2 * u * (-X / u) ^ 2 - 0 * 0 ^ 2 - 0 * 0 ^ 2 = 2 * X ^ 2 / u := by
    field_simp
    ring
  rwa [heq] at hh

/-- Child coefficients of opposite signs preserve the future quadratic
form. This is the cancellation that lets each later slot be charged only
its root defect mass. -/
theorem future_form_conservation (Ba Bb : BilinForm ℝ V)
    (haSymm : ∀ x y, Ba x y = Ba y x) (hbSymm : ∀ x y, Bb x y = Bb y x)
    (h ea eb : V) (c parent : ℝ)
    (hold : Ba h h + Bb h h = parent)
    (hcross : Ba h ea = Bb h eb) (haa : Ba ea ea = 0) (hbb : Bb eb eb = 0) :
    Ba (h + c • ea) (h + c • ea) + Bb (h - c • eb) (h - c • eb) = parent := by
  have hah : Ba ea h = Ba h ea := haSymm ea h
  have hbh : Bb eb h = Bb h eb := hbSymm eb h
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    haa, hbb, hah, hbh, hcross]
  linarith [hold]

end Split

section SplitPotential

variable {I : Type*} [Fintype I]

/-- Splitting old masses and assigning the fresh-hole coefficients gives
exactly the manuscript's potential increment `2 X²/(u Wt)`. -/
theorem split_potential_increment (sa sb h W : I → ℝ) (u X Wt : ℝ)
    (hu : u ≠ 0) (hWt : Wt ≠ 0) :
    ((∑ i, sa i * h i ^ 2 / W i) + u * (-X / u) ^ 2 / Wt) +
      ((∑ i, sb i * h i ^ 2 / W i) + u * (X / u) ^ 2 / Wt) =
        (∑ i, (sa i + sb i) * h i ^ 2 / W i) + 2 * X ^ 2 / (u * Wt) := by
  simp only [add_mul, add_div, Finset.sum_add_distrib]
  field_simp
  ring

/-- The new-hole coefficients balance the two child signed demands. -/
theorem split_child_balance (sa sb h : I → ℝ) (u : ℝ) (hu : u ≠ 0)
    (hbalance : ∑ i, (sa i + sb i) * h i = 0) :
    let X := ∑ i, sa i * h i
    (∑ i, sa i * h i) + u * (-X / u) = 0 ∧
      (∑ i, sb i * h i) + u * (X / u) = 0 := by
  dsimp
  simp only [add_mul, Finset.sum_add_distrib] at hbalance
  constructor
  · field_simp
    ring
  · field_simp
    linarith [hbalance]

end SplitPotential

end ContingencyTables.SignedTransport

end OAI
