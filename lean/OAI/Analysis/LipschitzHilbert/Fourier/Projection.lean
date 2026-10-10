import OAI.Analysis.LipschitzHilbert.Phase.PhaseCombinatorics
import OAI.Analysis.LipschitzHilbert.Estimates.Hellinger

namespace OAI

/-!
# Projection of the near-resonant quadruple measure

The quantile-gap argument in §7 projects the triple weight on quadruples
to coordinates `(i,k,l)`. Unique completion makes the Hellinger affinity
of the projected measures exactly the affinity before projection.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*}

abbrev Triple (ι : Type*) := ι × ι × ι

def insertSecond : (Triple ι × ι) ≃ Quadruple ι where
  toFun q := (q.1.1, q.2, q.1.2.1, q.1.2.2)
  invFun q := ((q.1, q.2.2.1, q.2.2.2), q.2.1)
  left_inv := by rintro ⟨⟨i, k, l⟩, j⟩; rfl
  right_inv := by rintro ⟨i, j, k, l⟩; rfl

def projectedMass [Fintype ι] (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ)
    (q : Triple ι) : ℝ :=
  ∑ j, marginal frequency gap x (q.1, j, q.2.1, q.2.2)

def independentMass (x : ι → ℝ) (q : Triple ι) : ℝ := x q.1 * x q.2.1 * x q.2.2

/-- The quantile event forces its resonant completion below the selected
central half interval. This is the geometric step behind the event deficit. -/
theorem resonant_event_completion_lt {frequency : ι → ℝ} {gap a b e h : ℝ}
    (hgap : 0 < gap) (hab : gap ≤ b - a) (heh : h - e ≤ (b - a) / 2)
    {i j k l : ι} (hr : Resonant frequency gap i j k l)
    (hi : b ≤ frequency i) (hk : frequency k ≤ a) (hl : frequency l ≤ h) :
    frequency j < e := by
  have hup := (abs_lt.mp hr).2
  linarith

theorem projectedMass_nonneg [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (q : Triple ι) : 0 ≤ projectedMass frequency gap x q :=
  Finset.sum_nonneg fun _ _ => marginal_nonneg hx _

theorem independentMass_nonneg {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (q : Triple ι) : 0 ≤ independentMass x q :=
  mul_nonneg (mul_nonneg (hx _) (hx _)) (hx _)

theorem sum_projectedMass_eq [Fintype ι]
    (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ) :
    (∑ q : Triple ι, projectedMass frequency gap x q) =
      ∑ q : Quadruple ι, marginal frequency gap x q := by
  calc
    _ = ∑ q : Triple ι × ι, marginal frequency gap x (insertSecond q) := by
      simp only [Fintype.sum_prod_type, projectedMass, insertSecond, Equiv.coe_fn_mk]
    _ = _ := Equiv.sum_comp insertSecond _

theorem sum_projectedMass_le_one [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    (∑ q : Triple ι, projectedMass frequency gap x q) ≤ 1 := by
  rw [sum_projectedMass_eq]
  exact marginal_mass_le_one hgap hsep x hx hsum

theorem sum_independentMass_eq_one [Fintype ι]
    (x : ι → ℝ) (hsum : ∑ i, x i = 1) :
    (∑ q : Triple ι, independentMass x q) = 1 := by
  simp [Fintype.sum_prod_type, independentMass, ← Finset.mul_sum, hsum]

/-- With at most one nonzero summand, taking this square root commutes
with the sum exactly. -/
theorem sqrt_sum_mul_of_unique_support [Fintype ι] (a : ι → ℝ) (b : ℝ)
    (hunique : ∀ i j, a i ≠ 0 → a j ≠ 0 → i = j) :
    Real.sqrt ((∑ i, a i) * b) = ∑ i, Real.sqrt (a i * b) := by
  classical
  by_cases hall : ∀ i, a i = 0
  · simp [hall]
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hz (j : ι) (hji : j ≠ i) : a j = 0 := by
      by_contra hj
      exact hji (hunique j i hj hi)
    have hsum : (∑ j, a j) = a i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hz j hji
      · simp
    have hsqrt : (∑ j, Real.sqrt (a j * b)) = Real.sqrt (a i * b) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [hz j hji]
      · simp
    rw [hsum, hsqrt]

theorem marginal_unique_support {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (x : ι → ℝ)
    (i k l j j' : ι)
    (hj : marginal frequency gap x (i, j, k, l) ≠ 0)
    (hj' : marginal frequency gap x (i, j', k, l) ≠ 0) : j = j' := by
  have hr : Resonant frequency gap i j k l := by
    by_contra hn
    exact hj (by simp [marginal, hn])
  have hr' : Resonant frequency gap i j' k l := by
    by_contra hn
    exact hj' (by simp [marginal, hn])
  exact unique_second hgap hsep hr hr'

theorem marginal_mul_permuted_eq_independent
    (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ) (i j k l : ι) :
    marginal frequency gap x (i, j, k, l) *
        marginal frequency gap x (swapPairs (i, j, k, l)) =
      marginal frequency gap x (i, j, k, l) * independentMass x (i, k, l) := by
  classical
  by_cases hr : Resonant frequency gap i j k l
  · have hp := resonant_swap_pairs.mp hr
    simp only [marginal, swapPairs, Equiv.coe_fn_mk, hr, hp, ite_true, independentMass]
    ring
  · simp [marginal, hr]

/-- The projection preserves the affinity, because each projected point
has at most one possible resonant completion. -/
theorem projected_affinity_eq [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ) :
    (∑ q : Triple ι,
      Real.sqrt (projectedMass frequency gap x q * independentMass x q)) =
      ∑ q : Quadruple ι, Real.sqrt
        (marginal frequency gap x q * marginal frequency gap x (swapPairs q)) := by
  calc
    _ = ∑ q : Triple ι, ∑ j,
        Real.sqrt (marginal frequency gap x (q.1, j, q.2.1, q.2.2) *
          independentMass x q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact sqrt_sum_mul_of_unique_support _ _
        (fun j j' hj hj' => marginal_unique_support hgap hsep x _ _ _ j j' hj hj')
    _ = ∑ q : Triple ι × ι, Real.sqrt
        (marginal frequency gap x (insertSecond q) *
          marginal frequency gap x (swapPairs (insertSecond q))) := by
      simp only [Fintype.sum_prod_type, insertSecond, Equiv.coe_fn_mk]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      rw [marginal_mul_permuted_eq_independent]
    _ = _ := Equiv.sum_comp insertSecond (fun q : Quadruple ι =>
      Real.sqrt (marginal frequency gap x q * marginal frequency gap x (swapPairs q)))

theorem resonanceSum_nonneg [Fintype ι]
    (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ) :
    0 ≤ resonanceSum frequency gap x :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- The bound in exactly the affinity convention used for finite probabilities. -/
theorem resonanceSum_sq_le_projected_affinity [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    resonanceSum frequency gap x ^ 2 ≤
      affinity (projectedMass frequency gap x) (independentMass x) := by
  calc
    _ ≤ ∑ q : Quadruple ι, Real.sqrt
        (marginal frequency gap x q * marginal frequency gap x (swapPairs q)) :=
      resonanceSum_sq_le_affinity hgap hsep x hx hsum
    _ = ∑ q : Triple ι,
        Real.sqrt (projectedMass frequency gap x q * independentMass x q) :=
      (projected_affinity_eq hgap hsep x).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      exact Real.sqrt_mul (projectedMass_nonneg hx q) _

/-- Any event with a definite deficit between the projected and independent
triple laws gives the quantitative improvement in the fourth-moment sum. -/
theorem resonanceSum_gap_of_event_deficit [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (s : Finset (Triple ι)) {g : ℝ} (hg : 0 ≤ g)
    (hdeficit : g ≤ ∑ q ∈ s,
      (independentMass x q - projectedMass frequency gap x q)) :
    resonanceSum frequency gap x ≤ 1 - g ^ 2 / 4 := by
  exact strict_gap_of_event_deficit
    (projectedMass frequency gap x) (independentMass x)
    (projectedMass_nonneg hx) (independentMass_nonneg hx)
    (sum_projectedMass_le_one hgap hsep x hx hsum)
    (sum_independentMass_eq_one x hsum) s
    (resonanceSum_nonneg frequency gap x) hg
    (resonanceSum_sq_le_projected_affinity hgap hsep x hx hsum) hdeficit

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
