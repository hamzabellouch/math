import Mathlib.Tactic

namespace OAI

/-! The scalar determinant loss in the radial comparison, using the three
eigenvalues of the averaged normal Jacobi curvature matrix. -/

namespace PositiveEinsteinFour.Jacobi

noncomputable section

def loss (β a b c : ℝ) : ℝ := 1 - (1 - β * a) * (1 - β * b) * (1 - β * c)

def lossFactor (β : ℝ) : ℝ := min 1 (β ^ 2 * max 1 (3 - β))

theorem loss_identity {a b c : ℝ} (htrace : a + b + c = 0) (β : ℝ) :
    loss β a b c = β ^ 2 / 2 * (a ^ 2 + b ^ 2 + c ^ 2) + β ^ 3 * (a * b * c) := by
  have hc : c = -a - b := by linarith
  rw [hc]
  unfold loss
  ring

private theorem loss_one_negative {β r a b : ℝ}
    (hβ : 0 ≤ β) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hab : a + b = r)
    (hβa : β * a ≤ 1) (hβb : β * b ≤ 1) :
    lossFactor β / 6 * ((-r) ^ 2 + a ^ 2 + b ^ 2) ≤ loss β (-r) a b := by
  let N := r ^ 2 + a ^ 2 + b ^ 2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hgap : 0 ≤ N - 6 * a * b := by
    dsimp [N]
    rw [← hab]
    nlinarith only [sq_nonneg (a - b)]
  have hprod := mul_nonneg (mul_nonneg (pow_nonneg hβ 3) hr) hgap
  have hfirst : β ^ 2 / 6 * (3 - β * r) * N ≤ loss β (-r) a b := by
    rw [loss_identity (by linarith)]
    dsimp [N] at *
    nlinarith only [hprod]
  have hβr : β * r ≤ 2 := by
    calc
      β * r = β * a + β * b := by rw [← hab]; ring
      _ ≤ 2 := by linarith
  have hβr' : β * r ≤ β := by simpa using mul_le_mul_of_nonneg_left hr1 hβ
  have hmax : max 1 (3 - β) ≤ 3 - β * r := max_le (by linarith) (by linarith)
  have hfactor : lossFactor β ≤ β ^ 2 * (3 - β * r) := by
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hmax (sq_nonneg β))
  have hscaled := mul_le_mul_of_nonneg_right hfactor (div_nonneg hN (by norm_num : (0 : ℝ) ≤ 6))
  calc
    lossFactor β / 6 * ((-r) ^ 2 + a ^ 2 + b ^ 2) = lossFactor β * (N / 6) := by
      dsimp [N]
      ring
    _ ≤ (β ^ 2 * (3 - β * r)) * (N / 6) := hscaled
    _ = β ^ 2 / 6 * (3 - β * r) * N := by ring
    _ ≤ loss β (-r) a b := hfirst

private theorem other_eigenvalues_nonneg {a b c : ℝ}
    (htrace : a + b + c = 0) (ha : a < 0) (hprod : a * b * c < 0) :
    0 ≤ b ∧ 0 ≤ c := by
  constructor
  · by_contra hb
    have hb' : b < 0 := lt_of_not_ge hb
    have hc : 0 < c := by linarith
    have hp := mul_pos (mul_pos_of_neg_of_neg ha hb') hc
    linarith
  · by_contra hc
    have hc' : c < 0 := lt_of_not_ge hc
    have hb : 0 < b := by linarith
    have hp := mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos ha hb) hc'
    linarith

/-- The full determinant-loss bound before the first conjugate point. The
semidefinite compression is expressed by `β*a, β*b, β*c ≤ 1`. No positive
definiteness or inversion at its singular endpoint is required. -/
theorem preconjugate_loss {β a b c : ℝ}
    (hβ : 0 ≤ β) (htrace : a + b + c = 0)
    (ha : -1 ≤ a) (hb : -1 ≤ b) (hc : -1 ≤ c)
    (hβa : β * a ≤ 1) (hβb : β * b ≤ 1) (hβc : β * c ≤ 1) :
    lossFactor β / 6 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ loss β a b c := by
  by_cases hprod : 0 ≤ a * b * c
  · have hmax : max (1 : ℝ) (3 - β) ≤ 3 := max_le (by norm_num) (by linarith)
    have hfactor : lossFactor β ≤ 3 * β ^ 2 := by
      calc
        _ ≤ β ^ 2 * max 1 (3 - β) := min_le_right _ _
        _ ≤ β ^ 2 * 3 := mul_le_mul_of_nonneg_left hmax (sq_nonneg β)
        _ = _ := by ring
    have hN : 0 ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 6 := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hfactor hN
    have hp := mul_nonneg (pow_nonneg hβ 3) hprod
    rw [loss_identity htrace]
    nlinarith only [hscaled, hp]
  · have hprod' : a * b * c < 0 := lt_of_not_ge hprod
    by_cases haneg : a < 0
    · obtain ⟨hb0, hc0⟩ := other_eigenvalues_nonneg htrace haneg hprod'
      simpa only [neg_neg] using loss_one_negative hβ (neg_nonneg.mpr haneg.le)
        (by linarith : -a ≤ 1) hb0 hc0 (by linarith : b + c = -a) hβb hβc
    · by_cases hbneg : b < 0
      · have hp : b * a * c < 0 := by nlinarith only [hprod']
        obtain ⟨ha0, hc0⟩ := other_eigenvalues_nonneg (by linarith) hbneg hp
        have h := loss_one_negative hβ (neg_nonneg.mpr hbneg.le)
          (by linarith : -b ≤ 1) ha0 hc0 (by linarith : a + c = -b) hβa hβc
        simp only [neg_neg] at h
        unfold loss at *
        nlinarith only [h]
      · have ha0 : 0 ≤ a := le_of_not_gt haneg
        have hb0 : 0 ≤ b := le_of_not_gt hbneg
        have hcneg : c < 0 := by
          by_contra h
          exact hprod (mul_nonneg (mul_nonneg ha0 hb0) (le_of_not_gt h))
        have h := loss_one_negative hβ (neg_nonneg.mpr hcneg.le)
          (by linarith : -c ≤ 1) ha0 hb0 (by linarith : a + b = -c) hβa hβb
        simp only [neg_neg] at h
        unfold loss at *
        nlinarith only [h]

/-- The eigenvalue box and trace condition give the global squared-norm cap. -/
theorem norm_sq_le_six {a b c : ℝ} (htrace : a + b + c = 0)
    (ha : a ∈ Set.Icc (-1 : ℝ) 2) (hb : b ∈ Set.Icc (-1 : ℝ) 2)
    (hc : c ∈ Set.Icc (-1 : ℝ) 2) : a ^ 2 + b ^ 2 + c ^ 2 ≤ 6 := by
  have h1 := mul_nonneg (by linarith [ha.1] : 0 ≤ a + 1) (by linarith [ha.2] : 0 ≤ 2 - a)
  have h2 := mul_nonneg (by linarith [hb.1] : 0 ≤ b + 1) (by linarith [hb.2] : 0 ≤ 2 - b)
  have h3 := mul_nonneg (by linarith [hc.1] : 0 ≤ c + 1) (by linarith [hc.2] : 0 ≤ 2 - c)
  nlinarith

/-- After conjugacy the truncated determinant is zero, and the same bound
follows from the norm cap. -/
theorem postconjugate_loss {β a b c : ℝ}
    (htrace : a + b + c = 0)
    (ha : a ∈ Set.Icc (-1 : ℝ) 2) (hb : b ∈ Set.Icc (-1 : ℝ) 2)
    (hc : c ∈ Set.Icc (-1 : ℝ) 2) :
    lossFactor β / 6 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 1 := by
  have hN := norm_sq_le_six htrace ha hb hc
  have hfactor : lossFactor β ≤ 1 := min_le_left _ _
  have h0 : 0 ≤ lossFactor β := le_min (by norm_num)
    (mul_nonneg (sq_nonneg β) (le_trans (by norm_num) (le_max_left _ _)))
  nlinarith [mul_le_mul_of_nonneg_left hN h0]

end

end PositiveEinsteinFour.Jacobi

end OAI
