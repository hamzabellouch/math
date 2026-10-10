import OAI.MeasureTheory.Falconer.Recursion.FrostmanProfiles
import OAI.MeasureTheory.Falconer.Recursion.UnitProfiles

namespace OAI

/-! # Unit-scale profiles and conditional mass ratios of the original classes -/

namespace Falconer.Regularization
open MeasureTheory Set
variable {d : ℕ}

noncomputable def sourceUnitProfile (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) : ℝ → ℝ :=
  unitProfile (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) N B p

theorem sourceUnitProfile_at_depth (Q : DyadicCube d) (μ : Measure (Space d))
    {N : ℕ} (hN : 0 < N) (B : ℕ) (p : CellPath d) (j : ℕ) :
    sourceUnitProfile Q μ N B p ((j:ℝ)/N) = sourceProfile Q μ N B p j := by
  unfold sourceUnitProfile unitProfile sourceProfile
  congr 1
  field_simp

theorem sourceUnitProfile_properties (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d) :
    Continuous (sourceUnitProfile Q μ N B p) ∧
    sourceUnitProfile Q μ N B p 0 = 0 ∧
    MonotoneOn (sourceUnitProfile Q μ N B p) (Icc 0 1) ∧
    LipschitzOnWith (d : NNReal) (sourceUnitProfile Q μ N B p) (Icc 0 1) ∧
    ∀ u ∈ Icc (0:ℝ) 1, sourceUnitProfile Q μ N B p u ∈ Icc (0:ℝ) d := by
  have hL : regularizationLeaves Q μ N ⊆ cubePaths d N := Finset.filter_subset _ _
  exact ⟨unitProfile_continuous _ _ _ _ _,unitProfile_zero _ _ _ _ _,
    unitProfile_monotoneOn hN hB hL _ _,unitProfile_lipschitzOn hN hB hL _ _,
    fun _ hu => unitProfile_range hN hB hL _ _ hu⟩

theorem sourceUnitProfile_lower_from_grid (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d)
    {s E : ℝ} (hs : 0 ≤ s)
    (hgrid : ∀ j ≤ N, s*(j:ℝ)/(N:ℝ)-E ≤ sourceProfile Q μ N B p j)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    s*u-E-s/N ≤ sourceUnitProfile Q μ N B p u := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  let j := Nat.floor ((N:ℝ)*u)
  have hfloor : (j:ℝ) ≤ (N:ℝ)*u := Nat.floor_le (mul_nonneg hNp.le hu.1)
  have hnext : (N:ℝ)*u < (j:ℝ)+1 := Nat.lt_floor_add_one _
  have hj : j ≤ N := by
    exact_mod_cast hfloor.trans (mul_le_of_le_one_right hNp.le hu.2)
  have hju : (j:ℝ)/(N:ℝ) ≤ u := (div_le_iff₀ hNp).mpr (by simpa [mul_comm] using hfloor)
  have hj0 : 0 ≤ (j:ℝ)/(N:ℝ) := by positivity
  have hm := (sourceUnitProfile_properties Q μ hN hB p).2.2.1
    ⟨hj0,hju.trans hu.2⟩ hu hju
  rw [sourceUnitProfile_at_depth Q μ hN B p j] at hm
  have hsj := mul_le_mul_of_nonneg_left
    ((le_div_iff₀ hNp).mpr (by simpa [mul_comm] using hnext.le)) hs
  have he : s*((j:ℝ)+1)/(N:ℝ) = s*(j:ℝ)/(N:ℝ)+s/N := by ring
  rw [← mul_div_assoc,he] at hsj
  linarith [hgrid j hj]

theorem profile_ratio_bounds {R C m₀ m₁ x₀ x₁ : ℝ}
    (hR : 0 < R)
    (h₀ : R^(-C)*R^(-m₀) ≤ x₀ ∧ x₀ ≤ R^C*R^(-m₀))
    (h₁ : R^(-C)*R^(-m₁) ≤ x₁ ∧ x₁ ≤ R^C*R^(-m₁)) :
    R^(-2*C)*R^(-(m₁-m₀)) ≤ x₁/x₀ ∧
    x₁/x₀ ≤ R^(2*C)*R^(-(m₁-m₀)) := by
  have hlo : 0 < R^(-C)*R^(-m₀) := by positivity
  have hx : 0 < x₀ := hlo.trans_le h₀.1
  have he₁ : R^(-C)*R^(-m₁)/(R^C*R^(-m₀)) = R^(-2*C)*R^(-(m₁-m₀)) := by
    rw [← Real.rpow_add hR,← Real.rpow_add hR,← Real.rpow_sub hR,← Real.rpow_add hR]
    congr 1
    ring
  have he₂ : R^C*R^(-m₁)/(R^(-C)*R^(-m₀)) = R^(2*C)*R^(-(m₁-m₀)) := by
    rw [← Real.rpow_add hR,← Real.rpow_add hR,← Real.rpow_sub hR,← Real.rpow_add hR]
    congr 1
    ring
  constructor
  · rw [← he₁]
    exact div_le_div₀ ((by positivity : 0 < R^(-C)*R^(-m₁)).le.trans h₁.1) h₁.1 hx h₀.2
  · rw [← he₂]
    exact div_le_div₀ (by positivity) h₁.2 hlo h₀.1

theorem sourceClass_conditional_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) {lam : ℝ}
    (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N)
    {P T : CellPath d} (hP : P.length = a) (hT : T.length = b)
    (hPpos : 0 < sourceClass Q μ N B p (Q.descendant P).carrier)
    (hTpos : 0 < sourceClass Q μ N B p (Q.descendant T).carrier) :
    ((2:ℝ)^N)^(-2*(((d:ℝ)+1)*lam)) *
        ((2:ℝ)^N)^(-(sourceProfile Q μ N B p b-sourceProfile Q μ N B p a)) ≤
      (sourceClass Q μ N B p (Q.descendant T).carrier).toReal /
        (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ∧
    (sourceClass Q μ N B p (Q.descendant T).carrier).toReal /
        (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ≤
      ((2:ℝ)^N)^(2*(((d:ℝ)+1)*lam)) *
        ((2:ℝ)^N)^(-(sourceProfile Q μ N B p b-sourceProfile Q μ N B p a)) := by
  apply profile_ratio_bounds (by positivity)
  · simpa only [neg_mul] using
      sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp ha hP hPpos
  · simpa only [neg_mul] using
      sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp hb hT hTpos

end Falconer.Regularization

end OAI
