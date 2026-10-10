import OAI.NumberTheory.DirichletL.Moments.SecondLedger

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDescentLedger
open CanonicalQuadraticSieve CenteredMomentSecondLedger CenteredMomentPartitionNorm
local notation "O" => ActualEisensteinCubic.O

def firstSaving (c D₀ w q wo B g ell : ℝ) : ℝ :=
  c/6+5*D₀/6+w/3+q/6+wo+B-5*g/6+ell

theorem firstSaving_lower (c d D₀ w q R wo B g ell σ δ : ℝ)
    (hc : 0 ≤ c) (hw : 0 ≤ w) (hq : 0 ≤ q) (hwo : 0 ≤ wo)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hδ : 0 ≤ δ)
    (hR : R ≤ q) (hBcost : max (3*c-5*d-R) 0/6 ≤ B)
    (hD : d-δ ≤ D₀) (hg : g ≤ max (D₀-c-2*w+wo) 0+2*σ)
    (hell : 0 ≤ ell) (hwσ : w ≤ 7*σ/3) :
    2*(c+w)/3-3*σ-5*δ/6 ≤ firstSaving c D₀ w q wo B g ell := by
  have hraw : 3*c-5*d-R ≤ 6*B := by
    have hm := le_max_left (3*c-5*d-R) 0
    linarith
  have hmax : max (3*c-5*D₀) 0/6-5*δ/6 ≤ B+q/6 := by
    apply (max_le_iff.mpr ⟨?_,?_⟩ : max (3*c-5*D₀) 0 ≤ 6*(B+q/6)+5*δ) |> fun h => by linarith
    · linarith
    · positivity
  unfold firstSaving
  by_cases hJ : 0 ≤ D₀-c-2*w+wo
  · rw [max_eq_left hJ] at hg
    linarith
  · rw [max_eq_right (le_of_not_ge hJ)] at hg
    have hm := le_max_left (3*c-5*D₀) 0
    linarith

section ActualSecond
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem common_log_ge_unit (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm (unitIdeal p U) : ℝ) ≤
      Real.logb Z (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  rw [unitIdeal,log_norm_radical p hp,commonIdeal,log_norm_power_product p hp]
  calc
    _ ≤ ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro i hi hni
      apply Real.logb_nonneg hZ
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : 0 ≤ Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
        Real.logb_nonneg hZ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))
      have hm : (1:ℝ) ≤ (min (c i) (d i) : ℕ) := by exact_mod_cast le_min (hc i) (hd i)
      nlinarith

omit [DecidableEq ι] in
theorem half_product_log_ge_radical (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ) ≤
      (Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ)+
       Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ))/2 := by
  rw [log_norm_radical p hp,log_norm_power_product p hp,log_norm_power_product p hp,
    ← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  have hn : 0 ≤ Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
    Real.logb_nonneg hZ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))
  have hcr : (1:ℝ) ≤ c i := by exact_mod_cast hc i
  have hdr : (1:ℝ) ≤ d i := by exact_mod_cast hd i
  nlinarith
end ActualSecond

theorem declared_width_drop (M J g g₂ t₂ σ m' q' δ : ℝ)
    (hwidth : m'+q'=M+J-g-g₂+t₂) (hg : J+σ ≤ g) (hcommon : t₂ ≤ g₂)
    (hnonempty : 0 ≤ m'+δ) :
    max 0 (m'+δ)+q' ≤ M-σ+δ := by
  rw [max_eq_right hnonempty]
  linarith

theorem child_allowance_lower (b₂ p₂ w B ell : ℝ)
    (hbp : p₂ ≤ b₂) (hB : 0 ≤ B) :
    w+ell ≤ b₂-p₂+w+B+ell := by linarith

theorem exceptional_excess_identity
    (A m q c d R E K w wo B g ell b₂ p₂ g₂ t₂ V f : ℝ) :
    let a₀ := A-c-w
    let K₀ := 2*A-c-d+R+E-m
    let m' := 2*a₀-K-g-g₂-V
    let q' := q+R+E+wo+t₂+V
    (m'-f)/6+a₀-b₂-(m'+q'+(b₂-p₂+w+B+ell)) =
      A-5*(m+q)/6-firstSaving c (d+K₀-K) w (q+R+E) wo B g ell -
        (2*b₂-5*g₂/6-p₂+t₂+V/6+f/6) := by
  dsimp only [firstSaving]
  ring

theorem inner_allowance_identity
    (a₀ q wo w B s₀ K g ell p₂ g₂ t₂ b₂ V : ℝ) :
    (a₀+q+wo+w+B-s₀)-(K+g-ell-a₀+p₂-s₀+g₂-t₂-b₂) =
      (2*a₀-K-g-g₂-V)+(q+wo+t₂+V)+(b₂-p₂+w+B+ell) := by ring

theorem exceptional_excess_bound
    (A M c w b₂ F₁ F₂ σ δ : ℝ)
    (hF₁ : 2*(c+w)/3-3*σ-5*δ/6 ≤ F₁)
    (hF₂ : 2*b₂/3 ≤ F₂) :
    A-5*M/6-F₁-F₂ ≤ A-5*M/6-2*(c+w+b₂)/3+3*σ+5*δ/6 := by linarith

theorem uncentered_exceptional_bound
    (A M c w b₂ F₁ F₂ σ δ : ℝ)
    (hA : A ≤ 5*M/6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb : 0 ≤ b₂)
    (hF₁ : 2*(c+w)/3-3*σ-5*δ/6 ≤ F₁)
    (hF₂ : 2*b₂/3 ≤ F₂) :
    A-5*M/6-F₁-F₂ ≤ 3*σ+5*δ/6 := by
  have hh := exceptional_excess_bound A M c w b₂ F₁ F₂ σ δ hF₁ hF₂
  linarith

end SevenEighths.CenteredMomentDescentLedger

end

end OAI
