import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebiusPolynomials

namespace OAI

/-! The short Möbius identity remains valid inside any fixed product of
prime-weight factors. This is the algebraic replacement before smoothing. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def NormLocalEq (F : ℝ) (A B : EisensteinArithmeticFunction) : Prop :=
  ∀ ν, idealExponentNorm ν ≤ F → MvPowerSeries.coeff ν A = MvPowerSeries.coeff ν B

lemma NormLocalEq.refl (F : ℝ) (A : EisensteinArithmeticFunction) : NormLocalEq F A A :=
  fun _ _ => rfl

lemma NormLocalEq.mul {F : ℝ} {A B C D : EisensteinArithmeticFunction}
    (hAB : NormLocalEq F A B) (hCD : NormLocalEq F C D) :
    NormLocalEq F (A*C) (B*D) := by
  intro ν hν
  rw [MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have h₁ : p.1 ≤ ν := by rw [← he]; exact le_add_of_nonneg_right zero_le
  have h₂ : p.2 ≤ ν := by rw [← he]; exact le_add_of_nonneg_left zero_le
  rw [hAB p.1 ((idealExponentNorm_mono h₁).trans hν),
    hCD p.2 ((idealExponentNorm_mono h₂).trans hν)]

lemma NormLocalEq.prod {ι : Type*} {F : ℝ} (S : Finset ι)
    (A B : ι → EisensteinArithmeticFunction) (h : ∀ i ∈ S, NormLocalEq F (A i) (B i)) :
    NormLocalEq F (∏ i ∈ S, A i) (∏ i ∈ S, B i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using NormLocalEq.refl F (1 : EisensteinArithmeticFunction)
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

def shortVonMangoldt (F : ℝ) : EisensteinArithmeticFunction :=
  (2*shortIdealMoebius F-shortIdealMoebius F*shortIdealMoebius F*idealZeta)*idealLogNorm

def shortTwoFactor (F : ℝ) : EisensteinArithmeticFunction := shortIdealMoebius F*idealLogNorm

def shortFourFactor (F : ℝ) : EisensteinArithmeticFunction :=
  shortIdealMoebius F*shortIdealMoebius F*idealZeta*idealLogNorm

lemma shortVonMangoldt_two_four (F : ℝ) :
    shortVonMangoldt F = 2*shortTwoFactor F-shortFourFactor F := by
  unfold shortVonMangoldt shortTwoFactor shortFourFactor
  ring

lemma shortVonMangoldt_local {F : ℝ} (hF : 0 ≤ F) :
    NormLocalEq F idealVonMangoldt (shortVonMangoldt F) :=
  fun ν hν => short_moebius_identity hF ν hν

/-- Every product of von Mangoldt factors can be replaced in the same
sharp norm range, with no analytic error term. -/
theorem shortVonMangoldt_product {ι : Type*} [Fintype ι]
    {F : ℝ} (hF : 0 ≤ F) (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν (∏ _i : ι, idealVonMangoldt) =
      MvPowerSeries.coeff ν (∏ _i : ι, shortVonMangoldt F) :=
  NormLocalEq.prod Finset.univ (fun _ : ι => idealVonMangoldt)
    (fun _ => shortVonMangoldt F) (fun _ _ => shortVonMangoldt_local hF) ν hν

/-- The exact finite expansion, leaving only two- and four-factor short
convolutions for the already proved moment bounds. -/
theorem shortVonMangoldt_product_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ℝ} (hF : 0 ≤ F) (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν (∏ _i : ι, idealVonMangoldt) =
      MvPowerSeries.coeff ν (∑ S ∈ (Finset.univ : Finset ι).powerset,
        (-1 : EisensteinArithmeticFunction)^S.card *
          (∏ _i ∈ S, shortFourFactor F)*
            ∏ _i ∈ Finset.univ\S, 2*shortTwoFactor F) := by
  rw [shortVonMangoldt_product (ι := ι) hF ν hν]
  simp_rw [shortVonMangoldt_two_four]
  have he := Finset.prod_sub (fun _ : ι => 2*shortTwoFactor F)
    (fun _ : ι => shortFourFactor F) Finset.univ
  have he' : (∏ _i : ι, (2*shortTwoFactor F-shortFourFactor F)) =
      ∑ S ∈ (Finset.univ : Finset ι).powerset,
        (-1 : EisensteinArithmeticFunction)^S.card *
          (∏ _i ∈ S, shortFourFactor F)*
            ∏ _i ∈ Finset.univ\S, 2*shortTwoFactor F := by
    rw [he]
    apply Finset.sum_congr rfl
    intro S _
    exact mul_right_comm _ _ _
  rw [he']

end CubicFirstMoment

end

end OAI
