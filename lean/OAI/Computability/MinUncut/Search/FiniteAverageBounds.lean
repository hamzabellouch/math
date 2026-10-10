import Mathlib
import OAI.Computability.MinUncut.Estimates.FirstError
import OAI.Computability.MinUncut.Analysis.FreshCorrelation
import OAI.Computability.MinUncut.Analysis.FiniteGaussianLaw
import OAI.Computability.MinUncut.Estimates.TableTestFunctions

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.FiniteGaussian
variable {A : Type*} [Fintype A] [Nonempty A]

lemma expect_abs_difference (f g : A → ℝ) {ε : ℝ} (h : ∀ a, |f a-g a|≤ε) :
    |(𝔼 a,f a)-(𝔼 a,g a)|≤ε := by
  rw [← Finset.expect_sub_distrib]
  exact (OuterSmoothness.Density.abs_expect_le _).trans
    ((Finset.expect_le_expect (fun a _ => h a)).trans_eq (Fintype.expect_const _))

omit [Nonempty A] in
lemma weighted_expect_abs_difference (w f g : A → ℝ) (hw : ∀ a, 0≤w a)
    (hs : (𝔼 a,w a)=1) {ε : ℝ} (h : ∀ a, |f a-g a|≤ε) :
    |(𝔼 a,w a*f a)-(𝔼 a,w a*g a)|≤ε := by
  rw [← Finset.expect_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ 𝔼 a, |w a*(f a-g a)| := OuterSmoothness.Density.abs_expect_le _
    _ ≤ 𝔼 a, w a*ε := Finset.expect_le_expect (fun a _ => by
      rw [abs_mul,abs_of_nonneg (hw a)]
      exact mul_le_mul_of_nonneg_left (h a) (hw a))
    _ = ε := by rw [← Finset.expect_mul,hs,one_mul]
end MinUncut.FiniteGaussian

end
end
section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
attribute [local instance] coordsDecEq
variable {V A V' A' : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A'] [Fintype A'] {m n : ℕ}

def tableAverage (g : GridData) (σ η : ℚ) (F : (ScoreIndex m n → Bool) → ℝ) : ℝ :=
  ∑ j : TestCoordinates m n → Fin g.L,
    (gridWeight g j:ℝ)*F (rationalScoreTable σ η (fun i => midpoint g.T g.L (j i)))

def finiteFirst (g : GridData) (f : FoldedProof A) (σ η : ℚ) : ℝ :=
  𝔼 B : FaceArray A m n, tableAverage g σ η (firstTable f B)

def finiteSecond (g : GridData) (f : FoldedProof A) (a : ℝ) (σ η : ℚ) : ℝ :=
  𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
    RowNoise.density a B C*tableAverage g σ η (secondTable f B C)

def finiteThird (g : GridData) (f : FoldedProof A) (σ η : ℚ) : ℝ :=
  𝔼 B : FaceArray A m n, 𝔼 z : Code m n, tableAverage g σ η (thirdTable f B z)

def finiteFourth (g : GridData) (π : A →ᵃ[F₂] A') (f : FoldedProof A) (f' : FoldedProof A')
    (σ η : ℚ) : ℝ :=
  𝔼 C : FaceArray A' m n, tableAverage g σ η (fourthTable f f' (pullbackFaces π C) C)

lemma tableAverage_difference (hn : 0<n) {σ η ε : ℚ} (hσ : 0≤σ) (hσ1 : σ≤1)
    (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε)
    (F : (ScoreIndex m n → Bool) → ℝ) (hF : ∀ t, 0≤F t ∧ F t≤1) :
    |(∫ x,F (thresholdTable (scoreFamily (σ:ℝ) (η:ℝ)) x) ∂gaussianLaw (TestCoordinates m n))-
      tableAverage (tableGrid m n ε hε) σ η F|≤ε :=
by
  simpa only [tableAverage] using (tableGrid_error hn hσ hσ1 hη hη1 hε F hF).le

lemma finiteFirst_difference (f : FoldedProof A) (hn : 0<n) {σ η ε : ℚ}
    (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε) :
    |firstError (m := m) (n := n) f σ η-finiteFirst (m := m) (n := n) (tableGrid m n ε hε) f σ η|≤ε := by
  apply expect_abs_difference
  intro B
  rw [firstTable_integral]
  exact tableAverage_difference hn hσ hσ1 hη hη1 hε _ (fun _ => disagreement_range _ _)

lemma finiteSecond_difference (f : FoldedProof A) (hn : 0<n) {σ η ε : ℚ}
    (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε)
    {a : ℝ} (ha : 0≤a) (ha1 : a≤1) :
    |secondError (m := m) (n := n) f a σ η-finiteSecond (m := m) (n := n) (tableGrid m n ε hε) f a σ η|≤ε := by
  apply expect_abs_difference
  intro B
  apply weighted_expect_abs_difference _ _ _ (fun C => RowNoise.density_nonneg ha ha1 B C)
    (RowNoise.density_mean a B)
  intro C
  rw [secondTable_integral]
  exact tableAverage_difference hn hσ hσ1 hη hη1 hε _ (fun _ => disagreement_range _ _)

lemma finiteThird_difference (f : FoldedProof A) (hn : 0<n) {σ η ε : ℚ}
    (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε) :
    |thirdError (m := m) (n := n) f σ η-finiteThird (m := m) (n := n) (tableGrid m n ε hε) f σ η|≤ε := by
  apply expect_abs_difference
  intro B
  rw [thirdTable_integral]
  apply expect_abs_difference
  intro z
  exact tableAverage_difference hn hσ hσ1 hη hη1 hε _ (fun _ => disagreement_range _ _)

omit [Fintype A] in
lemma finiteFourth_difference (π : A →ᵃ[F₂] A') (f : FoldedProof A) (f' : FoldedProof A')
    (hn : 0<n) {σ η ε : ℚ} (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε) :
    |fourthError (m := m) (n := n) π f f' σ η-
      finiteFourth (m := m) (n := n) (tableGrid m n ε hε) π f f' σ η|≤ε := by
  apply expect_abs_difference
  intro C
  rw [fourthTable_integral]
  exact tableAverage_difference hn hσ hσ1 hη hη1 hε _ (fun _ => disagreement_range _ _)
end MinUncut.FiniteGaussian

end
end

end OAI
