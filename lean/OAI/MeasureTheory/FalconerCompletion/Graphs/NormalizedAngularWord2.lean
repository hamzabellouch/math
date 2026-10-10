import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.NormalizedAngularWord
import OAI.MeasureTheory.FalconerCompletion.Graphs.SmoothFinsetProduct2

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set
open scoped ContDiff
variable {V α : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def normalizedAngularWordND (D : ℝ) (L : List (V →L[ℝ] V))
    (f : SmoothFunctionND V) : SmoothFunctionND V :=
  ((D:ℂ)^L.length)⁻¹ • angularWordOperatorND L f

lemma normalizedAngularWordND_extract {D : ℝ} (hD : D ≠ 0) (L : List (V →L[ℝ] V))
    (f : SmoothFunctionND V) :
    (D:ℂ)^L.length • normalizedAngularWordND D L f = angularWordOperatorND L f := by
  rw [normalizedAngularWordND,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hD)),one_smul]

lemma normalizedAngularWordND_support (D : ℝ) (L : List (V →L[ℝ] V))
    (f : SmoothFunctionND V) : tsupport (normalizedAngularWordND D L f).1 ⊆ tsupport f.1 := by
  apply subset_trans _ (angularWordOperatorND_support L f)
  change tsupport (fun x => ((D:ℂ)^L.length)⁻¹ * (angularWordOperatorND L f).1 x) ⊆ _
  apply closure_mono
  intro x hx hz
  exact hx (by simp [hz])

lemma smoothFinsetProductND_smul (S : Finset α) (c : α → ℂ) (f : α → SmoothFunctionND V) :
    smoothFinsetProductND S (fun i => c i • f i) = (∏ i ∈ S, c i) • smoothFinsetProductND S f := by
  apply Subtype.ext
  funext x
  change (∏ i ∈ S, c i*(f i).1 x)=(∏ i ∈ S,c i)*(∏ i ∈ S,(f i).1 x)
  exact Finset.prod_mul_distrib

lemma assignedAngularProductND_normalized (S : Finset α) (D : α → ℝ)
    (k : α → List (V →L[ℝ] V)) (f : α → SmoothFunctionND V) (hD : ∀ i ∈ S, D i ≠ 0) :
    smoothFinsetProductND S (fun i => angularWordOperatorND (k i) (f i)) =
      ((∏ i ∈ S, D i ^ (k i).length : ℝ):ℂ) •
        smoothFinsetProductND S (fun i => normalizedAngularWordND (D i) (k i) (f i)) := by
  simp only [Complex.ofReal_prod,Complex.ofReal_pow]
  rw [← smoothFinsetProductND_smul]
  apply Subtype.ext
  funext x
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun g : SmoothFunctionND V => g.1 x) (normalizedAngularWordND_extract (hD i hi) (k i) (f i)).symm

lemma assignedAngularScaleND_le (S : Finset α) (D : α → ℝ)
    (k : α → List (V →L[ℝ] V)) {M : ℝ} {b : ℕ} (hM : 1 ≤ M)
    (hD₀ : ∀ i ∈ S, 0 ≤ D i) (hD : ∀ i ∈ S, D i ≤ M)
    (hk : ∑ i ∈ S, (k i).length ≤ b) :
    ∏ i ∈ S, D i ^ (k i).length ≤ M^b := by
  calc
    _ ≤ ∏ i ∈ S, M^(k i).length := Finset.prod_le_prod₀
      (fun i hi => pow_nonneg (hD₀ i hi) _) (fun i hi => pow_le_pow_left₀ (hD₀ i hi) (hD i hi) _)
    _ = M^(∑ i ∈ S,(k i).length) := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ M^b := pow_le_pow_right₀ hM hk

lemma assignedAngularScaleND_paid (S : Finset α) (D : α → ℝ)
    (k : α → List (V →L[ℝ] V)) {M r : ℝ} {j : ℕ} (hM : 1 ≤ M)
    (hr : 0 ≤ r) (hpaid : r*M^2 ≤ 1)
    (hD₀ : ∀ i ∈ S, 0 ≤ D i) (hD : ∀ i ∈ S, D i ≤ M)
    (hk : ∑ i ∈ S, (k i).length ≤ 2*j) :
    r^j * (∏ i ∈ S, D i ^ (k i).length) ≤ 1 := by
  calc
    _ ≤ r^j * M^(2*j) := mul_le_mul_of_nonneg_left
      (assignedAngularScaleND_le S D k hM hD₀ hD hk) (pow_nonneg hr _)
    _ = (r*M^2)^j := by rw [mul_pow,pow_mul]
    _ ≤ 1 := by simpa using pow_le_pow_left₀ (by positivity) hpaid j

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
