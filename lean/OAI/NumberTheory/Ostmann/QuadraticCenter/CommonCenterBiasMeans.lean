import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionWindows
import OAI.NumberTheory.Ostmann.QuadraticCenter.CommonCenterBiasBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem mean_orientedQuadraticAverage (U : Finset ℤ) (P : Finset ℕ)
    (ε t : ℕ → ℤ) :
    (∑x∈U,orientedQuadraticAverage P ε t x)/U.card =
      (∑p∈P,(∑x∈U,((ε p*jacobiSym (x-t p) p:ℤ):ℝ))/U.card)/P.card := by
  unfold orientedQuadraticAverage
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem affineKernelAverage_mean_lower (U : Finset ℤ) (P : Finset ℕ)
    (hP : 0 < P.card) (ε t : ℕ → ℤ) (m : ℕ) (h : ℤ)
    (hcop : ∀p∈P,Nat.Coprime m p) (hcenter : ∀p∈P,(p:ℤ)∣h-(m:ℤ)*t p)
    {c : ℝ} (hbias : ∀p∈P,c≤(∑x∈U,((ε p*jacobiSym (x-t p) p:ℤ):ℝ))/U.card) :
    c≤(∑x∈U,affineKernelAverage P (commonCenterOrientation ε m) m h x)/U.card := by
  simp_rw [affineKernelAverage_eq_oriented P ε t m h hcop hcenter]
  rw [mean_orientedQuadraticAverage]
  apply (le_div_iff₀ (show (0:ℝ)<P.card by exact_mod_cast hP)).mpr
  calc
    _ = ∑p∈P,c := by simp; ring
    _ ≤ _ := Finset.sum_le_sum hbias

theorem affineKernelAverage_mean_upper (U : Finset ℤ) (P : Finset ℕ)
    (hP : 0 < P.card) (ε t : ℕ → ℤ) (m : ℕ) (h : ℤ)
    (hcop : ∀p∈P,Nat.Coprime m p) (hcenter : ∀p∈P,(p:ℤ)∣h-(m:ℤ)*t p)
    {c : ℝ} (hbias : ∀p∈P,(∑x∈U,((ε p*jacobiSym (x-t p) p:ℤ):ℝ))/U.card≤c) :
    (∑x∈U,affineKernelAverage P (commonCenterOrientation ε m) m h x)/U.card≤c := by
  simp_rw [affineKernelAverage_eq_oriented P ε t m h hcop hcenter]
  rw [mean_orientedQuadraticAverage]
  apply (div_le_iff₀ (show (0:ℝ)<P.card by exact_mod_cast hP)).mpr
  calc
    _ ≤ ∑p∈P,c := Finset.sum_le_sum hbias
    _ = _ := by simp; ring

theorem actual_commonCenter_bias_transport (d : Decomposition) (X : ℕ)
    (P : Finset ℕ) (hP : 0 < P.card) (ε t : ℕ → ℤ) (m : ℕ) (h : ℤ)
    (hm : 0 < m) (hprime : ∀p∈P,p.Prime ∧ m < p)
    (hcenter : ∀p∈P,(p:ℤ)∣h-(m:ℤ)*t p) (δ : ℝ)
    (hbias : ∀p∈P,(ε p=1 ∨ ε p=-1) ∧
      δ/4≤(∑x∈positiveIntegerWindow d.A X,((ε p*jacobiSym (x-t p) p:ℤ):ℝ))/
        (positiveIntegerWindow d.A X).card ∧
      (∑x∈negativeIntegerWindow d.B X,((ε p*jacobiSym (x-t p) p:ℤ):ℝ))/
        (negativeIntegerWindow d.B X).card≤-δ/4) :
    (∀p∈P,commonCenterOrientation ε m p=1 ∨ commonCenterOrientation ε m p=-1) ∧
    (∀x,|affineKernelAverage P (commonCenterOrientation ε m) m h x|≤1) ∧
    δ/4≤(∑x∈positiveIntegerWindow d.A X,
      affineKernelAverage P (commonCenterOrientation ε m) m h x)/(positiveIntegerWindow d.A X).card ∧
    (∑x∈negativeIntegerWindow d.B X,
      affineKernelAverage P (commonCenterOrientation ε m) m h x)/(negativeIntegerWindow d.B X).card≤-δ/4 := by
  have hcop (p : ℕ) (hp : p∈P) : Nat.Coprime m p :=
    commonCenter_multiplier_coprime (hprime p hp).1 hm (hprime p hp).2
  refine ⟨fun p hp => commonCenterOrientation_sign (hbias p hp).1 (hcop p hp),?_,?_,?_⟩
  · exact affineKernelAverage_abs_le_one P hP ε (fun p hp => (hbias p hp).1) m h hcop
  · exact affineKernelAverage_mean_lower _ P hP ε t m h hcop hcenter (fun p hp => (hbias p hp).2.1)
  · exact affineKernelAverage_mean_upper _ P hP ε t m h hcop hcenter (fun p hp => (hbias p hp).2.2)

end Ostmann.QuadraticCenter

end

end OAI
