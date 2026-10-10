import OAI.NumberTheory.DirichletL.Detector.GramIdealDilation
import OAI.NumberTheory.DirichletL.Detector.GramLatticeSource

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma primary_product (C d : O) (hC : λ₀^2∣C-1) (hd : λ₀^2∣d-1) : λ₀^2∣C*d-1 := by
  have h := dvd_add (hC.mul_right d) hd
  convert h using 1 ; ring

theorem jointExtension_divisor_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k : O) (hC : λ₀^2∣C-1)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (D : SupportedIdeal) (W : O→O→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      if D.val∣I.val ∧ D.val∣J.val then
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
          W (primaryGenerator I.val) (primaryGenerator J.val) else 0)=
      ∑'n : O,∑'m : O,
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator D.val*n) (primaryGenerator D.val*m)*
          W (primaryGenerator D.val*n) (primaryGenerator D.val*m) := by
  rw [supported_divisor_pair_tsum D (fun I J=>
    jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
      W (primaryGenerator I.val) (primaryGenerator J.val))]
  simp only [supported_dilation_generator]
  have hd : λ₀^2∣primaryGenerator D.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ D.property)).2
  exact jointExtension_ideal_lattice S hS hbad σ C k (primaryGenerator D.val) (primary_product C _ hC hd)
    u a b r hr P hg c (fun n m=>W (primaryGenerator D.val*n) (primaryGenerator D.val*m))

end SevenEighths.ProbeGramCommon
end

end OAI
