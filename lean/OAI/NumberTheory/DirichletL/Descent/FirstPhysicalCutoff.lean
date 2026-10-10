import OAI.NumberTheory.DirichletL.Descent.FirstCutoffScale

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def firstPhysicalMultiplier {ι : Type*} (p : ι→O) (S : Finset ι)
    (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) : O :=
  (ConcretePrimeRowBridge.idealGenerator f)^2 * dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂

lemma firstPhysicalMultiplier_ne_zero {ι : Type*} (p : ι→O) (hp : ∀ i,p i≠0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (S : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) (hf : f≠0) :
    firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f≠0 :=
  mul_ne_zero (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero f hf))
    (primeProduct_ne_zero p hp _ _)

lemma firstPhysicalMultiplier_row {ι : Type*} (p : ι→O) (S : Finset ι)
    (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) (h : O) :
    firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f*h =
      DescentWeightedCauchy.firstElementRowMap (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h) := by
  unfold firstPhysicalMultiplier DescentWeightedCauchy.firstElementRowMap
  ring

theorem first_physical_cutoff_raw_tail {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (hf0 : f≠0) (h : O)
    (Z M r ell V delta B j eta tau : ℝ) (hZ : 0<Z)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta))
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta))
    (hf : (Ideal.absNorm f : ℝ)≤Z^(V+eta))
    (hd : primeProductNorm p divisor≤Z^(delta+eta))
    (hc : Z^(B-eta)≤primeProductNorm p common)
    (hj : Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta))
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta))
    (hout : h∉childFrequencyBall (firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f)
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))) :
    Z^tau ≤ (Z^M/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2 := by
  by_contra hbad
  have hratio := (lt_of_not_ge hbad).le
  have hrow := first_ratio_canonical_row p hp S N Q v₁ v₂ ε₁ ε₂ hv hNQ hNS hQS common divisor f h
    Z M r ell V delta B j eta tau hZ hb₁ hb₂ hf hd hc hj hcol₁ hcol₂ hratio
  apply hout
  apply (mem_childFrequencyBall _ (firstPhysicalMultiplier_ne_zero p hp S v₁ v₂ ε₁ ε₂ f hf0) _ h).mpr
  simpa only [firstPhysicalMultiplier_row] using hrow

end
end SevenEighths.InverseMoment

end OAI
