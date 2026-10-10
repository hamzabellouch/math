import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Cutoff

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff

namespace OrdinaryAnalyticCentering
open Finset OrdinaryAnalyticCutoff OrdinaryTwistWidth
noncomputable def core (B : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Real.exp B⌋₊).filter (fun p=>p.Prime ∧
    B^(999999/1000000:ℝ)<Real.log p ∧ Real.log p≤B)
noncomputable def center (B : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Real.exp B⌋₊).filter (fun p=>p.Prime ∧
    B^(9999/10000:ℝ)<Real.log p ∧ Real.log p≤B^(999999/1000000:ℝ))
noncomputable def A : ℝ := Real.exp (2*(400/(1/1000000:ℝ)))
noncomputable def P₀ (B : ℝ) : ℝ := Real.exp (B^(9999/10000:ℝ))
noncomputable def J (C₀ B : ℝ) : ℕ := ⌈C₀*Real.log B⌉₊
noncomputable def coreMean (B : ℝ) : ℝ := ∑p∈core B,(p:ℝ)⁻¹
noncomputable def L₀ (B : ℝ) : ℝ :=
  (∏p∈core B,(1+A/(p:ℝ)))*(∏p∈center B,(1+(p:ℝ)⁻¹))
noncomputable def cut (phi : ℝ→ℝ) (B : ℝ) (d n : ℕ) : ℂ :=
  cutoff phi ((core B).filter (fun p=>¬p∣d)) (coreMean B) n
noncomputable def divisorWeight (B : ℝ) (d : ℕ) : ℝ :=
  A^(primeCount (core B) d)
noncomputable def kernel (phi : ℝ→ℝ) (B : ℝ) (d x y : ℕ) : ℂ :=
  cut phi B d x*cut phi B d y*(divisorWeight B d:ℂ)*
  (if (∏p∈(core B).filter (fun p=>p∣d),p)∣x then (1:ℂ) else 0)*
  ∏p∈(center B).filter (fun p=>p∣d),((if p∣x then (1:ℂ) else 0)-(1/4:ℂ)/(p:ℂ))
noncomputable def rawSum (phi : ℝ→ℝ) (B : ℝ) (D : Finset ℕ)
    (a f g : ℕ→ℂ) (h : ℕ) (X : ℝ) : ℂ :=
  ∑x∈Icc 1 ⌊X⌋₊,∑d∈D,a d*(divisorWeight B d:ℂ)*f x*g (x+h*d)*
    cut phi B d x*cut phi B d (x+h*d)*(if d∣x then (1:ℂ) else 0)
noncomputable def centeredSum (phi : ℝ→ℝ) (B : ℝ) (D : Finset ℕ)
    (a f g : ℕ→ℂ) (h : ℕ) (X : ℝ) : ℂ :=
  ∑x∈Icc 1 ⌊X⌋₊,∑d∈D,a d*f x*g (x+h*d)*kernel phi B d x (x+h*d)
def Admissible (B C₀ τ H : ℝ) (D : Finset ℕ) : Prop :=
  1≤H ∧ H≤Real.exp (C₀*B) ∧ ∀d∈D,
    Squarefree d ∧ d.primeFactors⊆core B∪center B ∧ 1<d ∧
    H<d ∧ (d:ℝ)≤τ*H ∧ d.primeFactors.card≤J C₀ B
end OrdinaryAnalyticCentering

end

end OAI
