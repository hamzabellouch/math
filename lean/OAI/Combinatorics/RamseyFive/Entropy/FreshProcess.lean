import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.CapDecoder
import OAI.Combinatorics.RamseyFive.Entropy.SubsetMixture

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def freshRejection (R : α→β→Prop) (q : ℝ)
    (W : Finset α) (hW : W.Nonempty) (h N : ℕ) (E : Finset (Fin h→α)) (b : β) : ℝ :=
  eventMass (map (iid (iid (uniformOn W hW) (Fin h)) (Fin N)) (firstAccepted E (n:=N)))
    ((Finset.univ.filter (fun x=>(1/(5*q))*h ≤ hits (Finset.univ.filter (fun a=>R a b)) x)).image some)

theorem finite_fresh_process {ι κ Θ : Type*} [Fintype ι] [Fintype κ] [Fintype Θ]
    (R : α→β→Prop) (p : Law α) (r : Law β) (μ : Law ι) (ν : Law κ)
    (X : ι→Finset α) (Y : κ→Finset β) (prior : ι→κ→Law Θ)
    (A W : ι→κ→Θ→Finset α)
    (hA : ∀i j θ,(A i j θ).Nonempty) (hW : ∀i j θ,(W i j θ).Nonempty)
    (hAW : ∀i j θ,A i j θ⊆W i j θ) (hAX : ∀i j θ,A i j θ⊆X i)
    (q c L : ℝ) (hq : 0 < q) (hc : 0 < c) (hL : 0 ≤ L)
    (hsize : ∀i j θ,c*(X i).card ≤ (A i j θ).card)
    (h N : ι→κ→Θ→ℕ) (hh : ∀i j θ,0 < h i j θ) (hN : ∀i j θ,0 < N i j θ)
    (E : ∀i j θ,Finset (Fin (h i j θ)→α))
    (hsource : ∀i j θ x,x∈E i j θ→∀k,x k∈A i j θ)
    (hE : ∀i j θ,(9:ℝ)/10 ≤ eventMass (iid (uniformOn (A i j θ) (hA i j θ))
      (Fin (h i j θ))) (E i j θ))
    (ready : ι→κ→Θ→Prop)
    (hX : ∀a,(∑i,μ i*uniformWeight (X i) a) ≤ L*p a)
    (hY : ∀b,(∑j,ν j*uniformWeight (Y j) b) ≤ L*r b) :
    (∑i,∑j,μ i*ν j*(∑θ,prior i j θ*(∑b,uniformWeight (Y j) b*
      (if ready i j θ then freshRejection R q (W i j θ) (hW i j θ)
        (h i j θ) (N i j θ) (E i j θ) b else 0)))) ≤
      (50*q/(9*c))*L^2*relationMass R p r := by
  apply adaptive_rejection_average R p r μ ν X Y prior
    (fun i j θ b=>if ready i j θ then freshRejection R q (W i j θ) (hW i j θ)
      (h i j θ) (N i j θ) (E i j θ) b else 0) _ L (by positivity) hL hX hY
  intro i j θ b
  by_cases hr : ready i j θ
  · rw [ite_eq_left hr]
    exact fresh_test_domination (A i j θ) (X i) (W i j θ)
      (Finset.univ.filter (fun a=>R a b)) (hA i j θ) (hW i j θ)
      (hAW i j θ) (hAX i j θ) q c hq hc (hsize i j θ)
      (h i j θ) (N i j θ) (hh i j θ) (hN i j θ) (E i j θ)
      (hsource i j θ) (hE i j θ)
  · rw [ite_eq_right hr]
    positivity

end SharpRamseyFive.FiniteEntropy

end OAI
