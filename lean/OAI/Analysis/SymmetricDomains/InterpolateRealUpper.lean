import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial Finset
open scoped BigOperators Classical

noncomputable def realPartPolynomial (P : ℂ[X]) : ℝ[X] :=
  .ofFinsupp ⟨P.toFinsupp.coeff.mapRange Complex.re (by simp)⟩

@[simp] lemma realPartPolynomial_coeff (P : ℂ[X]) (n : ℕ) :
    (realPartPolynomial P).coeff n = (P.coeff n).re := rfl

lemma realPartPolynomial_degree_lt {P : ℂ[X]} {n : ℕ} (hP : P.degree < n) :
    (realPartPolynomial P).degree < n := by
  rw [degree_lt_iff_coeff_zero] at *
  intro k hk
  simp [hP k hk]

lemma realPartPolynomial_map {P : ℂ[X]} (hP : P.map (starRingEnd ℂ) = P) :
    (realPartPolynomial P).map Complex.ofRealHom = P := by
  ext n
  rw [coeff_map,realPartPolynomial_coeff]
  apply Complex.conj_eq_iff_re.mp
  simpa only [coeff_map] using congrArg (fun p : ℂ[X] => p.coeff n) hP

theorem real_interpolation (S : Finset ℂ)
    (hS : ∀ z ∈ S, starRingEnd ℂ z ∈ S) (v : ℂ → ℂ)
    (hv : ∀ z ∈ S, v (starRingEnd ℂ z) = starRingEnd ℂ (v z)) :
    ∃ P : ℝ[X], P.degree < S.card ∧
      ∀ z ∈ S, P.eval₂ Complex.ofRealHom z = v z := by
  let P := Lagrange.interpolate S id v
  have hdeg : P.degree < S.card := Lagrange.degree_interpolate_lt _ (fun _ _ _ _ h => h)
  have heval : ∀ z ∈ S, P.eval z = v z := fun z hz =>
    Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => h) hz
  have hconj : P.map (starRingEnd ℂ) = P := by
    apply eq_of_degrees_lt_of_eval_finset_eq S (degree_map_le.trans_lt hdeg) hdeg
    intro z hz
    have hh := eval_map_apply (starRingEnd ℂ) (starRingEnd ℂ z) (p := P)
    simp only [starRingEnd_apply,star_star] at hh
    rw [hh]
    change (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) z)) = P.eval z
    rw [heval _ (hS z hz),hv z hz,heval z hz]
    simp
  refine ⟨realPartPolynomial P,realPartPolynomial_degree_lt hdeg,fun z hz => ?_⟩
  rw [eval₂_eq_eval_map,realPartPolynomial_map hconj,heval z hz]

theorem real_interpolation_indexed {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hx : Function.Injective x) (τ : ι → ι)
    (hτ : ∀ i, x (τ i) = starRingEnd ℂ (x i))
    (v : ι → ℂ) (hv : ∀ i, v (τ i) = starRingEnd ℂ (v i)) :
    ∃ P : ℝ[X], P.degree < Fintype.card ι ∧
      ∀ i, P.eval₂ Complex.ofRealHom (x i) = v i := by
  let P := Lagrange.interpolate univ x v
  have hdeg : P.degree < Fintype.card ι :=
    Lagrange.degree_interpolate_lt _ (fun _ _ _ _ h => hx h)
  have heval : ∀ i, P.eval (x i) = v i := fun i =>
    Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => hx h) (mem_univ i)
  have hconj : P.map (starRingEnd ℂ) = P := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq univ (fun _ _ _ _ h => hx h)
      (degree_map_le.trans_lt hdeg) hdeg
    intro i _
    have hh := eval_map_apply (starRingEnd ℂ) (starRingEnd ℂ (x i)) (p := P)
    simp only [starRingEnd_apply,star_star] at hh
    rw [hh]
    change (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) (x i))) = P.eval (x i)
    rw [← hτ i,heval,heval,hv]
    simp
  refine ⟨realPartPolynomial P,realPartPolynomial_degree_lt hdeg,fun i => ?_⟩
  rw [eval₂_eq_eval_map,realPartPolynomial_map hconj,heval]

def realComplexNodes {α β : Type*} (r : α → ℝ) (c : β → ℂ) : α ⊕ (β ⊕ β) → ℂ :=
  Sum.elim (fun a => (r a : ℂ)) (Sum.elim c (fun b => starRingEnd ℂ (c b)))

def conjugateSwap {α β : Type*} : α ⊕ (β ⊕ β) → α ⊕ (β ⊕ β) :=
  Sum.elim Sum.inl (Sum.elim (fun b => .inr (.inr b)) (fun b => .inr (.inl b)))

lemma realComplexNodes_conj {α β : Type*} (r : α → ℝ) (c : β → ℂ) (i) :
    realComplexNodes r c (conjugateSwap i) = starRingEnd ℂ (realComplexNodes r c i) := by
  rcases i with a | b
  · simp [realComplexNodes,conjugateSwap]
  · rcases b with b | b <;> simp [realComplexNodes,conjugateSwap]

lemma realComplexNodes_injective {α β : Type*} {r : α → ℝ} {c : β → ℂ}
    (hr : Function.Injective r) (hc : Function.Injective c) (hpos : ∀ b, 0 < (c b).im) :
    Function.Injective (realComplexNodes r c) := by
  intro i j h
  rcases i with a | (b | b) <;> rcases j with a' | (b' | b')
  · apply congrArg Sum.inl
    exact hr (Complex.ofReal_injective h)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_im] at hi
    exact False.elim ((hpos b').ne' hi.symm)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_im,
      Complex.conj_im] at hi
    have := hpos b'
    exact False.elim (by linarith)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_im] at hi
    exact False.elim ((hpos b).ne' hi)
  · exact congrArg (fun b => Sum.inr (Sum.inl b)) (hc h)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.conj_im] at hi
    have := hpos b
    have := hpos b'
    exact False.elim (by linarith)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_im,
      Complex.conj_im] at hi
    have := hpos b
    exact False.elim (by linarith)
  · have hi := congrArg Complex.im h
    simp only [realComplexNodes,Sum.elim_inl,Sum.elim_inr,Complex.conj_im] at hi
    have := hpos b
    have := hpos b'
    exact False.elim (by linarith)
  · exact congrArg (fun b => Sum.inr (Sum.inr b)) (hc ((starRingEnd ℂ).injective h))

theorem interpolate_real_and_upper {α β : Type*} [Fintype α] [Fintype β]
    (r : α → ℝ) (c : β → ℂ) (hr : Function.Injective r) (hc : Function.Injective c)
    (hpos : ∀ b, 0 < (c b).im) (v : α → ℝ) (w : β → ℂ) :
    ∃ P : ℝ[X], P.degree < ((Fintype.card α + 2*Fintype.card β : ℕ) : WithBot ℕ) ∧
      (∀ a, P.eval (r a) = v a) ∧ (∀ b, P.eval₂ Complex.ofRealHom (c b) = w b) := by
  obtain ⟨P,hP,he⟩ := real_interpolation_indexed (realComplexNodes r c)
    (realComplexNodes_injective hr hc hpos) conjugateSwap (realComplexNodes_conj r c)
    (realComplexNodes v w) (realComplexNodes_conj v w)
  refine ⟨P,?_,?_,?_⟩
  · simpa only [Fintype.card_sum,two_mul,add_assoc] using hP
  · intro a
    have h := he (.inl a)
    change P.eval₂ Complex.ofRealHom (r a) = (v a : ℂ) at h
    apply Complex.ofReal_injective
    exact (eval₂_at_apply Complex.ofRealHom (r a) (p := P)).symm.trans h
  · intro b
    exact he (.inr (.inl b))

end Release061.SignElimination

end

end OAI
