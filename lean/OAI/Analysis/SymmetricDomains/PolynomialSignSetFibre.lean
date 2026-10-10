import Mathlib
import OAI.Analysis.SymmetricDomains.SortedFiberSelection

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
namespace Release061
open Set Polynomial
open scoped Classical BigOperators

theorem polynomialSignSet_fibre_roots {n : ℕ} {S : Set ((Fin n → ℝ) × ℝ)}
    (hS : PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) S) :
    ∃ R : Set ((Fin n → ℝ) × ℝ), ∃ N : ℕ,
      PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) R ∧
      (∀ x, ∃ r ≤ N, ∃ v : Fin r → ℝ, (x,v) ∈ SortedFiber R r) ∧
      ∀ x I, IsPreconnected I → (∀ y ∈ I, (x,y) ∉ R) →
        ∀ y ∈ I, ∀ z ∈ I, ((x,y) ∈ S ↔ (x,z) ∈ S) := by
  obtain ⟨s,W,hW⟩ := hS.finite_sign_description
  let Q : s → (Fin n → ℝ) → ℝ[X] := fun p x =>
    (((MvPolynomial.optionEquivLeft ℝ (Fin n)) p.val).map (MvPolynomial.eval x))
  let d : s → ℕ := fun p => ((MvPolynomial.optionEquivLeft ℝ (Fin n)) p.val).natDegree
  let R : Set ((Fin n → ℝ) × ℝ) := {z | ∃ p : s, Q p z.1 ≠ 0 ∧ (Q p z.1).eval z.2 = 0}
  have hd (p : s) (x : Fin n → ℝ) : (Q p x).natDegree ≤ d p := natDegree_map_le
  have hR : PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) R := by
    apply PolynomialSignSet.exists_finite
    intro p
    have hz : PolynomialSignSet id {x : Fin n → ℝ | Q p x = 0} := by
      simpa only [univ_inter] using SignElimination.zero_stratum_signSet
        (PolynomialSignSet.univ (c := id)) (Q p) (d p)
        (fun k => by
          simpa only [Q,coeff_map,id_eq] using (SignElimination.RationalOn.polynomial (c := id) (S := univ)
            (((MvPolynomial.optionEquivLeft ℝ (Fin n)) p.val).coeff k)))
        (fun x _ => hd p x)
    have hn := hz.compl.coordinate_preimage (fun z : (Fin n → ℝ) × ℝ => z.1)
      some (d := fun z o => Option.elim o z.2 z.1) (by intro z i; rfl)
    have he := PolynomialSignSet.zero (c := fun z : (Fin n → ℝ) × ℝ =>
      fun o => Option.elim o z.2 z.1) p.val
    convert hn.inter he using 1
    ext z
    simp only [mem_preimage,mem_compl_iff,mem_inter_iff,mem_ofPred_eq,Q,SignElimination.eval_optionEquivLeft]
  refine ⟨R,∑ p, d p,hR,?_,?_⟩
  · intro x
    let F : Finset ℝ := Finset.univ.biUnion (fun p : s => (Q p x).roots.toFinset)
    have hF (y : ℝ) : y ∈ F ↔ (x,y) ∈ R := by
      simp only [F,Finset.mem_biUnion,Finset.mem_univ,true_and,Multiset.mem_toFinset,
        mem_roots',IsRoot.def,R,mem_ofPred_eq]
    have hcard : F.card ≤ ∑ p, d p := by
      calc
        F.card ≤ ∑ p : s, (Q p x).roots.toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ p : s, d p := Finset.sum_le_sum (fun p _ =>
          (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (hd p x)))
    refine ⟨F.card,hcard,F.orderEmbOfFin rfl,(F.orderEmbOfFin rfl).strictMono,?_⟩
    intro y
    have he := Set.ext_iff.mp (Finset.range_orderEmbOfFin F rfl) y
    rw [← hF]
    simpa only [mem_range,Finset.mem_coe,eq_comm] using he.symm
  · intro x I hI hIR y hy z hz
    have hs (p : s) : SignType.sign ((Q p x).eval y) = SignType.sign ((Q p x).eval z) := by
      by_cases hp : Q p x = 0
      · simp only [hp,eval_zero]
      · apply hI.constant (f := fun t => SignType.sign ((Q p x).eval t)) ?_ hy hz
        intro t ht
        apply ContinuousAt.continuousWithinAt
        apply (continuousAt_sign_of_ne_zero ?_).comp (Q p x).continuous.continuousAt
        intro he
        exact hIR t ht ⟨p,hp,he⟩
    rw [hW,hW]
    have he : (fun p : s => SignType.sign (MvPolynomial.eval (fun o => Option.elim o y x) p.val)) =
        (fun p : s => SignType.sign (MvPolynomial.eval (fun o => Option.elim o z x) p.val)) := by
      funext p
      simpa only [Q,SignElimination.eval_optionEquivLeft] using hs p
    rw [he]
end Release061

end

end OAI
