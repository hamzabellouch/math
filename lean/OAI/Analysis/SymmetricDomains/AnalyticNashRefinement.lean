import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicOffsetLimitsFamily
import OAI.Analysis.SymmetricDomains.FiniteUnion

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
open Set Filter Topology MeasureTheory
open scoped Classical

namespace SemialgebraicOn
lemma analytic_off_polynomial {n k : ℕ} {B : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → (Fin k → ℝ)} (hf : SemialgebraicOn B f) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ x ∈ B, MvPolynomial.eval x D ≠ 0 → AnalyticAt ℝ f x := by
  have hi (i : Fin k) : ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ x ∈ B, MvPolynomial.eval x D ≠ 0 → AnalyticAt ℝ (fun x => f x i) x := by
    have hp := (SemialgebraicOn.polynomial (B := (univ : Set (Fin k → ℝ)))
      PolynomialSignSet.univ (fun _ : Fin 1 => MvPolynomial.X i)).comp hf (fun _ _ => mem_univ _)
    have hs := hp.coordinate_preimage
      (fun x : Option (Fin n) → ℝ => ((fun i => x (some i)),fun _ => x none))
      (Sum.elim some (fun _ => none)) (d := id) (by intro x j; cases j <;> rfl)
    have he : PolynomialSignSet id
        {x : Option (Fin n) → ℝ | (fun i => x (some i)) ∈ B ∧
          x none = f (fun i => x (some i)) i} := by
      convert hs using 1
      ext x
      simp only [mem_preimage,mem_ofPred_eq,Function.comp_apply,MvPolynomial.eval_X,funext_iff,forall_const]
    exact semialgebraic_function_analytic_off_polynomial B (fun x => f x i) he
  choose D hD ha using hi
  refine ⟨∏ i, D i,Finset.prod_ne_zero_iff.mpr (fun i _ => hD i),?_⟩
  intro x hx hprod
  apply analyticAt_pi_iff.mpr
  intro i
  apply ha i x hx
  intro hz
  apply hprod
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz
end SemialgebraicOn

def HasAnalyticNashCover {n k : ℕ} (S : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → (Fin k → ℝ)) : Prop :=
  ∃ P : Finset (NashPatch n), (∀ x, x ∈ S ↔ ∃ p ∈ P, x ∈ p.image) ∧
    ∀ p ∈ P, AnalyticOnNhd ℝ (f ∘ p.toFun) p.domain

namespace HasAnalyticNashCover
variable {n k : ℕ} {S T : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → (Fin k → ℝ)}

lemma empty : HasAnalyticNashCover (∅ : Set (Fin n → ℝ)) f := by
  exact ⟨∅,by simp,by simp⟩

lemma union (hS : HasAnalyticNashCover S f) (hT : HasAnalyticNashCover T f) :
    HasAnalyticNashCover (S ∪ T) f := by
  obtain ⟨P,hP,haP⟩ := hS
  obtain ⟨Q,hQ,haQ⟩ := hT
  refine ⟨P ∪ Q,fun x => ?_,?_⟩
  · simp only [mem_union,hP,hQ,Finset.mem_union]
    aesop
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact haP p hp
    · exact haQ p hp

lemma finite_union {α : Type*} (s : Finset α) {S : α → Set (Fin n → ℝ)}
    (hS : ∀ i ∈ s, HasAnalyticNashCover (S i) f) : HasAnalyticNashCover (⋃ i ∈ s, S i) f := by
  induction s using Finset.induction_on with
  | empty => simpa using (empty (n := n) (f := f))
  | @insert i s hi ih =>
    simpa only [Finset.mem_insert,ofPred_or,iUnion_iUnion_eq_or_left] using
      (hS i (Finset.mem_insert_self _ _)).union
        (ih (fun j hj => hS j (Finset.mem_insert_of_mem hj)))

lemma of_analytic (hS : HasFiniteNashCover S) (hf : AnalyticOnNhd ℝ f S) :
    HasAnalyticNashCover S f := by
  obtain ⟨P,hP⟩ := hS
  refine ⟨P,hP,?_⟩
  intro p hp x hx
  exact (hf _ ((hP _).mpr ⟨p,hp,x,hx,rfl⟩)).comp (p.analytic_toFun x hx)

lemma compose_patch (p : NashPatch n)
    (h : HasAnalyticNashCover p.domain (f ∘ p.toFun)) : HasAnalyticNashCover p.image f := by
  obtain ⟨P,hP,haP⟩ := h
  have hsub (q : {q // q ∈ P}) : q.val.image ⊆ p.domain := by
    intro y hy
    exact (hP y).mpr ⟨q,q.property,hy⟩
  let Q := P.attach.image (fun q => p.comp q.val (hsub q))
  refine ⟨Q,fun y => ?_,?_⟩
  · constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨q,hq,z,hz,he⟩ := (hP x).mp hx
      refine ⟨p.comp q (hsub ⟨q,hq⟩),Finset.mem_image.mpr ⟨⟨q,hq⟩,by simp,rfl⟩,z,hz,?_⟩
      change p.toFun (q.toFun z) = p.toFun x
      rw [he]
    · rintro ⟨r,hr,y,hy,hye⟩
      obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hr
      exact ⟨q.val.toFun y,hsub q ⟨y,hy,rfl⟩,hye⟩
  · intro r hr
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hr
    exact haP q.val q.property

end HasAnalyticNashCover

theorem analytic_nash_refinement (n : ℕ)
    (H : ∀ d ≤ n, ∀ S : Set (Fin d → ℝ), PolynomialSignSet id S → HasFiniteNashCover S) :
    ∀ d ≤ n, ∀ k (S : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → (Fin k → ℝ)),
      SemialgebraicOn S f → HasAnalyticNashCover S f := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hdn k S f hf
    obtain ⟨D,hD,ha⟩ := hf.analytic_off_polynomial
    let G := S ∩ {x | MvPolynomial.eval x D ≠ 0}
    let E := S ∩ {x | MvPolynomial.eval x D = 0}
    have hGs : PolynomialSignSet id G := hf.domain.inter (PolynomialSignSet.zero D).compl
    have hEs : PolynomialSignSet id E := hf.domain.inter (PolynomialSignSet.zero D)
    have hG : HasAnalyticNashCover G f :=
      .of_analytic (H d hdn G hGs) (fun x hx => ha x hx.1 hx.2)
    have hE : HasAnalyticNashCover E f := by
      obtain ⟨P,hP⟩ := H d hdn E hEs
      have hpcover (p : NashPatch d) (hp : p ∈ P) : HasAnalyticNashCover p.image f := by
        have hsub : p.image ⊆ E := fun x hx => (hP x).mpr ⟨p,hp,hx⟩
        have hlt : p.dim < d := p.dim_lt_of_empty_interior
          ((volume : Measure (Fin d → ℝ)).interior_eq_empty_of_null (real_polynomial_zero_null D hD))
          (fun _ hx => (hsub hx).2)
        have hps : SemialgebraicOn p.domain (f ∘ p.toFun) := hf.comp p.semialgebraic_toFun
          (fun x hx => (hsub ⟨x,hx,rfl⟩).1)
        exact (ih p.dim hlt (p.dim_le.trans hdn) k p.domain _ hps).compose_patch p
      have he : E = ⋃ p ∈ P, p.image := by
        ext x
        simp only [mem_iUnion,hP]
        aesop
      rw [he]
      exact HasAnalyticNashCover.finite_union P hpcover
    have he : S = G ∪ E := by
      ext x
      simp only [G,E,mem_union,mem_inter_iff,mem_ofPred_eq]
      tauto
    rw [he]
    exact hG.union hE
end Release061

end

end OAI
