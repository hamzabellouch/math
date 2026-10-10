import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteNashCoverVertical
import OAI.Analysis.SymmetricDomains.PolynomialSignSetFibre

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
open Set
open scoped Classical

theorem polynomialSignSet_finite_nash_cover (n : ℕ) (S : Set (Fin n → ℝ))
    (hS : PolynomialSignSet id S) : HasFiniteNashCover S := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      by_cases hne : S.Nonempty
      · have hSuniv : S = univ := by
          obtain ⟨x,hx⟩ := hne
          apply eq_univ_of_forall
          intro y
          rwa [Subsingleton.elim y x]
        rw [hSuniv]
        simpa only [NashPatch.image,NashPatch.identity,image_id] using
          HasFiniteNashCover.patch (NashPatch.identity (univ : Set (Fin 0 → ℝ))
            isOpen_univ isConnected_univ PolynomialSignSet.univ)
      · rw [not_nonempty_iff_eq_empty.mp hne]
        exact HasFiniteNashCover.empty
    | succ n =>
      have H (d : ℕ) (hd : d ≤ n) (T : Set (Fin d → ℝ)) (hT : PolynomialSignSet id T) :
          HasFiniteNashCover T := ih d (Nat.lt_succ_of_le hd) T hT
      have Ha := analytic_nash_refinement n H n le_rfl
      let S' : Set ((Fin n → ℝ) × ℝ) := {z | Fin.cons z.2 z.1 ∈ S}
      have hs : PolynomialSignSet (fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) S' := by
        exact hS.coordinate_preimage (fun z : (Fin n → ℝ) × ℝ => Fin.cons z.2 z.1)
          (Fin.cases none some) (d := fun z : (Fin n → ℝ) × ℝ => fun o => Option.elim o z.2 z.1) (by intro z i; exact Fin.cases rfl (fun _ => rfl) i)
      obtain ⟨R,N,hR,hroots,hconstant⟩ := polynomialSignSet_fibre_roots hs
      choose B f _hB hf hmem hsort using (fun r : Fin (N+1) => sorted_fiber_selection hR r.val)
      let C (r : Fin (N+1)) (p : VerticalPiece r.val) : Set (Fin n → ℝ) :=
        {x | x ∈ B r ∧ (verticalPieceSet (f r x) p).Nonempty ∧
          ∀ t ∈ verticalPieceSet (f r x) p, (x,t) ∈ S'}
      have hC (r : Fin (N+1)) (p : VerticalPiece r.val) : PolynomialSignSet id (C r p) :=
        (hf r).predicate (verticalPiece_base_polynomialSignSet hs p)
      let T (r : Fin (N+1)) (p : VerticalPiece r.val) : Set (Fin (n+1) → ℝ) :=
        {y | Fin.tail y ∈ C r p ∧ y 0 ∈ verticalPieceSet (f r (Fin.tail y)) p}
      have hT (r : Fin (N+1)) (p : VerticalPiece r.val) : HasFiniteNashCover (T r p) := by
        apply hasFiniteNashCover_verticalPiece Ha ((hf r).mono (hC r p) (fun _ hx => hx.1)) p
        exact fun _ hx => hx.2.1
      have he : S = ⋃ r ∈ (Finset.univ : Finset (Fin (N+1))),
          ⋃ p ∈ (Finset.univ : Finset (VerticalPiece r.val)), T r p := by
        ext y
        simp only [mem_iUnion,Finset.mem_univ,exists_prop,true_and]
        constructor
        · intro hy
          obtain ⟨r,hr,v,hv⟩ := hroots (Fin.tail y)
          let a : Fin (N+1) := ⟨r,Nat.lt_succ_of_le hr⟩
          have hxb : Fin.tail y ∈ B a := (hmem a _).mpr ⟨v,hv⟩
          have hyS : (Fin.tail y,y 0) ∈ S' := by
            change Fin.cons (y 0) (Fin.tail y) ∈ S
            rwa [Fin.cons_self_tail]
          have hc : ∀ I, IsPreconnected I → (∀ z ∈ I, ∀ i, z ≠ f a (Fin.tail y) i) →
              ∀ t ∈ I, ∀ z ∈ I, ((Fin.tail y,t) ∈ S' ↔ (Fin.tail y,z) ∈ S') := by
            intro I hI hfree
            apply hconstant (Fin.tail y) I hI
            intro z hz hzr
            obtain ⟨i,hei⟩ := (hsort a _ hxb).2 z |>.mp hzr
            exact hfree z hz i hei
          obtain ⟨p,hyp,hpS⟩ := verticalPieces_cover (f a (Fin.tail y))
            {t | (Fin.tail y,t) ∈ S'} hc (y 0) hyS
          exact ⟨a,p,⟨hxb,⟨y 0,hyp⟩,hpS⟩,hyp⟩
        · rintro ⟨r,p,hy,hyp⟩
          have hh := hy.2.2 (y 0) hyp
          change Fin.cons (y 0) (Fin.tail y) ∈ S at hh
          rwa [Fin.cons_self_tail] at hh
      rw [he]
      apply HasFiniteNashCover.finite_union
      intro r _
      exact HasFiniteNashCover.finite_union Finset.univ (fun p _ => hT r p)

theorem semialgebraicOn_finite_analytic_nash_cover {n k : ℕ} {S : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → (Fin k → ℝ)} (hf : SemialgebraicOn S f) : HasAnalyticNashCover S f :=
  analytic_nash_refinement n (fun d _ T hT => polynomialSignSet_finite_nash_cover d T hT)
    n le_rfl k S f hf
end Release061

end

end OAI
