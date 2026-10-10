import Mathlib
import OAI.Probability.LogConcave.TensorGraphs.AdjointMatrix
import OAI.Probability.LogConcave.JetEstimates.MultisetProd2

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped BigOperators

variable {d : ℕ} {P C : Type*} [Fintype P] [DecidableEq P] [Fintype C]

omit [Fintype C] in

theorem branch_factor_polySmooth (S : State P) {H : Point d → ℝ}
    (hH : PolySmooth H) (b : P → Point d) (f : P → Point d → ℝ)
    (hf : ∀p,PolySmooth (f p)) :
    PolySmooth (fun x =>
      (∏p,JetCalculus.jet b (S.derivatives p) (f p) x)*
      (S.hessians.map (fun h => hessian H b h x)).prod) := by
  apply (PolySmooth.prod Finset.univ (fun p _ => (hf p).jet b (S.derivatives p))).mul
  apply PolySmooth.multiset_prod
  intro h _
  exact (((hH.directional (b h.second)).directional (b h.first)).jet b h.extra)

theorem finite_branch_integrable (S : State P) {H : Point d → ℝ}
    (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (b : C → P → Point d) (f : C → P → Point d → ℝ)
    (hf : ∀c p,PolySmooth (f c p)) :
    Integrable (fun x => ∑c,
      (∏p,JetCalculus.jet (b c) (S.derivatives p) (f c p) x)*
      (S.hessians.map (fun h => hessian H (b c) h x)).prod) (gibbs H) := by
  exact (PolySmooth.sum Finset.univ
    (fun c _ => branch_factor_polySmooth S hH (b c) (f c) (hf c))).integrable
    hH.smooth.continuous ht
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open scoped BigOperators Classical

variable {X P Z W : Type*}

def coloringSplit : (((X ⊕ P) ⊕ Z) → W) ≃ (((X ⊕ Z) → W) × (P → W)) where
  toFun c := (fun t => match t with
    | Sum.inl x => c (Sum.inl (Sum.inl x))
    | Sum.inr z => c (Sum.inr z),fun p => c (Sum.inl (Sum.inr p)))
  invFun c t := match t with
    | Sum.inl (Sum.inl x) => c.1 (Sum.inl x)
    | Sum.inl (Sum.inr p) => c.2 p
    | Sum.inr z => c.1 (Sum.inr z)
  left_inv c := by
    funext t
    rcases t with (x|p)|z <;> rfl
  right_inv c := by
    apply Prod.ext
    · funext t
      cases t <;> rfl
    · rfl

theorem sum_colorings_split [Fintype X] [Fintype P] [Fintype Z] [Fintype W]
    (f : (((X ⊕ P) ⊕ Z) → W) → ℝ) :
    (∑c,f c)=∑t : (X ⊕ Z) → W,∑a : P → W,f (coloringSplit.symm (t,a)) := by
  classical
  simpa only [Fintype.sum_prod_type] using (Equiv.sum_comp coloringSplit.symm f).symm
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped BigOperators NNReal

variable {d : ℕ} {P I T : Type*} [Fintype P] [DecidableEq P] [Fintype I] [Fintype T]

theorem parametrized_adjoint_expansion
    {H : Point d → ℝ} (b : I → Point d) (F : T → P → I → Point d → ℝ)
    {K : ℝ≥0} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hK : LipschitzWith K (gradient H)) (hF : ∀t p i,PolySmooth (F t p i)) :
    (∫x,(∑t,∏p,tensorAdjoint H b (F t p) x) ∂gibbs H)=
      ((expand (Fintype.card P) initial).map (fun S =>
        ∑t,∑a : P → I,∫x,
          (∏p,JetCalculus.jet (fun q => b (a q)) (S.derivatives p) (F t p (a p)) x)*
          (S.hessians.map (fun h => hessian H (fun q => b (a q)) h x)).prod ∂gibbs H)).sum := by
  have hi (t : T) : Integrable (fun x => ∏p,tensorAdjoint H b (F t p) x) (gibbs H) :=
    (PolySmooth.prod Finset.univ (fun p _ => hH.tensorAdjoint (hF t p) b)).integrable
      hH.smooth.continuous ht
  rw [integral_finsetSum Finset.univ (fun t _ => hi t)]
  have he (t : T) := tensor_actual_adjoint_expansion_branch_first
    (fun a : P → I => regular_of_polySmooth (fun p => b (a p)) hH ht hK (fun p => hF t p (a p)))
  simp_rw [he]
  generalize expand (Fintype.card P) (initial (P:=P))=L
  induction L with
  | nil => simp
  | cons S L ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
