import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetProjection

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
namespace Release061.PolynomialSignSet
open Set
open scoped Classical

lemma eval_substitution {ι κ : Type*} (d : κ → ℝ) (q : ι → MvPolynomial κ ℝ)
    (p : MvPolynomial ι ℝ) :
    MvPolynomial.eval d (MvPolynomial.eval₂Hom MvPolynomial.C q p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval d (q i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp only [map_add,hp,hr]
  | mul_X p i hp => simp only [map_mul,MvPolynomial.eval₂Hom_X',MvPolynomial.eval_X,hp]

theorem polynomial_preimage {X Y ι κ : Type*} {c : X → ι → ℝ} {d : Y → κ → ℝ}
    {S : Set X} (hS : PolynomialSignSet c S) (f : Y → X)
    (q : ι → MvPolynomial κ ℝ)
    (hc : ∀ y i, c (f y) i = MvPolynomial.eval (d y) (q i)) :
    PolynomialSignSet d (f ⁻¹' S) := by
  have hv (p : MvPolynomial ι ℝ) (y : Y) :
      MvPolynomial.eval (d y) (MvPolynomial.eval₂Hom MvPolynomial.C q p) =
        MvPolynomial.eval (c (f y)) p := by
    rw [eval_substitution]
    rw [show (fun i => MvPolynomial.eval (d y) (q i)) = c (f y) from
      funext (fun i => (hc y i).symm)]
  induction hS with
  | zero p =>
    convert PolynomialSignSet.zero (c := d) (MvPolynomial.eval₂Hom MvPolynomial.C q p) using 1
    ext y
    simp only [mem_preimage,mem_ofPred_eq,hv]
  | positive p =>
    convert PolynomialSignSet.positive (c := d) (MvPolynomial.eval₂Hom MvPolynomial.C q p) using 1
    ext y
    simp only [mem_preimage,mem_ofPred_eq,hv]
  | compl _ ih => simpa only [preimage_compl] using ih.compl
  | union _ _ ih ih' => simpa only [preimage_union] using ih.union ih'

theorem coordinate_preimage {X Y ι κ : Type*} {c : X → ι → ℝ} {d : Y → κ → ℝ}
    {S : Set X} (hS : PolynomialSignSet c S) (f : Y → X)
    (r : ι → κ) (hc : ∀ y i, c (f y) i = d y (r i)) :
    PolynomialSignSet d (f ⁻¹' S) :=
  hS.polynomial_preimage f (fun i => MvPolynomial.X (r i)) (by simpa using hc)

end Release061.PolynomialSignSet

namespace Release061.SignElimination
open Set
open scoped Classical

universe uX uI uK

theorem polynomialSignSet_projection_finite {X : Type uX} {ι : Type uI} {κ : Type uK} [Finite κ]
    {c : X → ι → ℝ} {A : Set (X × (κ → ℝ))}
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) A) :
    PolynomialSignSet c {x | ∃ y : κ → ℝ, (x,y) ∈ A} := by
  classical
  suffices hh : ∀ (κ : Type uK) [Finite κ], ∀ {X : Type uX} {ι : Type uI} (c : X → ι → ℝ)
      (A : Set (X × (κ → ℝ))),
      PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) A →
        PolynomialSignSet c {x | ∃ y : κ → ℝ, (x,y) ∈ A} from hh κ c A hA
  intro κ _
  induction κ using Finite.induction_empty_option with
  | @of_equiv α β e ih =>
    intro X ι c A hA
    let f : (X × (α → ℝ)) → X × (β → ℝ) := fun z => (z.1,z.2 ∘ e.symm)
    have hp := hA.coordinate_preimage f (Sum.map id e.symm)
      (d := fun z => Sum.elim (c z.1) z.2) (by intro z i; cases i <;> rfl)
    have hh := ih c (f ⁻¹' A) hp
    convert hh using 1
    ext x
    simp only [mem_ofPred_eq,mem_preimage]
    constructor
    · rintro ⟨y,hy⟩
      exact ⟨y ∘ e,by simpa [f,Function.comp_def] using hy⟩
    · rintro ⟨y,hy⟩
      exact ⟨y ∘ e.symm,hy⟩
  | h_empty =>
    intro X ι c A hA
    let f : X → X × (PEmpty.{uK+1} → ℝ) := fun x => (x,fun a => a.elim)
    have hp := hA.coordinate_preimage f (Sum.elim id PEmpty.elim)
      (d := c) (by intro x i; cases i with | inl i => rfl | inr a => exact a.elim)
    convert hp using 1
    ext x
    simp only [mem_ofPred_eq,mem_preimage]
    constructor
    · rintro ⟨y,hy⟩
      have he : y = fun a : PEmpty.{uK+1} => a.elim := funext fun a => a.elim
      simpa only [f,he] using hy
    · intro hx
      exact ⟨_,hx⟩
  | @h_option κ _ ih =>
    intro X ι c A hA
    let f : ((X × (κ → ℝ)) × ℝ) → X × (Option κ → ℝ) :=
      fun z => (z.1.1,fun o => o.elim z.2 z.1.2)
    let d : (X × (κ → ℝ)) → (ι ⊕ κ) → ℝ := fun z => Sum.elim (c z.1) z.2
    let r : (ι ⊕ Option κ) → Option (ι ⊕ κ) :=
      Sum.elim (fun i => some (Sum.inl i)) (Option.map Sum.inr)
    have hp := hA.coordinate_preimage f r
      (d := fun z : (X × (κ → ℝ)) × ℝ => fun o => o.elim z.2 (d z.1)) (by
        intro z i
        cases i with
        | inl i => rfl
        | inr o => cases o <;> rfl)
    have ho := polynomialSignSet_projection_one hp
    have hh := ih c _ ho
    convert hh using 1
    ext x
    simp only [mem_ofPred_eq,mem_preimage]
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨fun k => y (some k),y none,?_⟩
      have he : (fun o : Option κ => o.elim (y none) (fun k => y (some k))) = y := by
        funext o
        cases o <;> rfl
      simpa only [f,he] using hy
    · rintro ⟨y,t,hy⟩
      exact ⟨_,hy⟩

end Release061.SignElimination

end

end OAI
