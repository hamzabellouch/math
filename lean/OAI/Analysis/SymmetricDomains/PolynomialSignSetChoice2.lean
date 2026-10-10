import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetChoice

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
open Set
open scoped Classical

universe uX uI uK

theorem polynomialSignSet_choice_relation_finite {X : Type uX} {ι : Type uI} {κ : Type uK}
    [Finite κ] {c : X → ι → ℝ} {A : Set (X × (κ → ℝ))}
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) A) :
    ∃ B : Set (X × (κ → ℝ)),
      PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) B ∧
      B ⊆ A ∧ (∀ x y z, (x,y) ∈ B → (x,z) ∈ B → y = z) ∧
      ∀ x, (∃ y : κ → ℝ, (x,y) ∈ B) ↔ ∃ y : κ → ℝ, (x,y) ∈ A := by
  classical
  suffices hh : ∀ (κ : Type uK) [Finite κ], ∀ {X : Type uX} {ι : Type uI} (c : X → ι → ℝ)
      (A : Set (X × (κ → ℝ))),
      PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) A →
      ∃ B : Set (X × (κ → ℝ)),
        PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) B ∧
        B ⊆ A ∧ (∀ x y z, (x,y) ∈ B → (x,z) ∈ B → y = z) ∧
        ∀ x, (∃ y : κ → ℝ, (x,y) ∈ B) ↔ ∃ y : κ → ℝ, (x,y) ∈ A from hh κ c A hA
  intro κ _
  induction κ using Finite.induction_empty_option with
  | @of_equiv α β e ih =>
    intro X ι c A hA
    let f : (X × (α → ℝ)) → X × (β → ℝ) := fun z => (z.1,z.2 ∘ e.symm)
    let g : (X × (β → ℝ)) → X × (α → ℝ) := fun z => (z.1,z.2 ∘ e)
    have hf := hA.coordinate_preimage f (Sum.map id e.symm)
      (d := fun z => Sum.elim (c z.1) z.2) (by intro z i; cases i <;> rfl)
    obtain ⟨B,hB,hBA,huniq,hdom⟩ := ih c (f ⁻¹' A) hf
    have hg := hB.coordinate_preimage g (Sum.map id e)
      (d := fun z => Sum.elim (c z.1) z.2) (by intro z i; cases i <;> rfl)
    have hfg (z : X × (β → ℝ)) : f (g z) = z := by
      simp [f,g,Function.comp_def]
    have hgf (z : X × (α → ℝ)) : g (f z) = z := by
      simp [f,g,Function.comp_def]
    refine ⟨g ⁻¹' B,hg,fun z hz => ?_,?_,fun x => ?_⟩
    · simpa only [mem_preimage,hfg] using hBA hz
    · intro x y z hy hz
      have hh := huniq x (y ∘ e) (z ∘ e) hy hz
      funext j
      simpa only [Function.comp_apply,e.apply_symm_apply] using congrFun hh (e.symm j)
    · constructor
      · rintro ⟨y,hy⟩
        exact ⟨y,by simpa only [mem_preimage,hfg] using hBA hy⟩
      · rintro ⟨y,hy⟩
        have hx : ∃ u : α → ℝ, (x,u) ∈ f ⁻¹' A :=
          ⟨y ∘ e,by change f (g (x,y)) ∈ A; rwa [hfg]⟩
        obtain ⟨u,hu⟩ := (hdom x).mpr hx
        refine ⟨u ∘ e.symm,?_⟩
        change g (f (x,u)) ∈ B
        rwa [hgf]
  | h_empty =>
    intro X ι c A hA
    exact ⟨A,hA,Subset.rfl,fun _ _ _ _ _ => Subsingleton.elim _ _,fun _ => Iff.rfl⟩
  | @h_option κ _ ih =>
    intro X ι c A hA
    let f : ((X × (κ → ℝ)) × ℝ) → X × (Option κ → ℝ) :=
      fun z => (z.1.1,fun o => Option.elim o z.2 z.1.2)
    let g : (X × (Option κ → ℝ)) → (X × (κ → ℝ)) × ℝ :=
      fun z => ((z.1,z.2 ∘ some),z.2 none)
    let d := fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2
    have hfg (z : X × (Option κ → ℝ)) : f (g z) = z := by
      apply Prod.ext
      · rfl
      · funext o
        cases o <;> rfl
    have hgf (z : (X × (κ → ℝ)) × ℝ) : g (f z) = z := rfl
    have ha := hA.coordinate_preimage f
      (Sum.elim (fun i => some (Sum.inl i)) (Option.map Sum.inr))
      (d := fun z : (X × (κ → ℝ)) × ℝ => fun o => Option.elim o z.2 (d z.1)) (by
        intro z i
        cases i with
        | inl i => rfl
        | inr o => cases o <;> rfl)
    obtain ⟨B,hB,hBA,huniqB,hdomB⟩ := polynomialSignSet_choice_relation_one ha
    let C : Set (X × (κ → ℝ)) := {z | ∃ t : ℝ, (z,t) ∈ B}
    have hC : PolynomialSignSet d C := polynomialSignSet_projection_one hB
    obtain ⟨E,hE,hEC,huniqE,hdomE⟩ := ih c C hC
    let p : X × (Option κ → ℝ) → X × (κ → ℝ) := fun z => (z.1,z.2 ∘ some)
    have hbg := hB.coordinate_preimage g
      (fun o => Option.elim o (Sum.inr none) (Sum.elim Sum.inl (fun k => Sum.inr (some k))))
      (d := fun z : X × (Option κ → ℝ) => Sum.elim (c z.1) z.2) (by
        intro z o
        cases o with
        | none => rfl
        | some i => cases i <;> rfl)
    have hep := hE.coordinate_preimage p (Sum.map id some)
      (d := fun z : X × (Option κ → ℝ) => Sum.elim (c z.1) z.2)
      (by intro z i; cases i <;> rfl)
    let D := (g ⁻¹' B) ∩ (p ⁻¹' E)
    have hDA : D ⊆ A := by
      intro z hz
      simpa only [mem_preimage,hfg] using hBA hz.1
    refine ⟨D,hbg.inter hep,hDA,?_,fun x => ?_⟩
    · intro x y z hy hz
      have he := huniqE x (y ∘ some) (z ∘ some) hy.2 hz.2
      have ht : y none = z none := by
        apply huniqB (x,y ∘ some) (y none) (z none) hy.1
        rw [he]
        exact hz.1
      funext o
      cases o with
      | none => exact ht
      | some i => exact congrFun he i
    · constructor
      · rintro ⟨y,hy⟩
        exact ⟨y,hDA hy⟩
      · rintro ⟨y,hy⟩
        have hxC : (x,y ∘ some) ∈ C := by
          apply (hdomB (x,y ∘ some)).mpr
          refine ⟨y none,?_⟩
          change f (g (x,y)) ∈ A
          rwa [hfg]
        obtain ⟨u,hu⟩ := (hdomE x).mpr ⟨y ∘ some,hxC⟩
        obtain ⟨t,ht⟩ := hEC hu
        refine ⟨fun o => Option.elim o t u,ht,hu⟩

theorem polynomialSignSet_choice_finite {X : Type uX} {ι : Type uI} {κ : Type uK}
    [Finite κ] {c : X → ι → ℝ} {A : Set (X × (κ → ℝ))}
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2) A) :
    ∃ f : X → κ → ℝ,
      (∀ x, (∃ y : κ → ℝ, (x,y) ∈ A) → (x,f x) ∈ A) ∧
      PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
        {z | (∃ y : κ → ℝ, (z.1,y) ∈ A) ∧ z.2 = f z.1} := by
  classical
  obtain ⟨B,hB,hBA,huniq,hdom⟩ := polynomialSignSet_choice_relation_finite hA
  let f := fun x => if hx : ∃ y : κ → ℝ, (x,y) ∈ A then ((hdom x).mpr hx).choose else 0
  have hf (x : X) (hx : ∃ y : κ → ℝ, (x,y) ∈ A) : (x,f x) ∈ B := by
    simpa only [f,dite_eq_left hx] using ((hdom x).mpr hx).choose_spec
  refine ⟨f,fun x hx => hBA (hf x hx),?_⟩
  convert hB using 1
  ext z
  constructor
  · rintro ⟨hx,he⟩
    simpa only [← he] using hf z.1 hx
  · intro hz
    have hx := (hdom z.1).mp ⟨z.2,hz⟩
    exact ⟨hx,huniq z.1 z.2 (f z.1) hz (hf z.1 hx)⟩

end Release061.SignElimination

end

end OAI
