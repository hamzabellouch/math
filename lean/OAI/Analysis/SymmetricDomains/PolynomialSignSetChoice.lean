import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialSignSetFinite2

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

theorem polynomialSignSet_choice_relation_one {X ι : Type*} {c : X → ι → ℝ}
    {A : Set (X × ℝ)}
    (hA : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) A) :
    ∃ C : Set (X × ℝ),
      PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) C ∧
      C ⊆ A ∧ (∀ x y z, (x,y) ∈ C → (x,z) ∈ C → y = z) ∧
      ∀ x, (∃ y : ℝ, (x,y) ∈ C) ↔ ∃ y : ℝ, (x,y) ∈ A := by
  classical
  obtain ⟨B,hB,hBA,hfin,hdom⟩ := polynomialSignSet_finite_subrelation hA
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let C : Set (X × ℝ) := {z | z ∈ B ∧ ∀ t, (z.1,t) ∈ B → z.2 ≤ t}
  have hlt : PolynomialSignSet (fun z : (X × ℝ) × ℝ =>
      fun o => Option.elim o z.2 (d z.1))
      {z | (z.1.1,z.2) ∈ B ∧ z.2 < z.1.2} := by
    have hb := hB.coordinate_preimage (fun z : (X × ℝ) × ℝ => (z.1.1,z.2))
      (fun o => Option.elim o none (fun i => some (some i)))
      (d := fun z : (X × ℝ) × ℝ => fun o => Option.elim o z.2 (d z.1))
      (by intro z i; cases i <;> rfl)
    have hh : PolynomialSignSet (fun z : (X × ℝ) × ℝ =>
        fun o => Option.elim o z.2 (d z.1)) {z | z.2 < z.1.2} := by
      convert PolynomialSignSet.positive (c := fun z : (X × ℝ) × ℝ =>
          fun o => Option.elim o z.2 (d z.1))
          (MvPolynomial.X (some none) - MvPolynomial.X none) using 1
      ext z
      simp [d]
    exact hb.inter hh
  have hC : PolynomialSignSet d C := by
    have hh := hB.inter (polynomialSignSet_projection_one hlt).compl
    convert hh using 1
    ext z
    simp only [C,mem_ofPred_eq,mem_inter_iff,mem_compl_iff,not_exists,not_and,not_lt]
  have huniq : ∀ x y z, (x,y) ∈ C → (x,z) ∈ C → y = z := by
    intro x y z hy hz
    exact le_antisymm (hy.2 z hz.1) (hz.2 y hy.1)
  refine ⟨C,hC,fun z hz => hBA hz.1,huniq,fun x => ?_⟩
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y,hBA hy.1⟩
  · intro hx
    obtain ⟨y,hy⟩ := (hdom x).mpr hx
    let s := (hfin x).toFinset
    have hs : s.Nonempty := ⟨y,by simpa only [s,Set.Finite.mem_toFinset,mem_ofPred_eq] using hy⟩
    refine ⟨s.min' hs,?_,?_⟩
    · exact (hfin x).mem_toFinset.mp (s.min'_mem hs)
    · intro t ht
      exact s.min'_le t ((hfin x).mem_toFinset.mpr ht)

theorem polynomialSignSet_choice_one {X ι : Type*} {c : X → ι → ℝ}
    {A : Set (X × ℝ)}
    (hA : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)) A) :
    ∃ f : X → ℝ,
      (∀ x, (∃ y : ℝ, (x,y) ∈ A) → (x,f x) ∈ A) ∧
      PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
        {z | (∃ y : ℝ, (z.1,y) ∈ A) ∧ z.2 = f z.1} := by
  classical
  obtain ⟨C,hC,hCA,huniq,hdom⟩ := polynomialSignSet_choice_relation_one hA
  let f := fun x => if hx : ∃ y : ℝ, (x,y) ∈ A then ((hdom x).mpr hx).choose else 0
  have hf (x : X) (hx : ∃ y : ℝ, (x,y) ∈ A) : (x,f x) ∈ C := by
    simpa only [f,dite_eq_left hx] using ((hdom x).mpr hx).choose_spec
  refine ⟨f,fun x hx => hCA (hf x hx),?_⟩
  convert hC using 1
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
