import Mathlib
import OAI.Analysis.SymmetricDomains.InterpolateRealUpper

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

noncomputable abbrev complexify (P : ℝ[X]) : ℂ[X] := P.map Complex.ofRealHom

lemma complexify_conj (P : ℝ[X]) : (complexify P).map (starRingEnd ℂ) = complexify P := by
  ext n
  simp only [coeff_map,Complex.ofRealHom_eq_coe,Complex.conj_ofReal]

lemma complexify_ne_zero {P : ℝ[X]} (hP : P ≠ 0) : complexify P ≠ 0 :=
  (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hP

lemma complexify_eval_conj (P : ℝ[X]) (z : ℂ) :
    (complexify P).eval (starRingEnd ℂ z) = starRingEnd ℂ ((complexify P).eval z) := by
  have hh := eval_map_apply (starRingEnd ℂ) z (p := complexify P)
  rwa [complexify_conj] at hh

lemma complexify_real_eval (P : ℝ[X]) (x : ℝ) :
    (complexify P).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) :=
  eval_map_apply Complex.ofRealHom x

lemma complex_root_conj {P : ℝ[X]} (hP : P ≠ 0) {z : ℂ}
    (hz : z ∈ (complexify P).roots.toFinset) :
    starRingEnd ℂ z ∈ (complexify P).roots.toFinset := by
  rw [Multiset.mem_toFinset,mem_roots (complexify_ne_zero hP),IsRoot] at *
  rw [complexify_eval_conj,hz,map_zero]

lemma count_complex_root_conj (P : ℝ[X]) (z : ℂ) :
    (complexify P).roots.count (starRingEnd ℂ z) = (complexify P).roots.count z := by
  simp only [count_roots]
  have h := eq_rootMultiplicity_map (starRingEnd ℂ).injective z (p := complexify P)
  rw [complexify_conj] at h
  exact h.symm

lemma count_complex_root_real (P : ℝ[X]) (x : ℝ) :
    (complexify P).roots.count (x : ℂ) = P.roots.count x := by
  simp only [count_roots]
  exact (eq_rootMultiplicity_map Complex.ofReal_injective x (p := P)).symm

noncomputable abbrev RealRoot (P : ℝ[X]) := {x : ℝ // x ∈ P.roots.toFinset}
noncomputable abbrev UpperRoot (P : ℝ[X]) :=
  {z : ℂ // z ∈ (complexify P).roots.toFinset.filter (fun z => 0 < z.im)}

lemma realRoot_mem_complex {P : ℝ[X]} (hP : P ≠ 0) (a : RealRoot P) :
    (a.val : ℂ) ∈ (complexify P).roots.toFinset := by
  rw [Multiset.mem_toFinset,mem_roots (complexify_ne_zero hP),IsRoot,complexify_real_eval]
  have h := a.property
  rw [Multiset.mem_toFinset,mem_roots hP,IsRoot] at h
  simp [h]

noncomputable def rootNodes {P : ℝ[X]} (hP : P ≠ 0) :
    RealRoot P ⊕ (UpperRoot P ⊕ UpperRoot P) →
      {z : ℂ // z ∈ (complexify P).roots.toFinset} :=
  fun i => ⟨realComplexNodes (fun a : RealRoot P => a.val) (fun b : UpperRoot P => b.val) i,by
    rcases i with a | (b | b)
    · exact realRoot_mem_complex hP a
    · exact (mem_filter.mp b.property).1
    · exact complex_root_conj hP (mem_filter.mp b.property).1⟩

lemma rootNodes_bijective {P : ℝ[X]} (hP : P ≠ 0) : Function.Bijective (rootNodes hP) := by
  constructor
  · intro i j h
    have hh := congrArg Subtype.val h
    exact realComplexNodes_injective Subtype.val_injective Subtype.val_injective
      (fun b => (mem_filter.mp b.property).2) hh
  · intro z
    by_cases hz0 : z.val.im = 0
    · have he : (z.val.re : ℂ) = z.val := by
        apply Complex.ext <;> simp [hz0]
      have hr : z.val.re ∈ P.roots.toFinset := by
        rw [Multiset.mem_toFinset,mem_roots hP,IsRoot]
        apply Complex.ofReal_injective
        have hh := z.property
        rw [Multiset.mem_toFinset,mem_roots (complexify_ne_zero hP),IsRoot] at hh
        change ((P.eval z.val.re : ℝ) : ℂ) = (0:ℂ)
        rw [← complexify_real_eval,he,hh]
      exact ⟨.inl ⟨z.val.re,hr⟩,Subtype.ext he⟩
    · rcases lt_or_gt_of_ne hz0 with hneg | hpos
      · have hc : starRingEnd ℂ z.val ∈
            (complexify P).roots.toFinset.filter (fun z => 0 < z.im) := by
          exact mem_filter.mpr ⟨complex_root_conj hP z.property,by simpa using neg_pos.mpr hneg⟩
        refine ⟨.inr (.inr ⟨starRingEnd ℂ z.val,hc⟩),Subtype.ext ?_⟩
        simp [rootNodes,realComplexNodes]
      · exact ⟨.inr (.inl ⟨z.val,mem_filter.mpr ⟨z.property,hpos⟩⟩),rfl⟩

noncomputable def rootNodesEquiv {P : ℝ[X]} (hP : P ≠ 0) :
    (RealRoot P ⊕ (UpperRoot P ⊕ UpperRoot P)) ≃
      {z : ℂ // z ∈ (complexify P).roots.toFinset} :=
  Equiv.ofBijective (rootNodes hP) (rootNodes_bijective hP)

lemma root_dimension_le {P : ℝ[X]} (hP : P ≠ 0) :
    Fintype.card (RealRoot P) + 2*Fintype.card (UpperRoot P) ≤ P.natDegree := by
  have hc := Fintype.card_congr (rootNodesEquiv hP)
  have hcard : Fintype.card (RealRoot P) + 2*Fintype.card (UpperRoot P) =
      (complexify P).roots.toFinset.card := by
    simpa only [Fintype.card_sum,Fintype.card_coe,two_mul] using hc
  rw [hcard]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots_map_le_natDegree P)

noncomputable def rootEvaluation (P : ℝ[X]) :
    (degreeLT ℝ P.natDegree) →ₗ[ℝ] ((RealRoot P → ℝ) × (UpperRoot P → ℂ)) where
  toFun A := (fun a => (aeval a.val) A.val,fun b => (aeval b.val) A.val)
  map_add' A B := by ext <;> simp
  map_smul' r A := by ext <;> simp

lemma rootEvaluation_surjective {P : ℝ[X]} (hP : P ≠ 0) :
    Function.Surjective (rootEvaluation P) := by
  rintro ⟨v,w⟩
  obtain ⟨A,hA,hreal,hupper⟩ := interpolate_real_and_upper
    (fun a : RealRoot P => a.val) (fun b : UpperRoot P => b.val)
    Subtype.val_injective Subtype.val_injective (fun b => (mem_filter.mp b.property).2) v w
  have hdeg : A ∈ degreeLT ℝ P.natDegree := mem_degreeLT.mpr
    (hA.trans_le (WithBot.coe_le_coe.mpr (root_dimension_le hP)))
  refine ⟨⟨A,hdeg⟩,?_⟩
  ext i
  · exact (aeval_def _ _).trans ((by simp : A.eval₂ (algebraMap ℝ ℝ) i.val = A.eval i.val).trans (hreal i))
  · exact hupper i

end Release061.SignElimination

end

end OAI
