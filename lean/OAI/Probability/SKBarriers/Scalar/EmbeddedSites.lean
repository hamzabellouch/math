import Mathlib
import OAI.Probability.SKBarriers.Scalar.VectorHierarchy

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {A : Type} [Fintype A] [Nonempty A]

def siteValueTerminal (c : A → ℝ) : (A → ℝ) → ℝ :=
  affineLogPartition c (fun a => ContinuousLinearMap.proj a)

def embeddedSiteExponent {n r : ℕ} (e : Fin r → Fin n) (V : Fin r → A → ℝ)
    (a : A) : ParameterSpace n →L[ℝ] ℝ := ∑ j, V j a • coordinateProjection n (e j)

def embeddedVector {n r : ℕ} (e : Fin r → Fin n) (V : Fin r → A → ℝ)
    (t : Fin n) : A → ℝ := ∑ j, if e j=t then V j else 0

omit [Fintype A] [Nonempty A] in
theorem embeddedVector_at {n r : ℕ} (e : Fin r → Fin n) (he : Function.Injective e)
    (V : Fin r → A → ℝ) (j : Fin r) : embeddedVector e V (e j)=V j := by
  classical
  simp only [embeddedVector,he.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

omit [Fintype A] [Nonempty A] in
theorem embeddedVector_off {n r : ℕ} (e : Fin r → Fin n) (V : Fin r → A → ℝ)
    (t : Fin n) (ht : ∀ j, e j≠t) : embeddedVector e V t=0 := by
  simp only [embeddedVector,ht,ite_false,Finset.sum_const_zero]

omit [Nonempty A] in
theorem embeddedSite_terminal {n r : ℕ} (e : Fin r → Fin n) (V : Fin r → A → ℝ)
    (c : A → ℝ) :
    affineLogPartition c (embeddedSiteExponent e V)=fun z =>
      siteValueTerminal c (0+∑ t, coordinateProjection n t z • embeddedVector e V t) := by
  classical
  funext z
  simp only [affineLogPartition,embeddedSiteExponent,siteValueTerminal,sum_apply,smul_apply,
    smul_eq_mul,zero_add,ContinuousLinearMap.proj_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,embeddedVector,Finset.mul_sum,
    Finset.sum_apply,ite_apply,Pi.zero_apply,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Nonempty A] in

theorem embeddedSite_pressure {n r : ℕ} (e : Fin r → Fin n) (he : StrictMono e)
    (m : Fin n → ℝ) (V : Fin r → A → ℝ) (c : A → ℝ) (x : ℝ) :
    hierarchyPressure n m (affineLogPartition c (embeddedSiteExponent e V)) x=
      vectorHierarchy r (m ∘ e) V (siteValueTerminal c) 0 := by
  rw [embeddedSite_terminal,hierarchyPressure_vector_linear n m (embeddedVector e V) (siteValueTerminal c) (fun _ => 0)]
  rw [vectorHierarchy_compress n e he m (embeddedVector e V)
    (embeddedVector_off e V) (siteValueTerminal c)]
  have hV : embeddedVector e V ∘ e=V := by
    funext j
    exact embeddedVector_at e he.injective V j
  rw [hV]

omit [Nonempty A] in
theorem embeddedSite_invariant {n r : ℕ} (e : Fin r → Fin n) (V : Fin r → A → ℝ)
    (c : A → ℝ) (t : Fin n) (ht : ∀ j, e j≠t) :
    TranslationInvariant (affineLogPartition c (embeddedSiteExponent e V)) (coordinateAxis n t) := by
  apply affineLogPartition_translation
  intro a
  simp only [embeddedSiteExponent,sum_apply,smul_apply,smul_eq_mul,
    coordinateProjection_coordinateAxis,ht,ite_false,mul_zero,Finset.sum_const_zero]

theorem embeddedSites_tensorizes {I : Type} [Fintype I] [DecidableEq I]
    {n r : ℕ} (e : I → Fin r → Fin n) (he : ∀ i, StrictMono (e i))
    (owner : Fin n → I) (howner : ∀ i j, owner (e i j)=i)
    (m : Fin n → ℝ) (μ : Fin r → ℝ) (hm : ∀ i j, m (e i j)=μ j)
    (V : Fin r → A → ℝ) (c : A → ℝ) (x : ℝ) :
    hierarchyPressure n m
      (affineLogPartition (fun s : I → A => ∑ i, c (s i))
        (fun s => ∑ i, embeddedSiteExponent (e i) V (s i))) x=
      (Fintype.card I:ℝ)*vectorHierarchy r μ V (siteValueTerminal c) 0 := by
  have hterm : affineLogPartition (fun s : I → A => ∑ i, c (s i))
      (fun s => ∑ i, embeddedSiteExponent (e i) V (s i))=
      fun z => ∑ i, affineLogPartition c (embeddedSiteExponent (e i) V) z := by
    funext z
    simp only [affineLogPartition,sum_apply,← Finset.sum_add_distrib,Real.exp_sum]
    rw [← Fintype.prod_sum (fun i a => Real.exp (c a+embeddedSiteExponent (e i) V a z)),Real.log_prod]
    intro i _
    exact (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  rw [hterm,hierarchyPressure_sum_independent n m owner _
    (fun i => affineLogPartition_boundedDerivs c (embeddedSiteExponent (e i) V))
    (fun t i hi => embeddedSite_invariant (e i) V c t (fun j ht => by
      apply hi
      rw [← ht,howner]))]
  simp_rw [embeddedSite_pressure _ (he _) m V c x]
  have heq (i : I) : m ∘ e i=μ := funext (hm i)
  simp only [heq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
end

end SK.Analytic

end
end

end OAI
