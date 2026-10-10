import Mathlib
import OAI.Analysis.HardSphere.Conditioning.SharedRoute

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open HardSphere.Bridge
attribute [local instance] Classical.propDecidable
variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  {X Y : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)]

def routeConfigMap (f : ∀i,X i→Y i) (x : ∀i,X i) : ∀i,Y i := fun i ↦ f i (x i)
def routeFactorMap (f : ∀i,X i→Y i) (s : Finset I) (σ : Equiv.Perm I)
    (p : ∀i:s,X i×X (σ.symm i)) : ∀i:s,Y i×Y (σ.symm i) :=
  fun i ↦ (f i (p i).1,f (σ.symm i) (p i).2)
def routePairedMap (f : ∀i,X i→Y i) (s : Finset I) (σ : Equiv.Perm I)
    (p : (∀i,X i)×(∀i:s,X i×X (σ.symm i))) :=
  (routeConfigMap f p.1,routeFactorMap f s σ p.2)

omit [Fintype I] [DecidableEq I] in
lemma routeConfigMap_measurable (f : ∀i,X i→Y i) (hf : ∀i,Measurable (f i)) :
    Measurable (routeConfigMap f) :=
  Measurable.of_eval fun i ↦ (hf i).comp (measurable_pi_apply i)
omit [Fintype I] [DecidableEq I] in
lemma routeFactorMap_measurable (f : ∀i,X i→Y i) (hf : ∀i,Measurable (f i))
    (s : Finset I) (σ : Equiv.Perm I) : Measurable (routeFactorMap f s σ) :=
  Measurable.of_eval fun i ↦ ((hf i).comp (measurable_fst.comp (measurable_pi_apply i))).prodMk
    ((hf _).comp (measurable_snd.comp (measurable_pi_apply i)))
omit [Fintype I] [DecidableEq I] in
lemma routePairedMap_measurable (f : ∀i,X i→Y i) (hf : ∀i,Measurable (f i))
    (s : Finset I) (σ : Equiv.Perm I) : Measurable (routePairedMap f s σ) :=
  ((routeConfigMap_measurable f hf).comp measurable_fst).prodMk
    ((routeFactorMap_measurable f hf s σ).comp measurable_snd)

omit [Fintype I] [DecidableEq I] in
lemma fiberEquiv_natural (f : ∀i,X i→Y i) {i j : I} (h : i=j) (x : X i) :
    fiberEquiv h (f i x)=f j (fiberEquiv h x) := by cases h; rfl

omit [Fintype I] [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)] in
lemma ambientFirst_natural (f : ∀i,X i→Y i) (s : Finset I) (σ : Equiv.Perm I)
    (p : (∀i,X i)×(∀i:s,X i×X (σ.symm i))) :
    ambientFirst s σ (routePairedMap f s σ p)=routeConfigMap f (ambientFirst s σ p) := by
  funext i
  by_cases hi : i∈s
  · simp only [ambientFirst,routePairedMap,routeConfigMap,routeFactorMap,Function.updateFinset,dite_eq_left hi]
  · simp only [ambientFirst,routePairedMap,routeConfigMap,routeFactorMap,Function.updateFinset,dite_eq_right hi]

omit [Fintype I] in
lemma ambientSecond_natural (f : ∀i,X i→Y i) (s : Finset I) (σ : Equiv.Perm I)
    (hσ : ∀i,i∉s→σ i=i) (p : (∀i,X i)×(∀i:s,X i×X (σ.symm i))) :
    ambientSecond s σ hσ (routePairedMap f s σ p)=
      routeConfigMap f (ambientSecond s σ hσ p) := by
  funext i
  by_cases hi : i∈s
  · simp only [ambientSecond,routePairedMap,routeConfigMap,Function.updateFinset,dite_eq_left hi,
      reverseSelected_apply,routeFactorMap]
    exact fiberEquiv_natural f _ _
  · simp only [ambientSecond,routePairedMap,routeConfigMap,Function.updateFinset,dite_eq_right hi]

omit [Fintype I] in
lemma ambientSharedKernel_apply_measure (s : Finset I) (σ : Equiv.Perm I)
    (hσ : ∀i,i∉s→σ i=i) (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) (e : E) :
    ambientSharedKernel s σ hσ ξ ρ A e=(ξ e).compProd
      ((ambientRefreshKernel s σ hσ ρ A).comap (Prod.mk e) measurable_prodMk_left) := by
  ext C hC
  rw [ambientSharedKernel,Kernel.compProd_apply hC,Measure.compProd_apply hC]
  rfl

omit [Fintype I] in
lemma ambientRefresh_map (f : ∀i,X i→Y i) (hf : ∀i,Measurable (f i))
    (s : Finset I) (σ : Equiv.Perm I) (hσ : ∀i,i∉s→σ i=i)
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,Y i))) (hA : MeasurableSet A) (e : E) (x : ∀i,X i) :
    (ambientRefreshKernel s σ hσ ρ
      ((fun p : E×(∀i,X i) ↦ (p.1,routeConfigMap f p.2)) ⁻¹' A) (e,x)).map
        (routeFactorMap f s σ)=
    ambientRefreshKernel s σ hσ (fun i ↦ (ρ i).map (Prod.map (f i) (f (σ.symm i))))
      A (e,routeConfigMap f x) := by
  have hP : Measurable (fun p : E×(∀i,X i) ↦ (p.1,routeConfigMap f p.2)) :=
    measurable_fst.prodMk ((routeConfigMap_measurable f hf).comp measurable_snd)
  have hB : MeasurableSet {p : ∀i:s,Y i×Y (σ.symm i) |
      (e,ambientFirst s σ (routeConfigMap f x,p))∈A ∧
      (e,ambientSecond s σ hσ (routeConfigMap f x,p))∈A} :=
    (ambientRefreshEvent_measurable s σ hσ A hA).preimage
      (measurable_prodMk_left (x:=(e,routeConfigMap f x)))
  rw [ambientRefreshKernel_apply _ _ _ _ _ (hA.preimage hP),
    ambientRefreshKernel_apply _ _ _ _ _ hA]
  have he : {p : ∀i:s,X i×X (σ.symm i) |
      (e,ambientFirst s σ (x,p))∈((fun q : E×(∀i,X i) ↦ (q.1,routeConfigMap f q.2)) ⁻¹' A) ∧
      (e,ambientSecond s σ hσ (x,p))∈((fun q : E×(∀i,X i) ↦ (q.1,routeConfigMap f q.2)) ⁻¹' A)} =
      (routeFactorMap f s σ) ⁻¹' {p | (e,ambientFirst s σ (routeConfigMap f x,p))∈A ∧
        (e,ambientSecond s σ hσ (routeConfigMap f x,p))∈A} := by
    ext p
    simp only [mem_ofPred_eq,mem_preimage]
    change _ ↔ (e,ambientFirst s σ (routePairedMap f s σ (x,p)))∈A ∧
      (e,ambientSecond s σ hσ (routePairedMap f s σ (x,p)))∈A
    rw [ambientFirst_natural,ambientSecond_natural]
  rw [he,conditioned_map_preimage _ _ (routeFactorMap_measurable f hf s σ) hB]
  congr 1
  have hmap := Measure.pi_map_pi (μ:=fun i:s ↦ ρ i e)
    (fun i:s ↦ ((hf i).prodMap (hf (σ.symm i))).aemeasurable)
  simp only [Kernel.map_apply _ ((hf _).prodMap (hf _))]
  exact hmap

end HardSphere.Comparison
end
end

end OAI
