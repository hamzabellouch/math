import Mathlib
import OAI.Analysis.HardSphere.Bridges.ReversePair

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

omit [Fintype I] [DecidableEq I] in
lemma fiberEquiv_map (μ : ∀i,Measure (X i)) {i j : I} (h : i=j) :
    (μ i).map (fiberEquiv h)=μ j := by
  subst j
  exact Measure.map_id

omit [Fintype I] [DecidableEq I] in
lemma reverseFactor_fst (σ : Equiv.Perm I) (j : I)
    (ρ : Measure (X (σ j)×X (σ.symm (σ j)))) :
    (ρ.map (reverseFactor σ j)).fst=ρ.snd.map (fiberEquiv (σ.symm_apply_apply j)) := by
  rw [Measure.fst,Measure.snd,Measure.map_map measurable_fst (reverseFactor σ j).measurable,
    Measure.map_map (fiberEquiv (σ.symm_apply_apply j)).measurable measurable_snd]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma exists_two_auxiliary (σ : Equiv.Perm I)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    [∀i,StandardBorelSpace (X i)]
    (ρ : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsProbabilityMeasure (ρ i)]
    {G : ℝ≥0∞} (hG : G≠⊤)
    (hfst : ∀i,(ρ i).fst≤G • μ i) (hsnd : ∀i,(ρ i).snd≤G • ν (σ.symm i)) :
    ∃ (κ : ∀i,Kernel (X i) (X (σ.symm i))) (η : ∀i,Kernel (X i) (X (σ i))),
      (∀i,IsFiniteKernel (κ i)) ∧ (∀i,IsFiniteKernel (η i)) ∧
      (∀i,(μ i).compProd (κ i)=ρ i) ∧
      (∀i,(ν i).compProd (η i)=(ρ (σ i)).map (reverseFactor σ i)) ∧
      (∀i x,κ i x univ≤G) ∧ (∀i x,η i x univ≤G) ∧
      (∀i,∫⁻x,κ i x univ ∂μ i=1) ∧ (∀i,∫⁻x,η i x univ ∂ν i=1) := by
  let : ∀i,Nonempty (X i) := fun i ↦ nonempty_of_isProbabilityMeasure (μ i)
  have hκ := fun i ↦ exists_bounded_auxiliary_kernel (μ i) (ρ i) hG (hfst i)
  choose κ hκf hκe hκb hκm using hκ
  have hη : ∀i,∃ η : Kernel (X i) (X (σ i)),IsFiniteKernel η ∧
      (ν i).compProd η=(ρ (σ i)).map (reverseFactor σ i) ∧
      (∀x,η x univ≤G) ∧ (∫⁻x,η x univ ∂ν i)=1 := by
    intro i
    have : IsProbabilityMeasure ((ρ (σ i)).map (reverseFactor σ i)) :=
      (Measure.isProbabilityMeasure_map_iff
        (reverseFactor σ i).measurable.aemeasurable).mpr inferInstance
    apply exists_bounded_auxiliary_kernel _ _ hG
    rw [reverseFactor_fst]
    have hh := Measure.map_mono (hsnd (σ i)) (fiberEquiv (σ.symm_apply_apply i)).measurable
    rwa [Measure.map_smul G (fiberEquiv (σ.symm_apply_apply i)).measurable.aemeasurable,
      fiberEquiv_map] at hh
  choose η hηf hηe hηb hηm using hη
  exact ⟨κ,η,hκf,hηf,hκe,hηe,hκb,hηb,hκm,hηm⟩

def extendSelectedPair (σ : Equiv.Perm I) (s : Finset I)
    (μ ν : ∀i,Measure (X i)) (ρ : ∀i:s,Measure (X i×X (σ.symm i)))
    (i : I) : Measure (X i×X (σ.symm i)) :=
  if hi : i∈s then ρ ⟨i,hi⟩ else (μ i).prod (ν (σ.symm i))

omit [Fintype I] in
lemma extendSelectedPair_selected (σ : Equiv.Perm I) (s : Finset I)
    (μ ν : ∀i,Measure (X i)) (ρ : ∀i:s,Measure (X i×X (σ.symm i))) (i : s) :
    extendSelectedPair σ s μ ν ρ i=ρ i := by simp [extendSelectedPair,i.property]

omit [Fintype I] in
instance extendSelectedPair_probability (σ : Equiv.Perm I) (s : Finset I)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (ρ : ∀i:s,Measure (X i×X (σ.symm i))) [∀i,IsProbabilityMeasure (ρ i)] (i : I) :
    IsProbabilityMeasure (extendSelectedPair σ s μ ν ρ i) := by
  unfold extendSelectedPair
  split <;> infer_instance

omit [Fintype I] in
lemma extendSelectedPair_bounds (σ : Equiv.Perm I) (s : Finset I)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (ρ : ∀i:s,Measure (X i×X (σ.symm i))) {G : ℝ≥0∞} (hG : 1≤G)
    (hfst : ∀i,(ρ i).fst≤G • μ i) (hsnd : ∀i,(ρ i).snd≤G • ν (σ.symm i)) (i : I) :
    (extendSelectedPair σ s μ ν ρ i).fst≤G • μ i ∧
    (extendSelectedPair σ s μ ν ρ i).snd≤G • ν (σ.symm i) := by
  unfold extendSelectedPair
  split
  · exact ⟨hfst _,hsnd _⟩
  · rw [Measure.fst_prod,Measure.snd_prod]
    constructor <;> intro A
    · simpa only [Measure.smul_apply,smul_eq_mul,one_mul] using (mul_le_mul' hG (le_refl (μ i A)))
    · simpa only [Measure.smul_apply,smul_eq_mul,one_mul] using (mul_le_mul' hG (le_refl (ν (σ.symm i) A)))

end HardSphere.Bridge
end
end

end OAI
