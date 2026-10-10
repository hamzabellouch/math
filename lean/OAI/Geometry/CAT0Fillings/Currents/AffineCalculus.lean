import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Basic
import OAI.Geometry.CAT0Fillings.Currents.MultilinearPair

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
noncomputable def boundedLipSubmodule : Submodule ℝ (X → ℝ) where
  carrier := {b | BoundedLip b}
  zero_mem' := BoundedLip.const 0
  add_mem' := fun hb hc => hb.add hc
  smul_mem' := fun a _ hb => hb.const_mul a

local notation "BL" => boundedLipSubmodule (X := X)

omit [MeasurableSpace X] [BorelSpace X] in
lemma bl_coe_update {k : ℕ} (v : Fin k → BL) (i : Fin k) (f : BL) :
    (fun j => ((Function.update v i f) j : X → ℝ)) =
      Function.update (fun j => (v j : X → ℝ)) i (f : X → ℝ) := by
  funext j
  by_cases h : j=i <;> simp [h]

omit [MeasurableSpace X] [BorelSpace X] in
lemma bl_update_tail_zero {k : ℕ} (v : Fin (k+1) → BL) (f : BL) :
    (fun j : Fin k => ((Function.update v 0 f) j.succ : X → ℝ)) =
      fun j => (v j.succ : X → ℝ) := by
  funext j
  simp

omit [MeasurableSpace X] [BorelSpace X] in
lemma bl_update_tail_succ {k : ℕ} (v : Fin (k+1) → BL) (i : Fin k) (f : BL) :
    (fun j : Fin k => ((Function.update v i.succ f) j.succ : X → ℝ)) =
      Function.update (fun j => (v j.succ : X → ℝ)) i (f : X → ℝ) := by
  funext j
  by_cases h : j=i <;> simp [h]

noncomputable def IsMetricCurrent.fullMultilinear {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) : MultilinearMap ℝ (fun _ : Fin (k+1) => BL) ℝ :=
  MultilinearMap.mk' (fun v => T (v 0) (fun j => v j.succ)) (by
    intro v i f g
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Function.update_self,bl_update_tail_zero,Submodule.coe_add,Pi.add_def,
        one_mul] using hT.linearFirst f g (fun j => v j.succ) 1 1 f.property g.property
          (fun j => (v j.succ).property.1)
    · have h := hT.linearCoord (v 0 : X → ℝ)
        (Function.update (fun j => (v j.succ : X → ℝ)) j (f : X → ℝ)) j
        (g : X → ℝ) 1 1
        ⟨(v 0).property,fun l => by
          by_cases hl : l=j
          · simpa [hl] using f.property.1
          · simpa [hl] using (v l.succ).property.1⟩ g.property.1
      simpa only [Function.update_of_ne (Fin.succ_ne_zero j).symm,bl_update_tail_succ,
        Function.update_self,Submodule.coe_add,Pi.add_def,one_mul,Function.update_idem] using h)
    (by
      intro v i a f
      refine Fin.cases ?_ (fun j => ?_) i
      · have h := hT.linearFirst f f (fun j => v j.succ) a 0 f.property f.property
          (fun j => (v j.succ).property.1)
        simpa only [Function.update_self,bl_update_tail_zero,Submodule.coe_smul,Pi.smul_def,
          smul_eq_mul,zero_mul,add_zero] using h
      · have h := hT.linearCoord (v 0 : X → ℝ)
          (Function.update (fun j => (v j.succ : X → ℝ)) j (f : X → ℝ)) j
          (f : X → ℝ) a 0
          ⟨(v 0).property,fun l => by
            by_cases hl : l=j
            · simpa [hl] using f.property.1
            · simpa [hl] using (v l.succ).property.1⟩ f.property.1
        simpa only [Function.update_of_ne (Fin.succ_ne_zero j).symm,bl_update_tail_succ,
          Function.update_self,Submodule.coe_smul,Pi.smul_def,smul_eq_mul,
          zero_mul,add_zero,Function.update_idem] using h)

noncomputable def pairLinearCombination (f g : BL) : (ℝ × ℝ) →ₗ[ℝ] BL where
  toFun p := p.1 • f + p.2 • g
  map_add' p q := by simp only [Prod.fst_add,Prod.snd_add,add_smul]; module
  map_smul' a p := by simp only [Prod.smul_fst,Prod.smul_snd,smul_add,smul_smul,
    RingHom.id_apply]; rfl

noncomputable def IsMetricCurrent.affineCoefficients {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (f g : Fin (k+1) → BL) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k+1) => ℝ × ℝ) ℝ :=
  multilinearPairContinuous (hT.fullMultilinear.compLinearMap
    (fun i => pairLinearCombination (f i) (g i)))

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "BL" => boundedLipSubmodule (X := X)

lemma pairMultilinear_hasDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ContinuousMultilinearMap ℝ (fun _ : ι => ℝ × ℝ) ℝ) (t : ℝ) :
    HasDerivAt (fun s => M (fun _ => (1,s)))
      (∑ i, M (Function.update (fun _ => (1,t)) i (0,1))) t := by
  have h := (HasFDerivAt.multilinear_comp M (fun _ : ι =>
    ((hasDerivAt_const t (1:ℝ)).prodMk (hasDerivAt_id t)).hasFDerivAt)).hasDerivAt
  simpa using h

omit [BorelSpace X] in
lemma IsMetricCurrent.affineCoefficients_apply {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (f g : Fin (k+1) → BL) (p : Fin (k+1) → ℝ × ℝ) :
    hT.affineCoefficients f g p =
      hT.fullMultilinear (fun i => (p i).1 • f i + (p i).2 • g i) := rfl

omit [BorelSpace X] in

lemma IsMetricCurrent.hasDeriv_fullAffine {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (f g : Fin (k+1) → BL) (t : ℝ) :
    HasDerivAt (fun s => hT.fullMultilinear (fun i => f i + s • g i))
      (∑ i, hT.fullMultilinear (Function.update (fun j => f j + t • g j) i (g i))) t := by
  have h := pairMultilinear_hasDeriv (hT.affineCoefficients f g) t
  simp only [hT.affineCoefficients_apply,one_smul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases hj : j=i <;> simp [hj]

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)

end CAT0Fillings
end
end

end OAI
