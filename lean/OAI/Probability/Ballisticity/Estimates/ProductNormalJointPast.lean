import Mathlib
import OAI.Probability.Ballisticity.Estimates.CharacteristicProductLaw

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def pathPastCoordinates {q : ℕ} (v : Fin q → unitInterval) :
    C(C(unitInterval,ℝ),Fin q → ℝ) := ⟨fun P z => P (v z),by fun_prop⟩

noncomputable def pathIncrement (s t : unitInterval) : C(C(unitInterval,ℝ),ℝ) :=
  ⟨fun P => P t-P s,by fun_prop⟩

def NormalSinglePast (μ : Measure C(unitInterval,ℝ)) (c : ℝ≥0) : Prop :=
  ∀ (q : ℕ) (v : Fin q → unitInterval) (s t : unitInterval),
    (∀ z, v z ≤ s) → s < t → (t:ℝ) < 1 →
    μ.map (fun P => (pathPastCoordinates v P,pathIncrement s t P)) =
      (μ.map (pathPastCoordinates v)).prod (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)))

lemma normalJointPast_single (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (b : Bool) : NormalSinglePast (μ.map (fun P => if b then P.2 else P.1)) c := by
  intro q v s t hv hst ht
  let g := fun z : Fin q → ℝ × ℝ => fun j => if b then (z j).2 else (z j).1
  have hg : Measurable g := by cases b <;> simp [g] <;> fun_prop
  have hh := congrArg (fun M => M.map (Prod.map g id)) (h q v s t hv hst ht b)
  rw [Measure.map_map (hg.prodMap measurable_id) (by fun_prop),
    ← Measure.map_prod_map _ _ hg measurable_id,Measure.map_id,
    Measure.map_map hg (by fun_prop)] at hh
  rw [Measure.map_map (by fun_prop) (by cases b <;> simp <;> fun_prop),
    Measure.map_map (by fun_prop) (by cases b <;> simp <;> fun_prop)]
  cases b <;> exact hh

lemma normalSinglePast_prod (μ ν : Measure C(unitInterval,ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ≥0)
    (hμ : NormalSinglePast μ c) (hν : NormalSinglePast ν c) : FullNormalJointPast (μ.prod ν) c := by
  intro q v s t hv hst ht
  let Z := fun P : C(unitInterval,ℝ) => (pathPastCoordinates v P,pathIncrement s t P)
  have hZ : Measurable Z := by fun_prop
  let γ := gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))
  let Q := fun z : ((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ) => ((z.1.1,z.2.1),(z.1.2,z.2.2))
  have hQ : Measurable Q := by fun_prop
  let zip := fun z : (Fin q → ℝ) × (Fin q → ℝ) => fun j => (z.1 j,z.2 j)
  have hzip : Measurable zip := by fun_prop
  have hh : ((μ.prod ν).map (Prod.map Z Z)).map Q =
      ((μ.map (pathPastCoordinates v)).prod (ν.map (pathPastCoordinates v))).prod (γ.prod γ) := by
    rw [← Measure.map_prod_map _ _ hZ hZ,hμ q v s t hv hst ht,hν q v s t hv hst ht]
    exact measure_prod_shuffle _ _ _ _
  have he := congrArg (fun M => M.map (Prod.map zip id)) hh
  rw [Measure.map_map (hzip.prodMap measurable_id) hQ,
    Measure.map_map ((hzip.prodMap measurable_id).comp hQ) (hZ.prodMap hZ),
    ← Measure.map_prod_map _ _ hzip measurable_id,Measure.map_id,
    Measure.map_prod_map _ _ (pathPastCoordinates v).continuous.measurable (pathPastCoordinates v).continuous.measurable,
    Measure.map_map hzip (by fun_prop)] at he
  exact he

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def pairRestricted (I : Finset unitInterval) : C(RealPathPair,I → ℝ × ℝ) :=
  ⟨fun P z => (P.1 z,P.2 z),by fun_prop⟩

noncomputable def pairIncrement (s t : unitInterval) : C(RealPathPair,ℝ × ℝ) :=
  ⟨fun P => (P.1 t-P.1 s,P.2 t-P.2 s),by fun_prop⟩

lemma fullNormalJointPast_finset (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : FullNormalJointPast μ c) (I : Finset unitInterval)
    (s t : unitInterval) (hv : ∀ z ∈ I,z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1) :
    μ.map (fun P => (pairRestricted I P,pairIncrement s t P))=
      (μ.map (pairRestricted I)).prod
        ((gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))).prod
         (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)))) := by
  let e := Fintype.equivFin I
  let v := fun j : Fin (Fintype.card I) => ((e.symm j:I):unitInterval)
  let g := fun z : Fin (Fintype.card I) → ℝ × ℝ => fun j : I => z (e j)
  have hg : Measurable g := by fun_prop
  have hh := h (Fintype.card I) v s t (fun j => hv _ (e.symm j).property) hst ht
  have hh' := congrArg (fun M => M.map (Prod.map g id)) hh
  rw [Measure.map_map (hg.prodMap measurable_id) (by fun_prop),← Measure.map_prod_map _ _ hg measurable_id,
    Measure.map_id,Measure.map_map hg (by fun_prop)] at hh'
  convert hh' using 1
  · congr 1
    funext P
    apply Prod.ext
    · funext j
      simp [g,v,e,pairRestricted,pairPastCoordinates]
    · rfl
  · congr 2
    funext P j
    simp [g,v,e,pairRestricted,pairPastCoordinates]

lemma pairRestricted_empty_map (μ : Measure RealPathPair) [IsProbabilityMeasure μ] :
    μ.map (pairRestricted ∅)=Measure.dirac 0 := by
  have he : (pairRestricted ∅ : RealPathPair → (∅ : Finset unitInterval) → ℝ × ℝ)=fun _ => 0 := by
    funext P z
    exact False.elim (Finset.notMem_empty _ z.property)
  rw [he,Measure.map_const,measure_univ,one_smul]

lemma pairRestricted_singleton_zero_map (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (hzero : ∀ᵐ P ∂μ, P.1 0=0 ∧ P.2 0=0) :
    μ.map (pairRestricted {0})=Measure.dirac 0 := by
  have he : (pairRestricted {0} : RealPathPair → ({0} : Finset unitInterval) → ℝ × ℝ)=ᵐ[μ] fun _ => 0 := by
    filter_upwards [hzero] with P hP
    funext z
    have hz : z.val=0 := Finset.mem_singleton.mp z.property
    simp [pairRestricted,hz,hP.1,hP.2]
  rw [Measure.map_congr he,Measure.map_const,measure_univ,one_smul]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma pairRestricted_mono_eq (μ ν : Measure RealPathPair) {I J : Finset unitInterval}
    (hIJ : I ⊆ J) (h : μ.map (pairRestricted J)=ν.map (pairRestricted J)) :
    μ.map (pairRestricted I)=ν.map (pairRestricted I) := by
  let g := fun z : J → ℝ × ℝ => fun i : I => z ⟨i,hIJ i.property⟩
  have hg : Measurable g := by fun_prop
  have hh := congrArg (fun M => M.map g) h
  rw [Measure.map_map hg (pairRestricted J).continuous.measurable,
    Measure.map_map hg (pairRestricted J).continuous.measurable] at hh
  exact hh

noncomputable def pairExtend (I : Finset unitInterval) (t s : unitInterval) (hs : s ∈ I) :
    ((I → ℝ × ℝ) × (ℝ × ℝ)) → (↑(insert t I) → ℝ × ℝ) :=
  fun z j => if h : j.val=t then z.1 ⟨s,hs⟩+z.2 else
    z.1 ⟨j,Finset.mem_of_mem_insert_of_ne j.property h⟩

lemma pairExtend_measurable (I : Finset unitInterval) (t s : unitInterval) (hs : s ∈ I) :
    Measurable (pairExtend I t s hs) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j.val=t <;> simp [pairExtend,h] <;> fun_prop

lemma pairExtend_eval (I : Finset unitInterval) (t s : unitInterval) (hs : s ∈ I) (P : RealPathPair) :
    pairExtend I t s hs (pairRestricted I P,pairIncrement s t P)=pairRestricted (insert t I) P := by
  funext j
  by_cases h : j.val=t
  · simp [pairExtend,h,pairRestricted,pairIncrement]
  · simp [pairExtend,h,pairRestricted]

lemma pairRestricted_insert_eq (μ ν : Measure RealPathPair)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ≥0)
    (hμ : FullNormalJointPast μ c) (hν : FullNormalJointPast ν c)
    (I : Finset unitInterval) (t s : unitInterval) (hs : s ∈ I)
    (hIs : ∀ z ∈ I,z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1)
    (hI : μ.map (pairRestricted I)=ν.map (pairRestricted I)) :
    μ.map (pairRestricted (insert t I))=ν.map (pairRestricted (insert t I)) := by
  have hm := fullNormalJointPast_finset μ c hμ I s t hIs hst ht
  have hn := fullNormalJointPast_finset ν c hν I s t hIs hst ht
  rw [hI] at hm
  have he := hm.trans hn.symm
  have he' := congrArg (fun M => M.map (pairExtend I t s hs)) he
  rw [Measure.map_map (pairExtend_measurable I t s hs) (by fun_prop),
    Measure.map_map (pairExtend_measurable I t s hs) (by fun_prop)] at he'
  simpa only [Function.comp_def,pairExtend_eval] using he'

lemma fullNormalJointPast_finite_uniqueness (μ ν : Measure RealPathPair)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ≥0)
    (hμ : FullNormalJointPast μ c) (hν : FullNormalJointPast ν c)
    (hμ0 : ∀ᵐ P ∂μ, P.1 0=0 ∧ P.2 0=0) (hν0 : ∀ᵐ P ∂ν, P.1 0=0 ∧ P.2 0=0)
    (I : Finset unitInterval) (hI : ∀ z ∈ I,(z:ℝ) < 1) :
    μ.map (pairRestricted I)=ν.map (pairRestricted I) := by
  have hz : μ.map (pairRestricted {0})=ν.map (pairRestricted {0}) := by
    rw [pairRestricted_singleton_zero_map μ hμ0,pairRestricted_singleton_zero_map ν hν0]
  induction I using Finset.induction_on_max with
  | empty => rw [pairRestricted_empty_map,pairRestricted_empty_map]
  | insert t I hlt ih =>
    have ht : (t:ℝ) < 1 := hI t (Finset.mem_insert_self _ _)
    have hIp : ∀ z ∈ I,(z:ℝ) < 1 := fun z hz => hI z (Finset.mem_insert_of_mem hz)
    rcases I.eq_empty_or_nonempty with he | he
    · subst I
      simp only [Finset.insert_empty]
      by_cases ht0 : t=0
      · subst t
        exact hz
      · have h0t : (0:unitInterval) < t := lt_of_le_of_ne (show (0:unitInterval) ≤ t from t.property.1) (Ne.symm ht0)
        have hh := pairRestricted_insert_eq μ ν c hμ hν {0} t 0 (by simp)
          (by intro z hz; rw [Finset.mem_singleton.mp hz]) h0t ht hz
        apply pairRestricted_mono_eq μ ν (J := insert t {0}) (by intro z hz; simp_all)
        exact hh
    · apply pairRestricted_insert_eq μ ν c hμ hν I t (I.max' he) (Finset.max'_mem I he)
        (fun z hz => Finset.le_max' I z hz) (hlt _ (Finset.max'_mem I he)) ht
      exact ih hIp

end DirectionalTransience

end

end

end OAI
