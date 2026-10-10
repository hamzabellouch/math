import Mathlib
import OAI.Probability.LogConcave.Model

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

namespace LogConcaveSampling
@[fun_prop] lemma measurable_fin_snoc {X : Type*} [MeasurableSpace X] (n : ℕ) :
    Measurable (fun p : (Fin n → X) × X => Fin.snoc (α := fun _ : Fin (n+1) => X) p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (measurable_snd : Measurable (Prod.snd : (Fin n → X) × X → X))
  · simp only [Fin.snoc_castSucc]
    fun_prop

lemma pi_snoc_law {X : Type*} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => ν)).prod ν).map (fun p => Fin.snoc (α := fun _ : Fin (n+1) => X) p.1 p.2) =
      Measure.pi (fun _ : Fin (n+1) => ν) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm.map_eq
  have hs := Measure.prod_swap (μ := Measure.pi (fun _ : Fin n => ν)) (ν := ν)
  rw [← hs, Measure.map_map (by fun_prop) (by fun_prop)] at h
  convert h using 1
  congr 1
  funext p
  exact (Fin.insertNth_last' p.2 p.1).symm

end LogConcaveSampling

namespace LogConcaveSampling
open ProbabilityTheory

def unitUniform : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure unitUniform := by
  constructor
  simp [unitUniform]

lemma unitUniform_Iic {a : ℝ} (_ha : 0 ≤ a) (ha' : a ≤ 1) :
    unitUniform (Set.Iic a) = ENNReal.ofReal a := by
  rw [unitUniform,Measure.restrict_apply measurableSet_Iic]
  have hh : Set.Iic a ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 a := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_Iic,Set.mem_Icc]
    constructor
    · intro hx; exact ⟨hx.2.1,hx.1⟩
    · intro hx; exact ⟨hx.2,hx.1,hx.2.trans ha'⟩
  rw [hh,Real.volume_Icc,sub_zero]

variable {E : Type*} [MeasurableSpace E]

def acceptanceEvent (a : E → ℝ) : Set (E × ℝ) := {p | p.2 ≤ a p.1}

lemma measurable_acceptanceEvent {a : E → ℝ} (ha : Measurable a) :
    MeasurableSet (acceptanceEvent a) := measurableSet_le measurable_snd (ha.comp measurable_fst)

theorem accepted_measure (ν : Measure E) [IsProbabilityMeasure ν] {a : E → ℝ}
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1) :
    (((ν.prod unitUniform).restrict (acceptanceEvent a)).map Prod.fst) =
      ν.withDensity (fun x => ENNReal.ofReal (a x)) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (hs.preimage measurable_fst),
    Measure.prod_apply ((hs.preimage measurable_fst).inter (measurable_acceptanceEvent ha)),
    withDensity_apply _ hs]
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' s ∩ acceptanceEvent a) = Set.Iic (a x) := by
      ext t
      simp [acceptanceEvent,hx]
    rw [he]
    exact unitUniform_Iic (ha0 x) (ha1 x)
  · have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' s ∩ acceptanceEvent a) = ∅ := by
      ext t
      simp [acceptanceEvent,hx]
    rw [he,measure_empty,Set.indicator_of_notMem hx]

def rejectionPick (a : E → ℝ) (fallback : E) : (n : ℕ) → (Fin n → E × ℝ) → E
  | 0, _ => fallback
  | n+1, tape =>
      if (tape (Fin.last n)).2 ≤ a (tape (Fin.last n)).1 then (tape (Fin.last n)).1
      else rejectionPick a fallback n (fun i => tape i.castSucc)

@[fun_prop] lemma measurable_rejectionPick {a : E → ℝ} (ha : Measurable a) (fallback : E) (n : ℕ) :
    Measurable (rejectionPick a fallback n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      apply Measurable.ite
      · exact measurableSet_le ((measurable_pi_apply (Fin.last n)).snd)
          (ha.comp ((measurable_pi_apply (Fin.last n)).fst))
      · exact (measurable_pi_apply (Fin.last n)).fst
      · exact ih.comp (Measurable.of_eval fun index => measurable_pi_apply index.castSucc)

omit [MeasurableSpace E] in
lemma rejectionPick_snoc (a : E → ℝ) (fallback : E) (n : ℕ) (tape : Fin n → E × ℝ) (z : E × ℝ) :
    rejectionPick a fallback (n+1) (Fin.snoc tape z) =
      if z.2 ≤ a z.1 then z.1 else rejectionPick a fallback n tape := by
  simp only [rejectionPick,Fin.snoc_last,Fin.snoc_castSucc]

theorem rejection_law_succ (ν : Measure E) [IsProbabilityMeasure ν] {a : E → ℝ}
    (ha : Measurable a) (fallback : E) (n : ℕ) :
    (Measure.pi (fun _ : Fin (n+1) => ν.prod unitUniform)).map (rejectionPick a fallback (n+1)) =
      (((ν.prod unitUniform).restrict (acceptanceEvent a)).map Prod.fst) +
      ((ν.prod unitUniform) (acceptanceEvent a)ᶜ) •
        (Measure.pi (fun _ : Fin n => ν.prod unitUniform)).map (rejectionPick a fallback n) := by
  rw [← pi_snoc_law (ν.prod unitUniform) n,
    Measure.map_map (measurable_rejectionPick ha fallback (n+1)) (measurable_fin_snoc n)]
  ext s hs
  rw [Measure.map_apply ((measurable_rejectionPick ha fallback (n+1)).comp (measurable_fin_snoc n)) hs,
    Measure.add_apply,Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (hs.preimage measurable_fst),Measure.smul_apply,
    Measure.map_apply (measurable_rejectionPick ha fallback n) hs,smul_eq_mul]
  have he : (rejectionPick a fallback (n+1) ∘ (fun p => Fin.snoc p.1 p.2)) ⁻¹' s =
      (Set.univ ×ˢ (Prod.fst ⁻¹' s ∩ acceptanceEvent a)) ∪
      ((rejectionPick a fallback n ⁻¹' s) ×ˢ (acceptanceEvent a)ᶜ) := by
    ext ⟨t,z⟩
    simp only [Set.mem_preimage,Function.comp_apply,rejectionPick_snoc,Set.mem_union,
      Set.mem_prod,Set.mem_univ,true_and,Set.mem_inter_iff,Set.mem_compl_iff,acceptanceEvent,Set.mem_ofPred_eq]
    split_ifs <;> simp_all
  rw [he,measure_union]
  · rw [Measure.prod_prod,Measure.prod_prod,measure_univ,one_mul,mul_comm]
  · apply Set.disjoint_left.mpr
    rintro p ⟨_,_,hp⟩ ⟨_,hn⟩
    exact hn hp
  · exact (hs.preimage (measurable_rejectionPick ha fallback n)).prod (measurable_acceptanceEvent ha).compl

lemma rejection_failure_mass (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {a : E → ℝ} (ha : Measurable a) {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (hacc : (((ν.prod unitUniform).restrict (acceptanceEvent a)).map Prod.fst) =
      ENNReal.ofReal p • μ) :
    (ν.prod unitUniform) (acceptanceEvent a)ᶜ = ENNReal.ofReal (1-p) := by
  have he : (ν.prod unitUniform) (acceptanceEvent a) = ENNReal.ofReal p := by
    have hh := congrArg (fun η : Measure E => η Set.univ) hacc
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,Set.preimage_univ,
      Measure.restrict_apply_univ,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using hh
  rw [measure_compl (measurable_acceptanceEvent ha) (measure_ne_top _ _),measure_univ,he]
  exact by simpa using (ENNReal.ofReal_sub 1 hp0).symm

theorem capped_rejection_tv (ν μ : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {a : E → ℝ} (ha : Measurable a) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hacc : (((ν.prod unitUniform).restrict (acceptanceEvent a)).map Prod.fst) =
      ENNReal.ofReal p • μ) (fallback : E) (n : ℕ) :
    TVAtMost ((Measure.pi (fun _ : Fin n => ν.prod unitUniform)).map
      (rejectionPick a fallback n)) μ ((1-p)^n) := by
  let out := fun n => (Measure.pi (fun _ : Fin n => ν.prod unitUniform)).map
    (rejectionPick a fallback n)
  have ho : ∀ n, IsProbabilityMeasure (out n) := fun _ => inferInstance
  have hor : ∀ n s, 0 ≤ (out n).real s ∧ (out n).real s ≤ 1 := by
    intro n s
    have := ho n
    exact ⟨measureReal_nonneg,measureReal_le_one⟩
  have hμr : ∀ s, 0 ≤ μ.real s ∧ μ.real s ≤ 1 := fun s =>
    ⟨measureReal_nonneg,measureReal_le_one⟩
  have hrec : ∀ n s, MeasurableSet s →
      (out (n+1)).real s = p * μ.real s + (1-p) * (out n).real s := by
    intro n s _
    have he := rejection_law_succ ν ha fallback n
    rw [hacc,rejection_failure_mass ν μ ha hp0 hp1 hacc] at he
    change (out (n+1)) = _ at he
    rw [he,Measure.real,Measure.add_apply,ENNReal.toReal_add]
    · simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hp0,ENNReal.toReal_ofReal (sub_nonneg.mpr hp1),Measure.real]
      rfl
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    · have := ho n
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  intro s hs
  change |(out n).real s-μ.real s| ≤ _
  induction n with
  | zero =>
      simpa only [pow_zero] using (abs_sub_le_iff.mpr
        ⟨by linarith [(hor 0 s).2,(hμr s).1],by linarith [(hor 0 s).1,(hμr s).2]⟩)
  | succ n ih =>
      rw [hrec n s hs]
      have he : p*μ.real s+(1-p)*(out n).real s-μ.real s =
          (1-p)*((out n).real s-μ.real s) := by ring
      rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr hp1),pow_succ']
      exact mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp1)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
