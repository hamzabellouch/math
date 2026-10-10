import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma measurable_fin_cons {Y : Type*} [MeasurableSpace Y] {n : ℕ} :
    Measurable (fun z : Y × (Fin n → Y) => (Fin.cons z.1 z.2 : Fin (n+1) → Y)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : Y × (Fin n → Y) → Y))
  · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp measurable_snd

def piKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] :
    {n : ℕ} → (Fin n → Kernel X Y) → Kernel X (Fin n → Y)
  | 0, _ => Kernel.deterministic (fun _ i => Fin.elim0 i) (by fun_prop)
  | n+1, κ => ((κ 0) ×ₖ piKernel (fun i : Fin n => κ i.succ)).map
      (fun z => Fin.cons z.1 z.2)

instance piKernel_markov {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} (κ : Fin n → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (piKernel κ) := by
  induction n with
  | zero => unfold piKernel; infer_instance
  | succ n ih =>
    have : IsMarkovKernel (piKernel (fun i : Fin n => κ i.succ)) := ih _
    unfold piKernel
    exact Kernel.IsMarkovKernel.map _ (by fun_prop)

lemma piKernel_apply {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} (κ : Fin n → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] (x : X) :
    piKernel κ x = Measure.pi (fun i => κ i x) := by
  induction n with
  | zero =>
    rw [piKernel, Kernel.deterministic_apply, Measure.pi_of_empty _ (fun i => Fin.elim0 i)]
  | succ n ih =>
    have hκ : ∀ i : Fin n, IsMarkovKernel (κ i.succ) := inferInstance
    rw [piKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, ih]
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0).symm
    have he : (fun z : Y × (Fin n → Y) => Fin.cons z.1 z.2) = e := by
      funext z
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq]
    rw [he]
    exact (measurePreserving_piFinSuccAbove (fun i : Fin (n+1) => κ i x) 0).symm.map_eq

@[fun_prop] lemma measurable_piKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} (κ : Fin n → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] :
    Measurable (fun x => Measure.pi (fun i => κ i x)) := by
  simpa only [← piKernel_apply] using (piKernel κ).measurable

end PosteriorReplicas
end

end OAI
