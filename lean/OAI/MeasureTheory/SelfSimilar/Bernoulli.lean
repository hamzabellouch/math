import OAI.MeasureTheory.SelfSimilar.MassDimension

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

namespace EntropyRateDimension
namespace Bernoulli

variable {α : Type uα} [MeasurableSpace α]

def shift (ω : ℕ → α) (n : ℕ) : α := ω (n+1)

theorem shift_measurable : Measurable (shift (α := α)) :=
  measurable_pi_iff.mpr fun n => measurable_pi_apply (n+1)

omit [MeasurableSpace α] in
theorem shift_iterate (n : ℕ) (ω : ℕ → α) (k : ℕ) :
    shift^[n] ω k = ω (k+n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', shift, ih]
    congr 1
    omega

theorem shift_preserving (p : Measure α) [IsProbabilityMeasure p] :
    MeasurePreserving shift (Measure.infinitePi (fun _ : ℕ => p))
      (Measure.infinitePi (fun _ : ℕ => p)) where
  measurable := shift_measurable
  map_eq := by
    have hi : iIndepFun (fun n : ℕ => (@Function.eval ℕ (fun _ => α) n))
        (Measure.infinitePi fun _ : ℕ => p) :=
      iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
    have hh := (hi.precomp Nat.succ_injective).map_fun_eq_infinitePi_map
      (fun n => measurable_pi_apply (n+1))
    change Measure.map (fun ω : ℕ → α => fun n => ω (n+1))
      (Measure.infinitePi fun _ : ℕ => p) = _
    simpa only [Measure.infinitePi_map_eval, Function.eval] using hh

theorem head_indep_tail (p : Measure α) [IsProbabilityMeasure p] :
    IndepFun (fun ω : ℕ → α => ω 0) shift (Measure.infinitePi fun _ : ℕ => p) := by
  let m : ℕ → MeasurableSpace (ℕ → α) := fun n =>
    MeasurableSpace.comap (fun ω : ℕ → α => ω n) inferInstance
  have hi : iIndep m (Measure.infinitePi fun _ : ℕ => p) :=
    iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
  have h := indep_iSup_of_disjoint (fun n => (measurable_pi_apply n).comap_le) hi
    (S := {0}) (T := Set.range Nat.succ) (by
      apply Set.disjoint_left.mpr
      rintro n (hn : n = 0) ⟨k,hk⟩
      omega)
  apply indep_of_indep_of_le h
  · exact le_iSup_of_le 0 (le_iSup_of_le rfl le_rfl)
  · change MeasurableSpace.comap shift
      (⨆ k : ℕ, MeasurableSpace.comap (Function.eval k) (inferInstance : MeasurableSpace α)) ≤ _
    rw [MeasurableSpace.comap_iSup]
    apply iSup_le
    intro k
    rw [MeasurableSpace.comap_comp]
    exact le_iSup_of_le (k+1) (le_iSup_of_le ⟨k,rfl⟩ le_rfl)

theorem head_tail_law (p : Measure α) [IsProbabilityMeasure p] :
    (Measure.infinitePi fun _ : ℕ => p).map (fun ω => (ω 0,shift ω)) =
      p.prod (Measure.infinitePi fun _ : ℕ => p) := by
  rw [(head_indep_tail p).map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable shift_measurable.aemeasurable,
    Measure.infinitePi_map_eval, (shift_preserving p).map_eq]

theorem invariant_tail_measurable {s : Set (ℕ → α)} (hs : MeasurableSet s)
    (hinv : shift ⁻¹' s = s) :
    MeasurableSet[Filter.limsup (fun n : ℕ =>
      MeasurableSpace.comap (Function.eval n) (inferInstance : MeasurableSpace α)) atTop] s := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat']
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  have hm : @Measurable (ℕ → α) (ℕ → α)
      (⨆ i : ℕ, MeasurableSpace.comap (fun ω : ℕ → α => ω (i+n)) (inferInstance : MeasurableSpace α))
      inferInstance (fun ω k => ω (k+n)) := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap (fun ω : ℕ → α => fun k => ω (k+n))
      (⨆ k : ℕ, MeasurableSpace.comap (Function.eval k) (inferInstance : MeasurableSpace α)) ≤ _
    rw [MeasurableSpace.comap_iSup]
    apply iSup_le
    intro k
    rw [MeasurableSpace.comap_comp]
    exact le_iSup (fun i : ℕ => MeasurableSpace.comap (fun ω : ℕ → α => ω (i+n))
      (inferInstance : MeasurableSpace α)) k
  have he : (fun ω : ℕ → α => fun k => ω (k+n)) = shift^[n] := by
    funext ω k
    exact (shift_iterate n ω k).symm
  rw [he] at hm
  have hi : (shift^[n]) ⁻¹' s = s := Function.IsFixedPt.preimage_iterate hinv n
  rw [← hi]
  exact hm hs

theorem shift_ergodic (p : Measure α) [IsProbabilityMeasure p] :
    Ergodic shift (Measure.infinitePi (fun _ : ℕ => p)) where
  toMeasurePreserving := shift_preserving p
  aeconst_set := by
    intro s hs hi
    have hind : iIndepFun (fun n : ℕ => (@Function.eval ℕ (fun _ => α) n))
        (Measure.infinitePi fun _ : ℕ => p) :=
      iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
    have hz := measure_zero_or_one_of_measurableSet_limsup_atTop
      (fun n => (measurable_pi_apply n).comap_le) hind
      (invariant_tail_measurable hs hi)
    apply eventuallyEmptyOrUniv_iff.mpr
    rcases hz with h0 | h1
    · right
      exact measure_eq_zero_iff_ae_notMem.mp h0
    · left
      have hc : (Measure.infinitePi fun _ : ℕ => p) sᶜ = 0 := by
        rw [measure_compl hs (measure_ne_top _ _), h1]
        simp
      simpa only [mem_compl_iff, not_not] using measure_eq_zero_iff_ae_notMem.mp hc

end Bernoulli
end EntropyRateDimension
end

end OAI
