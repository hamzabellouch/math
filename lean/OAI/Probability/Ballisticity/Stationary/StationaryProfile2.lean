import Mathlib
import OAI.Probability.Ballisticity.Estimates.MarkedObservables

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

abbrev FullMarkedArray {d : ℕ} (e : Direction d) := MarkedArray e × Environment d
noncomputable def fullMarkedShift {d : ℕ} (e : Direction d) : FullMarkedArray e → FullMarkedArray e :=
  Prod.map (markedShift e) id

lemma fullMarkedShift_iterate_fst {d : ℕ} (e : Direction d) (p : FullMarkedArray e) (n : ℕ) :
    ((fullMarkedShift e)^[n] p).1=(markedShift e)^[n] p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change markedShift e (((fullMarkedShift e)^[n] p).1)=_
    rw [ih]

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

noncomputable def actualProfileSystem (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e)))
    (w₀ : ProperProfile e) (f : Fin d) (hef : e.1≠f) :
    StationaryProfileSystem ν e f (FullMarkedArray e) (ProperProfile e)
      ((markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event).prod (environmentLaw ν))
      (properProfileKernel e) := by
  let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
  haveI := markedArrayLaw_probability e (L.law : Measure (ActualEpisodeArray e)) G.event G.positive_event.ne'
  have hT := L.marked_preserving hue htrans G
  have hF := Measure.quasiMeasurePreserving_fst (μ := μ) (ν := environmentLaw ν)
  have hmarks := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event G.measurable_event
    (L.finite_marks.mono fun Y h _ => h)
  have hp := L.marked_profile_proper hue htrans G
  refine {
    T := fullMarkedShift e
    preserving := hT.prod (MeasurePreserving.id (environmentLaw ν))
    data := fun p => properData e w₀ (markedData e p.1)
    measurable_data := (properData_measurable e w₀).comp ((markedData_measurable e).comp measurable_fst)
    full := properProfileKernel_full e
    total := properProfileKernel_total e
    c := fun p => arrayRealCost e p.1.1
    measurable_c := (arrayRealCost_measurable e).comp measurable_fst.fst
    nonneg_c := ae_of_all _ fun p => arrayRealCost_nonneg e p.1.1
    integrable_c := (markedArrayLaw_integrable e _ G.event G.positive_event.ne' _
      (arrayRealCost_measurable e) L.integrable_cost).comp_fst (environmentLaw ν)
    h := fun p => arrayNatHeight e p.1.1
    measurable_h := (arrayNatHeight_measurable e).comp measurable_fst.fst
    positive_h := ?_
    integrable_log_h := ?_
    field := fun n p => fillUpper e (markedUpper e n p.1,p.2)
    measurable_field := fun n => (fillUpper_measurable e).comp
      (((markedUpper_measurable e n).comp measurable_fst).prodMk measurable_snd)
    finite_entropy := fun n _ => L.marked_full_entropy G w₀ n
    offset := fun n p => (markedDisplacement e n p.1).val f
    update := ?_
  }
  · filter_upwards [hF.ae hmarks] with p hm
    exact arrayNatHeight_positive e p.1.1 (hm 0).1 (hm 0).2.1
  · have hm : Measurable (fun Y : ActualEpisodeArray e => Real.log (1+(arrayNatHeight e Y:ℝ))) :=
      Real.measurable_log.comp (measurable_const.add ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
        (arrayNatHeight_measurable e)))
    exact (markedArrayLaw_integrable e _ G.event G.positive_event.ne' _ hm
      L.integrable_logheight).comp_fst (environmentLaw ν)
  · intro n hn
    have hcont := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event G.measurable_event
      (show ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
        ArrayProfilesConsistent e Y ∧ ArrayContinuation e Y from by
          filter_upwards [L.consistent,L.continuation] with Y ho hc _
          exact ⟨ho.2,hc⟩)
    have hrel := L.marked_related hue htrans G
    have hpn := (hT.iterate n).quasiMeasurePreserving.ae hp
    filter_upwards [hF.ae hcont,hF.ae hmarks,hF.ae hrel,hF.ae hp,hF.ae hpn] with p hco hm hr hp0 hpn0
    simp only [fullMarkedShift_iterate_fst]
    exact markedProfile_update e f hef w₀ p.1 p.2 n hco.1 hco.2
      (fun j => (hm j).2.1) (fun j => (hm j).2.2.2.ne) (hr n) hp0 hpn0

end StationaryArrayLaw
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

theorem impossible (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (f : Fin d) (hef : e.1≠f) : False := by
  obtain ⟨G⟩ := L.growth_sector hue htrans
  obtain ⟨w₀⟩ := L.properProfile_nonempty hue htrans G
  let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
  have : IsProbabilityMeasure μ := markedArrayLaw_probability e _ G.event G.positive_event.ne'
  let η := μ.prod (environmentLaw ν)
  let S := L.actualProfileSystem hue htrans G w₀ f hef
  have hn := stationary_profile_mean_nonpos ν hue e f hef htrans (FullMarkedArray e)
    (ProperProfile e) η (properProfileKernel e) S
  have hz : S.c =ᵐ[η] 0 := (integral_eq_zero_iff_of_nonneg_ae S.nonneg_c S.integrable_c).mp
    (le_antisymm hn (integral_nonneg_of_ae S.nonneg_c))
  have hzero : ∀ᵐ p ∂η, ∀ i : ℕ, S.c (S.T^[i] p)=0 :=
    ae_all_iff.mpr fun i => (S.preserving.iterate i).quasiMeasurePreserving.ae hz
  have hgrowth := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event
    G.measurable_event G.growth
  have hmarks := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event
    G.measurable_event (L.finite_marks.mono fun Y h _ => h)
  have hF := Measure.quasiMeasurePreserving_fst (μ := μ) (ν := environmentLaw ν)
  obtain ⟨p,hp0,hpg,hpm⟩ := (hzero.and ((hF.ae hgrowth).and (hF.ae hmarks))).exists
  have hwin (n : ℕ) : (arrayWindowCost e 0 n p.1.1).toReal=0 := by
    rw [arrayWindowCost_toReal e p.1.1 (fun j => (hpm j).2.2.2.ne)]
    apply Finset.sum_eq_zero
    intro i hi
    have h := hp0 i
    change arrayRealCost e (((fullMarkedShift e)^[i] p).1.1)=0 at h
    simpa only [fullMarkedShift_iterate_fst,markedShift_iterate_fst] using h
  obtain ⟨k,hk⟩ := hpg.exists
  rw [hwin] at hk
  exact (not_lt_of_ge (mul_nonneg G.positive_ζ.le (Nat.cast_nonneg _))) hk

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
