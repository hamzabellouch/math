import Mathlib
import OAI.Analysis.HardSphere.Geometry.BadComponent
import OAI.Analysis.HardSphere.Conditioning.Phase
import OAI.Analysis.HardSphere.Conditioning.PhaseTransfer

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace HardSphere

lemma cons_preserving {n : ℕ} (L : Length) :
    MeasurePreserving (fun p : Configuration n L × Torus L ↦ Fin.cons (α:=fun _ ↦ Torus L) p.2 p.1)
      (volume.prod volume) volume := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
  have hh := h.comp (measurePreserving_swap (μ:= (volume : Measure (Configuration n L))) (ν:=volume))
  convert hh using 1
  funext p i
  simp [MeasurableEquiv.piFinSuccAbove]

lemma allowed_cons {n : ℕ} {L : Length} {r : ℝ} {Y : Configuration n L} {x : Torus L}
    (hY : Y∈allowed n L r) (hx : x∈BathSlice.slice r Y) :
    Fin.cons x Y∈allowed (n+1) L r := by
  rw [allowed_iff_ne] at hY ⊢
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j =>
      simpa using (lt_of_not_ge (fun h ↦ hx ⟨j,h⟩))
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      simpa [torusDistance_comm] using (lt_of_not_ge (fun h ↦ hx ⟨i,h⟩))
    | succ j => exact hY i j (fun h ↦ hij (congrArg Fin.succ h))

lemma IsGroundVector.phaseRepresentative_eq_of_joined {n : ℕ} {L : Length} {r : ℝ}
    {u : Jet n L} (hu : IsGroundVector n L r u) {x y : Configuration n L}
    (h : JoinedIn (allowed n L r) x y) :
    groundPhaseRepresentative u x=groundPhaseRepresentative u y := by
  obtain ⟨p,hp⟩ := h
  apply hu.phaseRepresentative_eq_on_connected (S:=Set.range p)
    (isPreconnected_range p.continuous) (by rintro z ⟨t,rfl⟩; exact hp t)
  · exact ⟨0,p.source⟩
  · exact ⟨1,p.target⟩

lemma IsGroundVector.retained_phaseRepresentative {n : ℕ} {L : Length} {h r : ℝ}
    {u : Jet (n+1) L} (hu : IsGroundVector (n+1) L r u) (hh : 0<h)
    {Y : Configuration n L} {x y : Torus L}
    (hx : x∈BathSlice.retained h r Y) (hy : y∈BathSlice.retained h r Y) :
    groundPhaseRepresentative u (Fin.cons x Y)=groundPhaseRepresentative u (Fin.cons y Y) := by
  have hY : Y∈allowed n L r := by
    by_contra hn
    exact hx (Or.inl (Or.inl hn))
  have hj := BathSlice.retained_joined hh hx hy
  have hc : Continuous (fun z : Torus L ↦ Fin.cons (α:=fun _ ↦ Torus L) z Y) := by
    apply continuous_pi
    intro i
    induction i using Fin.cases <;> simp only [Fin.cons_zero,Fin.cons_succ] <;> fun_prop
  apply hu.phaseRepresentative_eq_of_joined
  exact (hj.map hc.continuousOn).mono (by rintro _ ⟨z,hz,rfl⟩; exact allowed_cons hY hz)

lemma commonPhase_of_ae_phase {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℂ}
    {U : Set α} {c : ℂ} (h : ∀ᵐ x ∂μ.restrict U, complexPhase (f x)=c) :
    Phase.HasCommonPhase f U μ := by
  by_cases hc : ‖c‖=1
  · refine ⟨c,hc,?_⟩
    filter_upwards [h] with x hx
    rw [←hx,complexPhase_mul_norm]
  · refine ⟨1,norm_one,?_⟩
    filter_upwards [h] with x hx
    have hz : f x=0 := by
      by_contra hn
      exact hc (hx ▸ norm_complexPhase hn)
    simp [hz]

lemma IsGroundVector.ae_retained_commonPhase {n : ℕ} {L : Length} {h r : ℝ}
    {u : Jet (n+1) L} (hu : IsGroundVector (n+1) L r u) (hh : 0<h) :
    ∀ᵐ Y : Configuration n L ∂volume,
      Phase.HasCommonPhase (fun x ↦ u.1 (Fin.cons x Y)) (BathSlice.retained h r Y) volume := by
  have ha : ∀ᵐ X ∂volume, X∈allowed (n+1) L r →
      complexPhase (u.1 X)=groundPhaseRepresentative u X :=
    (ae_restrict_iff' (isOpen_allowed (n+1) L r).measurableSet).mp hu.ae_phaseRepresentative
  have hb := ae_ae_of_ae_prod ((cons_preserving (n:=n) L).quasiMeasurePreserving.ae ha)
  filter_upwards [hb] with Y hY
  by_cases he : (BathSlice.retained h r Y).Nonempty
  · obtain ⟨x,hx⟩ := he
    apply commonPhase_of_ae_phase volume (c:=groundPhaseRepresentative u (Fin.cons x Y))
    filter_upwards [ae_restrict_of_ae hY,ae_restrict_mem (BathSlice.measurableSet_retained h r Y)] with y hy hym
    have hYa : Y∈allowed n L r := by
      by_contra hn
      exact hx (Or.inl (Or.inl hn))
    have hys := (BathSlice.retained_joined hh hym hym).source_mem
    exact (hy (allowed_cons hYa hys)).trans (hu.retained_phaseRepresentative hh hym hx)
  · rw [not_nonempty_iff_eq_empty.mp he]
    exact ⟨1,norm_one,by simp⟩

end HardSphere

end
end

end

end OAI
