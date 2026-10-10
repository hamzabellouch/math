import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.RelayProbability
import OAI.Probability.CriticalPercolation.GraphGeometry.CoordinateScheme
import OAI.Probability.CriticalPercolation.Criticality.GrowthEstimate
import OAI.Probability.CriticalPercolation.ProductMeasure.SourceMissLaw
import OAI.Probability.CriticalPercolation.Gluing.ProspectiveCorridor

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.CoordinateData
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (C : CoordinateData V E)

lemma active_slot_positive (n : ℕ) (S : GrowthState) (hv : S.Valid n)
    (ha : (incoming n S.good).isSome) : 0<n := by
  obtain ⟨e,he⟩ := Option.isSome_iff_exists.mp ha
  have ht := parent_slot_lt e (hv.2.1 _ (incoming_source he)).1
  rw [incoming_target he,gridSlot_slotSite] at ht
  omega

theorem prospective_estimate (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s))
    (n : ℕ) (S : GrowthState) (hv : S.Valid n) (_hc : S.Covered)
    (ha : (incoming n S.good).isSome) (ω : Set E) (b : Bool) :
    (blockProbability C.scheme.parameter (C.scheme.block S)
      (C.scheme.incomingHit n S\C.scheme.nextHit n S b) ω).toReal≤(C.L+1)*C.kappa := by
  let v := slotSite n
  let F := C.scheme.enlarged n S
  let U := F∪C.scheme.edgeDomain (v,b)
  have hdom := C.domain_eq v b
  have hDU : C.graph.inducedEdges (relayDomain (localTime C.time C.T v)
      (localHeight C.height C.T v) C.J C.T (sign b))⊆U := by
    rw [← hdom]
    exact Set.subset_union_right
  have hfresh : Disjoint (C.scheme.block S)
      (C.graph.inducedEdges (relayDomain (localTime C.time C.T v)
        (localHeight C.height C.T v) C.J C.T (sign b))) := by
    rw [← hdom]
    exact outgoing_unrevealed C.graph (normalized C.time C.height C.T) (C.J/C.T) (2520/C.T)
      (C.layout h).1 (C.layout h).2.1 (C.layout h).2.2 n S hv (active_slot_positive n S hv ha) rfl
  have hmoves : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove (localTime C.time C.T v) (localHeight C.height C.T v)
        C.m C.e y s) := by
    intro y s hs
    rw [coordinateMove_translate]
    exact hmove y s hs
  have hP : 1≤C.T := by
    have hh : (416 : ℝ)≤C.L := by exact_mod_cast C.L_large h
    dsimp [T]; linarith
  have hh := C.graph.coordinate_pinned_corridor_failure h.connected h.locallyFinite
    C.scheme.seed (C.graph.vertexBall_finite h.locallyFinite C.origin C.m) C.scheme.parameter
    (C.scheme.block S) F U ω Set.subset_union_left
    (localTime C.time C.T v) (localHeight C.height C.T v) (sign b) C.e C.rho C.J C.T
    C.L C.R C.m (sign_abs b) h.e_pos h.rho_nonneg h.J_lower (C.L_large h) h.e_small h.rho_small
    hP (C.source_behind h n (active_slot_positive n S hv ha))
    (fun {_ _} hh => C.local_time_step h v hh) (fun {_ _} hh => C.local_height_step h v hh) h.R_gt C.pc C.p h.pc_pos h.pc_lt
    h.p_lower h.p_upper (fun _ _ => rfl) hDU hfresh C.D C.k C.M C.VM h.degree h.M_pos
    h.M_bound h.VM_bound C.kappa C.eta h.kappa_pos h.kappa_le h.eta_nonneg h.eta_small
    h.k_large h.R_large hmoves
  change (blockProbability C.scheme.parameter (C.scheme.block S)
    (C.graph.restrictedSeed C.scheme.seed (relayMark (localTime C.time C.T v) (localHeight C.height C.T v) 0 (sign b) C.rho) F\
      C.graph.restrictedSeed C.scheme.seed (relayMark (localTime C.time C.T v) (localHeight C.height C.T v) C.T (sign b) C.rho) U) ω).toReal≤_ at hh
  rw [mark_initial,mark_target] at hh
  exact hh

lemma root_corridor_estimate (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) (b : Bool) :
    (BernoulliProduct.law C.scheme.parameter).real
      (C.scheme.hit (target ((0,0),b))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),b)))ᶜ≤C.eta+C.L*C.kappa := by
  let U := C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),b)
  have hDU : C.graph.inducedEdges (relayDomain (localTime C.time C.T (0,0))
      (localHeight C.height C.T (0,0)) C.J C.T (sign b))⊆U := by
    rw [← C.domain_eq]
    exact Set.subset_union_right
  have hmoves : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove (localTime C.time C.T (0,0)) (localHeight C.height C.T (0,0))
        C.m C.e y s) := by
    intro y s hs
    rw [coordinateMove_translate]
    exact hmove y s hs
  have hh := C.graph.original_root_corridor_miss h.connected h.locallyFinite C.origin
    (localTime C.time C.T (0,0)) (localHeight C.height C.T (0,0)) (sign b) C.e C.rho C.J
    C.L C.R C.m U hDU (sign_abs b) h.e_pos h.rho_nonneg h.J_lower (C.L_large h) h.e_small h.rho_small
    (by simp [localTime,timeCenter,h.time_origin]) (by simp [localHeight,heightCenter,h.height_origin])
    (fun {_ _} hh => C.local_time_step h (0,0) hh) (fun {_ _} hh => C.local_height_step h (0,0) hh) h.R_gt C.pc C.p h.pc_pos h.pc_lt
    h.p_lower h.p_upper C.D C.k C.M C.VM h.degree h.M_pos h.M_bound h.VM_bound
    C.kappa C.eta h.kappa_pos h.kappa_le h.eta_nonneg h.eta_small h.k_large h.R_large hmoves
  change (BernoulliProduct.law (fun _ : E => C.p)).real
    (C.graph.restrictedSeed (C.graph.vertexBall C.origin C.m)
      (relayMark (localTime C.time C.T (0,0)) (localHeight C.height C.T (0,0)) C.T (sign b) C.rho) U)ᶜ≤_ at hh
  rw [mark_target] at hh
  exact hh

lemma root_positive (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) :
    0<(BernoulliProduct.law C.scheme.parameter).real C.scheme.rootEvent := by
  have he : C.scheme.rootEvent=twoPredictions C.scheme.parameter (C.scheme.block GrowthState.initial)
      (C.scheme.hit (target ((0,0),true))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),true)))
      (C.scheme.hit (target ((0,0),false))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),false))) C.delta := by
    ext ω
    change (∀ b : Bool, 1-C.delta≤(blockProbability C.scheme.parameter
      (C.scheme.block GrowthState.initial) (C.scheme.hit (target ((0,0),b))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),b))) ω).toReal) ↔ (_ ∧ _)
    constructor
    · intro hh; exact ⟨hh true,hh false⟩
    · rintro ⟨ht,hf⟩ b; cases b <;> assumption
  rw [he]
  apply twoPredictions_positive _ _ _ _
    (C.graph.restrictedSeed_measurable _ _ _) (C.graph.restrictedSeed_measurable _ _ _)
    C.delta (C.eta+C.L*C.kappa) h.delta_pos h.root_error
    (C.root_corridor_estimate h hmove true) (C.root_corridor_estimate h hmove false)

theorem moves_force_percolation (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) :
    0<C.graph.law C.p C.graph.percolates := by
  let hf := C.graph.vertexBall_finite h.locallyFinite C.origin C.m
  exact C.scheme.exploration_percolates (C.layout h).1 (C.layout h).2.1 (C.layout h).2.2
    hf.toFinset (by simp only [Set.Finite.coe_toFinset]; rfl) (C.root_seed h) (C.marks_disjoint h)
    C.p rfl (C.root_positive h hmove) h.delta_pos ((C.L+1)*C.kappa) C.contour
    h.contour_nonneg h.contour_small (mul_nonneg (by positivity) h.kappa_pos.le) h.test_error (C.prospective_estimate h hmove)

theorem moves_impossible_below_criticality (h : C.Bounds)
    (hp : C.p<C.graph.criticalProbability)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) : False :=
  (not_le_of_gt hp) (C.graph.criticalProbability_le_of_pos (C.moves_force_percolation h hmove))

end CriticalPercolation.Corridor.CoordinateData
end
end
end

end OAI
