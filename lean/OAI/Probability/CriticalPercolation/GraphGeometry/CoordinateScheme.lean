import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.GrowthProcess
import OAI.Probability.CriticalPercolation.Gluing.CorridorNormalization
import OAI.Probability.CriticalPercolation.Gluing.RelayScales

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct

structure CoordinateData (V E : Type*) where
  graph : BondGraph V E
  origin : V
  time : V → ℝ
  height : V → ℝ
  J : ℝ
  L : ℕ
  R : ℕ
  m : ℕ
  D : ℕ
  k : ℕ
  M : ℕ
  VM : ℕ
  e : ℝ
  rho : ℝ
  kappa : ℝ
  eta : ℝ
  delta : ℝ
  contour : ℝ
  pc : unitInterval
  p : unitInterval

namespace CoordinateData
variable {V E : Type*} (C : CoordinateData V E)

def T : ℝ := C.L+1/2

def scheme : Scheme V E where
  graph := C.graph
  coordinate := normalized C.time C.height C.T
  j := C.J/C.T
  h := 2520/C.T
  seed := C.graph.vertexBall C.origin C.m
  mark := Corridor.mark C.time C.height C.T C.rho
  parameter := fun _ => C.p
  delta := C.delta

structure Bounds : Prop where
  connected : C.graph.fullGraph.Connected
  locallyFinite : C.graph.LocallyFinite
  time_origin : C.time C.origin=0
  height_origin : C.height C.origin=0
  time_step : ∀ ⦃u v⦄, C.graph.fullGraph.Adj u v → |C.time u-C.time v|≤C.rho
  height_step : ∀ ⦃u v⦄, C.graph.fullGraph.Adj u v → |C.height u-C.height v|≤C.rho
  J_lower : 26200<C.J
  L_lower : 10*(C.J+210)<C.L
  e_pos : 0<C.e
  rho_nonneg : 0≤C.rho
  e_small : (C.L+3)*C.e<1/100
  rho_small : (C.R+C.m+1)*C.rho<C.e/10
  R_gt : C.m<C.R
  pc_pos : 0<(C.pc : ℝ)
  pc_lt : (C.pc : ℝ)<1
  p_lower : (C.pc : ℝ)/2≤C.p
  p_upper : (C.p : ℝ)≤C.pc
  degree : ∀ v, (C.graph.incidentEdges {v}).ncard≤C.D
  M_pos : 0<C.M
  M_bound : ∀ v, (C.graph.vertexBall v (4*C.m+2)).ncard≤C.M
  VM_bound : ∀ v, (C.graph.vertexBall v C.m).ncard≤C.VM
  kappa_pos : 0<C.kappa
  kappa_le : C.kappa≤1
  eta_nonneg : 0≤C.eta
  eta_small : C.eta≤C.kappa*(C.kappa/4)/(4*(Real.log (4/C.kappa)+1))
  k_large : C.M*⌈Real.log (4/C.kappa)/((C.pc : ℝ)/2)^(C.m+1+C.VM)⌉₊≤C.k
  R_large : 4/(C.kappa*(1-(C.pc : ℝ))^(C.D*C.k))<(C.R : ℝ)-C.m
  delta_pos : 0<C.delta
  root_error : 2*(C.eta+C.L*C.kappa)<C.delta
  contour_nonneg : 0≤C.contour
  contour_small : 8*C.contour<1
  test_error : C.delta+2*((C.L+1)*C.kappa)/C.delta≤C.contour^4

lemma T_pos : 0<C.T := by unfold T; positivity

lemma L_large (h : C.Bounds) : 416≤C.L := by
  have : (416 : ℝ)≤C.L := by linarith [h.J_lower,h.L_lower]
  exact_mod_cast this

lemma small_rho (h : C.Bounds) : C.rho≤C.J := by
  have he := h.e_small
  have hr := h.rho_small
  have hle : C.rho≤C.e := (relay_coordinate_scale C.L C.R C.m C.e C.rho
    h.e_pos h.rho_nonneg he hr).1
  have hLp : 0≤(C.L : ℝ)*C.e := mul_nonneg (Nat.cast_nonneg _) h.e_pos.le
  linarith [h.J_lower]

lemma layout (h : C.Bounds) :
    0≤C.scheme.h ∧ C.scheme.h≤C.scheme.j ∧ 2*C.scheme.j+C.scheme.h<1 := by
  change 0≤2520/C.T ∧ 2520/C.T≤C.J/C.T ∧ 2*(C.J/C.T)+2520/C.T<1
  refine ⟨div_nonneg (by norm_num) C.T_pos.le, (div_le_div_iff_of_pos_right C.T_pos).mpr (by linarith [h.J_lower]),?_⟩
  rw [show 2*(C.J/C.T)+2520/C.T=(2*C.J+2520)/C.T by ring,div_lt_one C.T_pos]
  dsimp [T]
  linarith [h.J_lower,h.L_lower]

lemma root_seed (h : C.Bounds) : (C.scheme.seed∩C.scheme.mark (0,0)).Nonempty := by
  refine ⟨C.origin,C.graph.mem_vertexBall_self C.origin C.m,?_⟩
  change 0≤localTime C.time C.T (0,0) C.origin ∧
    localTime C.time C.T (0,0) C.origin≤C.rho ∧ |localHeight C.height C.T (0,0) C.origin|≤210
  simp [localTime,localHeight,timeCenter,heightCenter,h.time_origin,h.height_origin,h.rho_nonneg]

lemma marks_disjoint (h : C.Bounds) : Pairwise (Disjoint on C.scheme.mark) := by
  intro v w hvw
  exact (graph_boxes_disjoint (normalized C.time C.height C.T) (C.J/C.T) (2520/C.T)
    (C.layout h).2.2 hvw).mono
    (mark_subset_box C.time C.height C.T C.J C.rho C.T_pos (by linarith [h.J_lower]) (C.small_rho h) v)
    (mark_subset_box C.time C.height C.T C.J C.rho C.T_pos (by linarith [h.J_lower]) (C.small_rho h) w)

lemma domain_eq (v : Site) (b : Bool) : C.scheme.edgeDomain (v,b)=
    C.graph.inducedEdges (relayDomain (localTime C.time C.T v) (localHeight C.height C.T v)
      C.J C.T (sign b)) := by
  change C.graph.inducedEdges (graphDomain (normalized C.time C.height C.T) (C.J/C.T) (2520/C.T) (v,b))=_
  rw [normalized_domain C.time C.height C.T C.J C.T_pos]

lemma local_time_step (h : C.Bounds) (v : Site) {u w : V} (huw : C.graph.fullGraph.Adj u w) :
    |localTime C.time C.T v u-localTime C.time C.T v w|≤C.rho := by
  simpa only [localTime,sub_sub_sub_cancel_right] using h.time_step huw

lemma local_height_step (h : C.Bounds) (v : Site) {u w : V} (huw : C.graph.fullGraph.Adj u w) :
    |localHeight C.height C.T v u-localHeight C.height C.T v w|≤C.rho := by
  simpa only [localHeight,sub_sub_sub_cancel_right] using h.height_step huw

lemma source_behind (h : C.Bounds) (n : ℕ) (hn : 0<n) :
    ∀ a∈C.scheme.seed, localTime C.time C.T (slotSite n) a≤C.m*C.rho-C.T := by
  intro a ha
  have ht := (abs_le.mp (C.graph.coordinate_ball_bound C.time C.rho h.rho_nonneg h.time_step ha)).2
  rw [h.time_origin,sub_zero] at ht
  have hv := slotSite_quadrant n
  have hnz : slotSite n≠(0,0) := by
    intro he
    have he' := congrArg gridSlot he
    rw [gridSlot_slotSite] at he'
    change n=0 at he'
    omega
  have hsumInt : 1≤(slotSite n).1+(slotSite n).2 := by
    by_contra hs
    have hx : (slotSite n).1=0 := by dsimp [quadrant] at hv; omega
    have hy : (slotSite n).2=0 := by dsimp [quadrant] at hv; omega
    exact hnz (Prod.ext hx hy)
  have hsum : (1 : ℝ)≤((slotSite n).1 : ℝ)+(slotSite n).2 := by exact_mod_cast hsumInt
  have hmul := mul_le_mul_of_nonneg_right hsum C.T_pos.le
  change C.time a-(((slotSite n).1 : ℝ)+(slotSite n).2)*C.T≤_
  linarith

end CoordinateData
end CriticalPercolation.Corridor
end
end
end

end OAI
