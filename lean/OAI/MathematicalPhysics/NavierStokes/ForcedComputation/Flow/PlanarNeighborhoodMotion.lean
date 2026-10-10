import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarBranchBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarDormantMargin
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NormalizedDormantVelocity

namespace OAI

/-! Exact pulse equations on positive neighborhoods of the source boxes. -/

noncomputable section
namespace ForcedComputation.PlanarHamiltonian

open ShearFlows PlanarRouting Set

theorem mem_translatedPlateau (v : Fin 2 → ℚ) (R : RationalBox 2) (δ : ℚ) (x : Plane) :
    translatedPoint v x ∈ rectanglePlateau (translatedBox v R) δ ↔
      x ∈ rectanglePlateau R δ := by
  constructor <;> intro h j
  · have hj := h j
    change (R.lower j : ℝ) - δ < x j ∧ x j < (R.upper j : ℝ) + δ
    change ((R.lower j + v j : ℚ) : ℝ) - δ < x j + (v j : ℝ) ∧
      x j + (v j : ℝ) < ((R.upper j + v j : ℚ) : ℝ) + δ at hj
    push_cast at hj
    constructor <;> linarith [hj.1, hj.2]
  · have hj := h j
    change ((R.lower j + v j : ℚ) : ℝ) - δ < x j + (v j : ℝ) ∧
      x j + (v j : ℝ) < ((R.upper j + v j : ℚ) : ℝ) + δ
    push_cast
    constructor <;> linarith [hj.1, hj.2]

theorem Pulse.translated_velocity_plateau (v : Fin 2 → ℚ) {p : Pulse} (hp : p.Valid)
    {x : Plane} (hx : x ∈ rectanglePlateau p.rectangle p.collar) (t : ℝ) :
    (p.translated v).velocity t (translatedPoint v x) = p.velocity t x := by
  have ht : translatedPoint v x ∈
      rectanglePlateau (p.translated v).rectangle (p.translated v).collar :=
    (mem_translatedPlateau v p.rectangle p.collar x).mpr hx
  change smoothPulse p.start p.finish t • (p.translated v).spatial (translatedPoint v x) = _
  rw [Pulse.spatial_on_plateau (p.translated_valid v hp) ht]
  change smoothPulse p.start p.finish t • field (p.primitive.translated v).potential (translatedPoint v x) =
    smoothPulse p.start p.finish t • p.spatial x
  rw [p.primitive.translated_field v x, p.spatial_on_plateau hp hx]

theorem Pulse.translated_hasDerivAt_plateau (v : Fin 2 → ℚ) {p : Pulse} (hp : p.Valid)
    {γ : ℝ → Plane} {t : ℝ} (hx : γ t ∈ rectanglePlateau p.rectangle p.collar)
    (hγ : HasDerivAt γ (p.velocity t (γ t)) t) :
    HasDerivAt (fun s => translatedPoint v (γ s))
      ((p.translated v).velocity t (translatedPoint v (γ t))) t := by
  rw [p.translated_velocity_plateau v hp hx]
  exact hγ.add_const (fun j => (v j : ℝ))

theorem Pulse.plateau_in_unit {p : Pulse} (hp : p.Valid) (hu : p.InUnit)
    {x : Plane} (hx : x ∈ rectanglePlateau p.rectangle p.collar) (j : Fin 2) :
    x j ∈ Ioo (0 : ℝ) 1 := by
  have hb := hu.2.2 j
  have hb' : (0 : ℝ) < (p.rectangle.lower j : ℝ) - 2 * p.collar ∧
      (p.rectangle.upper j : ℝ) + 2 * p.collar < 1 := by exact_mod_cast hb
  have hδ : (0 : ℝ) < p.collar := by exact_mod_cast hp.1
  constructor <;> linarith [(hx j).1, (hx j).2, hb'.1, hb'.2]

end ForcedComputation.PlanarHamiltonian

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting PlanarHamiltonian PlanarTiming Set

theorem branchCurve_dist_lt_collar (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x y : Plane}
    (hxy : dist y x < (branchRadius M hM b : ℝ)) (k : Fin 8) (t : ℝ) :
    dist (branchCurve M hM b y k t) (branchCurve M hM b x k t) <
      (routingCollar M hM : ℝ) / 2 := by
  have h := branchPath_dist_lt_collar M hM b hxy k
    (smoothRamp (start (branchIndices M hM b k)) (finish (branchIndices M hM b k))) t
    (smoothRamp_range _ _ _)
  change dist (((actions M hM).get (branchIndices M hM b k)).primitive.path _ _ t)
    (((actions M hM).get (branchIndices M hM b k)).primitive.path _ _ t) < _
  rw [branchIndices_get]
  exact h

theorem branchCurve_near_plateau (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x y : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier)
    (hxy : dist y x < (branchRadius M hM b : ℝ)) (k : Fin 8) (t : ℝ) :
    branchCurve M hM b y k t ∈ rectanglePlateau
      (compiledPulse M hM (branchIndices M hM b k)).rectangle
      (compiledPulse M hM (branchIndices M hM b k)).collar := by
  apply rectanglePlateau_of_dist_lt (branch_curve_mem_rectangle M hM b hx k t)
  have hd := branchCurve_dist_lt_collar M hM b hxy k t
  have hδ : (0 : ℝ) < routingCollar M hM := by exact_mod_cast routingCollar_pos M hM
  exact hd.trans (by change (routingCollar M hM : ℝ) / 2 < routingCollar M hM; linarith)

theorem normalizedCurve_ode_near (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x y : Plane}
    (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (hxy : dist y x < (branchRadius (freshMachine I.1) (freshInput_valid hI).1 b : ℝ))
    (k : Fin 8) (t : ℝ)
    (ht : t ∈ Icc
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length
        (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k).val)
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length
        ((branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k).val + 1))) :
    HasDerivAt (normalizedCurve I hI b y k)
      (planarSlice (normalizedHamiltonian I hI) t (normalizedCurve I hI b y k t)) t := by
  have hm := branchCurve_near_plateau _ _ b hx hxy k t
  have hp := compiledPulse_valid (freshMachine I.1) (freshInput_valid hI).1
    (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)
  have hd := Pulse.translated_hasDerivAt_plateau
    (initialShift (freshInput I) (freshInput_valid hI)) hp hm
    (Pulse.curve_ode_plateau hp _ t hm)
  have hm' : normalizedCurve I hI b y k t ∈ rectanglePlateau
      (normalizedPulse I hI (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).rectangle
      (normalizedPulse I hI (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).collar :=
    (mem_translatedPlateau _ _ _ _).mpr hm
  have hunit := Pulse.plateau_in_unit
    (normalizedPulse_valid I hI (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k))
    (normalizedPulse_inUnit I hI (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)) hm'
  have he := normalizedSlice_on_cell I hI
    (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k) ht
    (normalizedCurve I hI b y k t) (hunit 0) (hunit 1)
  exact hd.congr_deriv he.symm

theorem translatedPoint_dist (v : Fin 2 → ℚ) (x y : Plane) :
    dist (translatedPoint v x) (translatedPoint v y) = dist x y := by
  simp only [dist_eq_norm]
  congr 1
  funext j
  simp only [translatedPoint, Pi.sub_apply]
  ring

theorem normalizedAnchors_dist_lt_collar (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x y : Plane}
    (hxy : dist y x < (branchRadius (freshMachine I.1) (freshInput_valid hI).1 b : ℝ))
    (k : Fin 9) :
    dist (normalizedAnchors I hI b y k) (normalizedAnchors I hI b x k) <
      (routingCollar (freshMachine I.1) (freshInput_valid hI).1 : ℝ) / 2 := by
  unfold normalizedAnchors
  rw [translatedPoint_dist]
  exact branchAnchor_dist_lt_collar _ _ b hxy k

theorem routingCollar_half_lt (M : Alternating.Machine) (hM : M.WellFormed) :
    (routingCollar M hM : ℝ) / 2 < 1 / 64 := by
  have h := routingCollar_parking_bound M hM
  have hu := parkingScale_le (geometricBranches M hM).length
  have hb : routingCollar M hM / 2 < (1 / 64 : ℚ) := by linarith
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_lt (K := ℝ)).mpr hb

theorem near_clock_in_unit {x y : Plane} (hx : x ∈ clockRectangle.carrier)
    (hxy : dist y x < (1 / 64 : ℝ)) (j : Fin 2) : y j ∈ Ioo (0 : ℝ) 1 := by
  have hj : |y j - x j| < (1 / 64 : ℝ) :=
    (norm_le_pi_norm (y - x) j).trans_lt (by simpa only [dist_eq_norm] using hxy)
  obtain ⟨hl, hu⟩ := abs_lt.mp hj
  have hb := hx j
  fin_cases j <;> norm_num [clockRectangle] at hb hl hu ⊢ <;>
    constructor <;> linarith [hb.1, hb.2]

theorem normalizedAnchors_near_unit (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x y : Plane}
    (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (hxy : dist y x < (branchRadius (freshMachine I.1) (freshInput_valid hI).1 b : ℝ))
    (k : Fin 9) (j : Fin 2) : normalizedAnchors I hI b y k j ∈ Ioo (0 : ℝ) 1 :=
  near_clock_in_unit (normalizedAnchors_clock I hI b hx k)
    ((normalizedAnchors_dist_lt_collar I hI b hxy k).trans (routingCollar_half_lt _ _)) j

theorem normalized_sparseAnchor_zero_near (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x y : Plane}
    (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (hxy : dist y x < (branchRadius (freshMachine I.1) (freshInput_valid hI).1 b : ℝ))
    (i : ℕ) (hi : i < (actions (freshMachine I.1) (freshInput_valid hI).1).length + 1)
    (hne : ∀ k, (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k).val ≠ i)
    (s : ℝ) (hs : s ∈ Ico
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length i)
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length (i + 1))) :
    planarSlice (normalizedHamiltonian I hI) s
      (sparseAnchor (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b)
        (normalizedAnchors I hI b y) i) = 0 := by
  let n := (actions (freshMachine I.1) (freshInput_valid hI).1).length
  let J := branchIndices (freshMachine I.1) (freshInput_valid hI).1 b
  have hunit : ∀ j, sparseAnchor J (normalizedAnchors I hI b y) i j ∈ Ioo (0 : ℝ) 1 :=
    normalizedAnchors_near_unit I hI b hx hxy _
  by_cases hin : i < n
  · let ii : Fin n := ⟨i, hin⟩
    have hd : dist
        (sparseAnchor J (branchAnchors (freshMachine I.1) (freshInput_valid hI).1 b y) i)
        (sparseAnchor J (branchAnchors (freshMachine I.1) (freshInput_valid hI).1 b x) i) <
        (routingCollar (freshMachine I.1) (freshInput_valid hI).1 : ℝ) := by
      have hb := branchAnchor_dist_lt_collar (freshMachine I.1) (freshInput_valid hI).1 b hxy
        (⟨stagesBefore J i, lt_of_le_of_lt (stagesBefore_le J i) (by decide)⟩ : Fin 9)
      have hp : (0 : ℝ) < routingCollar (freshMachine I.1) (freshInput_valid hI).1 := by
        exact_mod_cast routingCollar_pos (freshMachine I.1) (freshInput_valid hI).1
      exact hb.trans (by linarith)
    have hm := sparseAnchor_near_notMem_collar _ _ b hx ii hne hd
    have hm' : sparseAnchor J (normalizedAnchors I hI b y) i ∉
        (rectangleCollar (normalizedPulse I hI ii).rectangle (normalizedPulse I hI ii).collar).carrier := by
      intro he
      exact hm ((mem_translated_collar _ _ _ _).mp he)
    rw [normalizedSlice_on_cell I hI ii ⟨hs.1, hs.2.le⟩ _ (hunit 0) (hunit 1)]
    exact Pulse.velocity_zero_of_notMem (normalizedPulse_valid I hI ii) hm' s
  · have he : i = n := by omega
    subst i
    apply normalizedSlice_on_tail I hI _ _ (hunit 0) (hunit 1)
    exact ⟨hs.1, (hs.2.trans_le (by rw [cut_last])).le⟩

end ForcedComputation.Recorder.Planar

end

end OAI
