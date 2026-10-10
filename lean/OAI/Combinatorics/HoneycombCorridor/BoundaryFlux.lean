import Mathlib
import OAI.Combinatorics.HoneycombCorridor.VisitRecursion

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem mem_sourceExits (D : Finset Vertex) (g : Germ) (w : List Bool) :
    w ∈ sourceExits D g ↔ Stopped D g w ∧ (terminalGerm g w).1 ∉ D := by
  classical
  simp [sourceExits,mem_leaves_iff]

theorem boundary_source_flux (D : Finset Vertex) (g : Germ)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) :
    (∑ w ∈ sourceExits D g, wordWeight w) = 1 := by
  have h := exit_add_collision D g
  rw [(boundary_collision_cancellation D g hD hg).1,add_zero] at h
  simpa only [sourceExits,Finset.sum_filter,exitSum] using h

theorem boundary_source_weight_bound (D : Finset Vertex) (g : Germ)
    (hD : AdmissiblyConvex D) (hg : g.1 ∈ D) (hg' : (reverseGerm g).1 ∉ D) :
    (∑ w ∈ sourceExits D g, criticalActivity ^ w.length) ≤
      (Real.cos (3 * Real.pi / 8))⁻¹ := by
  have hflux := boundary_source_flux D g (admissiblyConvex_filled D hD) hg'
  have hreal := congrArg Complex.re hflux
  rw [Complex.re_sum,Complex.one_re] at hreal
  have hlower : Real.cos (3 * Real.pi / 8) *
      (∑ w ∈ sourceExits D g, criticalActivity ^ w.length) ≤ 1 := by
    rw [← hreal,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w hw
    obtain ⟨hs,ht⟩ := (mem_sourceExits D g w).mp hw
    exact convex_wordWeight_re_lower D hD (g,w) ⟨hg,hg',hs,ht⟩
  have hpos : 0 < Real.cos (3 * Real.pi / 8) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hpos).mpr
  rwa [mul_comm]

theorem convex_boundary_flux : ConvexBoundaryFlux := by
  intro D g hD hg hg'
  exact ⟨boundary_source_flux D g (admissiblyConvex_filled D hD) hg',
    boundary_source_weight_bound D g hD hg hg'⟩


def bottomSource : Germ := (.up 0 0,0)

def InStrip (h : ℕ) (v : Vertex) : Prop := 0 ≤ boxIndex v 0 ∧ boxIndex v 0 < (h : ℤ)

noncomputable def reachesDistance (t : ℝ) (w : List Bool) : Prop :=
  ∃ v ∈ traced bottomSource w, t ≤ |(position v).1|

noncomputable def lateralMass (D : Finset Vertex) (t : ℝ) : ℝ := by
  classical
  exact ∑ w ∈ sourceExits D bottomSource,
    if reachesDistance t w then criticalActivity ^ w.length else 0

noncomputable def lateralLengthMass (D : Finset Vertex) (t : ℝ) : ℝ := by
  classical
  exact ∑ w ∈ sourceExits D bottomSource,
    if reachesDistance t w then (w.length : ℝ) * criticalActivity ^ w.length else 0

def FiniteLateralTail : Prop := ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (h : ℕ) (D : Finset Vertex), 1 ≤ h → AdmissiblyConvex D →
    bottomSource.1 ∈ D → (∀ v ∈ D, InStrip h v) → ∀ t : ℝ, 0 ≤ t →
    lateralMass D t ≤ C * Real.exp (-c * t / (h+1)) ∧
    lateralLengthMass D t ≤ C * (h+1) * (h+t+1) * Real.exp (-c * t / (h+1))



def directionCode (g : Germ) : ℤ := match g.1 with
  | .up _ _ => if g.2 = 0 then 0 else if g.2 = 1 then 2 else 4
  | .down _ _ => if g.2 = 0 then 3 else if g.2 = 1 then 5 else 1

theorem advance_direction (g : Germ) (b : Bool) :
    (directionCode (advance g b) - directionCode g - turnUnit b) % 6 = 0 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> cases b <;>
    rfl

theorem terminal_direction (g : Germ) (w : List Bool) :
    (directionCode (terminalGerm g w) - directionCode g - turnUnits w) % 6 = 0 := by
  induction w generalizing g with
  | nil => simp [terminalGerm,turnUnits]
  | cons b w ih =>
    have ha := advance_direction g b
    have ht := ih (advance g b)
    simp only [terminalGerm,turnUnits_cons]
    omega

theorem right_cut_direction_one (v : Vertex) (k : Fin 3) (A : ℤ)
    (hv : boxIndex v 1 < A) (hu : A ≤ boxIndex (neighbor v k) 1) :
    directionCode (neighbor v k,k) = 4 := by
  cases v <;> fin_cases k <;>
    simp [boxIndex,neighbor,directionCode] at * <;> omega

theorem right_cut_direction_two (v : Vertex) (k : Fin 3) (A : ℤ)
    (hv : boxIndex v 2 < A) (hu : A ≤ boxIndex (neighbor v k) 2) :
    directionCode (neighbor v k,k) = 5 := by
  cases v <;> fin_cases k <;>
    simp [boxIndex,neighbor,directionCode] at * <;> omega

theorem convex_source_direction_turn (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (w : List Bool) (hw : w ∈ sourceExits D bottomSource) :
    (directionCode (terminalGerm bottomSource w) = 4 → turnUnits w = -2) ∧
    (directionCode (terminalGerm bottomSource w) = 5 → turnUnits w = -1) := by
  have hb := convex_excursion_turn_bound D hD (bottomSource,w)
    ⟨hg,hg',(mem_sourceExits D bottomSource w).mp hw⟩
  change -3 ≤ turnUnits w ∧ turnUnits w ≤ 3 at hb
  have hm := terminal_direction bottomSource w
  rw [show directionCode bottomSource = 0 from rfl,sub_zero] at hm
  constructor <;> intro h <;> rw [h] at hm <;> omega

end PolynomialVacuumBridge.Corridor

end

end OAI
