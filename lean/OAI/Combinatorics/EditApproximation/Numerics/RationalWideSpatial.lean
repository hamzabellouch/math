import OAI.Combinatorics.EditApproximation.Numerics.RationalWideStep

namespace OAI

/-! Spatial bounds for a literal rational refinement update. -/

namespace EditApproximation

open Finset

theorem rationalMinimum_map_spatial {ι : Type*} (indices : List ι)
    (fallback fallback' charge : ℚ) (value value' : ι → ℚ)
    (hfallback : fallback ≤ fallback' + charge)
    (hvalue : ∀ i ∈ indices, value i ≤ value' i + charge) :
    rationalMinimum fallback (indices.map value) ≤
      rationalMinimum fallback' (indices.map value') + charge := by
  induction indices with
  | nil => exact hfallback
  | cons i rest ih =>
    change min (value i) (rationalMinimum fallback (rest.map value)) ≤
      min (value' i) (rationalMinimum fallback' (rest.map value')) + charge
    rw [← min_add_add_right]
    exact min_le_min (hvalue i (by simp)) (ih fun j hj => hvalue j (by simp [hj]))

theorem rationalActionValue_spatial {ny : ℕ} {Child : Type*} {M : ℕ}
    (L : ℚ) (hL : 0 ≤ L) (child : Child → ℚ)
    (q q' : TargetInterval ny) (action : RationalBellmanAction (TargetInterval ny) Child M) :
    rationalActionValue (fun q r => targetEndpointDistance q r) L child q action ≤
      rationalActionValue (fun q r => targetEndpointDistance q r) L child q' action +
        L * targetEndpointDistance q q' := by
  have htriangle : (targetEndpointDistance q action.center : ℚ) ≤
      targetEndpointDistance q' action.center + targetEndpointDistance q q' := by
    exact_mod_cast targetEndpointDistance_triangle q q' action.center
  have h := mul_le_mul_of_nonneg_left htriangle hL
  dsimp only [rationalActionValue]
  linarith only [h]

theorem rationalBellman_spatial {ny : ℕ} {Child : Type*} {M : ℕ}
    (initial : TargetInterval ny → ℚ) (L : ℚ) (hL : 0 ≤ L)
    (actions : List (RationalBellmanAction (TargetInterval ny) Child M)) (child : Child → ℚ)
    (q q' : TargetInterval ny)
    (hinit : initial q ≤ initial q' + L * targetEndpointDistance q q') :
    rationalBellman initial (fun q r => targetEndpointDistance q r) L actions child q ≤
      rationalBellman initial (fun q r => targetEndpointDistance q r) L actions child q' +
        L * targetEndpointDistance q q' := by
  apply rationalMinimum_map_spatial _ _ _ _ _ _ hinit
  intro action _
  exact rationalActionValue_spatial L hL child q q' action

theorem rationalWideStepCone_spatial {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L : ℚ) (hL : 0 ≤ L)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (q q' : TargetInterval ny)
    (hinit : initial q ≤ initial q' + L * targetEndpointDistance q q') :
    rationalWideStepCone parent representatives P initial L old current groups q ≤
      rationalWideStepCone parent representatives P initial L old current groups q' +
        L * targetEndpointDistance q q' := by
  apply rationalMinimum_map_spatial _ _ _ _ _ _
    (rationalBellman_spatial initial L hL _ old q q' hinit)
  intro action _
  exact rationalActionValue_spatial L hL current q q' action

theorem rationalRefinementUpdate_le_cone (delta cone : ℚ) (online : Option ℚ) :
    rationalRefinementUpdate delta cone online ≤ cone := by
  cases online with
  | none => exact le_rfl
  | some value => exact min_le_left _ _

theorem rationalRefinementUpdate_div_lower (delta cone : ℚ) (online : Option ℚ)
    (hdelta : 0 ≤ delta) (hcone : 0 ≤ cone) :
    cone / (1 + delta) ≤ rationalRefinementUpdate delta cone online := by
  have hdiv : cone / (1 + delta) ≤ cone := div_le_self hcone (by linarith)
  cases online with
  | none => exact hdiv
  | some value => exact le_min hdiv (le_max_left _ _)

theorem rationalWideStep_spatial {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L delta : ℚ) (hL : 0 ≤ L) (hdelta : 0 ≤ delta)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (online : TargetInterval ny → List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (q q' : TargetInterval ny)
    (hinit : initial q ≤ initial q' + L * targetEndpointDistance q q')
    (hcone : 0 ≤ rationalWideStepCone parent representatives P initial L old current groups q') :
    rationalWideStep parent representatives P initial L delta old current groups (online q) q ≤
      (1 + delta) * rationalWideStep parent representatives P initial L delta old current groups (online q') q' +
        L * targetEndpointDistance q q' := by
  have hu := rationalRefinementUpdate_le_cone delta
    (rationalWideStepCone parent representatives P initial L old current groups q)
    (rationalOnlineMinimum ((online q).map (rationalActionValue (fun q r => targetEndpointDistance q r) L current q)))
  have hs := rationalWideStepCone_spatial parent representatives P initial L hL old current groups q q' hinit
  have hl := rationalRefinementUpdate_div_lower delta
    (rationalWideStepCone parent representatives P initial L old current groups q')
    (rationalOnlineMinimum ((online q').map (rationalActionValue (fun q r => targetEndpointDistance q r) L current q')))
    hdelta hcone
  have hd : (0 : ℚ) < 1 + delta := by linarith
  have hl' := (div_le_iff₀ hd).mp hl
  change _ ≤ (1 + delta) * _ + _
  dsimp only [rationalWideStep] at *
  nlinarith only [hu, hs, hl']

end EditApproximation

end OAI
