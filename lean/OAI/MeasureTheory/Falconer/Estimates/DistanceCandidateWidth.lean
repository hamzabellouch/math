import OAI.MeasureTheory.Falconer.Angular.RotatedParallelCandidates
import OAI.MeasureTheory.Falconer.Estimates.ProductCandidateWidth

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_distance_candidate_width {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p J i : ℕ, 0 < J → i < J →
    ∀ c₀ : ℝ, 0 < c₀ →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    2*(14028*(2:ℝ)^(-(a:ℝ))*θ)+(2/(2:ℝ)^a)*(4*θ) ≤
      sourceAngularWidth N sig J (i+1) p := by
  obtain ⟨N₁,hsmall⟩ := graph_representative_error_small hsig (C := 28064) (by norm_num)
  obtain ⟨N₂,hwidth⟩ := uniform_product_candidate_width hsig
  refine ⟨max N₁ N₂,?_⟩
  intro N hN a p J i hJ hi c₀ hc
  dsimp only
  let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
  have hθ : 0 ≤ θ := (graphAngularScale_pos N sig _ hc).le
  have hs := hsmall N ((le_max_left _ _).trans hN) a p θ
    (28064*(2:ℝ)^(-(a:ℝ))) hθ (by positivity) (min_le_right _ _) le_rfl
  have hw := hwidth N ((le_max_right _ _).trans hN) a a p J i le_rfl hJ hi c₀ hc
  have he : 2*(14028*(2:ℝ)^(-(a:ℝ))*θ)+(2/(2:ℝ)^a)*(4*θ) =
      θ*(28064*(2:ℝ)^(-(a:ℝ))) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    ring
  rw [he]
  have hp : 0 ≤ (2:ℝ)^(-(p:ℝ)) := by positivity
  have hS : 0 ≤ graphNonedgeThreshold N sig p := by unfold graphNonedgeThreshold; positivity
  have hv : 0 ≤ (2/(2:ℝ)^a)*(4*θ) := by positivity
  change 20*(2:ℝ)^(-(p:ℝ))+_ ≤ graphNonedgeThreshold N sig p/2 at hs
  change 2*(5*graphNonedgeThreshold N sig p)+(2/(2:ℝ)^a)*(4*θ) ≤ _ at hw
  linarith

theorem uniform_inherited_distance_candidates {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ), i < J → ∀ h : Plane → ℂ, ∀ e ∈ S, ∀ a p : ℕ,
    d e = .parallel a p → a ≤ p → p ≤ N →
    ∀ A : CellPath, A.length = a → ∀ C : Finset CellPath,
    C ⊆ occupiedAnchorPaths Q ρ p →
    (∀ c ∈ C, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier) →
    ∀ X Y : DyadicSquare, 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-(a:ℝ)) → Y.side ≤ (2:ℝ)^(-(a:ℝ)) →
    dist X.center Y.center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    (Q.descendant A).carrier ⊆ X.carrier ∪ Y.carrier →
    ∀ z ∈ X.carrier ∪ Y.carrier, ∀ (u : UnitCircle) (axis c₀ : ℝ),
    0 < c₀ → c₀ ≤ 2*Real.pi →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    ∀ (j : ℕ) (flip : Bool),
    sourceCircleRotate (-axis) u ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    (∀ c ∈ C, AngularBinActive (angularBinCount θ) j
      (sourceCircleRotate (-axis) (if flip then sourceRadialUnit z (Q.descendant c).center
        else sourceRadialUnit (Q.descendant c).center z)) (3*θ)) →
    (∀ c ∈ C, RotatedAngularLabelEligible ρ (Q.descendant c).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) (angularBinCount θ) j axis) →
    (C.card : ℝ) ≤ ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)) := by
  obtain ⟨N₁,hcount⟩ := uniform_inherited_rotated_parallel_candidates hsig hJ
  obtain ⟨N₂,hwidth⟩ := uniform_distance_candidate_width hsig
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i hi h e he a p hd hap hp A hA C hC hparent
    X Y hX hY hXa hYa hsep hAY z hz u axis c₀ hc hcap
  dsimp only
  intro j flip hu ha hel
  let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
  have hθ := graphAngularScale_pos N sig ((p:ℝ)-a) hc
  have hθcap := (min_le_left c₀ (graphUncappedAngularScale N sig ((p:ℝ)-a))).trans hcap
  apply hcount N ((le_max_left _ _).trans hN) S d k Q hQ ρ m lam i h e he a p hd hap hp A hA C hC hparent
    z u θ (14028*(2:ℝ)^(-(a:ℝ))*θ) axis hθ hθcap j hu ?_
    (hwidth N ((le_max_right _ _).trans hN) a p J i hJ hi c₀ hc) hel
  intro c hcC
  have hcY := hAY (hparent c hcC ((Q.descendant c).center_mem (Q.descendant_side_pos (by rw [hQ]; norm_num) c)))
  have hdist := dyadic_two_parent_diameter X Y hX hY hXa hYa hsep hz hcY
  have hdirection := active_rotated_bin_direction_bound hθ hθcap axis j _ u hu (ha c hcC)
  cases flip
  · exact (radial_perpendicular_bound z (Q.descendant c).center u hdist hdirection).trans_eq (by ring)
  · have hh := radial_perpendicular_bound (Q.descendant c).center z u
      (by simpa only [dist_comm] using hdist) hdirection
    rw [show (Q.descendant c).center-z = -(z-(Q.descendant c).center) by abel,
      inner_neg_right,abs_neg] at hh
    exact hh.trans_eq (by ring)

end PlanarFalconer

end OAI
