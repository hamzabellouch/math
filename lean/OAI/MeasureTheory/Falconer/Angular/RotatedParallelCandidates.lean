import OAI.MeasureTheory.Falconer.Estimates.DistanceActivityStrip
import OAI.MeasureTheory.Falconer.Angular.RotatedGraphEligibility

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem rotated_parallel_candidates_le_good_test
    (Q : DyadicSquare) (hQ : 0 < Q.side) (hQs : Q.side ≤ 1) (ρ : Measure Plane)
    (g p : ℕ) (A : CellPath) (hA : A.length = g) (S : Finset CellPath)
    (hS : S ⊆ occupiedAnchorPaths Q ρ p)
    (hparent : ∀ c ∈ S, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier)
    (z : Plane) (u : UnitCircle) {θ b W threshold : ℝ} (hθ : 0 < θ) (hcap : θ ≤ 2*Real.pi)
    (axis : ℝ) (j : ℕ) (hu : sourceCircleRotate (-axis) u ∈ tsupport (circleAngularBin (angularBinCount θ) j))
    (hstrip : ∀ c ∈ S, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ b)
    (hwidth : 2*b+(2/(2:ℝ)^g)*(4*θ) ≤ W) (hthreshold : 0 ≤ threshold)
    (hgood : ∀ c ∈ S, ∃ w, sourceCircleRotate (-axis) w ∈ tsupport (circleAngularBin (angularBinCount θ) j) ∧
      w ∈ parallelGoodSet Q ρ g p c W threshold) :
    (S.card : ℝ) ≤ threshold := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨c₀,hc₀⟩ := hne
    obtain ⟨w,hw,hgoodw⟩ := hgood c₀ hc₀
    have hside : (Q.descendant A).side ≤ 1/(2:ℝ)^g := by
      rw [DyadicSquare.descendant_side,hA]
      exact div_le_div_of_nonneg_right hQs (by positivity)
    have hd (c : CellPath) (hc : c ∈ S) :
        dist (Q.descendant c).center (Q.descendant c₀).center ≤ 2/(2:ℝ)^g := by
      apply ((Q.descendant A).dist_le (Q.descendant_side_pos hQ A).le
        (hparent c hc ((Q.descendant c).center_mem (Q.descendant_side_pos hQ c)))
        (hparent c₀ hc₀ ((Q.descendant c₀).center_mem (Q.descendant_side_pos hQ c₀)))).trans
      exact (mul_le_mul_of_nonneg_left hside (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
    have hsub : S ⊆ (parallelTestCells Q ρ g p c₀).filter (fun c =>
        |planeDot ((Q.descendant c).center-(Q.descendant c₀).center) (quarterTurn (w:Plane))| ≤ W) := by
      intro c hc
      obtain ⟨hlen,hocc⟩ := Finset.mem_filter.mp (hS hc)
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨hlen,hocc,?_⟩
        exact (hd c hc).trans_lt (div_lt_div_of_pos_right (by norm_num : (2:ℝ) < 10) (by positivity))
      · exact (common_strip_relative_bound z (Q.descendant c).center (Q.descendant c₀).center u w
          (by positivity) (by positivity) (hstrip c hc) (hstrip c₀ hc₀) (hd c hc)
          (by simpa only [sourceCircleRotate_dist] using
            circleAngularBin_scale_diameter hθ hcap j hu hw)).trans hwidth
    have hcard : S.card ≤ parallelTestCount Q ρ g p c₀ W (w:Plane) := Finset.card_le_card hsub
    exact (Nat.cast_le.mpr hcard).trans hgoodw
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa only [Finset.card_empty,Nat.cast_zero] using hthreshold

theorem uniform_inherited_rotated_parallel_candidates {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (h : Plane → ℂ), ∀ e ∈ S, ∀ a p : ℕ,
    d e = .parallel a p → a ≤ p → p ≤ N →
    ∀ A : CellPath, A.length = a → ∀ C : Finset CellPath,
    C ⊆ occupiedAnchorPaths Q ρ p →
    (∀ c ∈ C, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier) →
    ∀ (z : Plane) (u : UnitCircle) (θ b axis : ℝ), 0 < θ → θ ≤ 2*Real.pi →
    ∀ j : ℕ, sourceCircleRotate (-axis) u ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    (∀ c ∈ C, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ b) →
    2*b+(2/(2:ℝ)^a)*(4*θ) ≤ sourceAngularWidth N sig J (i+1) p →
    (∀ c ∈ C, RotatedAngularLabelEligible ρ (Q.descendant c).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) (angularBinCount θ) j axis) →
    (C.card : ℝ) ≤ ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)) := by
  obtain ⟨N₀,hgood⟩ := uniform_inheritedCircleSymbol_good hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i h e he a p hd hap hp A hA C hC hparent
    z u θ b axis hθ hcap j hu hstrip hwidth hel
  apply rotated_parallel_candidates_le_good_test Q (by rw [hQ]; norm_num) hQ.le ρ a p A hA C hC hparent
    z u hθ hcap axis j hu hstrip hwidth (by positivity)
  intro c hc
  obtain ⟨w,hw,x,hx,hn,_⟩ := rotated_eligible_label_witness (Q.descendant c).measurable
    (hel c hc) (fun _ _ => True) (fun _ => Filter.Eventually.of_forall (fun _ _ => True.intro))
  refine ⟨w,hw,?_⟩
  have hg := hgood N hN S d k Q hQ ρ m lam i h e he
    (by simpa only [hd,ValidDescriptor] using And.intro hap hp)
    c (by simpa only [hd,descriptorAnchor] using hC hc) x hx w hn
  simpa only [hd,descriptorGoodSet] using hg

end PlanarFalconer

end OAI
