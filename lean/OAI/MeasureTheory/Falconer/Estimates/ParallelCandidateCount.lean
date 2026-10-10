import OAI.MeasureTheory.Falconer.Recursion.ProductRetainedStrip
import OAI.MeasureTheory.Falconer.Recursion.InheritedEligibleWitness

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem common_strip_relative_bound (z x y : Plane) (u w : UnitCircle)
    {b D d : ℝ} (_ : 0 ≤ D) (hd : 0 ≤ d)
    (hx : |inner ℝ (quarterTurn (u:Plane)) (z-x)| ≤ b)
    (hy : |inner ℝ (quarterTurn (u:Plane)) (z-y)| ≤ b)
    (hxy : dist x y ≤ D) (huw : dist u w ≤ d) :
    |planeDot (x-y) (quarterTurn (w:Plane))| ≤ 2*b+D*d := by
  have he : inner ℝ (quarterTurn (u:Plane)) (x-y) =
      inner ℝ (quarterTurn (u:Plane)) (z-y) - inner ℝ (quarterTurn (u:Plane)) (z-x) := by
    rw [← inner_sub_right]
    congr 1
    abel
  have hbase : |inner ℝ (quarterTurn (u:Plane)) (x-y)| ≤ 2*b := by
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add hy hx).trans_eq (by ring))
  have hnorm : ‖quarterTurn ((w:Plane)-(u:Plane))‖ ≤ d := by
    rw [graph_quarterTurn_norm,← dist_eq_norm,dist_comm]
    exact huw
  have herr : |inner ℝ (quarterTurn ((w:Plane)-(u:Plane))) (x-y)| ≤ D*d := by
    apply (abs_real_inner_le_norm _ _).trans
    rw [← dist_eq_norm]
    exact (mul_le_mul hnorm hxy (dist_nonneg) hd).trans_eq (mul_comm _ _)
  have hw : quarterTurn (w:Plane) = quarterTurn (u:Plane)+quarterTurn ((w:Plane)-(u:Plane)) := by
    rw [quarterTurn_sub]
    abel
  rw [planeDot_eq_inner,real_inner_comm,hw,inner_add_left]
  exact (abs_add_le _ _).trans (add_le_add hbase herr)

theorem parallel_candidates_le_good_test
    (Q : DyadicSquare) (hQ : 0 < Q.side) (hQs : Q.side ≤ 1) (ρ : Measure Plane)
    (g p : ℕ) (A : CellPath) (hA : A.length = g) (S : Finset CellPath)
    (hS : S ⊆ occupiedAnchorPaths Q ρ p)
    (hparent : ∀ c ∈ S, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier)
    (z : Plane) (u : UnitCircle) {θ b W threshold : ℝ} (hθ : 0 < θ) (hcap : θ ≤ 2*Real.pi)
    (j : ℕ) (hu : u ∈ tsupport (circleAngularBin (angularBinCount θ) j))
    (hstrip : ∀ c ∈ S, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ b)
    (hwidth : 2*b+(2/(2:ℝ)^g)*(4*θ) ≤ W) (hthreshold : 0 ≤ threshold)
    (hgood : ∀ c ∈ S, ∃ w ∈ tsupport (circleAngularBin (angularBinCount θ) j),
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
          (circleAngularBin_scale_diameter hθ hcap j hu hw)).trans hwidth
    have hcard : S.card ≤ parallelTestCount Q ρ g p c₀ W (w:Plane) := Finset.card_le_card hsub
    exact (Nat.cast_le.mpr hcard).trans hgoodw
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa only [Finset.card_empty,Nat.cast_zero] using hthreshold

theorem uniform_inherited_parallel_candidates {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (h : Plane → ℂ), ∀ e ∈ S, ∀ g p : ℕ,
    d e = .parallel g p → g ≤ p → p ≤ N →
    ∀ A : CellPath, A.length = g → ∀ C : Finset CellPath,
    C ⊆ occupiedAnchorPaths Q ρ p →
    (∀ c ∈ C, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier) →
    ∀ (z : Plane) (u : UnitCircle) (θ b : ℝ), 0 < θ → θ ≤ 2*Real.pi →
    ∀ j : ℕ, u ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    (∀ c ∈ C, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ b) →
    2*b+(2/(2:ℝ)^g)*(4*θ) ≤ sourceAngularWidth N sig J (i+1) p →
    (∀ c ∈ C, AngularLabelEligible ρ (Q.descendant c).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) (angularBinCount θ) j) →
    (C.card : ℝ) ≤ ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) g p+2000*(lam+sig)) := by
  obtain ⟨N₀,hgood⟩ := uniform_inherited_eligible_good_witness hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i h e he g p hd hgp hp A hA C hC hparent
    z u θ b hθ hcap j hu hstrip hwidth hel
  apply parallel_candidates_le_good_test Q (by rw [hQ]; norm_num) hQ.le ρ g p A hA C hC hparent
    z u hθ hcap j hu hstrip hwidth (by positivity)
  intro c hc
  have hh := hgood N hN S d k Q hQ ρ m lam i h e he (by simpa only [hd,ValidDescriptor] using And.intro hgp hp)
    c (by simpa only [hd,descriptorAnchor] using hC hc) (angularBinCount θ) j (hel c hc)
  simpa only [hd,descriptorGoodSet] using hh

end PlanarFalconer

end OAI
