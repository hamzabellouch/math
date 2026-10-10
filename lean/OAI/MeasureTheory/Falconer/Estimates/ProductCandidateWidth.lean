import OAI.MeasureTheory.Falconer.Estimates.ParallelCandidateCount

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_product_candidate_width {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a g p J i : ℕ, a ≤ g → 0 < J → i < J →
    ∀ c₀ : ℝ, 0 < c₀ →
      2*(5*graphNonedgeThreshold N sig p)+(2/(2:ℝ)^g)*(4*graphAngularScale N sig ((p:ℝ)-a) c₀) ≤
        sourceAngularWidth N sig J (i+1) p := by
  obtain ⟨N₁,hsmall⟩ := graph_representative_error_small hsig (C := 8) (by norm_num)
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed (by positivity : 0 < 970*sig) 11
  refine ⟨max N₁ N₂,?_⟩
  intro N hN a g p J i hag hJ hi c₀ hc
  have hgscale : 8/(2:ℝ)^g ≤ 8*(2:ℝ)^(-(a:ℝ)) := by
    rw [div_eq_mul_inv,← Real.rpow_natCast (2:ℝ) g,← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg (Nat.cast_le.mpr hag))
  have hs := hsmall N ((le_max_left _ _).trans hN) a p (graphAngularScale N sig ((p:ℝ)-a) c₀)
    (8/(2:ℝ)^g) (graphAngularScale_pos N sig _ hc).le (by positivity) (min_le_right _ _) hgscale
  change 20*(2:ℝ)^(-(p:ℝ))+_ ≤ graphNonedgeThreshold N sig p/2 at hs
  have hnorm : 11*graphNonedgeThreshold N sig p ≤ (1/(2:ℝ)^p)*((2:ℝ)^N)^(1000*sig) := by
    have hh := mul_le_mul_of_nonneg_right (hconst N ((le_max_right _ _).trans hN))
      (by positivity : 0 ≤ (2:ℝ)^(-(p:ℝ))*((2:ℝ)^N)^(30*sig))
    have he : ((2:ℝ)^N)^(970*sig)*((2:ℝ)^N)^(30*sig) = ((2:ℝ)^N)^(1000*sig) := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
      congr 1
      ring
    calc
      _ ≤ ((2:ℝ)^N)^(970*sig)*((2:ℝ)^(-(p:ℝ))*((2:ℝ)^N)^(30*sig)) := hh
      _ = (2:ℝ)^(-(p:ℝ))*((2:ℝ)^N)^(1000*sig) := by rw [mul_left_comm,he]
      _ = _ := by rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  have hiR : ((i+1:ℕ):ℝ)/(J:ℝ) ≤ 1 :=
    (div_le_one (by exact_mod_cast hJ)).mpr (by exact_mod_cast hi)
  have hw : (1/(2:ℝ)^p)*((2:ℝ)^N)^(1000*sig) ≤ sourceAngularWidth N sig J (i+1) p := by
    unfold sourceAngularWidth
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) (by positivity)) (by positivity)
  apply le_trans _ (hnorm.trans hw)
  have hspos : 0 ≤ graphNonedgeThreshold N sig p := by unfold graphNonedgeThreshold; positivity
  have hp : 0 ≤ (2:ℝ)^(-(p:ℝ)) := by positivity
  rw [show (2/(2:ℝ)^g)*(4*graphAngularScale N sig ((p:ℝ)-a) c₀) =
    graphAngularScale N sig ((p:ℝ)-a) c₀*(8/(2:ℝ)^g) by ring]
  nlinarith

theorem uniform_inherited_product_group_count {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ), i < J → ∀ h : Plane → ℂ, ∀ e ∈ S, ∀ a g p : ℕ,
    d e = .parallel g p → a ≤ g → g ≤ p → p ≤ N →
    ∀ A : CellPath, A.length = g → ∀ C : Finset CellPath,
    C ⊆ occupiedAnchorPaths Q ρ p →
    (∀ c ∈ C, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier) →
    ∀ (z : Plane) (u : UnitCircle) (c₀ : ℝ), 0 < c₀ → c₀ ≤ 2*Real.pi →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    ∀ j : ℕ, u ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    (∀ c ∈ C, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ 5*graphNonedgeThreshold N sig p) →
    (∀ c ∈ C, AngularLabelEligible ρ (Q.descendant c).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) (angularBinCount θ) j) →
    (C.card : ℝ) ≤ ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) g p+2000*(lam+sig)) := by
  obtain ⟨N₁,hcount⟩ := uniform_inherited_parallel_candidates hsig hJ
  obtain ⟨N₂,hwidth⟩ := uniform_product_candidate_width hsig
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i hi h e he a g p hd hag hgp hp A hA C hC hparent z u c₀ hc hcap
  dsimp only
  intro j hu hstrip hel
  exact hcount N ((le_max_left _ _).trans hN) S d k Q hQ ρ m lam i h e he g p hd hgp hp A hA C hC hparent
    z u _ (5*graphNonedgeThreshold N sig p) (graphAngularScale_pos N sig _ hc)
    ((min_le_left _ _).trans hcap) j hu hstrip
    (hwidth N ((le_max_right _ _).trans hN) a g p J i hag hJ hi c₀ hc) hel

end PlanarFalconer

end OAI
