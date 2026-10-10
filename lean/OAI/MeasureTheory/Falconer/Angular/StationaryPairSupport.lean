import OAI.MeasureTheory.Falconer.Angular.SignedStationaryJet
import OAI.MeasureTheory.Falconer.Fourier.InheritedSymbolSupport
import OAI.MeasureTheory.Falconer.Angular.InheritedCircleRegularity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate Topology

 theorem normalizedStationaryJet_support (j : ℕ) (f : ℝ → ℂ) (θ Λ : ℝ)
    (hn : normalizedStationaryJet j f θ Λ ≠ 0) : θ ∈ tsupport f := by
  have hd : directStationaryOperator j f θ ≠ 0 := by
    intro hz
    exact hn (by simp [normalizedStationaryJet,hz])
  apply (directStationaryExpr j).apply_tsupport f
  apply subset_tsupport
  simpa only [Function.mem_support,directStationaryExpr_apply] using hd

 theorem signedStationaryJet_support (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (θ Λ : ℝ)
    (hn : signedStationaryJet plus j f θ Λ ≠ 0) :
    (if plus then θ else θ+Real.pi) ∈ tsupport f := by
  cases plus
  · simp only [signedStationaryJet,Bool.false_eq_true,↓reduceIte,map_ne_zero] at hn
    have hh := normalizedStationaryJet_support j (fun t => conj (f (t+Real.pi))) θ Λ hn
    have hc : tsupport (fun t => conj (f (t+Real.pi))) ⊆ tsupport (fun t => f (t+Real.pi)) :=
      tsupport_comp_subset (show conj (0:ℂ) = 0 by simp) _
    exact tsupport_comp_subset_preimage f (continuous_id.add continuous_const) (hc hh)
  · simp only [signedStationaryJet,↓reduceIte] at hn ⊢
    exact normalizedStationaryJet_support j f θ Λ hn

 theorem inheritedCircleSymbol_mask_support {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) :
    tsupport (fun θ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection θ)) ⊆
      tsupport (inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x)) := by
  apply closure_mono
  intro θ ht
  simp only [Function.mem_support,inheritedCircleSymbol_comp] at ht ⊢
  intro hz
  exact ht (by simp [hz])

 theorem pair_tsupport_left_right (f g : ℝ → ℂ) :
    tsupport (fun t => f t*conj (g t)) ⊆ tsupport f ∩ tsupport g := by
  exact subset_inter tsupport_mul_subset_left
    (tsupport_mul_subset_right.trans (tsupport_comp_subset (show conj (0:ℂ) = 0 by simp) g))

 theorem uniform_actual_pair_jet_good {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (h : Plane → ℂ) (x y : Plane) (plus : Bool) (j : ℕ) (θ Λ : ℝ),
    let f := fun t => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection t) *
      conj (inheritedCircleSymbol S b k Q ρ m N lam sig J i h y (sourceUnitDirection t))
    signedStationaryJet plus j f θ Λ ≠ 0 →
    ∀ a ∈ S, ValidDescriptor N (b a) →
    ∀ Px Py : CellPath,
    Px ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (b a)) →
    Py ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (b a)) →
    x ∈ (Q.descendant Px).carrier → y ∈ (Q.descendant Py).carrier →
    sourceUnitDirection θ ∈ descriptorGoodSet Q ρ m N lam sig J (i+1) Px (b a) ∧
    sourceUnitDirection θ ∈ descriptorGoodSet Q ρ m N lam sig J (i+1) Py (b a) := by
  obtain ⟨N₀,h₀⟩ := uniform_inheritedMaskProduct_support hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S b k Q hQ ρ m lam i h x y plus j θ Λ f hn a ha hb Px Py hPx hPy hx hy
  have ht := signedStationaryJet_support plus j f θ Λ hn
  have hpair := pair_tsupport_left_right
    (fun t => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection t))
    (fun t => inheritedCircleSymbol S b k Q ρ m N lam sig J i h y (sourceUnitDirection t)) ht
  have hmx := inheritedCircleSymbol_mask_support S b k Q ρ m N lam sig J i h x hpair.1
  have hmy := inheritedCircleSymbol_mask_support S b k Q ρ m N lam sig J i h y hpair.2
  have hgx := h₀ N hN S b k Q hQ ρ m lam i (fun _ => x) 0 a ha hb Px hPx hx
  have hgy := h₀ N hN S b k Q hQ ρ m lam i (fun _ => y) 0 a ha hb Py hPy hy
  simp only [iteratedDeriv_zero] at hgx hgy
  have hh := And.intro (hgx hmx) (hgy hmy)
  change sourceUnitDirection (if plus then θ else θ+Real.pi) ∈
      descriptorGoodSet Q ρ m N lam sig J (i+1) Px (b a) ∧
    sourceUnitDirection (if plus then θ else θ+Real.pi) ∈
      descriptorGoodSet Q ρ m N lam sig J (i+1) Py (b a) at hh
  cases plus
  · simpa only [Bool.false_eq_true,↓reduceIte,sourceUnitDirection_add_pi,
      descriptorGoodSet_antipodal] using hh
  · simpa only [↓reduceIte] using hh

end PlanarFalconer

end OAI
