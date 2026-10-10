import OAI.MeasureTheory.Falconer.Estimates.ComparableComplexRebin
import OAI.MeasureTheory.Falconer.Angular.ActualStationaryProductKernel
import OAI.MeasureTheory.Falconer.Angular.ActualFourStationarySupport
import OAI.MeasureTheory.Falconer.Angular.AngularComparableCarrier

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_comparable_shell_rebin {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K o : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : Fin 2 → ℝ → ℝ) (q a₀ t₀ a d n v : ℕ),
    0 < q → a₀ ≤ a+n → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m l t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (lam : Fin 2 → ℝ) (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m l)
      N (lam l) sig J (i l) (hsp l)
    let good := fun l => positiveDistanceGoodSet (Q l) (ρ l) (m l) N q (a+n) v (lam l) sig J (i l+1)
    ‖∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
      ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
        if ¬ angularNear (Q 0) (Q 1) (a+d) row col then
          ∫ x in angularLengthShell (a+n), angularStationarySpatialKernel (β 0) (β 1) o v Ψ x
            ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
        else 0‖ₑ ≤
    (ENNReal.ofReal H * ENNReal.ofReal ((2:ℝ)^(-((v:ℝ)-(a+n:ℕ))))) *
      ∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n,
        ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n,
          if angularSeparated (Q 0) (Q 1) (a+n) row col then
            ∫⁻ x in angularLengthShell (a+n),
              (fourPairGood (good 0) (good 1)).indicator (distanceDifferenceKernel v) x
                ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
          else 0 := by
  obtain ⟨H,hH,N₁,h₁⟩ := uniform_actual_stationary_product_kernel hΨ hsΨ hsig K o
  obtain ⟨N₂,h₂⟩ := uniform_actual_four_approximant_good hsig hJ
  refine ⟨H,hH,max N₁ N₂,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a d n v hq ha₀ ht hv S k hS hcard hK L hL
    L₀ hvh hLL hL₀ lam i hsp hspb A B hA hB
  let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m l)
    N (lam l) sig J (i l) (hsp l)
  let good := fun l => positiveDistanceGoodSet (Q l) (ρ l) (m l) N q (a+n) v (lam l) sig J (i l+1)
  have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  dsimp only
  convert angular_complex_shell_rebin (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1) A B a d n hA hB
    (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)
    (angularStationarySpatialKernel (β 0) (β 1) o v Ψ) (distanceDifferenceKernel v)
    (fourPairGood (good 0) (good 1))
    (measurable_fourPairGood (measurable_positiveDistanceGoodSet _ _ _ _ _ _ _ _ _ _ _)
      (measurable_positiveDistanceGoodSet _ _ _ _ _ _ _ _ _ _ _))
    (ENNReal.ofReal H * ENNReal.ofReal ((2:ℝ)^(-((v:ℝ)-(a+n:ℕ))))) (by finiteness) ?_ ?_ using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro row hr
    apply Finset.sum_congr rfl
    intro col hc
    by_cases hg : ¬ angularNear (Q 0) (Q 1) (a+d) row col <;> simp only [hg,↓reduceIte,β]
  · intro row hr col hc hfar
    have hf := angular_comparable_far_ae (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1) (a+d) row col
      (sourceProductVertices_subset _ _ _ _ _ _ a d hA hB hr)
      (sourceProductVertices_subset _ _ _ _ _ _ a d hA hB hc) hfar
    have hf' := ae_restrict_of_ae_restrict_of_subset (show angularLengthShell (a+n) ⊆
      angularLengthComparable from inter_subset_left) hf
    filter_upwards [hf',ae_restrict_mem (measurable_angularLengthShell (a+n))] with x hx hs
    have hl := angularLengthShell_lengths (a+n) hs
    have hd : ∀ l : Fin 2, (2:ℝ)^(-(a+n:ℕ):ℝ) ≤ ‖(![x 0,x 2] : Fin 2 → Plane) l-(![x 1,x 3] : Fin 2 → Plane) l‖ := by
      intro l
      have hp : 0 < (2:ℝ)^(-(a+n:ℕ):ℝ) := by positivity
      fin_cases l
      · change (2:ℝ)^(-((a+n:ℕ):ℝ)) ≤ ‖x 0-x 1‖
        rw [← dist_eq_norm]
        linarith [hl.1.1]
      · change (2:ℝ)^(-((a+n:ℕ):ℝ)) ≤ ‖x 2-x 3‖
        rw [← dist_eq_norm]
        linarith [hl.2.1]
    have hD : ∀ l : Fin 2, sourceSymbolScale N sig L^2 ≤
        (2:ℝ)^(v:ℝ)*‖(![x 0,x 2] : Fin 2 → Plane) l-(![x 1,x 3] : Fin 2 → Plane) l‖ := by
      intro l
      apply sourceSymbolScale_far_frequency_le hsig.le N L hvh hLL hL₀
      fin_cases l
      · exact hx.1
      · exact hx.2
    have he := h₁ N ((le_max_left _ _).trans hN) S (fun _ => id) k hcard hK L hL
      Q hQp ρ m lam (fun _ => J) i hsp ![x 0,x 2] ![x 1,x 3]
      (fun l => hspb l _) (fun l => hspb l _) v (a+n:ℕ) hd hD
    have hxvec : (![x 0,x 1,x 2,x 3] : Fin 4 → Plane) = x := by ext j; fin_cases j <;> rfl
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,hxvec,← dist_eq_norm] at he
    rw [← ofReal_norm]
    have he' := ENNReal.ofReal_le_ofReal he
    convert he' using 1
    dsimp [distanceDifferenceKernel]
    rw [← ENNReal.ofReal_mul hH,← ENNReal.ofReal_mul (mul_nonneg hH (by positivity))]
    congr 1
    ring
  · intro row hr col hc hfar
    let X : Fin 4 → Set Plane := ![((Q 0).descendant row.1).carrier,((Q 0).descendant col.1).carrier,
      ((Q 1).descendant row.2).carrier,((Q 1).descendant col.2).carrier]
    have hs := h₂ N ((le_max_right _ _).trans hN) Q hQ ρ hcarry m q a₀ t₀ a (a+n) v
      hq ha₀ ht (Nat.le_add_right _ _) hv S k hS lam i hsp X
    have hs' : ∀ᵐ x ∂(angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col).restrict
        (angularLengthShell (a+n)), ∀ (o : ℕ) (w : ℝ) (Ψ : ℝ → ℝ),
        (∀ t, Ψ t ≠ 0 → 0 < t) → x 0 ≠ x 1 → x 2 ≠ x 3 →
        angularStationarySpatialKernel (β 0) (β 1) o w Ψ x ≠ 0 →
        (x 0,x 1) ∈ good 0 ∧ (x 2,x 3) ∈ good 1 := ae_restrict_of_ae hs
    filter_upwards [hs',ae_restrict_mem (measurable_angularLengthShell (a+n))] with x hx hshell
    have hl := angularLengthShell_lengths (a+n) hshell
    have hp : 0 < 256*(2:ℝ)^(-(a+n:ℕ):ℝ) := by positivity
    exact hx o v Ψ (fun t ht => lt_trans (by norm_num) (hsΨ t ht).1)
      (dist_pos.mp (hp.trans hl.1.1)) (dist_pos.mp (hp.trans hl.2.1))

end PlanarFalconer

end OAI
