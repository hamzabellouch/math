import OAI.Analysis.LipschitzHilbert.Phase.SourceGridPrediction
import OAI.Analysis.LipschitzHilbert.Trees.SourcePathValues

namespace OAI

/-! Zero snapshot vectors do not enter the angular count. Retain the chosen
path even when its snapshot vanishes, so all relative errors use the same path. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

private theorem sum_restrict_zero {ι M : Type} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] (S : Finset ι) (F : ι → M) (hzero : ∀ i ∉ S, F i = 0) :
    (∑ i : S, F i) = ∑ i, F i := by
  rw [Finset.sum_coe_sort]
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hzero i hi)

private theorem sum_injective_nonneg {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : ι → ι') (he : Function.Injective e) (F : ι' → ℝ) (hF : ∀ i, 0 ≤ F i) :
    (∑ i, F (e i)) ≤ ∑ i, F i := by
  classical
  exact Finset.sum_le_sum_of_injOn e (fun _ _ _ _ h => he h)
    (by simp) (fun _ _ => le_rfl) (fun i _ _ => hF i)

private theorem restricted_neighborhood_mass {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (G : ι → ι → Prop) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (i : S) :
    orderMass (fun j : S => w j) (closedNeighborhood (fun j k : S => G j k) i) ≤
      orderMass w (closedNeighborhood G i) := by
  classical
  unfold orderMass
  let J := closedNeighborhood (fun j k : S => G j k) i
  have hsub : J.image Subtype.val ⊆ closedNeighborhood G i := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    rcases (mem_closedNeighborhood _ _ _).mp hk with he | hg
    · exact (mem_closedNeighborhood _ _ _).mpr (Or.inl (congrArg Subtype.val he))
    · exact (mem_closedNeighborhood _ _ _).mpr (Or.inr hg)
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at h
  exact h

/-- The graph count is needed only on nonzero snapshot children and the path.
The original prediction and its full off-path coefficient budget are preserved. -/
theorem exists_source_supported_grid_prediction :
    ∃ C L0 : ℝ, 1 ≤ C ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
      ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
      ∀ (w m : ι → ℝ), (∀ i, 0 < w i) →
      (∀ i, orderMass w (closedNeighborhood G i) ≤ m i) →
      ∀ (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
        (lam : ι → ℂ) (i₀ : ι) (D p K u freqBound θ : ℝ),
      1 ≤ D → 4 ≤ p →
      (∀ i j, i ≠ j → ¬G i j → ∀ k,
        1/(grid.width*SourceParameters.step L^(-(1/8:ℝ))) ≤
          |frequency i k-frequency j k|) →
      (∀ S : Finset ι, (∀ i ∈ S, X i ≠ 0 ∨ i = i₀) →
        (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
      (∀ i, 0 ≤ l i) → (∑ i, l i) ≤ 1 →
      (∀ i, ‖lam i‖ ≤ (w i/m i)^phaseMu D p) →
      0 ≤ K → 0 ≤ u → 0 ≤ freqBound →
      (∑ i : RemainderIndex i₀, ‖predictionCoefficients l X lam D p i‖) ≤ K*u →
      (∀ i : RemainderIndex i₀, ∀ j, |frequency i j-frequency i₀ j| ≤ freqBound) →
      0 ≤ θ → θ ≤ 1 →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ t, 0 ≤ Γ t) ∧
        (∫ t, Γ t ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ t ∈ grid.root, (1-θ)*graphPredictionValue frequency l X lam D p t+θ ≤
          Real.exp ((4*C*SourceParameters.step L^(-(1/16:ℝ))*p*K+
            p*freqBound*K*(grid.width/(grid.branching:ℝ)^level))*u)*Γ t := by
  classical
  obtain ⟨C,L0,hC,hgrid⟩ := exists_source_grid_prediction
  refine ⟨C,L0,hC,?_⟩
  intro L hL ι κ _ _ grid level hlevel G hG w m hw hm frequency l X lam i₀
    D p K u freqBound θ hD hp hsep hcard hl htotal hlam hK hu hfreq hmass hfreqBound hθ0 hθ1
  let S : Finset ι := Finset.univ.filter (fun i => X i ≠ 0 ∨ i = i₀)
  let : DecidableEq S := fun a b => Classical.propDecidable (a = b)
  have hpath : i₀ ∈ S := by simp [S]
  let path : S := ⟨i₀,hpath⟩
  have hsupport (i : ι) (hi : i ∉ S) : X i = 0 := by
    have h : X i = 0 ∧ i ≠ i₀ := by simpa [S] using hi
    exact h.1
  have hcard' (J : Finset S)
      (hJ : (J : Set S).Pairwise (fun i j => ¬G i.val j.val)) : (J.card:ℝ) ≤ D := by
    have h := hcard (J.image Subtype.val) (by
      intro i hi
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp j.property).2) (by
      intro i hi j hj hij
      obtain ⟨i',hi',rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨j',hj',rfl⟩ := Finset.mem_image.mp hj
      exact hJ hi' hj' (fun h => hij (congrArg Subtype.val h)))
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h
  let e : RemainderIndex path → RemainderIndex i₀ := fun i =>
    ⟨i.val.val, fun hi => i.property (Subtype.ext hi)⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : RemainderIndex i₀ => a.val) hij
  have hmass' : (∑ i : RemainderIndex path,
      ‖predictionCoefficients (fun i : S => l i) (fun i => X i) (fun i => lam i) D p i‖) ≤ K*u :=
    (sum_injective_nonneg e he (fun i => ‖predictionCoefficients l X lam D p i‖)
      (fun _ => norm_nonneg _)).trans hmass
  have htotal' : (∑ i : S, l i) ≤ 1 :=
    (sum_injective_nonneg Subtype.val Subtype.val_injective l hl).trans htotal
  have hm' (i : S) : orderMass (fun j : S => w j)
      (closedNeighborhood (fun j k : S => G j k) i) ≤ m i := by
    convert (restricted_neighborhood_mass S G w (fun i => (hw i).le) i).trans (hm i) using 1
    congr 1
    ext j
    simp only [mem_closedNeighborhood]
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := hgrid L hL S κ grid level hlevel
    (fun i j : S => G i j) (fun {_ _} h => hG h) (fun i : S => w i) (fun i => m i)
    (fun i => hw i) hm'
    (fun i : S => frequency i) (fun i => l i) (fun i => X i) (fun i => lam i) path
    D p K u freqBound θ hD hp
    (fun i j hij hfar k => hsep i j (fun h => hij (Subtype.ext h)) hfar k)
    hcard' (fun i => hl i) htotal' (fun i => hlam i) hK hu hfreq hmass'
    (fun i k => hfreqBound (e i) k) hθ0 hθ1
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  have heq (t : ℝ) : graphPredictionValue (fun i : S => frequency i) (fun i => l i)
      (fun i => X i) (fun i => lam i) D p t = graphPredictionValue frequency l X lam D p t := by
    unfold graphPredictionValue
    rw [diagonalFourierSum_eq_sum,diagonalFourierSum_eq_sum]
    apply congrArg₂ (energyRatio p)
    · apply congrArg (fun r : ℝ => 1+r)
      exact sum_restrict_zero S (fun i => l i*‖X i‖^p) (by
        intro i hi
        simp only [hsupport i hi,norm_zero,Real.zero_rpow (by linarith : p ≠ 0),mul_zero])
    · exact sum_restrict_zero S
        (fun i => diagonalModulation (frequency i) (predictionCoefficients l X lam D p i) t)
        (by intro i hi; simp only [predictionCoefficients,hsupport i hi,smul_zero];
            exact (diagonalModulationIsometry (frequency i) t).map_zero)
  intro t ht
  simpa only [heq] using hpoint t ht

end LipschitzHilbert

end

end OAI
