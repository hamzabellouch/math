import OAI.Analysis.CircleDomains.Transfer.FilledCoordinates
import OAI.Analysis.CircleDomains.Sobolev.LocalCoordinateMetric

namespace OAI

/-!
# Passing from filled coordinates to a small-energy metric

The actual pointwise wedge inequality for the patched coordinates passes
through the integral and then through metric selection. Only smoothness
near the compact completed piece is used.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def natCoordinateFamily {X : Type*} {n : ℕ} (f : Fin n → X → ℝ) : ℕ → X → ℝ :=
  fun i => if hi : i < n then f ⟨i, hi⟩ else fun _ => 0

theorem contDiffOn_natCoordinateFamily
    {n : ℕ} {Ω : Set (ℝ × ℝ)} {f : Fin n → (ℝ × ℝ) → ℝ}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω) (i : ℕ) :
    ContDiffOn ℝ ∞ (natCoordinateFamily f i) Ω := by
  by_cases hi : i < n
  · simpa only [natCoordinateFamily, dite_eq_left hi] using hf ⟨i, hi⟩
  · simp only [natCoordinateFamily, dite_eq_right hi]
    exact contDiffOn_const

theorem continuousOn_coordinateWedges
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (f : ℕ → (ℝ × ℝ) → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω) (n : ℕ) :
    ContinuousOn (coordinateWedges f n) Ω := by
  have hx (i : ℕ) : ContinuousOn (fun z => (planarGradient (f i) z).1) Ω :=
    ((hf i).fderiv_of_isOpen (m := ∞) hΩ (by simp)).continuousOn.clm_apply continuousOn_const
  have hy (i : ℕ) : ContinuousOn (fun z => (planarGradient (f i) z).2) Ω :=
    ((hf i).fderiv_of_isOpen (m := ∞) hΩ (by simp)).continuousOn.clm_apply continuousOn_const
  unfold coordinateWedges covectorWedges
  apply continuousOn_finsetSum
  intro j _
  apply continuousOn_finsetSum
  intro i _
  exact ((hx i).mul (hy j) |>.sub ((hx j).mul (hy i))).abs

theorem IsFilledCoordinateFamily.coordinateWedges_le
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {v F : Fin n → (ℝ × ℝ) → ℝ} (hF : IsFilledCoordinateFamily D Ω v F)
    (hD : ∀ i, IsOpen (D i)) (z : ℝ × ℝ) :
    coordinateWedges (natCoordinateFamily F) n z ≤
      coordinateWedges (natCoordinateFamily v) n z := by
  unfold coordinateWedges covectorWedges
  apply sum_le_sum
  intro j hj
  have hjn := mem_range.mp hj
  apply sum_le_sum
  intro i hi
  have hij := mem_range.mp hi
  have hin := hij.trans hjn
  have hne : (⟨i,hin⟩ : Fin n) ≠ ⟨j,hjn⟩ :=
    fun heq => (Nat.ne_of_lt hij) (congrArg Fin.val heq)
  simpa only [natCoordinateFamily, dite_eq_left hin, dite_eq_left hjn, planarWedge, mul_comm]
    using hF.abs_wedge_le hD ⟨i,hin⟩ ⟨j,hjn⟩ hne z

/-- The completed coordinates admit an actual smooth positive definite
metric retaining the original metric near the core and satisfying the
same strict wedge-derived energy budget. -/
theorem IsFilledCoordinateFamily.exists_small_energy_metric
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)}
    {Ω Q K U : Set (ℝ × ℝ)} {v F : Fin n → (ℝ × ℝ) → ℝ}
    (hF : IsFilledCoordinateFamily D Ω v F) (hD : ∀ i, IsOpen (D i))
    (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hv : IntegrableOn (fun z => 2 * coordinateWedges (natCoordinateFamily v) n z) (Q \ K))
    {ε : ℝ} (hε : (∫ z in Q \ K, 2 * coordinateWedges (natCoordinateFamily v) n z) < ε) :
    ∃ (τ : ℝ) (N : Set (ℝ × ℝ)) (g : (ℝ × ℝ) → PlanarMetric),
      0 < τ ∧ IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧ (∀ᶠ z in 𝓝ˢ K, g z = 1) ∧
      (∀ z ∈ Q \ N, g z = coordinateGram (natCoordinateFamily F) n z + τ • 1) ∧
      (∫ z in Q \ K, matrixEnergy (coordinateGram (natCoordinateFamily F) n z) (g z)) < ε := by
  have hFs := contDiffOn_natCoordinateFamily hF.1
  have hFi : IntegrableOn (fun z => 2 * coordinateWedges (natCoordinateFamily F) n z) (Q \ K) :=
    (((continuousOn_coordinateWedges hΩ _ hFs n).const_mul 2).mono hQΩ
      |>.integrableOn_compact hQ).mono_set sdiff_subset
  have hbudget : (∫ z in Q \ K, 2 * coordinateWedges (natCoordinateFamily F) n z) < ε :=
    lt_of_le_of_lt
      (setIntegral_mono_on hFi hv (hQ.isClosed.measurableSet.diff hK.isClosed.measurableSet)
        (fun z _ => mul_le_mul_of_nonneg_left (hF.coordinateWedges_le hD z) (by norm_num))) hε
  exact exists_metric_for_local_coordinates _ n hΩ hQ hQΩ hFs hK hU hKU hbudget

end CircleDomainRigidity.FiniteTransfer

end

end OAI
