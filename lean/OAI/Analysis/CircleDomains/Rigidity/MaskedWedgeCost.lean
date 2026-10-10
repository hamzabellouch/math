import OAI.Analysis.CircleDomains.Modulus.FiniteWedgeCosts

namespace OAI

/-!
# Random wedge cost on different coordinate masks

Each pair is integrated on the intersection of its two masks. Thus
the original fields need square-integrable norm only on their own masks.
The same independent-shift estimate controls this actual masked cost.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def maskedStaircaseCost {X P : Type*} [MeasurableSpace X] [Fintype P]
    (μ : Measure X) {n : ℕ} (pairs : P → Fin n × Fin n) (M : Fin n → Set X)
    (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ) (h δ : ℝ) (θ : Fin n → ℝ) : ℝ :=
  ∑ p, staircasePairCost (μ.restrict (M (pairs p).1 ∩ M (pairs p).2))
    u c x χ h δ (pairs p).1 (pairs p).2 θ

theorem abs_wedge_indicators {X : Type*} (A B : Set X) (u v : X → ℝ × ℝ) (z : X) :
    |planarWedge (A.indicator u z) (B.indicator v z)| =
      (A ∩ B).indicator (fun z => |planarWedge (u z) (v z)|) z := by
  by_cases ha : z ∈ A <;> by_cases hb : z ∈ B <;>
    simp [ha, hb, planarWedge]

theorem integral_abs_wedge_indicators {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (u v : X → ℝ × ℝ) :
    (∫ z, |planarWedge (A.indicator u z) (B.indicator v z)| ∂μ) =
      ∫ z in A ∩ B, |planarWedge (u z) (v z)| ∂μ := by
  simp_rw [abs_wedge_indicators]
  exact integral_indicator (hA.inter hB)

theorem maskedStaircaseCost_nonneg
    {X P : Type*} [MeasurableSpace X] [Fintype P] (μ : Measure X) {n : ℕ}
    (pairs : P → Fin n × Fin n) (M : Fin n → Set X)
    (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ) (h δ : ℝ) (θ : Fin n → ℝ) :
    0 ≤ maskedStaircaseCost μ pairs M u c x χ h δ θ :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))

theorem integrable_maskedStaircaseCost_and_mean_le
    {X P : Type*} [MeasurableSpace X] [Fintype P] {μ : Measure X} [SFinite μ] {n : ℕ}
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (M : Fin n → Set X) (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ)
    (hu : ∀ i, Measurable (u i)) (hc : Measurable c)
    (hx : ∀ i, Measurable (x i)) (hχ : Measurable χ)
    (hu2 : ∀ i, MemLp (u i) 2 (μ.restrict (M i))) (hc2 : MemLp c 2 μ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1) :
    Integrable (maskedStaircaseCost μ pairs M u c x χ h δ)
        (Measure.pi (fun _ : Fin n => shiftLaw h)) ∧
      (∫ θ, maskedStaircaseCost μ pairs M u c x χ h δ θ
        ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
        (∑ p, ∫ z in M (pairs p).1 ∩ M (pairs p).2,
          |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂μ) +
          h * (∑ p, ∫ z in M (pairs p).1 ∩ M (pairs p).2,
            |planarWedge (u (pairs p).1 z) (c z)| +
              |planarWedge (c z) (u (pairs p).2 z)| ∂μ) := by
  let ν : P → Measure X := fun p => μ.restrict (M (pairs p).1 ∩ M (pairs p).2)
  have hui p : MemLp (u (pairs p).1) 2 (ν p) :=
    (hu2 _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have huj p : MemLp (u (pairs p).2) 2 (ν p) :=
    (hu2 _).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  have hci p : MemLp c 2 (ν p) := hc2.mono_measure Measure.restrict_le_self
  have hbase p := integrable_abs_planarWedge_of_memLp (hui p) (huj p)
  have herr p := (integrable_abs_planarWedge_of_memLp (hui p) (hci p)).add
    (integrable_abs_planarWedge_of_memLp (hci p) (huj p))
  have hb p := (hbase p).add ((herr p).const_mul h)
  have hi p := integrable_staircasePairCost u c x χ hu hc hx hχ
    hh hδ hδh hχ0 hχ1 (hpairs p) (hb p)
  refine ⟨integrable_finsetSum _ (fun p _ => hi p), ?_⟩
  unfold maskedStaircaseCost
  rw [integral_finsetSum _ (fun p _ => hi p)]
  calc
    _ ≤ ∑ p, ∫ z, |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| +
        h * (|planarWedge (u (pairs p).1 z) (c z)| +
          |planarWedge (c z) (u (pairs p).2 z)|) ∂ν p := by
      apply Finset.sum_le_sum
      intro p _
      exact expected_integrated_grid_pair_wedge_le (hpairs p)
        (u (pairs p).1) (u (pairs p).2) c (x (pairs p).1) (x (pairs p).2) χ
        hh hδ hδh hχ0 hχ1
        (integrable_staircase_pair_density _ _ _ _ _ _
          (hu _) (hu _) hc (hx _) (hx _) hχ hh hδ hδh hχ0 hχ1 (hb p)) (hb p)
    _ = (∑ p, ((∫ z, |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂ν p) +
        h * (∫ z, |planarWedge (u (pairs p).1 z) (c z)| +
          |planarWedge (c z) (u (pairs p).2 z)| ∂ν p))) := by
      apply Finset.sum_congr rfl
      intro p _
      exact (integral_add (hbase p) ((herr p).const_mul h)).trans
        (congrArg (fun t => (∫ z, |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂ν p) + t)
          (integral_const_mul h _))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
