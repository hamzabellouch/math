import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTrimming
import OAI.Analysis.IrrationalRotation.Product.ProductScaleTail

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel.TailTrimming

theorem tsum_outside_range_ofReal (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθsum : Summable θ) (d : ℕ) :
    (∑' i : {i : ℕ // i ∉ Finset.range d}, ENNReal.ofReal (θ i)) =
      ENNReal.ofReal (∑' k, θ (d + k)) := by
  let e : ℕ ≃ {i : ℕ // i ∉ Finset.range d} := Equiv.ofBijective
    (fun k => ⟨d + k, by simp⟩) (by
      constructor
      · intro i j hij
        have h := congrArg Subtype.val hij
        exact Nat.add_left_cancel h
      · intro i
        refine ⟨i.val - d, ?_⟩
        apply Subtype.ext
        have hi := i.property
        simp only [Finset.mem_range, not_lt] at hi
        dsimp
        omega)
  rw [← e.tsum_eq (fun i => ENNReal.ofReal (θ i))]
  change (∑' k, ENNReal.ofReal (θ (d + k))) = _
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => hθ0 _)
    (hθsum.comp_injective (fun _ _ h => Nat.add_left_cancel h))).symm

theorem source_horizon_angle_tail_le {p : ProductScaleData} (hp : ProductScaleLaws p)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hθ : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j)) (l t : ℕ)
    (ht : (t : ℝ) ≤ (p.m l : ℝ) ^ ((7 / 10 : ℝ) * p.m l)) :
    ENNReal.ofReal (t : ℝ) *
      (∑' i : {i : ℕ // i ∉ Finset.range (p.prefixCount (l + 1))},
        ENNReal.ofReal (θ i)) ≤
      ENNReal.ofReal (4 * (p.m l : ℝ) ^ (-(p.m l : ℝ) / 20)) := by
  rw [tsum_outside_range_ofReal θ hθ0 hθsum,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg t)]
  exact ENNReal.ofReal_le_ofReal (hp.power_mul_angle_tail_le θ hθ0 hθ l t ht)

theorem source_horizon_angle_tail_tendsto_zero {p : ProductScaleData}
    (hp : ProductScaleLaws p) (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθsum : Summable θ)
    (hθ : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j)) (M : ℕ → ℕ)
    (hM : ∀ l, (M l : ℝ) ≤ (p.m l : ℝ) ^ ((7 / 10 : ℝ) * p.m l)) :
    Tendsto (fun l => ENNReal.ofReal (M l : ℝ) *
      ∑' i : {i : ℕ // i ∉ Finset.range (p.prefixCount (l + 1))},
        ENNReal.ofReal (θ i)) atTop (𝓝 0) := by
  have hb := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp.tendsto_tail_trim_bound
  have hb' : Tendsto (fun l => ENNReal.ofReal
      (4 * (p.m l : ℝ) ^ (-(p.m l : ℝ) / 20))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using! hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb'
  · intro l
    exact bot_le
  · intro l
    exact source_horizon_angle_tail_le hp θ hθ0 hθsum hθ l (M l) (hM l)

theorem orderedOrbitSampling_of_source_prefix_samples {p : ProductScaleData}
    (hp : ProductScaleLaws p) (θ : ℕ → ℝ) (I : Finset ℕ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hθ : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j))
    (N : ℕ → Finset ℕ)
    (w : ∀ l, ℕ → (Finset.range (p.prefixCount (l + 1)) → Circle) → ℝ≥0∞)
    (hw : ∀ l, ∀ n ∈ N l, Measurable (w l n))
    (hNpos : ∀ l, ∀ n ∈ N l, 0 < n)
    (hNupper : ∀ l, ∀ n ∈ N l,
      (n : ℝ) ≤ (p.m l : ℝ) ^ ((7 / 10 : ℝ) * p.m l))
    (hprefix : ∀ l, ∀ n ∈ N l,
      ∀ᵐ x ∂baseMeasure.withDensity (fun x : Base =>
        w l n (fun i : Finset.range (p.prefixCount (l + 1)) => x i)),
        ∀ i ∈ Finset.range (p.prefixCount (l + 1)), circleRepresentative (x i) ≤
          circleRepresentative (rotationIterate θ (n : ℤ) x i))
    (hL2 : HasUniformL2Marginals (fun l => orbitAverageMeasure θ (N l)
      (fun n x => w l n (fun i : Finset.range (p.prefixCount (l + 1)) => x i))))
    (hweak : WeaklyConverges (fun l => orbitAverageMeasure θ (N l)
      (fun n x => w l n (fun i : Finset.range (p.prefixCount (l + 1)) => x i)))
      (triangularLaw I)) :
    OrderedOrbitSampling θ I := by
  let M : ℕ → ℕ := fun l => ⌊(p.m l : ℝ) ^ ((7 / 10 : ℝ) * p.m l)⌋₊
  apply orderedOrbitSampling_of_prefix_samples θ I hθ0
    (fun l => Finset.range (p.prefixCount (l + 1))) N M w hw hNpos
  · intro l n hn
    exact Nat.le_floor (hNupper l n hn)
  · exact hprefix
  · exact hL2
  · exact hweak
  · apply source_horizon_angle_tail_tendsto_zero hp θ hθ0 hθsum hθ M
    intro l
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end Invariant233.ProductModel.TailTrimming

end

end OAI
