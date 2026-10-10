import OAI.Analysis.FiniteFactor.CrossedProduct.Operator
import OAI.Analysis.FiniteFactor.CrossedProduct.Attenuation
import OAI.Analysis.FiniteFactor.Quasinilpotence

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Composition of the actual representative rotations. -/
theorem coordinateRotate_add {ι : Type*} (θ : ι → ℝ) (k n : ℤ) (x : ι → ℝ) :
    coordinateRotate θ n (coordinateRotate θ k x) = coordinateRotate θ (k+n) x := by
  funext i
  unfold coordinateRotate
  rw [Int.fract_eq_fract]
  refine ⟨-Int.floor (x i + (k : ℝ)*θ i), ?_⟩
  rw [Int.fract]
  push_cast
  ring

def sourceShiftNIndex {ι : Type*} (n : ℕ) (z : (ι → ℝ) × ℤ) : (ι → ℝ) × ℤ :=
  (z.1, z.2-(n : ℤ))

theorem sourceShiftNIndex_preserving (ι : Type*) (n : ℕ) :
    MeasurePreserving (sourceShiftNIndex (ι := ι) n) (sourceMeasure ι) (sourceMeasure ι) := by
  induction n with
  | zero =>
    have he : sourceShiftNIndex (ι := ι) 0 = id := by funext z; simp [sourceShiftNIndex]
    rw [he]
    exact MeasurePreserving.id _
  | succ n ih =>
    convert ih.comp (sourceShiftIndex_preserving ι) using 1
    funext z
    simp [sourceShiftNIndex, sourceShiftIndex, sub_sub, add_comm]

theorem sourceOperator_apply_ae {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (f : SourceHilbert ι) :
    sourceOperator θ c hθ hc f =ᵐ[sourceMeasure ι] fun z =>
      sourceDiagonal θ c (sourceShiftIndex z) * f (sourceShiftIndex z) := by
  have he := Lp.coeFn_compMeasurePreserving (sourceMultiplication θ c hθ hc f)
    (sourceShiftIndex_preserving ι)
  have hm := (sourceShiftIndex_preserving ι).quasiMeasurePreserving.ae
    (sourceMultiplication_apply_ae θ c hθ hc f)
  exact he.trans hm

/-- The actual powers of the constructed weighted shift, on the conull
finite-floor-support domain. No power formula is assumed. -/
theorem sourceOperator_pow_apply_ae {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hs : Summable (fun i => |θ i|)) (n : ℕ) (f : SourceHilbert ι) :
    (sourceOperator θ c hθ hc ^ n) f =ᵐ[sourceMeasure ι] fun z =>
      (sourceCocycle θ c n (coordinateRotate θ (z.2-(n : ℤ)) z.1) : ℂ) *
        f (sourceShiftNIndex n z) := by
  induction n with
  | zero =>
    apply Eventually.of_forall
    intro z
    have hzero : sourceCocycle θ c 0 (coordinateRotate θ z.2 z.1) = 1 :=
      sourceCocycle_zero θ c (fun i => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
    simp [sourceShiftNIndex, hzero]
  | succ n ih =>
    have hfs : ∀ᵐ z ∂sourceMeasure ι, finiteFloorSupport θ z.1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_finiteFloorSupport θ hs)
    have hih := (sourceShiftIndex_preserving ι).quasiMeasurePreserving.ae ih
    have he := sourceOperator_apply_ae θ c hθ hc ((sourceOperator θ c hθ hc ^ n) f)
    have hpow : (sourceOperator θ c hθ hc ^ (n+1)) f =
        sourceOperator θ c hθ hc ((sourceOperator θ c hθ hc ^ n) f) := by
      rw [pow_succ']
      rfl
    rw [hpow]
    filter_upwards [he, hih, hfs] with z hz hi hx
    rw [hz, hi]
    have hrot : coordinateRotate θ (n : ℤ) (coordinateRotate θ (z.2-((n+1 : ℕ) : ℤ)) z.1) =
        coordinateRotate θ (z.2-1) z.1 := by
      rw [coordinateRotate_add]
      congr 1
      push_cast
      omega
    have hcoe := sourceCocycle_add θ c (finiteFloorSupport_rotate θ hx (z.2-((n+1 : ℕ) : ℤ)))
      (n : ℤ) 1
    rw [hrot] at hcoe
    have hind : sourceShiftNIndex n (sourceShiftIndex z) = sourceShiftNIndex (n+1) z := by
      simp [sourceShiftNIndex, sourceShiftIndex, sub_sub, add_comm]
    have hidx : (sourceShiftIndex z).2-(n : ℤ) = z.2-((n+1 : ℕ) : ℤ) := by
      simp [sourceShiftIndex]
      omega
    simp only [sourceDiagonal, sourceShiftIndex] at *
    rw [show z.2-1-(n : ℤ) = z.2-((n+1 : ℕ) : ℤ) from hidx, hind]
    simp only [Nat.cast_add, Nat.cast_one] at hcoe ⊢
    rw [hcoe, Complex.ofReal_mul]
    exact (mul_assoc _ _ _).symm

/-- The source's finite-prefix operator bound, now for the constructed T. -/
theorem sourceOperator_pow_norm_prefix_bound {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hs : Summable (fun i => |θ i|)) (I : Finset ι) (n : ℕ) :
    ‖sourceOperator θ c hθ hc ^ n‖ ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ)*(∑ i ∈ I, c i*θ i)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro f
  let g := Lp.compMeasurePreserving (sourceShiftNIndex n) (sourceShiftNIndex_preserving ι n) f
  have hg := Lp.coeFn_compMeasurePreserving f (sourceShiftNIndex_preserving ι n)
  have hfs : ∀ᵐ z ∂sourceMeasure ι, finiteFloorSupport θ z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_finiteFloorSupport θ hs)
  have hle : ‖(sourceOperator θ c hθ hc ^ n) f‖ ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ)*(∑ i ∈ I, c i*θ i)) * ‖g‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [sourceOperator_pow_apply_ae θ c hθ hc hs n f, hg, hfs] with z hz hg hx
    rw [hz, hg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (sourceCocycle_pos _ _ _ _).le]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact sourceCocycle_prefix_bound θ c hθ hc
      (finiteFloorSupport_rotate θ hx _) (fun i => Int.fract_nonneg _) I n
  simpa [g, Lp.norm_compMeasurePreserving] using hle

/-- Norm quasinilpotence of this concrete operator follows from divergence of
its coordinate weighted-angle sums, not from any assumed operator property. -/
theorem sourceOperator_norm_quasinilpotent {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hs : Summable (fun i => |θ i|)) (I : ℕ → Finset ι)
    (hdiv : Tendsto (fun q => ∑ i ∈ I q, c i*θ i) atTop atTop) :
    Tendsto (fun n : ℕ => ‖sourceOperator θ c hθ hc ^ n‖ ^ (1/(n : ℝ))) atTop (𝓝 0) :=
  norm_quasinilpotent_of_prefix_bounds _ _ _ hdiv
    (fun q n _ => sourceOperator_pow_norm_prefix_bound θ c hθ hc hs (I q) n)

end
end FiniteFactor

end OAI
