import Mathlib
import OAI.Probability.Ballisticity.Crossings.BoundaryCrossBound
import OAI.Probability.Ballisticity.Estimates.TripleTestPerturbation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_boundary_cross_replacement {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i)=signedHeight e (y i))
    (H k : ℕ → ℕ) (hH : ∀ i, 0<H i) (θ r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (F : ℕ → BoundaryData d → ℝ) (C : ℝ) (hC : 0≤C) (hF : ∀ i j, ‖F i j‖≤C)
    (g : ℝ →ᵇ ℝ) (hg : UniformContinuous g) (w : ℝ≥0) :
    let ℓ := realPosition (step e)
    let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    let S := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    Tendsto (fun i => ∫ P, F i (D i P)*(
      g (physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i)*
      (symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (x i) P.1)*
      symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (y i) P.2))-
      g (signedCoordinate f ((boundaryTerminal (D i P)).1-(boundaryTerminal (D i P)).2)/r i)*
      centeredClipCross ℓ f (θ i) (r i) (k i) w
        (boundaryTerminal (D i P)).1 (boundaryTerminal (D i P)).2 (S i P))
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let S := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  let X : Fin 3 → ℕ → (Path d × Path d) → ℝ := ![
    (fun i P => centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (x i) P.1),
    (fun i P => centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (y i) P.2),
    (fun i P => physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i)]
  let Y : Fin 3 → ℕ → (Path d × Path d) → ℝ := ![
    (fun i P => centeredFirstHit ℓ f (θ i) (r i) (k i) (boundaryTerminal (D i P)).1 (S i P).1),
    (fun i P => centeredFirstHit ℓ f (θ i) (r i) (k i) (boundaryTerminal (D i P)).2 (S i P).2),
    (fun i P => signedCoordinate f ((boundaryTerminal (D i P)).1-(boundaryTerminal (D i P)).2)/r i)]
  have hX (j i) : Measurable (X j i) := by
    fin_cases j
    · exact (measurable_centeredHitIncrement _ _ _ _ _ _ _).comp measurable_fst
    · exact (measurable_centeredHitIncrement _ _ _ _ _ _ _).comp measurable_snd
    · exact (measurable_physicalFirstHitGap _ _ _ _ _).div_const _
  have hY (j i) : Measurable (Y j i) := by
    fin_cases j
    · exact measurable_boundary_centeredFirstHit _ _ _ _ _ _ false
    · exact measurable_boundary_centeredFirstHit _ _ _ _ _ _ true
    · exact ((measurable_of_countable (fun z : BoundaryData d => signedCoordinate f
        ((boundaryTerminal z).1-(boundaryTerminal z).2))).comp (measurable_boundaryData _ _)).div_const _
  have hc (j) (ε : ℝ) (hε : 0<ε) : Tendsto (fun i => (μ i).real
      {P | ε≤|X j i P-Y j i P|}) atTop (𝓝 0) := by
    fin_cases j
    · exact shared_boundary_increment_replacement ν hue e f htrans x y hxy H k hH θ r hr false ε hε
    · exact shared_boundary_increment_replacement ν hue e f htrans x y hxy H k hH θ r hr true ε hε
    · change Tendsto (fun i => (μ i).real {P | ε≤|physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i-
        signedCoordinate f ((boundaryTerminal (D i P)).1-(boundaryTerminal (D i P)).2)/r i|}) atTop (𝓝 0)
      simpa only [abs_sub_comm] using shared_boundary_gap_replacement ν hue e f htrans x y hxy H hH r hr ε hε
  have hh := weighted_three_test_perturbation μ X Y hX hY (fun i P => F i (D i P))
    (fun i => (measurable_of_countable (F i)).comp (measurable_boundaryData _ _)) C hC
    (fun i P => hF i (D i P)) ![symmetricClip w,symmetricClip w,g]
    (by intro j; fin_cases j; exact symmetricClip_uniformContinuous w; exact symmetricClip_uniformContinuous w; exact hg) hc
  apply hh.congr
  intro i
  congr 1
  funext P
  change F i (D i P)*(
    symmetricClip w (X 0 i P)*symmetricClip w (X 1 i P)*g (X 2 i P)-
    symmetricClip w (Y 0 i P)*symmetricClip w (Y 1 i P)*g (Y 2 i P)) =
    F i (D i P)*(g (X 2 i P)*(symmetricClip w (X 0 i P)*symmetricClip w (X 1 i P))-
    g (Y 2 i P)*(symmetricClip w (Y 0 i P)*symmetricClip w (Y 1 i P)))
  ring

lemma shared_deterministic_cross_bound {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0<r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i)=signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0<H i) (F : ℕ → BoundaryData d → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀ i j, ‖F i j‖≤C)
    (g : ℝ →ᵇ ℝ) (hg : UniformContinuous g) (hgb : ∀ z, |g z|≤1)
    {a t : ℝ} (ha : 0<a) (ht : 0<t) (hgzero : ∀ z, |z|≤a → g z=0)
    (w : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    ∀ᶠ i in atTop, |∫ P, F i (D i P)*
      (g (physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i)*
      (symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (x i) P.1)*
      symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (y i) P.2)))
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)| ≤
      C*(16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t)))+ε := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let k := fun i => ⌊t*n i⌋₊
  let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let S := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let A := fun i P => g (physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i)*
    (symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (x i) P.1)*
    symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (y i) P.2))
  let B := fun i P => g (signedCoordinate f ((boundaryTerminal (D i P)).1-(boundaryTerminal (D i P)).2)/r i)*
    centeredClipCross ℓ f (θ i) (r i) (k i) w (boundaryTerminal (D i P)).1 (boundaryTerminal (D i P)).2 (S i P)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  have hA (i) : Measurable (A i) := (g.continuous.measurable.comp ((measurable_physicalFirstHitGap _ _ _ _ _).div_const _)).mul
    (((symmetricClip w).continuous.measurable.comp ((measurable_centeredHitIncrement _ _ _ _ _ _ _).comp measurable_fst)).mul
    ((symmetricClip w).continuous.measurable.comp ((measurable_centeredHitIncrement _ _ _ _ _ _ _).comp measurable_snd)))
  have hB (i) : Measurable (B i) := (g.continuous.measurable.comp
    (((measurable_of_countable (fun z : BoundaryData d => signedCoordinate f ((boundaryTerminal z).1-(boundaryTerminal z).2))).comp
      (measurable_boundaryData _ _)).div_const _)).mul
    (((symmetricClip w).continuous.measurable.comp (measurable_boundary_centeredFirstHit _ _ _ _ _ _ false)).mul
    ((symmetricClip w).continuous.measurable.comp (measurable_boundary_centeredFirstHit _ _ _ _ _ _ true)))
  have hA_b (i P) : ‖A i P‖≤(w:ℝ)^2 := by
    dsimp only [A]
    simp only [Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ 1*((w:ℝ)*(w:ℝ)) := mul_le_mul (hgb _) (mul_le_mul (symmetricClip_bound _ _)
        (symmetricClip_bound _ _) (abs_nonneg _) w.coe_nonneg) (by positivity) (by norm_num)
      _ = _ := by ring
  have hB_b (i P) : ‖B i P‖≤(w:ℝ)^2 := by
    dsimp only [B]
    rw [norm_mul,Real.norm_eq_abs (g _)]
    exact (mul_le_mul (hgb _) (centeredClipCross_bound _ _ _ _ _ _ _ _ _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hd := shared_boundary_cross_replacement ν hue e f htrans x y hxy H k hH θ r hr.1 F C hC hF g hg w
  have hd' : Tendsto (fun i => (∫ P, F i (D i P)*A i P ∂μ i)-
      (∫ P, F i (D i P)*B i P ∂μ i)) atTop (𝓝 0) := by
    apply hd.congr
    intro i
    exact integral_weighted_sub_bounded (μ i) _ _ _ ((measurable_of_countable (F i)).comp
      (measurable_boundaryData _ _)) (hA i) (hB i) C ((w:ℝ)^2) hC (fun P => hF i (D i P)) (hA_b i) (hB_b i)
  have he : 0<ε/(2*(C+1)) := by positivity
  have hb := shared_boundary_cross_bound ν hue e f hef htrans r hrpos hr x y hxy H hH F C hC hF
    g hgb ha ht hgzero w he
  filter_upwards [hb,(Metric.tendsto_nhds.mp hd') (ε/2) (by positivity)] with i hi hj
  simp only [Real.dist_eq,sub_zero] at hj
  have hab := abs_le_abs_sub_add (∫ P, F i (D i P)*A i P ∂μ i) (∫ P, F i (D i P)*B i P ∂μ i)
  have hh : C*(ε/(2*(C+1))) ≤ ε/2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  change |∫ P, F i (D i P)*A i P ∂μ i| ≤ _
  simp_rw [mul_assoc] at hi
  change |∫ P, F i (D i P)*B i P ∂μ i| ≤ _ at hi
  nlinarith

end DirectionalTransience

end

end

end OAI
