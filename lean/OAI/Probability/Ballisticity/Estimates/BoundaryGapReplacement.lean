import Mathlib
import OAI.Probability.Ballisticity.Estimates.WeightedTestPerturbation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma boundary_gap_identity {d : ℕ} (e f : Direction d)
    (x y : Lattice d) (hxy : signedHeight e x=signedHeight e y)
    (H : ℕ) (hH : 0<H) (P : Path d × Path d)
    (hx : P.1 ∈ RegularPath (realPosition (step e)) x)
    (hy : P.2 ∈ RegularPath (realPosition (step e)) y)
    (hD : P.1 ∈ NoDrop (realPosition (step e)) x)
    (hE : P.2 ∈ NoDrop (realPosition (step e)) y)
    (hc : ∃ k : ℕ, P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e x+H+k)) :
    let ℓ := realPosition (step e)
    let z := boundaryTerminal (boundaryData ℓ ((signedHeight e x+H : ℤ) : ℝ) P)
    signedCoordinate f (z.1-z.2)=physicalFirstHitGap ℓ f x y
      (H+commonOffset ℓ (signedHeight e) (signedHeight e x+H) P) P := by
  dsimp only
  have h0 := boundarySuffix_record_identity e x y hxy H hH P hx hy hD hE hc 0
  dsimp only at h0
  simp only [zero_add,recordIndexPosition_at_zero,boundarySuffix,commonPairSuffix,
    Nat.add_zero,boundaryTerminal_data,sub_self] at h0
  simp only [physicalFirstHitGap,firstHitPairGap,h0.1,h0.2,signedCoordinate_sub,boundaryTerminal_data]
  ring

lemma shared_boundary_gap_replacement {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i)=signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0<H i) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (ε : ℝ) (hε : 0<ε) :
    let ℓ := realPosition (step e)
    let z := fun i P => boundaryTerminal (boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ) P)
    Tendsto (fun i => (sharedConditionedPairLaw ν ℓ (x i) (y i)).real {P |
      ε≤|signedCoordinate f ((z i P).1-(z i P).2)/r i-
        physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i|}) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let z := fun i P => boundaryTerminal (boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ) P)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  have hsmall := shared_common_displacement_small ν hue ℓ (signed_direction_unit e) f htrans
    (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)
    x y hxy H (fun i => (ε/2)*r i) (hr.const_mul_atTop (by positivity : 0<ε/2))
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hsmall
  filter_upwards [hr.eventually_gt_atTop 0] with i hri
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [sharedConditioned_regularPath ν ℓ htrans (x i) (y i),
    shared_common_boundary_exists ν hue ℓ (signed_direction_unit e) htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) (x i) (y i) (hxy i) (H i)] with P hP hc
  intro hh
  have he := boundary_gap_identity e f (x i) (y i) (hxy i) (H i) (hH i) P
    hP.1.1 hP.2.1 hP.1.2 hP.2.2 hc
  dsimp only at he
  change ε≤|_ - _| at hh
  rw [he] at hh
  by_contra hn
  change ¬(_ ∨ _) at hn
  simp only [not_or,not_le] at hn
  have hp : ε*r i ≤ |physicalFirstHitGap ℓ f (x i) (y i)
      (H i+commonOffset ℓ (signedHeight e) (signedHeight e (x i)+H i) P) P-
      physicalFirstHitGap ℓ f (x i) (y i) (H i) P| := by
    rw [← sub_div,abs_div,abs_of_pos hri] at hh
    exact (le_div_iff₀ hri).mp hh
  dsimp [physicalFirstHitGap,firstHitPairGap] at hp
  have hab := abs_sub
    (signedCoordinate f (recordIndexPosition ℓ (H i+commonOffset ℓ (signedHeight e) (signedHeight e (x i)+H i) P) (fun n => P.1 n-x i))-
      signedCoordinate f (recordIndexPosition ℓ (H i) (fun n => P.1 n-x i)))
    (signedCoordinate f (recordIndexPosition ℓ (H i+commonOffset ℓ (signedHeight e) (signedHeight e (x i)+H i) P) (fun n => P.2 n-y i))-
      signedCoordinate f (recordIndexPosition ℓ (H i) (fun n => P.2 n-y i)))
  have heq : ∀ a b c d z : ℝ, z+(a-b)-(z+(c-d))=(a-c)-(b-d) := by intros; ring
  rw [heq] at hp
  linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma weighted_product_test_perturbation {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X₁ Y₁ X₂ Y₂ : ℕ → Ω → ℝ)
    (hX₁ : ∀ i, Measurable (X₁ i)) (hY₁ : ∀ i, Measurable (Y₁ i))
    (hX₂ : ∀ i, Measurable (X₂ i)) (hY₂ : ∀ i, Measurable (Y₂ i))
    (F : ℕ → Ω → ℝ) (hF : ∀ i, Measurable (F i)) (C : ℝ) (hC : 0≤C)
    (hFb : ∀ i ω, ‖F i ω‖≤C) (f g : ℝ →ᵇ ℝ) (hf : UniformContinuous f) (hg : UniformContinuous g)
    (hc₁ : ∀ ε : ℝ, 0<ε → Tendsto (fun i => (μ i).real {ω | ε≤|X₁ i ω-Y₁ i ω|}) atTop (𝓝 0))
    (hc₂ : ∀ ε : ℝ, 0<ε → Tendsto (fun i => (μ i).real {ω | ε≤|X₂ i ω-Y₂ i ω|}) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ ω, F i ω*(f (X₁ i ω)*g (X₂ i ω)-f (Y₁ i ω)*g (Y₂ i ω)) ∂μ i)
      atTop (𝓝 0) := by
  have h1 := weighted_test_perturbation μ X₁ Y₁ hX₁ hY₁ (fun i ω => F i ω*g (X₂ i ω))
    (fun i => (hF i).mul (g.continuous.measurable.comp (hX₂ i))) (C*‖g‖) (by positivity)
    (fun i ω => by rw [norm_mul]; exact mul_le_mul (hFb i ω) (g.norm_coe_le_norm _) (norm_nonneg _) hC) f hf hc₁
  have h2 := weighted_test_perturbation μ X₂ Y₂ hX₂ hY₂ (fun i ω => F i ω*f (Y₁ i ω))
    (fun i => (hF i).mul (f.continuous.measurable.comp (hY₁ i))) (C*‖f‖) (by positivity)
    (fun i ω => by rw [norm_mul]; exact mul_le_mul (hFb i ω) (f.norm_coe_le_norm _) (norm_nonneg _) hC) g hg hc₂
  have hi (i : ℕ) (A B : Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
      (α β : ℝ) (hbA : ∀ ω, ‖A ω‖≤α) (hbB : ∀ ω, ‖B ω‖≤β) (hα : 0≤α) :
      Integrable (fun ω => A ω*B ω) (μ i) :=
    Integrable.of_bound (hA.mul hB).aestronglyMeasurable (α*β) (ae_of_all _ fun ω => by
      rw [norm_mul]; exact mul_le_mul (hbA ω) (hbB ω) (norm_nonneg _) hα)
  have hs := h1.add h2
  simp only [add_zero] at hs
  apply hs.congr
  intro i
  rw [← integral_add]
  · congr 1
    funext ω
    ring
  · apply hi i _ _ ((hF i).mul (g.continuous.measurable.comp (hX₂ i)))
      ((f.continuous.measurable.comp (hX₁ i)).sub (f.continuous.measurable.comp (hY₁ i)))
      (C*‖g‖) (2*‖f‖)
    · intro ω
      change ‖F i ω * _‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (hFb i ω) (g.norm_coe_le_norm _) (norm_nonneg _) hC
    · intro ω
      change ‖f (X₁ i ω) - f (Y₁ i ω)‖ ≤ _
      exact (norm_sub_le _ _).trans (by linarith [f.norm_coe_le_norm (X₁ i ω),f.norm_coe_le_norm (Y₁ i ω)])
    · positivity
  · apply hi i _ _ ((hF i).mul (f.continuous.measurable.comp (hY₁ i)))
      ((g.continuous.measurable.comp (hX₂ i)).sub (g.continuous.measurable.comp (hY₂ i)))
      (C*‖f‖) (2*‖g‖)
    · intro ω
      change ‖F i ω * _‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (hFb i ω) (f.norm_coe_le_norm _) (norm_nonneg _) hC
    · intro ω
      change ‖g (X₂ i ω) - g (Y₂ i ω)‖ ≤ _
      exact (norm_sub_le _ _).trans (by linarith [g.norm_coe_le_norm (X₂ i ω),g.norm_coe_le_norm (Y₂ i ω)])
    · positivity

end DirectionalTransience

end

end

end OAI
