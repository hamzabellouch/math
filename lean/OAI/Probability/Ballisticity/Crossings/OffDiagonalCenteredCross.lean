import Mathlib
import OAI.Probability.Ballisticity.Estimates.IndependentRecenterMap
import OAI.Probability.Ballisticity.Estimates.SignedPrefixComparison

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma abs_le_abs_sub_add (a b : ℝ) : |a| ≤ |a-b|+|b| := by
  calc
    |a| = |a-b+b| := by congr 1; ring
    _ ≤ |a-b|+|b| := abs_add_le _ _

noncomputable def centeredClipCross {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (H : ℕ) (w : ℝ≥0) (x y : Lattice d) (P : Path d × Path d) : ℝ :=
  symmetricClip w (centeredFirstHit ℓ f θ r H x P.1)*
    symmetricClip w (centeredFirstHit ℓ f θ r H y P.2)

lemma measurable_centeredClipCross {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (H : ℕ) (w : ℝ≥0) (x y : Lattice d) :
    Measurable (centeredClipCross ℓ f θ r H w x y) := by
  exact (((symmetricClip w).continuous.measurable.comp (measurable_centeredFirstHit _ _ _ _ _ _)).comp measurable_fst).mul
    (((symmetricClip w).continuous.measurable.comp (measurable_centeredFirstHit _ _ _ _ _ _)).comp measurable_snd)

lemma centeredClipCross_bound {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (H : ℕ) (w : ℝ≥0) (x y : Lattice d) (P : Path d × Path d) :
    ‖centeredClipCross ℓ f θ r H w x y P‖ ≤ (w:ℝ)^2 := by
  rw [Real.norm_eq_abs,centeredClipCross,abs_mul,pow_two]
  exact mul_le_mul (symmetricClip_bound _ _) (symmetricClip_bound _ _) (abs_nonneg _) w.coe_nonneg

lemma shared_centered_cross_eventual_bound {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i)=signedHeight e (y i))
    {a t : ℝ} (ha : 0<a) (ht : 0<t) (hsep : ∀ i, a*r i≤|signedCoordinate f (y i-x i)|)
    (w : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    ∀ᶠ i in atTop, |∫ P, centeredClipCross ℓ f (θ i) (r i) ⌊t*n i⌋₊ w (x i) (y i) P
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)| ≤
      16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t))+ε := by
  dsimp only
  let ℓ := realPosition (step e)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let H := fun i => ⌊t*n i⌋₊
  let v := fun i => prefixVariation ν ℓ (x i) (y i) (H i)
  let B := 8*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t))
  let C := 2*‖symmetricClip w‖^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hv := off_diagonal_comparison ν hue e f hef htrans r hrpos hr x y hxy ha ht hsep
  have hvb : IsBoundedUnder (·≤·) atTop v := by
    refine ⟨1,show ∀ᶠ i in atTop, v i≤1 from Eventually.of_forall fun i => ?_⟩
    exact prefixVariation_le_one ν hue ℓ (signed_direction_unit e) htrans (x i) (y i) (H i)
  have he : 0<ε/(2*(C+1)) := by positivity
  have hevent := eventually_lt_of_limsup_lt (lt_of_le_of_lt hv (lt_add_of_pos_right B he)) hvb
  have hind := independent_centered_clip_product_limit ν hue e f hef htrans r hrpos hr x y ht w
  have hn := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have hH : Tendsto H atTop atTop := tendsto_nat_floor_atTop.comp (hn.const_mul_atTop ht)
  filter_upwards [hevent,(Metric.tendsto_nhds.mp hind) (ε/2) (by positivity),hH.eventually_gt_atTop 0]
    with i hi hj hHi
  have hc := centeredPairTest_prefix_comparison ν hue e f htrans (x i) (y i) (hxy i)
    (recordMedianSlope ν ℓ (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)) f (r i))
    (r i) hHi (symmetricClip w) (symmetricClip w)
  simp only [Real.dist_eq,sub_zero] at hj
  have hab := (abs_le_abs_sub_add _ _).trans (add_le_add hc hj.le)
  change |∫ P, centeredClipCross ℓ f _ _ (H i) w _ _ P ∂sharedConditionedPairLaw ν ℓ _ _| ≤ _
  apply hab.trans
  change (2*(‖symmetricClip w‖*‖symmetricClip w‖))*v i+ε/2≤_
  rw [← pow_two]
  have hmul := mul_le_mul_of_nonneg_left hi.le hC
  have hfrac : C*(ε/(2*(C+1)))≤ε/2 := by
    rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
    nlinarith
  change C*v i+ε/2≤16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t))+ε
  have heq : C*B=16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t)) := by dsimp [C,B]; ring
  nlinarith

lemma same_height_separated_exists {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) (R : ℝ) :
    ∃ x y : Lattice d, signedHeight e x=signedHeight e y ∧ R≤|signedCoordinate f (y-x)| := by
  refine ⟨0,⌈R⌉₊ • step f,?_,?_⟩
  · apply Int.cast_injective (α := ℝ)
    rw [← signedHeight_projection,← signedHeight_projection,dot_signed_direction,dot_signed_direction,
      signedCoordinate_nsmul,signedCoordinate_step_other e f hef,mul_zero]
    simp [signedCoordinate]
  · simp only [sub_zero,signedCoordinate_nsmul,signedCoordinate_step_self,mul_one,Nat.abs_cast]
    exact Nat.le_ceil R

lemma uniform_eventually_of_dependent_sequences {A : Type*} (V : ℕ → A → Prop)
    (hV : ∀ i, ∃ a, V i a) (P : ℕ → A → Prop)
    (hP : ∀ a : ℕ → A, (∀ i, V i (a i)) → ∀ᶠ i in atTop, P i (a i)) :
    ∀ᶠ i in atTop, ∀ a, V i a → P i a := by
  let a (i : ℕ) : A := if h : ∃ x, V i x ∧ ¬P i x then h.choose else (hV i).choose
  have ha (i : ℕ) : V i (a i) := by
    dsimp only [a]
    split_ifs with h
    · exact h.choose_spec.1
    · exact (hV i).choose_spec
  filter_upwards [hP a ha] with i hi x hx
  by_contra hp
  have hh : ∃ x, V i x ∧ ¬P i x := ⟨x,hx,hp⟩
  have hn : ¬P i (a i) := by simpa only [a,dite_eq_left hh] using hh.choose_spec.2
  exact hn hi

lemma shared_centered_cross_uniform_bound {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    {a t : ℝ} (ha : 0<a) (ht : 0<t) (w : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    ∀ᶠ i in atTop, ∀ x y : Lattice d, signedHeight e x=signedHeight e y →
      a*r i≤|signedCoordinate f (y-x)| →
      |∫ P, centeredClipCross ℓ f (θ i) (r i) ⌊t*n i⌋₊ w x y P ∂sharedConditionedPairLaw ν ℓ x y| ≤
        16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t))+ε := by
  dsimp only
  have hh := uniform_eventually_of_dependent_sequences
    (fun i (p : Lattice d × Lattice d) => signedHeight e p.1=signedHeight e p.2 ∧
      a*r i≤|signedCoordinate f (p.2-p.1)|)
    (fun i => by obtain ⟨x,y,h⟩ := same_height_separated_exists e f hef (a*r i); exact ⟨(x,y),h⟩)
    (fun i p => |∫ P, centeredClipCross (realPosition (step e)) f
      (recordMedianSlope ν _ (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans)) f (r i))
      (r i) ⌊t*(fluctuationScale (independentConditionedPairLaw ν _) (commonIncrementProcess _ f 0) (r i))⌋₊ w p.1 p.2 P
      ∂sharedConditionedPairLaw ν (realPosition (step e)) p.1 p.2|≤
        16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν (realPosition (step e))*a^2/(9*t))+ε)
    (fun p h => shared_centered_cross_eventual_bound ν hue e f hef htrans r hrpos hr
      (fun i => (p i).1) (fun i => (p i).2) (fun i => (h i).1) ha ht (fun i => (h i).2) w hε)
  filter_upwards [hh] with i hi x y hxy hsep
  exact hi (x,y) ⟨hxy,hsep⟩

end DirectionalTransience

end

end

end OAI
