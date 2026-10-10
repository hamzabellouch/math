import Mathlib
import OAI.Probability.Ballisticity.Walk.TransverseFirstHitSinglePathLimit
import OAI.Probability.Ballisticity.Geometry.CenteredHeightAdditiveUniform

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma median_eq_of_ae_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → ℝ) {c b : ℝ} (hF : ∀ᵐ x ∂μ, F x = c)
    (hl : (1/2 : ℝ≥0∞) ≤ μ {x | F x ≤ b})
    (hr : (1/2 : ℝ≥0∞) ≤ μ {x | b ≤ F x}) : b = c := by
  apply le_antisymm
  · by_contra! hh
    have hz : μ {x | b ≤ F x} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hF] with x hx
      simpa only [Set.mem_ofPred_eq,hx,not_le] using hh
    rw [hz] at hr
    norm_num at hr
  · by_contra! hh
    have hz : μ {x | F x ≤ b} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hF] with x hx
      simpa only [Set.mem_ofPred_eq,hx,not_le] using hh
    rw [hz] at hl
    norm_num at hl

lemma recordMedian_zero {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d) :
    recordMedian ν ℓ hp f 0 = 0 := by
  have hx := (conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν)
  have h0 : ∀ᵐ X ∂conditionedLaw ν ℓ, signedCoordinate f (recordIndexPosition ℓ 0 X) = 0 := by
    filter_upwards [hx] with X hX
    simp [recordIndexPosition,recordIndexTime_zero,hX,signedCoordinate]
  have he := median_eq_of_ae_const _ _ h0 (recordMedian_spec ν ℓ hp f 0).1
    (recordMedian_spec ν ℓ hp f 0).2
  exact_mod_cast he

theorem recordMedian_additive_uniform {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans)
    ∀ᶠ i in atTop, ∀ k j : ℕ,
      ((k+j:ℕ):ℝ) ≤ T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) (r i) →
      |((recordMedian ν (realPosition (step e)) hp f (k+j):ℝ)-
        recordMedian ν (realPosition (step e)) hp f k-recordMedian ν (realPosition (step e)) hp f j)/r i| < ε := by
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ hp
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ hp
  let F := fun h X => signedCoordinate f (recordIndexPosition ℓ h X)
  have hF (h : ℕ) : Measurable (F h) :=
    (measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ h)
  let b := fun h => (recordMedian ν ℓ hp f h:ℝ)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  have hi := independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e)
    htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto _ _
    (measurable_commonIncrementProcess ℓ f 0) hi hne).comp hr.1
  have hc := commonMeanWidth_ge_one ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)
  apply centered_height_additive_uniform μ F hF b
    (by simp [b,recordMedian_zero]) r n hn (1/(2*commonMeanWidth ν ℓ)) (by positivity)
      _ (annealedLaw ν (NoDrop ℓ 0)).toReal (ENNReal.toReal_pos hp (measure_ne_top _ _)) _ T hε
  · intro S hS
    obtain ⟨W,hW,hWf⟩ := transverse_firstHit_single_path_limit ν hue e f hef htrans r hr hS.le
    refine ⟨W,hW,?_⟩
    intro I
    simpa only [div_eq_mul_inv,one_mul] using hWf I
  · intro k j hk hj
    have hh := Measure.map_mono (conditioned_record_convolution_domination ν ℓ htrans hk hj)
      (measurable_of_countable (signedCoordinate f))
    have hsum : Measurable (fun P : Path d × Path d =>
        recordIndexPosition ℓ k P.1+recordIndexPosition ℓ j P.2) :=
      ((measurable_recordIndexPosition ℓ k).comp measurable_fst).add
        ((measurable_recordIndexPosition ℓ j).comp measurable_snd)
    rw [Measure.map_smul _ (measurable_of_countable (signedCoordinate f)).aemeasurable,
      Measure.map_map (measurable_of_countable _) hsum,
      Measure.map_map (measurable_of_countable _) (measurable_recordIndexPosition ℓ (k+j))] at hh
    simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _),Function.comp_def,signedCoordinate_add,independentConditionedPairLaw,μ,F] using hh

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma approximate_additive_linear_on_interval (b : ℕ → ℝ) (hb0 : b 0 = 0)
    {N : ℕ} (hN : 0 < N) {E : ℝ} (hE : 0 ≤ E)
    (ha : ∀ i j : ℕ, i+j ≤ 2*N → |b (i+j)-b i-b j| ≤ E) :
    ∀ j ≤ N, |b j-(j:ℝ)*b N/N| ≤ 2*E := by
  let D := fun j : ℕ => b j-(j:ℝ)*b N/N
  have hNreal : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hDz : D 0 = 0 := by simp [D,hb0]
  have hDN : D N = 0 := by simp [D,mul_div_cancel_left₀ _ hNreal]
  obtain ⟨k,hk,hmax⟩ := (Finset.range (N+1)).exists_max_image (fun j => |D j|)
    ⟨0,by simp⟩
  have hkN : k ≤ N := by simpa using hk
  have hmax' (j : ℕ) (hj : j ≤ N) : |D j| ≤ |D k| := hmax j (by simpa using hj)
  have hkbound : |D k| ≤ 2*E := by
    by_cases hkeq : k = N
    · simpa only [hkeq,hDN,abs_zero] using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hE
    have hklt : k < N := lt_of_le_of_ne hkN hkeq
    by_cases h2 : k+k ≤ N
    · have he : |D (k+k)-2*D k| ≤ E := by
        convert ha k k (by omega) using 1
        congr 1
        simp only [D,Nat.cast_add]
        ring
      have ht := abs_sub (2*D k) (D (k+k)-2*D k)
      have he' := abs_add_le (D (k+k)) (-(D (k+k)-2*D k))
      have heq : D (k+k)+ -(D (k+k)-2*D k) = 2*D k := by ring
      rw [heq,abs_neg] at he'
      have hn := hmax' (k+k) h2
      rw [abs_mul,show |(2:ℝ)| = 2 by norm_num] at he'
      linarith
    · let l := k+k-N
      have hl : l ≤ N := by dsimp [l]; omega
      have hsum : N+l = k+k := by dsimp [l]; omega
      have hcast : (N:ℝ)+(l:ℝ) = (k:ℝ)+(k:ℝ) := by exact_mod_cast hsum
      have he1 := ha k k (by omega)
      have he2 := ha N l (by omega)
      rw [hsum] at he2
      have he : |D l-2*D k| ≤ 2*E := by
        have heq : D l-2*D k =
            (b (k+k)-b k-b k)-(b (k+k)-b N-b l) := by
          dsimp [D]
          rw [show (l:ℝ) = (k:ℝ)+(k:ℝ)-N by linarith]
          field_simp
          ring
        rw [heq]
        exact le_trans (abs_sub _ _) (by linarith)
      have he' := abs_add_le (D l) (-(D l-2*D k))
      have heq : D l+ -(D l-2*D k) = 2*D k := by ring
      rw [heq,abs_neg,abs_mul,show |(2:ℝ)| = 2 by norm_num] at he'
      have hn := hmax' l hl
      linarith
  intro j hj
  exact (hmax' j hj).trans hkbound

lemma approximate_additive_common_slope (b : ℕ → ℝ) (hb0 : b 0 = 0)
    {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M) {E : ℝ} (hE : 0 ≤ E)
    (ha : ∀ i j : ℕ, i+j ≤ 2*M → |b (i+j)-b i-b j| ≤ E)
    {j : ℕ} (hj : j ≤ M) :
    |b j-(j:ℝ)*b N/N| ≤ 2*E*(1+(j:ℝ)/N) := by
  have hb := approximate_additive_linear_on_interval b hb0 (lt_of_lt_of_le hN hNM) hE ha
  have hNr : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : b j-(j:ℝ)*b N/N = (b j-(j:ℝ)*b M/M) +
      ((j:ℝ)/N)*((N:ℝ)*b M/M-b N) := by field_simp; ring
  rw [he]
  calc
    _ ≤ |b j-(j:ℝ)*b M/M|+|((j:ℝ)/N)*((N:ℝ)*b M/M-b N)| := abs_add_le _ _
    _ = |b j-(j:ℝ)*b M/M|+((j:ℝ)/N)*|b N-(N:ℝ)*b M/M| := by
      rw [abs_mul,abs_of_nonneg (show 0 ≤ (j:ℝ)/(N:ℝ) from div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
        show |(N:ℝ)*b M/M-b N| = |b N-(N:ℝ)*b M/M| from abs_sub_comm _ _]
    _ ≤ 2*E+((j:ℝ)/N)*(2*E) := by gcongr; exact hb j hj; exact hb N hNM
    _ = _ := by ring

theorem height_center_linearization (b : ℕ → ℝ) (hb0 : b 0 = 0) (r n : ℕ → ℝ)
    (hn : Tendsto n atTop atTop)
    (ha : ∀ T : ℝ, ∀ ε > 0, ∀ᶠ i in atTop, ∀ k j : ℕ,
      ((k+j:ℕ):ℝ) ≤ T*n i → |(b (k+j)-b k-b j)/r i| < ε)
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ h : ℕ, (h:ℝ) ≤ T*n i →
      |(b h-(h:ℝ)*(b ⌊n i⌋₊/⌊n i⌋₊))/r i| < ε := by
  let S := max T 1
  have hS : 1 ≤ S := le_max_right _ _
  let δ := ε/(8*(S+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [ha (2*S) δ hδ,hn.eventually (eventually_ge_atTop (1:ℝ))] with i hi hni
  let N := ⌊n i⌋₊
  let M := ⌊S*n i⌋₊
  have hN : 0 < N := Nat.lt_of_lt_of_le (by omega : 0 < 1) (Nat.le_floor (by exact_mod_cast hni))
  have hNM : N ≤ M := Nat.floor_mono (by nlinarith : n i ≤ S*n i)
  have hSn : 0 ≤ S*n i := by positivity
  have hM : (M:ℝ) ≤ S*n i := Nat.floor_le hSn
  have hNl : n i < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn2 : n i ≤ 2*(N:ℝ) := by linarith
  let B := fun h => b h/r i
  have hB0 : B 0 = 0 := by simp [B,hb0]
  have hBa (k j : ℕ) (hkj : k+j ≤ 2*M) : |B (k+j)-B k-B j| ≤ δ := by
    have hbnd : ((k+j:ℕ):ℝ) ≤ (2*S)*n i := by
      have hkk : ((k+j:ℕ):ℝ) ≤ 2*(M:ℝ) := by exact_mod_cast hkj
      nlinarith
    simpa only [B,← sub_div] using (hi k j hbnd).le
  intro h hh
  have hhS : (h:ℝ) ≤ S*n i := hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hhM : h ≤ M := Nat.le_floor hhS
  have hhN : (h:ℝ)/(N:ℝ) ≤ 2*S := (div_le_iff₀ hNr).mpr (by nlinarith)
  have hb := approximate_additive_common_slope B hB0 hN hNM hδ.le hBa hhM
  have he : (b h-(h:ℝ)*(b N/N))/r i = B h-(h:ℝ)*B N/N := by dsimp [B]; ring
  change |(b h-(h:ℝ)*(b N/N))/r i| < ε
  rw [he]
  apply lt_of_le_of_lt hb
  calc
    _ ≤ 2*δ*(1+2*S) := by gcongr
    _ < ε := by
      dsimp [δ]
      have hden : 0 < 8*(S+1) := by positivity
      rw [show 2*(ε/(8*(S+1)))*(1+2*S) = (2*ε*(1+2*S))/(8*(S+1)) by ring]
      apply (div_lt_iff₀ hden).mpr
      nlinarith

lemma height_center_slope_small (b : ℕ → ℝ) (r n : ℕ → ℝ)
    (hr : Tendsto r atTop atTop) (hn : Tendsto n atTop atTop)
    (hl : ∀ ε > 0, ∀ᶠ i in atTop, ∀ h : ℕ, (h:ℝ) ≤ n i →
      |(b h-(h:ℝ)*(b ⌊n i⌋₊/⌊n i⌋₊))/r i| < ε) :
    Tendsto (fun i => (b ⌊n i⌋₊/⌊n i⌋₊)/r i) atTop (𝓝 0) := by
  have he : Tendsto (fun i => (b 1-b ⌊n i⌋₊/⌊n i⌋₊)/r i) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hl ε hε,hn.eventually (eventually_ge_atTop (1:ℝ))] with i hi hni
    simpa only [Real.dist_eq,sub_zero,Nat.cast_one,one_mul] using hi 1 (by simpa using hni)
  have hh := (hr.const_div_atTop (b 1)).sub he
  simpa only [zero_sub,neg_zero,sub_div,sub_sub_cancel] using hh

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
