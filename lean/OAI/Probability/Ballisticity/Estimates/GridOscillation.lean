import Mathlib
import OAI.Probability.Ballisticity.Geometry.SignedHeight

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma shifted_iid_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ) (s : ℕ) :
    IdentDistrib (fun ω k => X (s+k) ω) (fun ω k => X k ω) μ μ := by
  exact IdentDistrib.pi (fun k => (hident _).trans (hident k).symm)
    (hind.precomp (fun _ _ h => Nat.add_left_cancel h)) hind

lemma measureReal_shifted_max {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ) (s H : ℕ) (a : ℝ) :
    μ.real {ω | a < partialSumMax (fun k => X (s+k) ω) H} =
      μ.real {ω | a < partialSumMax (fun k => X k ω) H} := by
  apply congrArg ENNReal.toReal
  exact ((shifted_iid_identDistrib μ X hind hident s).comp
    (measurable_partialSumMax (fun k (f : ℕ → ℝ) => f k)
      (fun k => measurable_pi_apply k) H)).measure_mem_eq measurableSet_Ioi

lemma measureReal_max_scaled_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0}) {r η ε α : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (_hα : 0 ≤ α) (H s : ℕ) (hH : (H : ℝ) ≤ α*fluctuationScale μ (X 0) r) :
    μ.real {ω | ε*r < partialSumMax (fun k => X (s+k) ω) H} ≤
      α*(fluctuationScale μ (X 0) r*μ.real {ω | η*r < |X 0 ω|}) +
      (32*α*η^2+96*α^2)/ε^4 := by
  rw [measureReal_shifted_max μ X hind hident]
  have hm := truncatedVariance_pos μ (X 0) (hX 0) hne hr
  have hn : 0 < fluctuationScale μ (X 0) r := div_pos (sq_pos_of_pos hr) hm
  have hb := measureReal_iid_max_gt_fourth_bound μ X hX hind hident hsym
    (mul_nonneg hη hr.le) (by nlinarith : η*r ≤ r) (mul_pos hε hr) H
  apply hb.trans
  calc
    _ ≤ (α*fluctuationScale μ (X 0) r)*μ.real {ω | η*r < |X 0 ω|} +
        (32*(α*fluctuationScale μ (X 0) r)*(η*r)^2*truncatedVariance μ (X 0) r+
          96*(α*fluctuationScale μ (X 0) r)^2*(truncatedVariance μ (X 0) r)^2)/(ε*r)^4 := by
      gcongr
    _ = _ := by
      unfold fluctuationScale
      field_simp

lemma gaussian_max_block_eventually {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0}) (r : ℕ → ℝ)
    (hr : IsGaussianSequence μ (X 0) r) {α ε ζ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) (hζ : 0 < ζ)
    (H : ℕ → ℕ) (hH : ∀ᶠ i in atTop, (H i : ℝ) ≤ α*fluctuationScale μ (X 0) (r i)) :
    ∀ᶠ i in atTop, ∀ s : ℕ,
      μ.real {ω | ε*r i < partialSumMax (fun k => X (s+k) ω) (H i)} ≤
        128*α^2/ε^4+ζ := by
  have ht := (hr.2 (Real.sqrt α) (Real.sqrt_pos.2 hα)).const_mul α
  have he := (tendsto_order.mp ht).2 ζ (by simpa using hζ)
  filter_upwards [hr.1.eventually (eventually_gt_atTop (0:ℝ)),hH,he] with i hri hHi hti
  intro s
  have hb := measureReal_max_scaled_fourth_le μ X hX hind hident hsym hne hri
    (Real.sqrt_nonneg α) (by simpa using Real.sqrt_le_sqrt hα1) hε hα.le (H i) s hHi
  rw [Real.sq_sqrt hα.le] at hb
  have ha : (32*α*α+96*α^2)/ε^4 = 128*α^2/ε^4 := by ring
  rw [ha] at hb
  linarith

lemma realPartialSum_add (x : ℕ → ℝ) (s n : ℕ) :
    realPartialSum x (s+n) = realPartialSum x s + realPartialSum (fun k => x (s+k)) n := by
  simp only [realPartialSum,Finset.sum_range_add]

lemma grid_oscillation_block {x : ℕ → ℝ} {H j k : ℕ} (hH : 0 < H)
    (hjk : j ≤ k) (hkj : k ≤ j+H) {a : ℝ}
    (hmax : partialSumMax (fun l => x (j/H*H+l)) (2*H) ≤ a) :
    |realPartialSum x k-realPartialSum x j| ≤ 2*a := by
  let s := j/H*H
  have hsj : s ≤ j := Nat.div_mul_le_self j H
  have hsk : s ≤ k := hsj.trans hjk
  have hj2 : j-s ≤ 2*H := by
    have hjrem := Nat.mod_lt j hH
    have hjdecomp : j%H+s = j := by simpa [s,Nat.mul_comm] using Nat.mod_add_div j H
    omega
  have hk2 : k-s ≤ 2*H := by
    have hjrem := Nat.mod_lt j hH
    have hjdecomp : j%H+s = j := by simpa [s,Nat.mul_comm] using Nat.mod_add_div j H
    omega
  have hjb := (abs_partialSum_le_max (fun l => x (s+l)) (j-s)).trans
    ((partialSumMax_mono _ hj2).trans hmax)
  have hkb := (abs_partialSum_le_max (fun l => x (s+l)) (k-s)).trans
    ((partialSumMax_mono _ hk2).trans hmax)
  have hej := realPartialSum_add x s (j-s)
  have hek := realPartialSum_add x s (k-s)
  rw [Nat.add_sub_of_le hsj] at hej
  rw [Nat.add_sub_of_le hsk] at hek
  rw [hej,hek]
  have he : realPartialSum x s + realPartialSum (fun l => x (s+l)) (k-s)-
      (realPartialSum x s + realPartialSum (fun l => x (s+l)) (j-s)) =
      realPartialSum (fun l => x (s+l)) (k-s)-realPartialSum (fun l => x (s+l)) (j-s) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

def GridOscillation {Ω : Type*} (X : ℕ → Ω → ℝ) (N H : ℕ) (a : ℝ) : Set Ω :=
  {ω | ∃ j ≤ N, ∃ k ≤ N, j ≤ k ∧ k ≤ j+H ∧
    a < |realPartialSum (fun l => X l ω) k-realPartialSum (fun l => X l ω) j|}

lemma measureReal_gridOscillation_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    {N H M : ℕ} (hH : 0 < H) (hN : N < M*H) (a : ℝ) :
    μ.real (GridOscillation X N H (2*a)) ≤
      M*μ.real {ω | a < partialSumMax (fun k => X k ω) (2*H)} := by
  let A : ℕ → Set Ω := fun b => {ω | a < partialSumMax (fun k => X (b*H+k) ω) (2*H)}
  have hsub : GridOscillation X N H (2*a) ⊆ ⋃ b ∈ Finset.range M, A b := by
    intro ω hω
    rcases hω with ⟨j,hj,k,_hk,hjk,hkj,hoff⟩
    refine Set.mem_iUnion.mpr ⟨j/H,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ?_,?_⟩⟩
    · exact (Nat.div_lt_iff_lt_mul hH).2 (hj.trans_lt hN)
    · by_contra h
      exact (not_le_of_gt hoff) (grid_oscillation_block hH hjk hkj (le_of_not_gt h))
  calc
    _ ≤ μ.real (⋃ b ∈ Finset.range M, A b) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ b ∈ Finset.range M, μ.real (A b) := measureReal_biUnion_finset_le _ _
    _ = _ := by
      simp only [A,measureReal_shifted_max μ X hind hident,Finset.sum_const,
        Finset.card_range,nsmul_eq_mul]

lemma eventually_floor_horizon_covered (n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (M : ℕ) (hM : T < (M:ℝ)*δ) :
    ∀ᶠ i in atTop, 0 < ⌊δ*n i⌋₊ ∧ ⌊T*n i⌋₊ < M*⌊δ*n i⌋₊ := by
  have hH := (tendsto_nat_floor_mul_div_atTop hδ.le).comp hn
  have hN := (tendsto_nat_floor_mul_div_atTop hT).comp hn
  have hlt := hN.eventually_lt (hH.const_mul (M:ℝ)) hM
  have hpos := (tendsto_order.mp hH).1 (δ/2) (by linarith)
  filter_upwards [hlt,hpos,hn.eventually (eventually_gt_atTop (0:ℝ))] with i hi hp hni
  change (⌊T*n i⌋₊ : ℝ)/n i < (M:ℝ)*((⌊δ*n i⌋₊ : ℝ)/n i) at hi
  change δ/2 < (⌊δ*n i⌋₊ : ℝ)/n i at hp
  have hfloor : 0 < (⌊δ*n i⌋₊ : ℝ) := (div_pos_iff_of_pos_right hni).mp (lt_trans (by linarith) hp)
  refine ⟨by exact_mod_cast hfloor,?_⟩
  rw [← mul_div_assoc] at hi
  have hc := (div_lt_div_iff_of_pos_right hni).mp hi
  exact_mod_cast hc

lemma gaussian_gridOscillation_eventually {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T δ ε ζ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hε : 0 < ε) (hζ : 0 < ζ) (M : ℕ) (hM : T < (M:ℝ)*δ) :
    ∀ᶠ i in atTop,
      μ.real (GridOscillation X ⌊T*fluctuationScale μ (X 0) (r i)⌋₊
        ⌊δ*fluctuationScale μ (X 0) (r i)⌋₊ (ε*r i)) ≤
        M*(8192*δ^2/ε^4+ζ) := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  have hlen : ∀ᶠ i in atTop, ((2*⌊δ*n i⌋₊ : ℕ) : ℝ) ≤ (2*δ)*n i := by
    filter_upwards [hn.eventually (eventually_gt_atTop (0:ℝ))] with i hni
    have hf := Nat.floor_le (mul_nonneg hδ.le hni.le)
    push_cast
    linarith
  have hb := gaussian_max_block_eventually μ X hX hind hident hsym hne r hr
    (by linarith : 0 < 2*δ) (by linarith : 2*δ ≤ 1) (by linarith : 0 < ε/2)
    hζ (fun i => 2*⌊δ*n i⌋₊) hlen
  filter_upwards [hb,eventually_floor_horizon_covered n hn hT hδ M hM] with i hi hcov
  have hm := measureReal_gridOscillation_le μ X hind hident hcov.1 hcov.2 ((ε/2)*r i)
  have he : 2*((ε/2)*r i) = ε*r i := by ring
  rw [he] at hm
  apply hm.trans
  have hb0 := hi 0
  simp only [zero_add] at hb0
  have hec : 128*(2*δ)^2/(ε/2)^4 = 8192*δ^2/ε^4 := by ring
  rw [hec] at hb0
  exact mul_le_mul_of_nonneg_left hb0 (Nat.cast_nonneg M)

theorem gaussian_grid_modulus {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T ε β : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop,
      μ.real (GridOscillation X ⌊T*fluctuationScale μ (X 0) (r i)⌋₊
        ⌊δ*fluctuationScale μ (X 0) (r i)⌋₊ (ε*r i)) ≤ β := by
  have he4 : 0 < ε^4 := pow_pos hε 4
  have hT2 : 0 < T+2 := by linarith
  let δ := min (1/2:ℝ) (β*ε^4/(32768*(T+2)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos (mul_pos hβ he4) (by positivity))
  have hδ1 : δ ≤ 1/2 := min_le_left _ _
  have hbudget : δ*(32768*(T+2)) ≤ β*ε^4 :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  let M := ⌈T/δ⌉₊+1
  have hMpos : 0 < (M:ℝ) := by dsimp [M]; positivity
  have hceil := Nat.le_ceil (T/δ)
  have hM : T < (M:ℝ)*δ := by
    have h := (div_le_iff₀ hδ).1 hceil
    dsimp [M]
    push_cast
    nlinarith
  have hMb : (M:ℝ) ≤ T/δ+2 := by
    have hc := Nat.ceil_lt_add_one (div_nonneg hT hδ.le)
    dsimp [M]
    push_cast
    linarith
  have hMδ : (M:ℝ)*δ^2 ≤ (T+2)*δ := by
    have hm : (M:ℝ)*δ ≤ T+2*δ := by
      have hc := mul_le_mul_of_nonneg_right hMb hδ.le
      field_simp at hc
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hm hδ.le]
  have hsmall : (M:ℝ)*(8192*δ^2/ε^4) ≤ β/2 := by
    rw [← mul_div_assoc,div_le_iff₀ he4]
    nlinarith
  have hζ : 0 < β/(2*(M:ℝ)) := div_pos hβ (by positivity)
  refine ⟨δ,hδ,?_⟩
  have hb := gaussian_gridOscillation_eventually μ X hX hind hident hsym hI hne r hr
    hT hδ hδ1 hε hζ M hM
  filter_upwards [hb] with i hi
  apply hi.trans
  rw [mul_add]
  have he : (M:ℝ)*(β/(2*(M:ℝ))) = β/2 := by field_simp
  rw [he]
  linarith

theorem transverse_common_gaussian_grid_modulus {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    {T ε β : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop,
      (independentConditionedPairLaw ν (realPosition (step e))).real
        (GridOscillation (commonIncrementProcess (realPosition (step e)) f)
          ⌊T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) (r i)⌋₊
          ⌊δ*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) (r i)⌋₊ (ε*r i)) ≤ β := by
  let ℓ := realPosition (step e)
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  exact gaussian_grid_modulus _ _ (measurable_commonIncrementProcess ℓ f)
    (commonIncrements_independent ν ℓ htrans (signedHeight e) (signedHeight_projection e)
      (signedHeight_step_le e) f)
    (commonIncrements_identDistrib ν ℓ htrans (signedHeight e) (signedHeight_projection e)
      (signedHeight_step_le e) f)
    (independent_commonWordIncrement_symmetric ν ℓ htrans f)
    (independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e) htrans
      (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
    (independent_commonWordIncrement_nonzero ν hue e f hef htrans) r hr hT hε hβ

def unitRamp (t : ℝ) : ℝ := min 1 (max 0 t)

lemma unitRamp_zero {t : ℝ} (ht : t ≤ 0) : unitRamp t = 0 := by
  simp [unitRamp,max_eq_left ht]
lemma unitRamp_one {t : ℝ} (ht : 1 ≤ t) : unitRamp t = 1 := by
  simp [unitRamp,max_eq_right (by linarith : 0 ≤ t),min_eq_left ht]
lemma unitRamp_self {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : unitRamp t = t := by
  simp [unitRamp,max_eq_right ht,min_eq_right ht1]
@[continuity, fun_prop] lemma continuous_unitRamp : Continuous unitRamp := by unfold unitRamp; fun_prop

noncomputable def linearPolygon (x : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, unitRamp (t-k)*x k

lemma linearPolygon_formula (x : ℕ → ℝ) (N : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (hN : ⌊t⌋₊ < N) :
    linearPolygon x N t = realPartialSum x ⌊t⌋₊ + (t-⌊t⌋₊)*x ⌊t⌋₊ := by
  let j := ⌊t⌋₊
  have hj : (j:ℝ) ≤ t := Nat.floor_le ht
  have hj1 : t < j+1 := Nat.lt_floor_add_one t
  have hNj : j+1 ≤ N := hN
  have hsplit : N = j+1+(N-(j+1)) := (Nat.add_sub_of_le hNj).symm
  unfold linearPolygon
  rw [hsplit,Finset.sum_range_add,Finset.sum_range_succ]
  have hleft : (∑ k ∈ Finset.range j, unitRamp (t-k)*x k) = realPartialSum x j := by
    unfold realPartialSum
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : (k:ℝ)+1 ≤ j := by exact_mod_cast Finset.mem_range.mp hk
    rw [unitRamp_one (by linarith),one_mul]
  rw [hleft,unitRamp_self (by linarith) (by linarith)]
  have htail : (∑ k ∈ Finset.range (N-(j+1)), unitRamp (t-(j+1+k))*x (j+1+k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    rw [unitRamp_zero (by linarith),zero_mul]
  simpa [j] using congrArg (fun z => realPartialSum x j+(t-j)*x j+z) htail

noncomputable instance continuousPathMeasurableSpace : MeasurableSpace C(unitInterval,ℝ) := borel _

instance continuousPathBorelSpace : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

noncomputable def polygonPath (N : ℕ) (scale : ℝ) (x : ℕ → ℝ) : C(unitInterval,ℝ) :=
  ∑ k ∈ Finset.range N, (x k) •
    (⟨fun t => unitRamp (scale*(t:ℝ)-k),by fun_prop⟩ : C(unitInterval,ℝ))

lemma polygonPath_apply (N : ℕ) (scale : ℝ) (x : ℕ → ℝ) (t : unitInterval) :
    polygonPath N scale x t = linearPolygon x N (scale*t) := by
  simp only [polygonPath,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.coe_mk,smul_eq_mul,linearPolygon]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma measurable_polygonPath {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (N : ℕ) (scale : ℝ) :
    Measurable (fun ω => polygonPath N scale (fun k => X k ω)) := by
  unfold polygonPath
  fun_prop

lemma linearPolygon_near_partialSum {x : ℕ → ℝ} {N : ℕ} {t a : ℝ}
    (ht : 0 ≤ t) (hN : ⌊t⌋₊ < N) (hb : |x ⌊t⌋₊| ≤ a) :
    |linearPolygon x N t-realPartialSum x ⌊t⌋₊| ≤ a := by
  rw [linearPolygon_formula x N ht hN]
  have hj := Nat.floor_le ht
  have hj1 := Nat.lt_floor_add_one t
  have he : realPartialSum x ⌊t⌋₊+(t-⌊t⌋₊)*x ⌊t⌋₊-realPartialSum x ⌊t⌋₊ =
      (t-⌊t⌋₊)*x ⌊t⌋₊ := by ring
  rw [he,abs_mul,abs_of_nonneg (by linarith)]
  have ha : 0 ≤ a := (abs_nonneg _).trans hb
  nlinarith [mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ t-⌊t⌋₊)]

lemma realPartialSum_step (x : ℕ → ℝ) (j : ℕ) :
    realPartialSum x (j+1)-realPartialSum x j = x j := by
  simp [realPartialSum,Finset.sum_range_succ]

lemma not_gridOscillation_bound {Ω : Type*} (X : ℕ → Ω → ℝ) {ω : Ω}
    {N H : ℕ} {a : ℝ} (hω : ω ∉ GridOscillation X N H a)
    {j k : ℕ} (hj : j ≤ N) (hk : k ≤ N) (hd : j ≤ k+H) (hd' : k ≤ j+H) :
    |realPartialSum (fun l => X l ω) k-realPartialSum (fun l => X l ω) j| ≤ a := by
  by_cases hjk : j ≤ k
  · exact le_of_not_gt (fun h => hω ⟨j,hj,k,hk,hjk,hd',h⟩)
  · rw [abs_sub_comm]
    exact le_of_not_gt (fun h => hω ⟨k,hk,j,hj,by omega,hd,h⟩)

lemma linearPolygon_oscillation_le {Ω : Type*} (X : ℕ → Ω → ℝ) {ω : Ω}
    {N H P : ℕ} {a s t : ℝ} (hω : ω ∉ GridOscillation X N H a)
    (hH : 1 ≤ H) (hP : P ≤ N) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsP : ⌊s⌋₊ < P) (htP : ⌊t⌋₊ < P)
    (hst : ⌊s⌋₊ ≤ ⌊t⌋₊+H) (hts : ⌊t⌋₊ ≤ ⌊s⌋₊+H) :
    |linearPolygon (fun l => X l ω) P t-linearPolygon (fun l => X l ω) P s| ≤ 3*a := by
  have hsb : |X ⌊s⌋₊ ω| ≤ a := by
    rw [← realPartialSum_step (fun l => X l ω)]
    exact not_gridOscillation_bound X hω (by omega) (by omega) (by omega) (by omega)
  have htb : |X ⌊t⌋₊ ω| ≤ a := by
    rw [← realPartialSum_step (fun l => X l ω)]
    exact not_gridOscillation_bound X hω (by omega) (by omega) (by omega) (by omega)
  have hm := not_gridOscillation_bound X hω (j := ⌊s⌋₊) (k := ⌊t⌋₊)
    (by omega) (by omega) hst hts
  have hl := linearPolygon_near_partialSum (x := fun l => X l ω) hs hsP hsb
  have hr := linearPolygon_near_partialSum (x := fun l => X l ω) ht htP htb
  have hb := abs_add_three (linearPolygon (fun l => X l ω) P t-realPartialSum (fun l => X l ω) ⌊t⌋₊)
    (realPartialSum (fun l => X l ω) ⌊t⌋₊-realPartialSum (fun l => X l ω) ⌊s⌋₊)
    (realPartialSum (fun l => X l ω) ⌊s⌋₊-linearPolygon (fun l => X l ω) P s)
  rw [abs_sub_comm (realPartialSum (fun l => X l ω) ⌊s⌋₊)] at hb
  have he : linearPolygon (fun l => X l ω) P t-linearPolygon (fun l => X l ω) P s =
      (linearPolygon (fun l => X l ω) P t-realPartialSum (fun l => X l ω) ⌊t⌋₊)+
      (realPartialSum (fun l => X l ω) ⌊t⌋₊-realPartialSum (fun l => X l ω) ⌊s⌋₊)+
      (realPartialSum (fun l => X l ω) ⌊s⌋₊-linearPolygon (fun l => X l ω) P s) := by ring
  rw [he]
  exact hb.trans (by linarith)

noncomputable def scaledPolygon (x : ℕ → ℝ) (r n T : ℝ) : C(unitInterval,ℝ) :=
  r⁻¹ • polygonPath (⌊T*n⌋₊+1) (T*n) x

lemma scaledPolygon_apply (x : ℕ → ℝ) (r n T : ℝ) (t : unitInterval) :
    scaledPolygon x r n T t = linearPolygon x (⌊T*n⌋₊+1) (T*n*t)/r := by
  simp [scaledPolygon,polygonPath_apply,div_eq_inv_mul]

lemma measurable_scaledPolygon {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (r n T : ℝ) :
    Measurable (fun ω => scaledPolygon (fun k => X k ω) r n T) := by
  exact (measurable_polygonPath X hX _ _).const_smul (r⁻¹ : ℝ)

lemma scaledPolygon_zero (x : ℕ → ℝ) (r n T : ℝ) :
    scaledPolygon x r n T 0 = 0 := by
  rw [scaledPolygon_apply]
  change (∑ k ∈ Finset.range (⌊T*n⌋₊+1), unitRamp (T*n*(0:ℝ)-k)*x k)/r = 0
  simp only [mul_zero]
  have he : (∑ k ∈ Finset.range (⌊T*n⌋₊+1), unitRamp (0-k)*x k) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [unitRamp_zero (by linarith [Nat.cast_nonneg (α := ℝ) k]),zero_mul]
  rw [he,zero_div]

def ContinuousOscillation (ε δ : ℝ) : Set C(unitInterval,ℝ) :=
  {f | ∃ s t : unitInterval, dist s t ≤ δ ∧ ε < |f s-f t|}

lemma isOpen_continuousOscillation (ε δ : ℝ) : IsOpen (ContinuousOscillation ε δ) := by
  have he : ContinuousOscillation ε δ =
      ⋃ (s : unitInterval) (t : unitInterval) (_h : dist s t ≤ δ), {f : C(unitInterval,ℝ) | ε < |f s-f t|} := by
    ext f
    simp only [ContinuousOscillation,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]
  rw [he]
  exact isOpen_iUnion (fun s => isOpen_iUnion (fun t => isOpen_iUnion (fun _ =>
    isOpen_lt continuous_const ((continuous_eval_const s).sub
      (continuous_eval_const t)).abs)))

end DirectionalTransience
end
end

end OAI
