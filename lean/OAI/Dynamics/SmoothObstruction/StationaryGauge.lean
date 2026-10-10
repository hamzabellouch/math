import OAI.Dynamics.SmoothObstruction.OrthogonalCocycle
import OAI.Dynamics.SmoothObstruction.DyadicChord

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators

namespace SmoothObstruction.GoodStationary
open MeasureTheory Finset Filter Topology
open SmoothObstruction.DyadicChord
open scoped ENNReal NNReal

/-- The literal geometric floor used throughout the source. -/
noncomputable def floorAt (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℝ) / 10)

lemma floorAt_pos (k : ℕ) : 0 < floorAt k := Real.rpow_pos_of_pos (by norm_num) _

lemma floorAt_sq (k : ℕ) : (floorAt k)^2 = ((2 : ℝ)^(-1/5 : ℝ))^k := by
  rw [floorAt, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

lemma floorAt_square_summable : Summable (fun k => (floorAt k)^2) := by
  simp_rw [floorAt_sq]
  exact summable_geometric_of_norm_lt_one (by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

/-- Here `a h` is the sum over the diagonal coordinates of the dyadic
squared chord errors. Its square root replaces the optional convolution
upper bound in the manuscript's example of the choice of sequence. -/
noncomputable def bAt (η : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  (40 / Real.sqrt η) * Real.sqrt (a (k + 1)) + floorAt k

lemma bAt_floor {η : ℝ} (hη : 0 < η) (a : ℕ → ℝ) (k : ℕ) :
    floorAt k ≤ bAt η a k := by
  dsimp [bAt]
  exact le_add_of_nonneg_left (by positivity)

lemma bAt_pos {η : ℝ} (hη : 0 < η) (a : ℕ → ℝ) (k : ℕ) :
    0 < bAt η a k := (floorAt_pos k).trans_le (bAt_floor hη a k)

lemma bAt_square_summable {η : ℝ} {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) (hsum : Summable a) :
    Summable (fun k => (bAt η a k)^2) := by
  have hs : Summable (fun k => a (k + 1)) := (summable_nat_add_iff 1).2 hsum
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
    ((hs.mul_left (2 * (40 / Real.sqrt η)^2)).add
      (floorAt_square_summable.mul_left 2))
  intro k
  dsimp [bAt]
  have := Real.sq_sqrt (ha (k + 1))
  nlinarith [sq_nonneg ((40 / Real.sqrt η) * Real.sqrt (a (k + 1)) - floorAt k)]

lemma error_ratio {η : ℝ} (hη : 0 < η) {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) (k : ℕ) :
    4 * a (k + 1) / (bAt η a k)^2 ≤ η / 400 := by
  have hr : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hb := bAt_pos hη a k
  have hbase : (40 / Real.sqrt η) * Real.sqrt (a (k + 1)) ≤ bAt η a k := by
    dsimp [bAt]
    linarith [floorAt_pos k]
  have hs : ((40 / Real.sqrt η) * Real.sqrt (a (k + 1)))^2 ≤ (bAt η a k)^2 :=
    pow_le_pow_left₀ (by positivity) hbase 2
  have hsq : ((40 / Real.sqrt η) * Real.sqrt (a (k + 1)))^2 =
      1600 * a (k + 1) / η := by
    rw [mul_pow, div_pow, Real.sq_sqrt (ha _), Real.sq_sqrt hη.le]
    ring
  rw [hsq] at hs
  have := (div_le_iff₀ hη).mp hs
  apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def jointEnergy {d : ℕ} (T : Ω → Ω) (f : Fin d → Ω → ℝ)
    (μ : Measure Ω) (h : ℕ) : ℝ :=
  ∑ j, deviationEnergy T (f j) μ (2^h)

lemma jointEnergy_nonneg {d : ℕ} (T : Ω → Ω) (f : Fin d → Ω → ℝ) (h : ℕ) :
    0 ≤ jointEnergy T f μ h := sum_nonneg (fun j _ => deviationEnergy_nonneg T (f j) _)

lemma jointEnergy_summable {d : ℕ} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Fin d → Ω → ℝ} (hf : ∀ j, MemLp (f j) 2 μ) :
    Summable (jointEnergy T f μ) := by
  exact summable_sum (fun j _ => (dyadic_square_summable hT (hf j)).1)

/-- A finite set of forward chord inequalities. Centered integer intervals
are precisely these sets pulled back by the negative iterate of a homeomorphism. -/
def Good {d : ℕ} (T : Ω → Ω) (f : Fin d → Ω → ℝ) (k : ℕ) (b : ℝ) : Set Ω :=
  {x | ∀ j, ∀ u ≤ 2^(k + 1), |chord (orbit T (f j) x) (2^(k + 1)) u| ≤ b * (2 : ℝ)^k}

omit [MeasurableSpace Ω] in
lemma good_iff_deviation {d : ℕ} (T : Ω → Ω) (f : Fin d → Ω → ℝ)
    (k : ℕ) (b : ℝ) (x : Ω) :
    x ∈ Good T f k b ↔ ∀ j, deviation (orbit T (f j) x) (2^(k + 1)) ≤ b / 2 := by
  have hn : 0 < 2^(k + 1) := pow_pos (by omega : 0 < 2) _
  have hn' : (2 : ℝ)^(k + 1) = 2 * 2^k := pow_succ' _ _
  constructor
  · intro hx j
    apply deviation_le _ hn
    intro u hu
    have := hx j u hu
    simp only [Nat.cast_pow, Nat.cast_ofNat, hn']
    nlinarith
  · intro hx j u hu
    have hh := abs_chord_le (orbit T (f j) x) hn hu
    have hh' := mul_le_mul_of_nonneg_left (hx j) (Nat.cast_nonneg (2^(k + 1)))
    simp only [Nat.cast_pow, Nat.cast_ofNat, hn'] at hh hh'
    nlinarith

/-- Quantitative squared Markov bound for all coordinate chords together.
The measure is UNNORMALIZED; no conditioning of the original law occurs. -/
theorem bad_measure {d : ℕ} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Fin d → Ω → ℝ} (hf : ∀ j, MemLp (f j) 2 μ)
    {b : ℝ} (hb : 0 < b) (k : ℕ) :
    μ (Good T f k b)ᶜ ≤ ENNReal.ofReal (4 * jointEnergy T f μ (k + 1) / b^2) := by
  let F : Ω → ℝ := fun x => (4 / b^2) * ∑ j, (deviation (orbit T (f j) x) (2^(k + 1)))^2
  have hF : Integrable F μ :=
    (integrable_finsetSum _ (fun j _ =>
      (deviation_memLp (orbit_memLp hT (hf j)) _).integrable_sq)).const_mul _
  have hnonneg : ∀ x, 0 ≤ F x := by
    intro x
    dsimp [F]
    positivity
  have hbad : ∀ x ∈ (Good T f k b)ᶜ, 1 ≤ F x := by
    intro x hx
    have hnot : ¬ ∀ j, deviation (orbit T (f j) x) (2^(k + 1)) ≤ b / 2 := by
      simpa only [Set.mem_compl_iff, good_iff_deviation] using hx
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have hsmall : (deviation (orbit T (f j) x) (2^(k + 1)))^2 ≤
        ∑ i, (deviation (orbit T (f i) x) (2^(k + 1)))^2 :=
      single_le_sum (f := fun i : Fin d => (deviation (orbit T (f i) x) (2^(k + 1)))^2)
        (fun _ _ => sq_nonneg _) (mem_univ j)
    have hsum : b^2 / 4 ≤ ∑ i, (deviation (orbit T (f i) x) (2^(k + 1)))^2 := by
      nlinarith [deviation_nonneg (orbit T (f j) x) (2^(k + 1))]
    dsimp [F]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
    nlinarith
  convert hF.measure_le_integral (Filter.Eventually.of_forall hnonneg) hbad using 2
  dsimp [F, jointEnergy, deviationEnergy]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
    (deviation_memLp (orbit_memLp hT (hf j)) _).integrable_sq)]
  ring

/-- The actual simultaneous good-segment sequence, not an assumed rate of
convergence. No ergodicity or rate assumption is used. -/
theorem good_segments {d : ℕ} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Fin d → Ω → ℝ} (hf : ∀ j, MemLp (f j) 2 μ) {η : ℝ} (hη : 0 < η) :
    ∃ b : ℕ → ℝ, (∀ k, 0 < b k) ∧ (∀ k, floorAt k ≤ b k) ∧
      Summable (fun k => (b k)^2) ∧
      ∀ k, μ (Good T f k (b k))ᶜ ≤ ENNReal.ofReal (η / 400) := by
  let a := jointEnergy T f μ
  refine ⟨bAt η a, bAt_pos hη a, bAt_floor hη a,
    bAt_square_summable (jointEnergy_nonneg T f) (jointEnergy_summable hT hf), ?_⟩
  intro k
  exact (bad_measure hT hf (bAt_pos hη a k) k).trans
    (ENNReal.ofReal_le_ofReal (error_ratio hη (jointEnergy_nonneg T f) k))

section Compact
variable [TopologicalSpace Ω]

omit [MeasurableSpace Ω] in
lemma chord_continuous {T : Ω → Ω} (hT : Continuous T) {f : Ω → ℝ}
    (hf : Continuous f) (n u : ℕ) : Continuous (fun x => chord (orbit T f x) n u) := by
  have hs (m : ℕ) : Continuous (fun x => prefixSum (orbit T f x) m) :=
    continuous_finsetSum _ (fun j _ => hf.comp (hT.iterate j))
  exact (hs u).sub (continuous_const.mul ((hs n).div_const _))

omit [MeasurableSpace Ω] in
lemma good_isClosed {d : ℕ} {T : Ω → Ω} (hT : Continuous T)
    {f : Fin d → Ω → ℝ} (hf : ∀ j, Continuous (f j)) (k : ℕ) (b : ℝ) :
    IsClosed (Good T f k b) := by
  have heq : Good T f k b = ⋂ j, ⋂ u, ⋂ (_ : u ≤ 2^(k + 1)),
      {x | |chord (orbit T (f j) x) (2^(k + 1)) u| ≤ b * (2 : ℝ)^k} := by
    ext x
    simp only [Good, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter (fun j => isClosed_iInter (fun u => isClosed_iInter
    (fun _ => isClosed_le (chord_continuous hT (hf j) _ u).abs continuous_const)))

variable [CompactSpace Ω] [BorelSpace Ω] [IsProbabilityMeasure μ]

/-- Compact good sets, with the source's 1−η/100 lower bound. The proof
actually gives 1−η/400. The displayed natural-coordinate block has length
2^(k+1), corresponding to the source's centered block [-2^k,2^k). -/
theorem compact_good_segments {d : ℕ} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hTc : Continuous T) {f : Fin d → Ω → ℝ} (hf : ∀ j, Continuous (f j))
    {η : ℝ} (hη : 0 < η) :
    ∃ b : ℕ → ℝ, (∀ k, 0 < b k) ∧ (∀ k, floorAt k ≤ b k) ∧
      Summable (fun k => (b k)^2) ∧ ∀ k,
      IsCompact (Good T f k (b k)) ∧ 1 - η / 100 ≤ μ.real (Good T f k (b k)) := by
  obtain ⟨b, hbpos, hbfloor, hbsum, hbad⟩ := good_segments hT
    (fun j => (hf j).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hη
  refine ⟨b, hbpos, hbfloor, hbsum, fun k => ⟨(good_isClosed hTc hf k (b k)).isCompact, ?_⟩⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbad k)
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  change μ.real (Good T f k (b k))ᶜ ≤ η / 400 at hreal
  rw [measureReal_compl (good_isClosed hTc hf k (b k)).measurableSet] at hreal
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at hreal
  change _ ≤ (μ (Good T f k (b k))).toReal
  linarith

/-- The actual centered good set, with the left endpoint at time −2^k. -/
def CenteredGood {d : ℕ} (S : Ω ≃ₜ Ω) (f : Fin d → Ω → ℝ) (k : ℕ) (b : ℝ) : Set Ω :=
  ((S.symm : Ω → Ω)^[2^k]) ⁻¹' Good S f k b

omit [MeasurableSpace Ω] [CompactSpace Ω] [BorelSpace Ω] in
lemma centeredGood_isClosed {d : ℕ} (S : Ω ≃ₜ Ω)
    {f : Fin d → Ω → ℝ} (hf : ∀ j, Continuous (f j)) (k : ℕ) (b : ℝ) :
    IsClosed (CenteredGood S f k b) :=
  (good_isClosed S.continuous hf k b).preimage (S.symm.continuous.iterate _)

omit [CompactSpace Ω] [IsProbabilityMeasure μ] in
/-- Centering does not alter the measure, since the inverse as well as the
forward transformation preserves the original measure. -/
lemma centeredGood_measure {d : ℕ} {S : Ω ≃ₜ Ω} (hS : MeasurePreserving S μ μ)
    {f : Fin d → Ω → ℝ} (hf : ∀ j, Continuous (f j)) (k : ℕ) (b : ℝ) :
    μ.real (CenteredGood S f k b) = μ.real (Good S f k b) := by
  have hinv : MeasurePreserving (S.symm : Ω → Ω) μ μ :=
    MeasurePreserving.symm S.toMeasurableEquiv hS
  exact (hinv.iterate _).measureReal_preimage (good_isClosed S.continuous hf k b).measurableSet.nullMeasurableSet

omit [MeasurableSpace Ω] [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω] in
lemma subinterval_chord {d : ℕ} {T : Ω → Ω} {f : Fin d → Ω → ℝ}
    {k : ℕ} {b : ℝ} {x : Ω} (hx : x ∈ Good T f k b)
    (j : Fin d) {u v : ℕ} (huv : u ≤ v) (hv : v ≤ 2^(k + 1)) :
    |prefixSum (orbit T (f j) x) v - prefixSum (orbit T (f j) x) u -
      (v - u : ℕ) * average (orbit T (f j) x) (2^(k + 1))| ≤ 2 * b * (2 : ℝ)^k := by
  have heq : prefixSum (orbit T (f j) x) v - prefixSum (orbit T (f j) x) u -
      (v - u : ℕ) * average (orbit T (f j) x) (2^(k + 1)) =
      chord (orbit T (f j) x) (2^(k + 1)) v - chord (orbit T (f j) x) (2^(k + 1)) u := by
    rw [Nat.cast_sub huv]
    dsimp [chord]
    ring
  rw [heq]
  calc
    _ ≤ |chord (orbit T (f j) x) (2^(k + 1)) v| +
        |chord (orbit T (f j) x) (2^(k + 1)) u| := abs_sub _ _
    _ ≤ _ := by linarith [hx j v hv, hx j u (huv.trans hv)]

/-- The simultaneous compact centered good sets of the stationary part of
Proposition good-frames. The geometric frame lift and its coordinate functions
are not postulated here: this lemma takes any compact stationary system. -/
theorem compact_centered_good_segments {d : ℕ} {S : Ω ≃ₜ Ω}
    (hS : MeasurePreserving S μ μ) {f : Fin d → Ω → ℝ} (hf : ∀ j, Continuous (f j))
    {η : ℝ} (hη : 0 < η) :
    ∃ b : ℕ → ℝ, (∀ k, 0 < b k) ∧ (∀ k, floorAt k ≤ b k) ∧
      Summable (fun k => (b k)^2) ∧ ∀ k,
      IsCompact (CenteredGood S f k (b k)) ∧
      1 - η / 100 ≤ μ.real (CenteredGood S f k (b k)) := by
  obtain ⟨b, hbp, hbf, hbs, hG⟩ := compact_good_segments hS S.continuous hf hη
  refine ⟨b, hbp, hbf, hbs, fun k => ⟨(centeredGood_isClosed S hf k (b k)).isCompact, ?_⟩⟩
  rw [centeredGood_measure hS hf]
  exact (hG k).2

end Compact

/-- Projection of a compact good set needs no measurable frame selection.
The sole measure input is the genuine pushforward identity. -/
theorem compact_projection_good {Γ : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
    [BorelSpace Ω] [IsProbabilityMeasure μ] [TopologicalSpace Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] {ν : Measure Γ} [IsProbabilityMeasure ν]
    {π : Ω → Γ} (hπ : Continuous π) (hpush : MeasurePreserving π μ ν)
    {G : Set Ω} (hG : IsCompact G) {a : ℝ} (ha : a ≤ μ.real G) :
    IsCompact (π '' G) ∧ a ≤ ν.real (π '' G) := by
  have himage := hG.image hπ
  refine ⟨himage, ha.trans ?_⟩
  calc
    μ.real G ≤ μ.real (π ⁻¹' (π '' G)) := measureReal_mono (Set.subset_preimage_image π G)
    _ = ν.real (π '' G) := hpush.measureReal_preimage himage.isClosed.measurableSet.nullMeasurableSet

end SmoothObstruction.GoodStationary

namespace SmoothObstruction.OrbitCocycle
open MeasureTheory Filter Topology Set
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {d : ℕ} {K : ℝ}

noncomputable def logDiagonal (j : Fin d) (z : Path (X:=X) (d:=d) (K:=K) × QR.Frame d) :=
  Real.log (QR.triangular (matrix z.1) z.2 j j)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_logDiagonal (j : Fin d) :
    Continuous (logDiagonal (X:=X) (K:=K) j) := by
  let := TopologicalSpace.metrizableSpaceMetric (Path (X:=X) (d:=d) (K:=K))
  exact QR.continuous_log_diagonal (matrix (X:=X) (d:=d) (K:=K)) continuous_matrix j

/-- The actual good-frame burden for a bounded coordinate cocycle is
constructed from stationarity, with compactness restored inside the Borel
full-measure genuine-code locus rather than asserted for a measurable graph.
The projection uses the middle of each length-2n block. -/
theorem compact_actual_good (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K)
    (hA : Measurable A) (μ : ProbabilityMeasure X)
    (hS : MeasurePreserving S (μ : Measure X) (μ : Measure X))
    {η : ℝ} (hη : 0<η) :
    ∃ (ν : ProbabilityMeasure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d))
      (b : ℕ → ℝ) (G : ℕ → Set (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)),
      (∀ k, 0<b k) ∧ (∀ k,GoodStationary.floorAt k≤b k) ∧
      Summable (fun k => (b k)^2) ∧ ∀ k,
      IsCompact (G k) ∧
      (∀ z∈G k,z.1∈Actual S A ∧
        z∈GoodStationary.Good (QR.skew shift matrix) logDiagonal k (b k)) ∧
      1-η/100≤(ν : Measure (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)).real (G k) ∧
      IsCompact ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k) ∧
      1-η/100≤(μ : Measure X).real ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k) := by
  let := TopologicalSpace.metrizableSpaceMetric (Path (X:=X) (d:=d) (K:=K))
  obtain ⟨ν,hν,hπ,hact⟩ := stationary_qr_code S A hA μ hS
  have hTc : Continuous (QR.skew (shift (X:=X) (d:=d) (K:=K)) matrix) :=
    QR.continuous_skew _ continuous_shift _ continuous_matrix
  obtain ⟨b,hbp,hbf,hbs,hG⟩ := GoodStationary.compact_good_segments hν hTc
    (fun j => continuous_logDiagonal j) (show 0<η/2 by linarith)
  have hco : MeasurableSet (Prod.fst ⁻¹' Actual S A :
      Set (Path (X:=X) (d:=d) (K:=K) × QR.Frame d)) :=
    (actual_measurable S A hA).preimage measurable_fst
  have hchoose (k : ℕ) : ∃ F : Set (Path (X:=X) (d:=d) (K:=K) × QR.Frame d),
      F ⊆ GoodStationary.Good (QR.skew shift matrix) logDiagonal k (b k) ∩
        Prod.fst ⁻¹' Actual S A ∧ IsCompact F ∧
        1-η/100≤(ν : Measure _).real F := by
    let H : Set (Path (X:=X) (d:=d) (K:=K) × QR.Frame d) :=
      GoodStationary.Good (QR.skew shift matrix) logDiagonal k (b k)
    have hh : MeasurableSet H := (hG k).1.isClosed.measurableSet
    have he : (ν : Measure _) (H∩Prod.fst ⁻¹' Actual S A)=(ν : Measure _) H := by
      apply measure_congr
      filter_upwards [hact] with z hz
      change (z ∈ H ∧ z.1 ∈ Actual S A) = (z ∈ H)
      exact propext (and_iff_left hz)
    obtain ⟨F,hF,hFc,hFm⟩ := (hh.inter hco).exists_isCompact_lt_add
      (measure_ne_top (ν : Measure _) _) (show ENNReal.ofReal (η/400)≠0 by positivity)
    refine ⟨F,hF,hFc,?_⟩
    rw [he] at hFm
    have hr := (ENNReal.toReal_lt_toReal (measure_ne_top (ν : Measure _) H)
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top (ν : Measure _) F,ENNReal.ofReal_ne_top⟩)).mpr hFm
    rw [ENNReal.toReal_add (measure_ne_top (ν : Measure _) F) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at hr
    have hg := (hG k).2
    change 1-(η/2)/100≤((ν : Measure _) H).toReal at hg
    change 1-η/100≤((ν : Measure _) F).toReal
    linarith
  choose G hsub hGc hGm using hchoose
  refine ⟨ν,b,G,hbp,hbf,hbs,?_⟩
  intro k
  have hp : Continuous (fun z : Path (X:=X) (d:=d) (K:=K) × QR.Frame d =>
      (z.1 ((2^k : ℕ) : ℤ)).1) :=
    continuous_fst.comp ((continuous_apply _).comp continuous_fst)
  have hmp : MeasurePreserving (fun z : Path (X:=X) (d:=d) (K:=K) × QR.Frame d =>
      (z.1 ((2^k : ℕ) : ℤ)).1) (ν : Measure _) (μ : Measure X) :=
    ⟨hp.measurable,marginal_at S A hA μ hS ν hπ (2^k)⟩
  have hproj := GoodStationary.compact_projection_good hp hmp (hGc k) (hGm k)
  exact ⟨hGc k,fun z hz => ⟨(hsub k hz).2,(hsub k hz).1⟩,hGm k,hproj⟩

end SmoothObstruction.OrbitCocycle

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology MeasureTheory
open scoped Manifold ContDiff
universe u
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Genuine manifold good frames, with no stationary-frame or bounded-
cocycle assumption. The finite compact atlas, actual chart derivative,
invariant QR lift, square-summable burden, and compact good base sets
are all constructed. The model may have corners, in particular boundary. -/
theorem manifold_good_frames (S : Diffeomorph I I M M ∞)
    (μ : ProbabilityMeasure M) (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M))
    {η : ℝ} (hη : 0<η) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : MeasurableSpace ι) (_ : MeasurableSingletonClass ι)
      (a : ι → M) (K : ι → Set M) (c : M → ι) (C : ℝ)
      (A : M → CompactMatrix.Alphabet d C),
      (∀ i,IsCompact (K i)) ∧ (∀ i,K i⊆(chartAt H (a i)).source) ∧
      Measurable c ∧ (∀ x,x∈K (c x)) ∧ 0<C ∧ Measurable A ∧
      (∀ x,(A x).val=coord I S (a (c x)) (a (c (S x))) x) ∧
      ∃ (ν : ProbabilityMeasure (OrbitCocycle.Path (X:=M) (d:=d) (K:=C) × QR.Frame d))
        (b : ℕ → ℝ) (G : ℕ → Set (OrbitCocycle.Path (X:=M) (d:=d) (K:=C) × QR.Frame d)),
        (∀ k,0<b k) ∧ (∀ k,GoodStationary.floorAt k≤b k) ∧
        Summable (fun k => (b k)^2) ∧ ∀ k,
        IsCompact (G k) ∧
        (∀ z∈G k,z.1∈OrbitCocycle.Actual S.toHomeomorph A ∧
          z∈GoodStationary.Good (QR.skew OrbitCocycle.shift OrbitCocycle.matrix)
            OrbitCocycle.logDiagonal k (b k)) ∧
        1-η/100≤(ν : Measure _).real (G k) ∧
        IsCompact ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k) ∧
        1-η/100≤(μ : Measure M).real ((fun z => (z.1 ((2^k : ℕ) : ℤ)).1) '' G k) := by
  obtain ⟨ι,hfin,hmeas,hsc,a,K,c,C,A,hK,hKU,hc,hcK,hC,hA,heq⟩ := actual_coordinate_cocycle_discrete I S
  let : Fintype ι := hfin
  let : MeasurableSpace ι := hmeas
  refine ⟨ι,hfin,hmeas,hsc,a,K,c,C,A,hK,hKU,hc,hcK,hC,hA,heq,?_⟩
  exact OrbitCocycle.compact_actual_good S.toHomeomorph A hA μ hS hη
end SmoothObstruction.ManifoldCoordinates

end

end OAI
