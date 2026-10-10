import OAI.Analysis.TracialSplitting.Model

namespace OAI

universe uA uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

def IsFull {D : Type uD} [CStarAlgebra D] (g : D) : Prop :=
  closure (TwoSidedIdeal.span {g} : Set D) = Set.univ

def uniformTwoNorm {D : Type uD} [CStarAlgebra D] [PartialOrder D] (a : D) : ℝ :=
  ⨆ τ : TracialState D, traceTwoNorm τ a

def uniformHalvingError {D : Type uD} [CStarAlgebra D] [PartialOrder D]
    (p x : D) : ℝ :=
  ⨆ τ : TracialState D, ‖τ.functional (p * x) - (1 / 2 : ℂ) * τ.functional x‖

section TraceIdentities

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D]

lemma trace_projection_corner (τ : TracialState D) {p : D}
    (hp : IsStarProjection p) (a : D) :
    τ.functional (p * a * p) = τ.functional (p * a) := by
  rw [τ.tracial (p * a) p, ← mul_assoc, hp.isIdempotentElem]

lemma trace_unitary_conjugate (τ : TracialState D) (x : unitary D) (a : D) :
    τ.functional ((x : D) * a * star (x : D)) = τ.functional a := by
  rw [τ.tracial ((x : D) * a) (star (x : D))]
  simp only [← mul_assoc, Unitary.coe_star_mul_self, one_mul]

lemma trace_unitary_commutator_square (τ : TracialState D) (x : unitary D)
    {p : D} (hp : IsStarProjection p) :
    τ.functional (star ((x : D) * p - p * (x : D)) *
      ((x : D) * p - p * (x : D))) =
    2 * τ.functional p - 2 * τ.functional
      (star (p * (x : D) * p) * (p * (x : D) * p)) := by
  have hpp : p * p = p := hp.isIdempotentElem
  have hsp : star p = p := hp.isSelfAdjoint
  have h1 : p * star (x : D) * ((x : D) * p) = p := by
    rw [mul_assoc, ← mul_assoc (star (x : D)), Unitary.coe_star_mul_self,
      one_mul, hpp]
  have h2 : star (x : D) * p * (p * (x : D)) =
      star (x : D) * p * (x : D) := by
    simp only [mul_assoc, ← mul_assoc p p, hpp]
  have ht : τ.functional (star (x : D) * p * (x : D)) = τ.functional p := by
    rw [τ.tracial (star (x : D) * p) (x : D)]
    rw [← mul_assoc, x.property.2, one_mul]
  have hcross : τ.functional (star (x : D) * p * ((x : D) * p)) =
      τ.functional (p * star (x : D) * (p * (x : D))) := by
    rw [τ.tracial (star (x : D) * p) ((x : D) * p)]
    simp only [mul_assoc]
    rw [τ.tracial (x : D) (p * (star (x : D) * p))]
    simp only [mul_assoc]
  have hcompress : τ.functional (star (p * (x : D) * p) *
      (p * (x : D) * p)) =
      τ.functional (p * star (x : D) * (p * (x : D))) := by
    simp only [star_mul, hsp]
    have he : p * (star (x : D) * p) * (p * (x : D) * p) =
        p * (star (x : D) * (p * (x : D))) * p := by
      simp only [mul_assoc, ← mul_assoc p p, hpp]
    rw [he, trace_projection_corner τ hp]
    simp only [mul_assoc]
  rw [hcompress]
  simp only [star_sub, star_mul, hsp, sub_mul, mul_sub, h1, h2,
    map_sub, ht, hcross]
  ring

end TraceIdentities

section TraceBounds

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_sq (τ : TracialState D) (a : D) :
    traceTwoNorm τ a ^ 2 = (τ.functional (star a * a)).re := by
  exact Real.sq_sqrt (τ.functional.map_nonneg (star_mul_self_nonneg a)).1

lemma traceTwoNorm_smul (τ : TracialState D) (z : ℂ) (a : D) :
    traceTwoNorm τ (z • a) = ‖z‖ * traceTwoNorm τ a := by
  simp only [traceTwoNorm_eq_gns, map_smul, norm_smul]

lemma trace_norm_mul_le (τ : TracialState D) (a b : D) :
    ‖τ.functional (a * b)‖ ≤ traceTwoNorm τ a * traceTwoNorm τ b := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (τ.functional.toPreGNS (star a))
    (τ.functional.toPreGNS b)
  simpa only [PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_star,
    ← traceTwoNorm_eq_gns, traceTwoNorm_star] using h

lemma unitary_commutator_energy (τ : TracialState D) (x : unitary D)
    {p : D} (hp : IsStarProjection p) :
    traceTwoNorm τ ((x : D) * p - p * (x : D)) ^ 2 =
      2 * (τ.functional p).re - 2 * traceTwoNorm τ (p * (x : D) * p) ^ 2 := by
  simp only [traceTwoNorm_sq]
  rw [trace_unitary_commutator_square τ x hp]
  simp

end TraceBounds

section OrthogonalEnergy

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D]

lemma trace_commutator_square_expansion (τ : TracialState D)
    {p : D} (hp : IsStarProjection p) (x : D) :
    τ.functional (star (x * p - p * x) * (x * p - p * x)) =
      τ.functional (star x * x * p) + τ.functional (star x * p * x) -
        2 * τ.functional (p * star x * p * x) := by
  have hsp : star p = p := hp.isSelfAdjoint
  have hpp : p * p = p := hp.isIdempotentElem
  have h1 : τ.functional (p * star x * (x * p)) =
      τ.functional (star x * x * p) := by
    calc
      τ.functional (p * star x * (x * p)) =
          τ.functional (p * (star x * x) * p) := by simp only [mul_assoc]
      _ = τ.functional (p * (star x * x)) := trace_projection_corner τ hp _
      _ = τ.functional (star x * x * p) := τ.tracial _ _
  have h2 : star x * p * (p * x) = star x * p * x := by
    simp only [mul_assoc, ← mul_assoc p p, hpp]
  have h3 : τ.functional (star x * p * (x * p)) =
      τ.functional (p * star x * p * x) := by
    simpa only [mul_assoc] using τ.tracial (star x * p * x) p
  simp only [star_sub, star_mul, hsp, sub_mul, mul_sub, map_sub, h1, h2, h3]
  simp only [← mul_assoc]
  ring

lemma trace_cross_compression_square (τ : TracialState D) {p q : D}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (x : D) :
    τ.functional (star (q * x * p) * (q * x * p)) =
      τ.functional (p * star x * q * x) := by
  have hsp : star p = p := hp.isSelfAdjoint
  have hsq : star q = q := hq.isSelfAdjoint
  have hqq : q * q = q := hq.isIdempotentElem
  calc
    τ.functional (star (q * x * p) * (q * x * p)) =
        τ.functional (p * (star x * q * x) * p) := by
      simp only [star_mul, hsp, hsq, mul_assoc, ← mul_assoc q q, hqq]
    _ = τ.functional (p * (star x * q * x)) := trace_projection_corner τ hp _
    _ = τ.functional (p * star x * q * x) := by simp only [mul_assoc]

variable [StarOrderedRing D]

lemma orthogonal_pair_energy_identity (τ : TracialState D) {p q : D}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) (x : D) :
    traceTwoNorm τ (x * (p + q) - (p + q) * x) ^ 2 =
      traceTwoNorm τ (x * p - p * x) ^ 2 + traceTwoNorm τ (x * q - q * x) ^ 2 -
        2 * traceTwoNorm τ (q * x * p) ^ 2 - 2 * traceTwoNorm τ (p * x * q) ^ 2 := by
  have hid : τ.functional (star (x * (p + q) - (p + q) * x) *
      (x * (p + q) - (p + q) * x)) =
      τ.functional (star (x * p - p * x) * (x * p - p * x)) +
      τ.functional (star (x * q - q * x) * (x * q - q * x)) -
      2 * τ.functional (star (q * x * p) * (q * x * p)) -
      2 * τ.functional (star (p * x * q) * (p * x * q)) := by
    rw [trace_commutator_square_expansion τ (hp.add hq hpq),
      trace_commutator_square_expansion τ hp, trace_commutator_square_expansion τ hq,
      trace_cross_compression_square τ hp hq, trace_cross_compression_square τ hq hp]
    simp only [mul_add, add_mul, map_add]
    ring
  simpa [traceTwoNorm_sq] using congrArg Complex.re hid

lemma orthogonal_pair_energy_le (τ : TracialState D) {p q : D}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) (x : D) :
    traceTwoNorm τ (x * (p + q) - (p + q) * x) ^ 2 ≤
      traceTwoNorm τ (x * p - p * x) ^ 2 + traceTwoNorm τ (x * q - q * x) ^ 2 := by
  rw [orthogonal_pair_energy_identity τ hp hq hpq]
  nlinarith [sq_nonneg (traceTwoNorm τ (q * x * p)),
    sq_nonneg (traceTwoNorm τ (p * x * q))]

theorem orthogonal_sum_energy_le {I : Type uI} (s : Finset I) (t : I → D)
    (ht : ∀ i ∈ s, IsStarProjection (t i))
    (hortho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i * t j = 0)
    (τ : TracialState D) (x : D) :
    IsStarProjection (∑ i ∈ s, t i) ∧
      traceTwoNorm τ (x * (∑ i ∈ s, t i) - (∑ i ∈ s, t i) * x) ^ 2 ≤
        ∑ i ∈ s, traceTwoNorm τ (x * t i - t i * x) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsStarProjection.zero]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, IsStarProjection (t i) := fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have hso : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i * t j = 0 :=
      fun i hi j hj hij => hortho i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij
    obtain ⟨hproj, henergy⟩ := ih hs hso
    have ha0 : t a * ∑ i ∈ s, t i = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact hortho a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    have hap := ht a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha]
    refine ⟨hap.add hproj ha0, ?_⟩
    rw [Finset.sum_insert ha]
    exact (orthogonal_pair_energy_le τ hap hproj ha0 x).trans (add_le_add (le_refl _) henergy)

end OrthogonalEnergy

section WeightedAveraging

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Fintype I]

def weightedAverage (w : I → ℝ) (v : I → D) (b : D) : D :=
  ∑ i, w i • (v i * b * star (v i))

lemma weightedAverage_nonneg (w : I → ℝ) (v : I → D)
    (hw : ∀ i, 0 ≤ w i) {b : D} (hb : 0 ≤ b) :
    0 ≤ weightedAverage w v b := by
  exact Finset.sum_nonneg fun i _ => smul_nonneg (hw i) (star_right_conjugate_nonneg hb (v i))

lemma weightedAverage_le_one (w : I → ℝ) (v : I → D)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) {b : D} (hb : 0 ≤ b) (hb1 : ‖b‖ ≤ 1) :
    weightedAverage w v b ≤ 1 := by
  have hi (i : I) : v i * b * star (v i) ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (star_right_conjugate_nonneg hb (v i))).mp
    calc
      ‖v i * b * star (v i)‖ ≤ ‖v i * b‖ * ‖star (v i)‖ := norm_mul_le _ _
      _ ≤ (‖v i‖ * ‖b‖) * ‖v i‖ := by
        rw [norm_star]
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ 1 := by
        calc
          (‖v i‖ * ‖b‖) * ‖v i‖ ≤ (1 * 1) * 1 :=
            mul_le_mul (mul_le_mul (hv i) hb1 (norm_nonneg _) (by norm_num))
              (hv i) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
  calc
    weightedAverage w v b ≤ ∑ i, w i • (1 : D) :=
      Finset.sum_le_sum fun i _ => smul_le_smul_of_nonneg_left (hi i) (hw i)
    _ = 1 := by rw [← Finset.sum_smul, hwsum, one_smul]

lemma trace_mul_nonneg (τ : TracialState D) {a b : D} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ τ.functional (a * b) := by
  have hs : star (CFC.sqrt a) = CFC.sqrt a := (CFC.sqrt_nonneg a).star_eq
  have ht : τ.functional (CFC.sqrt a * b * CFC.sqrt a) = τ.functional (a * b) := by
    rw [τ.tracial (CFC.sqrt a * b) (CFC.sqrt a), ← mul_assoc,
      CFC.sqrt_mul_sqrt_self a ha]
  rw [← ht]
  apply τ.functional.map_nonneg
  simpa only [hs] using (star_left_conjugate_nonneg hb (CFC.sqrt a))

lemma trace_projection_mul_bounds (τ : TracialState D) {q c : D}
    (hq : IsStarProjection q) (hc : 0 ≤ c) :
    0 ≤ (τ.functional (q * c)).re ∧ (τ.functional (q * c)).re ≤ (τ.functional c).re := by
  refine ⟨(trace_mul_nonneg τ hq.nonneg hc).1, ?_⟩
  have h := (trace_mul_nonneg τ hq.one_sub.nonneg hc).1
  simp only [sub_mul, one_mul, map_sub, Complex.sub_re, Complex.zero_re] at h
  linarith

lemma weightedAverage_mass (τ : TracialState D) (w : I → ℝ) (v : I → D)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) {q : D} (hq : IsStarProjection q)
    {μ : ℝ} (hdefect : ‖1 - weightedAverage w v 1‖ < μ) :
    (τ.functional q).re - μ ≤ (τ.functional (weightedAverage w v q)).re ∧
      (τ.functional (weightedAverage w v q)).re ≤ (τ.functional q).re := by
  let c : D := 1 - weightedAverage w (fun i => star (v i)) 1
  have hcov : weightedAverage w (fun i => star (v i)) 1 ≤ 1 :=
    weightedAverage_le_one w (fun i => star (v i)) hw hwsum
      (fun i => by simpa only [norm_star] using hv i) zero_le_one ((CStarAlgebra.norm_le_one_iff_of_nonneg (1 : D) zero_le_one).mpr le_rfl)
  have hc : 0 ≤ c := sub_nonneg.mpr hcov
  have htrace : τ.functional c = τ.functional (1 - weightedAverage w v 1) := by
    simp only [c, weightedAverage, map_sub, map_sum, τ.functional.map_smul_of_tower,
      mul_one, star_star]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [τ.tracial (star (v i)) (v i)]
  have hmass : τ.functional (q * c) =
      τ.functional q - τ.functional (weightedAverage w v q) := by
    simp only [c, weightedAverage, mul_sub, mul_one, Finset.mul_sum,
      mul_smul_comm, mul_one, star_star, map_sub, map_sum,
      τ.functional.map_smul_of_tower]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [τ.tracial (v i * q) (star (v i))]
    congr 1
    rw [τ.tracial q (star (v i) * v i)]
    simp only [mul_assoc]
  have hbound := trace_projection_mul_bounds τ hq hc
  rw [hmass, Complex.sub_re] at hbound
  have hcμ : (τ.functional c).re < μ := calc
    (τ.functional c).re = (τ.functional (1 - weightedAverage w v 1)).re := congrArg Complex.re htrace
    _ ≤ ‖τ.functional (1 - weightedAverage w v 1)‖ := Complex.re_le_norm _
    _ ≤ ‖1 - weightedAverage w v 1‖ := trace_norm_le_norm τ _
    _ < μ := hdefect
  constructor <;> linarith [hbound.1, hbound.2]

end WeightedAveraging

section PowersStormer

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def traceOneNorm (τ : TracialState D) (a : D) : ℝ :=
  (τ.functional (CFC.abs a)).re

lemma traceOneNorm_nonneg (τ : TracialState D) (a : D) : 0 ≤ traceOneNorm τ a :=
  (τ.functional.map_nonneg (CFC.abs_nonneg a)).1

lemma trace_selfAdjoint_contraction_mul_le (τ : TracialState D)
    {s h : D} (hs : IsSelfAdjoint s) (hh : IsSelfAdjoint h) (hsn : ‖s‖ ≤ 1) :
    (τ.functional (s * h)).re ≤ traceOneNorm τ h := by
  have hmap : algebraMap ℝ D ‖s‖ ≤ 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using
      (smul_le_smul_of_nonneg_right hsn (zero_le_one : (0 : D) ≤ 1))
  have hs1 : s ≤ 1 := hs.le_algebraMap_norm_self.trans hmap
  have h1s : -(1 : D) ≤ s := (neg_le_neg hmap).trans hs.neg_algebraMap_norm_le_self
  have hp := (trace_mul_nonneg τ (sub_nonneg.mpr hs1) (CFC.posPart_nonneg h)).1
  have hn := (trace_mul_nonneg τ (neg_le_iff_add_nonneg'.mp h1s)
    (CFC.negPart_nonneg h)).1
  have he : (1 - s) * h⁺ + (1 + s) * h⁻ = CFC.abs h - s * h := by
    calc
      _ = (h⁺ + h⁻) - s * (h⁺ - h⁻) := by noncomm_ring
      _ = _ := by rw [CFC.posPart_add_negPart h hh, CFC.posPart_sub_negPart h hh]
  have he' := congrArg (fun a => (τ.functional a).re) he
  simp only [map_add, map_sub, Complex.add_re, Complex.sub_re] at he'
  change (τ.functional (s * h)).re ≤ (τ.functional (CFC.abs h)).re
  simp only [Complex.zero_re] at hp hn
  linarith

lemma trace_square_sub_le_abs (τ : TracialState D) {u v : D}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (τ.functional ((u - v) * (u - v))).re ≤
      (τ.functional ((u + v) * CFC.abs (u - v))).re := by
  have hd : IsSelfAdjoint (u - v) := (IsSelfAdjoint.of_nonneg hu).sub
    (IsSelfAdjoint.of_nonneg hv)
  have hp := (trace_mul_nonneg τ (add_nonneg hv hv) (CFC.posPart_nonneg (u - v))).1
  have hn := (trace_mul_nonneg τ (add_nonneg hu hu) (CFC.negPart_nonneg (u - v))).1
  have he : (v + v) * (u - v)⁺ + (u + u) * (u - v)⁻ =
      (u + v) * CFC.abs (u - v) - (u - v) * (u - v) := by
    rw [← CFC.posPart_add_negPart (u - v) hd]
    have hde := CFC.posPart_sub_negPart (u - v) hd
    calc
      _ = (u + v) * ((u - v)⁺ + (u - v)⁻) -
          (u - v) * ((u - v)⁺ - (u - v)⁻) := by noncomm_ring
      _ = _ := by rw [hde]
  have he' := congrArg (fun a => (τ.functional a).re) he
  simp only [map_add, map_sub, Complex.add_re, Complex.sub_re] at he'
  simp only [Complex.zero_re] at hp hn
  linarith

def regularizedSign (ε : ℝ) (d : D) : D :=
  cfc (fun t : ℝ => t / (|t| + ε)) d

lemma continuous_regularizedSign {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun t : ℝ => t / (|t| + ε)) :=
  continuous_id.div (continuous_abs.add continuous_const)
    (fun t => ne_of_gt (add_pos_of_nonneg_of_pos (abs_nonneg t) hε))

omit [PartialOrder D] [StarOrderedRing D] in
lemma regularizedSign_selfAdjoint (ε : ℝ) (d : D) :
    IsSelfAdjoint (regularizedSign ε d) := cfc_predicate _ _

omit [PartialOrder D] [StarOrderedRing D] in
lemma regularizedSign_norm_le {ε : ℝ} (hε : 0 < ε) (d : D) :
    ‖regularizedSign ε d‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro t _
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (add_pos_of_nonneg_of_pos (abs_nonneg t) hε)]
  apply (div_le_one (add_pos_of_nonneg_of_pos (abs_nonneg t) hε)).mpr
  linarith

omit [PartialOrder D] [StarOrderedRing D] in
lemma regularizedSign_commute (ε : ℝ) {d : D} (hd : IsSelfAdjoint d) :
    Commute (regularizedSign ε d) d :=
  hd.commute_cfc (.refl d) _

lemma regularizedSign_scalar_error {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖‖t‖ - t / (|t| + ε) * t‖ ≤ ε := by
  have hpos := add_pos_of_nonneg_of_pos (abs_nonneg t) hε
  have heq : |t| - t / (|t| + ε) * t = ε * |t| / (|t| + ε) := by
    field_simp
    nlinarith [sq_abs t]
  rw [Real.norm_eq_abs t, heq, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg hε.le (abs_nonneg t)) hpos.le)]
  apply (div_le_iff₀ hpos).mpr
  nlinarith

lemma regularizedSign_error {ε : ℝ} (hε : 0 < ε) {d : D}
    (hd : IsSelfAdjoint d) :
    ‖CFC.abs d - regularizedSign ε d * d‖ ≤ ε := by
  have hf := continuous_regularizedSign hε
  have hmul : cfc (fun t : ℝ => t / (|t| + ε) * t) d =
      regularizedSign ε d * d := by
    rw [cfc_mul (fun t : ℝ => t / (|t| + ε)) (fun t : ℝ => t) d
      (hf := hf.continuousOn), cfc_id' ℝ d]
    rfl
  rw [CFC.abs_eq_cfcₙ_norm d hd, cfcₙ_eq_cfc (hf0 := norm_zero), ← hmul,
    ← cfc_sub (fun t : ℝ => ‖t‖) (fun t : ℝ => t / (|t| + ε) * t) d
      (hf := continuous_norm.continuousOn) (hg := (hf.mul continuous_id).continuousOn)]
  exact norm_cfc_le hε.le (fun t _ => regularizedSign_scalar_error hε t)

omit [StarOrderedRing D] in
lemma trace_square_difference_sign (τ : TracialState D) (u v s : D)
    (hcomm : Commute s (u - v)) :
    τ.functional (s * (u * u - v * v)) =
      τ.functional ((u + v) * s * (u - v)) := by
  have he : s * (u * u - v * v) =
      s * u * (u - v) + s * (u - v) * v := by noncomm_ring
  have ht : τ.functional (s * u * (u - v)) =
      τ.functional (u * s * (u - v)) := by
    rw [τ.tracial (s * u) (u - v), ← mul_assoc, ← hcomm.eq,
      τ.tracial (s * (u - v)) u, mul_assoc]
  rw [he, map_add, ht, τ.tracial (s * (u - v)) v, ← map_add]
  congr 1
  noncomm_ring

lemma trace_square_sub_le_oneNorm (τ : TracialState D) {u v : D}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (τ.functional ((u - v) * (u - v))).re ≤ traceOneNorm τ (u * u - v * v) := by
  have hd : IsSelfAdjoint (u - v) := (IsSelfAdjoint.of_nonneg hu).sub
    (IsSelfAdjoint.of_nonneg hv)
  have hh : IsSelfAdjoint (u * u - v * v) := by
    change star (u * u - v * v) = _
    simp only [star_sub, star_mul, hu.star_eq, hv.star_eq]
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := δ / (‖u + v‖ + 1)
  have hepos : 0 < ε := div_pos hδ (by positivity)
  let s := regularizedSign ε (u - v)
  have hs := regularizedSign_selfAdjoint ε (u - v)
  have hsb := trace_selfAdjoint_contraction_mul_le τ hs hh (regularizedSign_norm_le hepos _)
  have hre := congrArg Complex.re (trace_square_difference_sign τ u v s
    (regularizedSign_commute ε hd))
  have hnear : (τ.functional ((u + v) * CFC.abs (u - v))).re -
      (τ.functional ((u + v) * s * (u - v))).re ≤ ‖u + v‖ * ε := by
    calc
      _ = (τ.functional ((u + v) * (CFC.abs (u - v) - s * (u - v)))).re := by
        simp only [mul_sub, map_sub, Complex.sub_re, mul_assoc]
      _ ≤ ‖τ.functional ((u + v) * (CFC.abs (u - v) - s * (u - v)))‖ :=
        Complex.re_le_norm _
      _ ≤ ‖(u + v) * (CFC.abs (u - v) - s * (u - v))‖ := trace_norm_le_norm τ _
      _ ≤ ‖u + v‖ * ‖CFC.abs (u - v) - s * (u - v)‖ := norm_mul_le _ _
      _ ≤ ‖u + v‖ * ε := mul_le_mul_of_nonneg_left (regularizedSign_error hepos hd)
        (norm_nonneg _)
  have heδ : ‖u + v‖ * ε ≤ δ := by
    have ht : (‖u + v‖ + 1) * ε = δ := by
      dsimp [ε]
      field_simp
    nlinarith [norm_nonneg (u + v)]
  have hl := trace_square_sub_le_abs τ hu hv
  linarith

theorem powers_stormer (τ : TracialState D) {b c : D} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    traceTwoNorm τ (CFC.sqrt b - CFC.sqrt c) ^ 2 ≤ traceOneNorm τ (b - c) := by
  have h := trace_square_sub_le_oneNorm τ (CFC.sqrt_nonneg b) (CFC.sqrt_nonneg c)
  rw [CFC.sqrt_mul_sqrt_self b hb, CFC.sqrt_mul_sqrt_self c hc] at h
  rw [traceTwoNorm_sq, ((CFC.sqrt_nonneg b).isSelfAdjoint.sub
    (CFC.sqrt_nonneg c).isSelfAdjoint).star_eq]
  exact h

lemma traceOneNorm_le_of_pairing (τ : TracialState D) {h : D} (hh : IsSelfAdjoint h)
    {C : ℝ} (hC : ∀ s : D, IsSelfAdjoint s → ‖s‖ ≤ 1 →
      (τ.functional (s * h)).re ≤ C) : traceOneNorm τ h ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let s := regularizedSign ε h
  have hbound := hC s (regularizedSign_selfAdjoint ε h) (regularizedSign_norm_le hε h)
  have herror : traceOneNorm τ h - (τ.functional (s * h)).re ≤ ε := by
    calc
      _ = (τ.functional (CFC.abs h - s * h)).re := by
        simp only [traceOneNorm, map_sub, Complex.sub_re]
      _ ≤ ‖τ.functional (CFC.abs h - s * h)‖ := Complex.re_le_norm _
      _ ≤ ‖CFC.abs h - s * h‖ := trace_norm_le_norm τ _
      _ ≤ ε := regularizedSign_error hε hh
  linarith

lemma traceOneNorm_add_le (τ : TracialState D) {a b : D}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    traceOneNorm τ (a + b) ≤ traceOneNorm τ a + traceOneNorm τ b := by
  apply traceOneNorm_le_of_pairing τ (ha.add hb)
  intro s hs hsn
  simp only [mul_add, map_add, Complex.add_re]
  exact add_le_add (trace_selfAdjoint_contraction_mul_le τ hs ha hsn)
    (trace_selfAdjoint_contraction_mul_le τ hs hb hsn)

@[simp] lemma traceOneNorm_neg (τ : TracialState D) (a : D) :
    traceOneNorm τ (-a) = traceOneNorm τ a := by simp [traceOneNorm]

end PowersStormer

section ProjectiveAveraging

open scoped TensorProduct

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_projection_sq (τ : TracialState D) {q : D}
    (hq : IsStarProjection q) : traceTwoNorm τ q ^ 2 = (τ.functional q).re := by
  rw [traceTwoNorm_sq, hq.isSelfAdjoint.star_eq, hq.isIdempotentElem]

lemma trace_sandwich_pairing_le (τ : TracialState D) {q : D}
    (hq : IsStarProjection q) (s a b : D) :
    ‖τ.functional (s * a * q * b)‖ ≤
      ‖s‖ * (τ.functional q).re * (‖a‖ * ‖b‖) := by
  have heq : s * a * q * b = ((s * a) * q) * (q * b) := by
    simp only [mul_assoc]
    rw [← mul_assoc q q b, hq.isIdempotentElem]
  have hq0 := traceTwoNorm_nonneg τ q
  calc
    _ ≤ traceTwoNorm τ ((s * a) * q) * traceTwoNorm τ (q * b) := by
      rw [heq]; exact trace_norm_mul_le τ _ _
    _ ≤ (‖s * a‖ * traceTwoNorm τ q) * (‖b‖ * traceTwoNorm τ q) :=
      mul_le_mul (traceTwoNorm_mul_left τ _ _) (traceTwoNorm_mul_right τ _ _)
        (traceTwoNorm_nonneg τ _) (by positivity)
    _ ≤ (‖s‖ * ‖a‖ * traceTwoNorm τ q) * (‖b‖ * traceTwoNorm τ q) := by
      gcongr; exact norm_mul_le _ _
    _ = ‖s‖ * (τ.functional q).re * (‖a‖ * ‖b‖) := by
      rw [← traceTwoNorm_projection_sq τ hq]; ring

def sandwichMultilinear (q : D) : MultilinearMap ℂ (fun _ : Fin 2 => D) D :=
  MultilinearMap.mk' (fun z => z 0 * q * z 1)
    (by intro z i a b; fin_cases i <;> simp [mul_add, add_mul])
    (by
      intro z i c a
      fin_cases i
      · simp
      · simp)

omit [PartialOrder D] [StarOrderedRing D] in
@[simp] lemma sandwichMultilinear_apply (q : D) (z : Fin 2 → D) :
    sandwichMultilinear q z = z 0 * q * z 1 := rfl

def traceSandwichMultilinear (τ : TracialState D) (q s : D) :
    MultilinearMap ℂ (fun _ : Fin 2 => D) ℂ :=
  (τ.functional.toLinearMap.comp (LinearMap.mulLeft ℂ s)).compMultilinearMap
    (sandwichMultilinear q)

omit [StarOrderedRing D] in
@[simp] lemma traceSandwichMultilinear_apply (τ : TracialState D) (q s : D)
    (z : Fin 2 → D) : traceSandwichMultilinear τ q s z =
    τ.functional (s * (z 0 * q * z 1)) := rfl

lemma traceSandwichMultilinear_bound (τ : TracialState D) {q : D}
    (hq : IsStarProjection q) (s : D) (z : Fin 2 → D) :
    ‖traceSandwichMultilinear τ q s z‖ ≤
      (‖s‖ * (τ.functional q).re) * ∏ i, ‖z i‖ := by
  simpa only [traceSandwichMultilinear_apply, Fin.prod_univ_two, mul_assoc] using
    trace_sandwich_pairing_le τ hq s (z 0) (z 1)

def traceSandwichContinuous (τ : TracialState D) {q : D}
    (hq : IsStarProjection q) (s : D) :
    ContinuousMultilinearMap ℂ (fun _ : Fin 2 => D) ℂ :=
  (traceSandwichMultilinear τ q s).mkContinuous (‖s‖ * (τ.functional q).re)
    (traceSandwichMultilinear_bound τ hq s)

lemma traceSandwichContinuous_norm_le (τ : TracialState D) {q : D}
    (hq : IsStarProjection q) (s : D) :
    ‖traceSandwichContinuous τ hq s‖ ≤ ‖s‖ * (τ.functional q).re := by
  exact MultilinearMap.mkContinuous_norm_le _
    (mul_nonneg (norm_nonneg _) (τ.functional.map_nonneg hq.nonneg).1) _

lemma trace_projective_sandwich_le (τ : TracialState D) {q : D}
    (hq : IsStarProjection q) (s : D) (d : ⨂[ℂ] (_ : Fin 2), D) :
    ‖τ.functional (s * PiTensorProduct.lift (sandwichMultilinear q) d)‖ ≤
      ‖s‖ * (τ.functional q).re * ‖d‖ := by
  have heq : τ.functional (s * PiTensorProduct.lift (sandwichMultilinear q) d) =
      PiTensorProduct.lift (traceSandwichContinuous τ hq s).toMultilinearMap d := by
    change (τ.functional.toLinearMap.comp (LinearMap.mulLeft ℂ s))
      (PiTensorProduct.lift (sandwichMultilinear q) d) = _
    rw [← LinearMap.comp_apply]
    congr 1
    apply PiTensorProduct.ext
    ext z
    simp [traceSandwichContinuous, traceSandwichMultilinear]
  rw [heq]
  exact (PiTensorProduct.norm_eval_le_projectiveSeminorm _ d).trans
    (mul_le_mul_of_nonneg_right (traceSandwichContinuous_norm_le τ hq s) (norm_nonneg d))

lemma traceOneNorm_projective_sandwich_le (τ : TracialState D) {q : D}
    (hq : IsStarProjection q) (d : ⨂[ℂ] (_ : Fin 2), D)
    (hd : IsSelfAdjoint (PiTensorProduct.lift (sandwichMultilinear q) d)) :
    traceOneNorm τ (PiTensorProduct.lift (sandwichMultilinear q) d) ≤
      (τ.functional q).re * ‖d‖ := by
  apply traceOneNorm_le_of_pairing τ hd
  intro s _ hsn
  calc
    _ ≤ ‖τ.functional (s * PiTensorProduct.lift (sandwichMultilinear q) d)‖ :=
      Complex.re_le_norm _
    _ ≤ ‖s‖ * (τ.functional q).re * ‖d‖ := trace_projective_sandwich_le τ hq s d
    _ ≤ 1 * (τ.functional q).re * ‖d‖ := by
      gcongr
      exact (τ.functional.map_nonneg hq.nonneg).1
    _ = (τ.functional q).re * ‖d‖ := by rw [one_mul]

lemma traceOneNorm_projective_sandwich_mul_unitary_le (τ : TracialState D) {q : D}
    (hq : IsStarProjection q) (d : ⨂[ℂ] (_ : Fin 2), D) (x : unitary D)
    (hd : IsSelfAdjoint (PiTensorProduct.lift (sandwichMultilinear q) d * (x : D))) :
    traceOneNorm τ (PiTensorProduct.lift (sandwichMultilinear q) d * (x : D)) ≤
      (τ.functional q).re * ‖d‖ := by
  apply traceOneNorm_le_of_pairing τ hd
  intro s _ hsn
  have heq : τ.functional (s * (PiTensorProduct.lift (sandwichMultilinear q) d * (x : D))) =
      τ.functional (((x : D) * s) * PiTensorProduct.lift (sandwichMultilinear q) d) := by
    rw [← mul_assoc, τ.tracial (s * PiTensorProduct.lift (sandwichMultilinear q) d)]
    simp only [mul_assoc]
  rw [heq]
  calc
    _ ≤ ‖τ.functional (((x : D) * s) * PiTensorProduct.lift (sandwichMultilinear q) d)‖ :=
      Complex.re_le_norm _
    _ ≤ ‖(x : D) * s‖ * (τ.functional q).re * ‖d‖ :=
      trace_projective_sandwich_le τ hq _ d
    _ = ‖s‖ * (τ.functional q).re * ‖d‖ := by rw [CStarRing.norm_coe_unitary_mul]
    _ ≤ 1 * (τ.functional q).re * ‖d‖ := by
      gcongr
      exact (τ.functional.map_nonneg hq.nonneg).1
    _ = (τ.functional q).re * ‖d‖ := by rw [one_mul]

variable {A : Type uA} [CStarAlgebra A]

def inclusionTensorMap (ι : A →⋆ₐ[ℂ] D) :
    (⨂[ℂ] (_ : Fin 2), A) →ₗ[ℂ] (⨂[ℂ] (_ : Fin 2), D) :=
  PiTensorProduct.map fun _ => ι.toLinearMap

omit [PartialOrder D] [StarOrderedRing D] in
lemma inclusionTensorMap_norm_le (ι : A →⋆ₐ[ℂ] D) (d : ⨂[ℂ] (_ : Fin 2), A) :
    ‖inclusionTensorMap ι d‖ ≤ ‖d‖ := by
  let L : A →L[ℂ] D := ι.toLinearMap.mkContinuous 1 (fun a => by
    change ‖ι a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le ι a)
  have hL : ‖L‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hnorm : ‖PiTensorProduct.mapL (fun _ : Fin 2 => L)‖ ≤ 1 := by
    apply (PiTensorProduct.opNorm_mapL _).trans
    simp only [Fin.prod_univ_two]
    nlinarith [norm_nonneg L]
  change ‖PiTensorProduct.mapL (fun _ : Fin 2 => L) d‖ ≤ ‖d‖
  apply (ContinuousLinearMap.le_opNorm _ d).trans
  simpa only [one_mul] using (mul_le_mul_of_nonneg_right hnorm (norm_nonneg d))

def tensorPair (a b : A) : ⨂[ℂ] (_ : Fin 2), A :=
  PiTensorProduct.tprod ℂ ![a, b]

omit [PartialOrder D] [StarOrderedRing D] in
@[simp] lemma inclusionTensorMap_tensorPair (ι : A →⋆ₐ[ℂ] D) (a b : A) :
    inclusionTensorMap ι (tensorPair a b) = tensorPair (ι a) (ι b) := by
  simp only [inclusionTensorMap, tensorPair, PiTensorProduct.map_tprod]
  congr 1
  ext i
  fin_cases i <;> rfl

omit [PartialOrder D] [StarOrderedRing D] in
@[simp] lemma sandwich_tensorPair (q a b : D) :
    PiTensorProduct.lift (sandwichMultilinear q) (tensorPair a b) = a * q * b := by
  rw [tensorPair, PiTensorProduct.lift.tprod]
  rfl

variable {I : Type uI} [Fintype I]

def diagonalCommutator (w : I → ℝ) (v : I → A) (x : A) :
    ⨂[ℂ] (_ : Fin 2), A :=
  ∑ i, w i • (tensorPair (x * v i) (star (v i)) -
    tensorPair (v i) (star (v i) * x))

omit [PartialOrder D] [StarOrderedRing D] in
lemma sandwich_diagonalCommutator (ι : A →⋆ₐ[ℂ] D) (w : I → ℝ) (v : I → A)
    (x : A) (q : D) :
    PiTensorProduct.lift (sandwichMultilinear q)
      (inclusionTensorMap ι (diagonalCommutator w v x)) =
    ι x * weightedAverage w (fun i => ι (v i)) q -
      weightedAverage w (fun i => ι (v i)) q * ι x := by
  simp only [diagonalCommutator, map_sum, LinearMap.map_smul_of_tower, map_sub,
    inclusionTensorMap_tensorPair, sandwich_tensorPair, map_mul, map_star, weightedAverage,
    Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_sub, mul_assoc]

lemma weightedAverage_central (τ : TracialState D) (ι : A →⋆ₐ[ℂ] D)
    (w : I → ℝ) (v : I → A) (hw : ∀ i, 0 ≤ w i)
    {q : D} (hq : IsStarProjection q) (x : unitary A) {μ : ℝ}
    (hcomm : ‖diagonalCommutator w v (x : A)‖ ≤ μ) :
    traceOneNorm τ (weightedAverage w (fun i => ι (v i)) q -
      ι (x : A) * weightedAverage w (fun i => ι (v i)) q * star (ι (x : A))) ≤
        μ * (τ.functional q).re := by
  let d := inclusionTensorMap ι (diagonalCommutator w v (x : A))
  let y : unitary D := ⟨ι (x : A), by
    constructor
    · rw [← map_star, ← map_mul, Unitary.coe_star_mul_self, map_one]
    · rw [← map_star, ← map_mul, x.property.2, map_one]⟩
  let b := weightedAverage w (fun i => ι (v i)) q
  have hb : 0 ≤ b := weightedAverage_nonneg w _ hw hq.nonneg
  have hs : IsSelfAdjoint ((y : D) * b * star (y : D) - b) :=
    (hb.isSelfAdjoint.conjugate _).sub hb.isSelfAdjoint
  have heq : PiTensorProduct.lift (sandwichMultilinear q) d * (star y : unitary D) =
      (y : D) * b * star (y : D) - b := by
    rw [sandwich_diagonalCommutator]
    change ((y : D) * b - b * (y : D)) * star (y : D) = _
    rw [sub_mul, mul_assoc b, y.property.2, mul_one]
  have h := traceOneNorm_projective_sandwich_mul_unitary_le τ hq d (star y)
    (heq ▸ hs)
  rw [heq] at h
  have hn : ‖d‖ ≤ μ := (inclusionTensorMap_norm_le ι _).trans hcomm
  have ht : traceOneNorm τ (b - (y : D) * b * star (y : D)) =
      traceOneNorm τ ((y : D) * b * star (y : D) - b) := by
    rw [← neg_sub, traceOneNorm_neg]
  change traceOneNorm τ (b - (y : D) * b * star (y : D)) ≤ _
  rw [ht]
  apply h.trans
  rw [mul_comm μ]
  exact mul_le_mul_of_nonneg_left hn (τ.functional.map_nonneg hq.nonneg).1

end ProjectiveAveraging

end CurrentMain

end

end

end OAI
