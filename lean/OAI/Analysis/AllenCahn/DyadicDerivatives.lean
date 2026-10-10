import OAI.Analysis.AllenCahn.Differences

namespace OAI

noncomputable section
namespace RegularitySupport.DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open MeasureTheory
open scoped ENNReal

lemma allenCahn_difference_bounds {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hrange : ∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) (hpde : AllenCahn v) :
    ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ DifferenceBound k v M := by
  intro k
  induction k with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro l hl x
    have he : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
    subst l
    simpa [iterDifference, differenceScale] using abs_le.mpr (hrange x)
  | succ k ih =>
    obtain ⟨M, hM, hbound⟩ := ih
    let N := (2 : ℝ) ^ k * ((2 : ℝ) ^ k * M * M) * M + M
    have hN : 0 ≤ N := by dsimp [N]; positivity
    have hnonlin : DifferenceBound k (fun x => v x ^ 3 - v x) N := by
      have hm := (hbound.mul hM hM hbound).mul (by positivity) hM hbound
      have hs := hm.sub hbound
      convert hs using 1
      ext x
      ring
    let K := 2 * (2 * M + N + 1)
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hMK : M ≤ K := by dsimp [K]; linarith
    refine ⟨K, hK, ?_⟩
    intro l hl x
    cases l with
    | nil =>
      have hb := hbound [] (by simp) x
      simpa [iterDifference, differenceScale] using (by simpa [iterDifference, differenceScale] using hb : |v x| ≤ M).trans hMK
    | cons h l =>
      have hl' : l.length ≤ k := Nat.le_of_succ_le_succ hl
      by_cases hP : differenceScale l = 0
      · rw [iterDifference, iterDifference_eq_zero_of_scale_eq_zero l hP]
        simp [difference, differenceScale, show (List.map (fun h : Space n => ‖h‖) l).prod = 0 from hP]
      have hPpos : 0 < differenceScale l := lt_of_le_of_ne (differenceScale_nonneg l) (Ne.symm hP)
      let f : Space n → ℝ := fun y => (differenceScale l)⁻¹ * iterDifference l v y
      have hf : ContDiff ℝ 2 f := contDiff_const.mul (iterDifference_contDiff hv l)
      have hfb : ∀ y, |f y| ≤ M := by
        intro y
        dsimp [f]
        rw [abs_mul, abs_of_pos (inv_pos.mpr hPpos)]
        have hb := mul_le_mul_of_nonneg_left (hbound l hl' y) (le_of_lt (inv_pos.mpr hPpos))
        calc
          _ ≤ (differenceScale l)⁻¹ * (M * differenceScale l) := hb
          _ = M := by field_simp
      have hfl : ∀ y, |Laplacian.laplacian f y| ≤ N := by
        intro y
        have he : Laplacian.laplacian f y = (differenceScale l)⁻¹ * iterDifference l (fun z => v z ^ 3 - v z) y := by
          change Laplacian.laplacian ((differenceScale l)⁻¹ • iterDifference l v) y = _
          rw [InnerProductSpace.laplacian_smul _ (iterDifference_contDiff hv l).contDiffAt,
            laplacian_iterDifference hv, show Laplacian.laplacian v = (fun z => v z ^ 3 - v z) from funext hpde]
          rfl
        rw [he, abs_mul, abs_of_pos (inv_pos.mpr hPpos)]
        have hb := mul_le_mul_of_nonneg_left (hnonlin l hl' y) (le_of_lt (inv_pos.mpr hPpos))
        calc
          _ ≤ (differenceScale l)⁻¹ * (N * differenceScale l) := hb
          _ = N := by field_simp
      have hLip := bounded_poisson_lipschitz hf hM hN hfb hfl x (x + h)
      have ht : |iterDifference (h :: l) v x| = differenceScale l * |f (x + h) - f x| := by
        dsimp [iterDifference, difference, f]
        rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hPpos)]
        field_simp
      rw [ht]
      have hb := mul_le_mul_of_nonneg_left hLip (le_of_lt hPpos)
      calc
        _ ≤ differenceScale l * (K * ‖h‖) := by simpa [K] using hb
        _ = K * differenceScale (h :: l) := by simp [differenceScale]; ring

lemma allenCahn_difference_bounds_uniform (n : ℕ) :
    ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ v : Space n → ℝ,
      ContDiff ℝ 2 v → (∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) → AllenCahn v → DifferenceBound k v M := by
  intro k
  induction k with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro v hv hrange hpde l hl x
    have he : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
    subst l
    simpa [iterDifference, differenceScale] using abs_le.mpr (hrange x)
  | succ k ih =>
    obtain ⟨M, hM, hboundAll⟩ := ih
    let N := (2 : ℝ) ^ k * ((2 : ℝ) ^ k * M * M) * M + M
    have hN : 0 ≤ N := by dsimp [N]; positivity
    let K := 2 * (2 * M + N + 1)
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hMK : M ≤ K := by dsimp [K]; linarith
    refine ⟨K, hK, ?_⟩
    intro v hv hrange hpde
    have hbound := hboundAll v hv hrange hpde
    have hnonlin : DifferenceBound k (fun x => v x ^ 3 - v x) N := by
      have hm := (hbound.mul hM hM hbound).mul (by positivity) hM hbound
      have hs := hm.sub hbound
      convert hs using 1
      ext x
      ring
    intro l hl x
    cases l with
    | nil =>
      have hb := hbound [] (by simp) x
      simpa [iterDifference, differenceScale] using (by simpa [iterDifference, differenceScale] using hb : |v x| ≤ M).trans hMK
    | cons h l =>
      have hl' : l.length ≤ k := Nat.le_of_succ_le_succ hl
      by_cases hP : differenceScale l = 0
      · rw [iterDifference, iterDifference_eq_zero_of_scale_eq_zero l hP]
        simp [difference, differenceScale, show (List.map (fun h : Space n => ‖h‖) l).prod = 0 from hP]
      have hPpos : 0 < differenceScale l := lt_of_le_of_ne (differenceScale_nonneg l) (Ne.symm hP)
      let f : Space n → ℝ := fun y => (differenceScale l)⁻¹ * iterDifference l v y
      have hf : ContDiff ℝ 2 f := contDiff_const.mul (iterDifference_contDiff hv l)
      have hfb : ∀ y, |f y| ≤ M := by
        intro y
        dsimp [f]
        rw [abs_mul, abs_of_pos (inv_pos.mpr hPpos)]
        have hb := mul_le_mul_of_nonneg_left (hbound l hl' y) (le_of_lt (inv_pos.mpr hPpos))
        calc
          _ ≤ (differenceScale l)⁻¹ * (M * differenceScale l) := hb
          _ = M := by field_simp
      have hfl : ∀ y, |Laplacian.laplacian f y| ≤ N := by
        intro y
        have he : Laplacian.laplacian f y = (differenceScale l)⁻¹ * iterDifference l (fun z => v z ^ 3 - v z) y := by
          change Laplacian.laplacian ((differenceScale l)⁻¹ • iterDifference l v) y = _
          rw [InnerProductSpace.laplacian_smul _ (iterDifference_contDiff hv l).contDiffAt,
            laplacian_iterDifference hv, show Laplacian.laplacian v = (fun z => v z ^ 3 - v z) from funext hpde]
          rfl
        rw [he, abs_mul, abs_of_pos (inv_pos.mpr hPpos)]
        have hb := mul_le_mul_of_nonneg_left (hnonlin l hl' y) (le_of_lt (inv_pos.mpr hPpos))
        calc
          _ ≤ (differenceScale l)⁻¹ * (N * differenceScale l) := hb
          _ = N := by field_simp
      have hLip := bounded_poisson_lipschitz hf hM hN hfb hfl x (x + h)
      have ht : |iterDifference (h :: l) v x| = differenceScale l * |f (x + h) - f x| := by
        dsimp [iterDifference, difference, f]
        rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hPpos)]
        field_simp
      rw [ht]
      have hb := mul_le_mul_of_nonneg_left hLip (le_of_lt hPpos)
      calc
        _ ≤ differenceScale l * (K * ‖h‖) := by simpa [K] using hb
        _ = K * differenceScale (h :: l) := by simp [differenceScale]; ring

end RegularitySupport.DeGiorgi
end

noncomputable section
namespace RegularitySupport.DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open MeasureTheory
open scoped ENNReal

def dyadicSlope {n : ℕ} (f : Space n → ℝ) (x h : Space n) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * (f (x + ((2 : ℝ) ^ j)⁻¹ • h) - f x)

lemma dyadicSlope_step {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (x h : Space n) (j : ℕ) :
    dist (dyadicSlope f x h j) (dyadicSlope f x h (j + 1)) ≤
      (M * ‖h‖ ^ 2 / 2) / 2 / (2 : ℝ) ^ j := by
  let a : Space n := ((2 : ℝ) ^ (j + 1))⁻¹ • h
  have ha : a + a = ((2 : ℝ) ^ j)⁻¹ • h := by
    dsimp [a]
    rw [← add_smul, pow_succ]
    congr 1
    field_simp
    ring
  have hb := hf [a, a] (by simp) x
  have he : dyadicSlope f x h j - dyadicSlope f x h (j + 1) =
      (2 : ℝ) ^ j * iterDifference [a, a] f x := by
    simp only [dyadicSlope, iterDifference, difference, pow_succ]
    rw [add_assoc x a a, ha]
    change _ = 2 ^ j * (f (x + ((2 : ℝ) ^ j)⁻¹ • h) - f (x + a) - (f (x + a) - f x))
    dsimp [a]
    rw [pow_succ]
    ring
  rw [Real.dist_eq, he, abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j)]
  calc
    _ ≤ (2 : ℝ) ^ j * (M * differenceScale [a, a]) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (M * ‖h‖ ^ 2 / 2) / 2 / (2 : ℝ) ^ j := by
      have hna : ‖a‖ = ((2 : ℝ) ^ (j + 1))⁻¹ * ‖h‖ := by
        dsimp only [a]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((2 : ℝ) ^ (j + 1))⁻¹)]
      simp only [differenceScale, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hna, pow_succ]
      field_simp

lemma dyadicSlope_converges {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (x h : Space n) :
    ∃ a : ℝ, Tendsto (dyadicSlope f x h) atTop (𝓝 a) :=
  cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two (dyadicSlope_step hf x h))

lemma dyadicSlope_remainder {n : ℕ} {f : Space n → ℝ} {M a : ℝ}
    (hf : DifferenceBound 2 f M) (x h : Space n)
    (ha : Tendsto (dyadicSlope f x h) atTop (𝓝 a)) :
    |f (x + h) - f x - a| ≤ M * ‖h‖ ^ 2 / 2 := by
  simpa only [dyadicSlope, pow_zero, inv_one, one_smul, one_mul, Real.dist_eq] using
    dist_le_of_le_geometric_two_of_tendsto₀ (dyadicSlope_step hf x h) ha

lemma dyadicSlope_bound {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (x h : Space n) (j : ℕ) :
    |dyadicSlope f x h j| ≤ M * ‖h‖ := by
  have hb := hf [((2 : ℝ) ^ j)⁻¹ • h] (by simp) x
  simp only [iterDifference, difference, differenceScale, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ((2 : ℝ) ^ j)⁻¹)] at hb
  dsimp [dyadicSlope]
  rw [abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j)]
  calc
    _ ≤ (2 : ℝ) ^ j * (M * (((2 : ℝ) ^ j)⁻¹ * ‖h‖)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = M * ‖h‖ := by field_simp

def dyadicDerivative {n : ℕ} (f : Space n → ℝ) (x h : Space n) : ℝ :=
  limUnder atTop (dyadicSlope f x h)

lemma tendsto_dyadicDerivative {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (x h : Space n) :
    Tendsto (dyadicSlope f x h) atTop (𝓝 (dyadicDerivative f x h)) :=
  tendsto_nhds_limUnder (dyadicSlope_converges hf x h)

lemma dyadicDerivative_bound {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (x h : Space n) :
    |dyadicDerivative f x h| ≤ M * ‖h‖ := by
  exact le_of_tendsto (tendsto_dyadicDerivative hf x h).abs
    (Filter.Eventually.of_forall (dyadicSlope_bound hf x h))

lemma dyadicDerivative_remainder {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (x h : Space n) :
    |f (x + h) - f x - dyadicDerivative f x h| ≤ M * ‖h‖ ^ 2 / 2 :=
  dyadicSlope_remainder hf x h (tendsto_dyadicDerivative hf x h)

lemma dyadicSlope_add_error {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (x h k : Space n) (j : ℕ) :
    |dyadicSlope f x (h + k) j - (dyadicSlope f x h j + dyadicSlope f x k j)| ≤
      M * ‖h‖ * ‖k‖ * ((2 : ℝ) ^ j)⁻¹ := by
  let a : Space n := ((2 : ℝ) ^ j)⁻¹ • h
  let b : Space n := ((2 : ℝ) ^ j)⁻¹ • k
  have hb := hf [a, b] (by simp) x
  have he : dyadicSlope f x (h + k) j - (dyadicSlope f x h j + dyadicSlope f x k j) =
      (2 : ℝ) ^ j * iterDifference [a, b] f x := by
    simp only [dyadicSlope, iterDifference, difference, smul_add, add_assoc, a, b]
    ring
  rw [he, abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j)]
  calc
    _ ≤ (2 : ℝ) ^ j * (M * differenceScale [a, b]) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = M * ‖h‖ * ‖k‖ * ((2 : ℝ) ^ j)⁻¹ := by
      have hn (u : Space n) : ‖((2 : ℝ) ^ j)⁻¹ • u‖ = ((2 : ℝ) ^ j)⁻¹ * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((2 : ℝ) ^ j)⁻¹)]
      simp only [differenceScale, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, a, b, hn]
      field_simp

lemma dyadicDerivative_add {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (x h k : Space n) :
    dyadicDerivative f x (h + k) = dyadicDerivative f x h + dyadicDerivative f x k := by
  have ht : Tendsto (fun j : ℕ => ((2 : ℝ) ^ j)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have herr : Tendsto (fun j => dyadicSlope f x (h + k) j -
      (dyadicSlope f x h j + dyadicSlope f x k j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => ?_)
      (show Tendsto (fun j => M * ‖h‖ * ‖k‖ * ((2 : ℝ) ^ j)⁻¹) atTop (𝓝 0) from by simpa using ht.const_mul (M * ‖h‖ * ‖k‖))
    simpa only [Real.norm_eq_abs] using dyadicSlope_add_error hf x h k j
  have hlim := (tendsto_dyadicDerivative hf x (h + k)).sub
    ((tendsto_dyadicDerivative hf x h).add (tendsto_dyadicDerivative hf x k))
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim herr)

def dyadicDerivativeHom {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (x : Space n) : Space n →+ ℝ where
  toFun := dyadicDerivative f x
  map_zero' := by
    have hb := dyadicDerivative_bound hf x 0
    simpa using hb
  map_add' := dyadicDerivative_add hf x

lemma dyadicDerivative_continuous {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (x : Space n) : Continuous (dyadicDerivativeHom hf x) := by
  apply AddMonoidHomClass.continuous_of_bound _ M
  intro h
  change |dyadicDerivative f x h| ≤ M * ‖h‖
  exact dyadicDerivative_bound hf x h

def dyadicDerivativeCLM {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (x : Space n) : Space n →L[ℝ] ℝ :=
  (dyadicDerivativeHom hf x).toRealLinearMap (dyadicDerivative_continuous hf x)

lemma hasFDerivAt_dyadicDerivative {n : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound 2 f M) (hM : 0 ≤ M) (x : Space n) :
    HasFDerivAt f (dyadicDerivativeCLM hf x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hden : 0 < M + 1 := by linarith
  have hδ : 0 < ε / (M + 1) := div_pos hε hden
  filter_upwards [Metric.ball_mem_nhds (0 : Space n) hδ] with h hh
  have hnorm : ‖h‖ < ε / (M + 1) := by simpa [Metric.mem_ball, dist_zero_right] using hh
  have hsmall : M * ‖h‖ / 2 ≤ ε := by
    have ht := (lt_div_iff₀ hden).mp hnorm
    nlinarith [norm_nonneg h, mul_nonneg hM (norm_nonneg h)]
  calc
    _ ≤ M * ‖h‖ ^ 2 / 2 := by
      change |f (x + h) - f x - dyadicDerivative f x h| ≤ _
      exact dyadicDerivative_remainder hf x h
    _ ≤ ε * ‖h‖ := by nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg h)]

lemma iterDifference_tendsto {n : ℕ} {F : ℕ → Space n → ℝ} {g : Space n → ℝ}
    (hf : ∀ x, Tendsto (fun j => F j x) atTop (𝓝 (g x)))
    (l : List (Space n)) (x : Space n) :
    Tendsto (fun j => iterDifference l (F j) x) atTop (𝓝 (iterDifference l g x)) := by
  induction l generalizing x with
  | nil => exact hf x
  | cons h l ih => exact (ih (x + h)).sub (ih x)

lemma differenceBound_fderiv_apply {n k : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : DifferenceBound (k + 2) f M) (hM : 0 ≤ M) (h : Space n) :
    DifferenceBound k (fun x => fderiv ℝ f x h) (M * ‖h‖) := by
  have h2 : DifferenceBound 2 f M := hf.mono (by omega)
  have hlim (x : Space n) : Tendsto (fun j => dyadicSlope f x h j) atTop (𝓝 (fderiv ℝ f x h)) := by
    rw [(hasFDerivAt_dyadicDerivative h2 hM x).fderiv]
    exact tendsto_dyadicDerivative h2 x h
  intro l hl x
  have ht := iterDifference_tendsto hlim l x
  apply le_of_tendsto ht.abs
  apply Filter.Eventually.of_forall
  intro j
  have he : (fun x => dyadicSlope f x h j) = fun x => (2 : ℝ) ^ j * difference (((2 : ℝ) ^ j)⁻¹ • h) f x := rfl
  rw [he, iterDifference_const_mul, iterDifference_difference, abs_mul,
    abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j)]
  have hb := hf (((2 : ℝ) ^ j)⁻¹ • h :: l) (by simp only [List.length_cons]; omega) x
  change |difference (((2 : ℝ) ^ j)⁻¹ • h) (iterDifference l f) x| ≤
    M * (‖((2 : ℝ) ^ j)⁻¹ • h‖ * differenceScale l) at hb
  have hn : ‖((2 : ℝ) ^ j)⁻¹ • h‖ = ((2 : ℝ) ^ j)⁻¹ * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((2 : ℝ) ^ j)⁻¹)]
  rw [hn] at hb
  calc
    _ ≤ (2 : ℝ) ^ j * (M * ((((2 : ℝ) ^ j)⁻¹ * ‖h‖) * differenceScale l)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = M * ‖h‖ * differenceScale l := by field_simp

lemma contDiff_infty_of_difference_bounds {n : ℕ} {f : Space n → ℝ}
    (hf : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ DifferenceBound k f M) : ContDiff ℝ ∞ f := by
  apply contDiff_infty.mpr
  intro k
  induction k generalizing f with
  | zero =>
    obtain ⟨M, hM, h2⟩ := hf 2
    apply contDiff_zero.mpr
    exact (show Differentiable ℝ f from fun x => (hasFDerivAt_dyadicDerivative h2 hM x).differentiableAt).continuous
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by simp,
      contDiff_succ_iff_fderiv_apply]
    obtain ⟨M, hM, h2⟩ := hf 2
    refine ⟨fun x => (hasFDerivAt_dyadicDerivative h2 hM x).differentiableAt, ?_, ?_⟩
    · simp
    · intro h
      apply ih
      intro j
      obtain ⟨N, hN, hbound⟩ := hf (j + 2)
      exact ⟨N * ‖h‖, mul_nonneg hN (norm_nonneg h), differenceBound_fderiv_apply hbound hN h⟩

end RegularitySupport.DeGiorgi
end

end OAI
