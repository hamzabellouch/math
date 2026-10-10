import OAI.Analysis.LipschitzHilbert.Phase.SourceBalancedPrediction
import OAI.Analysis.LipschitzHilbert.Phase.SourcePathPhaseMotion
import OAI.Analysis.LipschitzHilbert.Trees.SourceSnapshotSize
import OAI.Analysis.LipschitzHilbert.Phase.DominantPredictionBlend
import OAI.Analysis.LipschitzHilbert.Trees.GraphPathBaseline

namespace OAI

/-! Actual dominant-path coordinates for the source prediction. The path
amplitude stays unshrunk; only the complementary children are shrunk. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

variable {ι κ : Type} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/-- Removing the snapshot path carrier is an exact isometry. -/
theorem diagonalModulation_inverse (f : κ → ℝ) (v : EuclideanSpace ℂ κ) (b : ℝ) :
    diagonalModulation (fun k => -f k) (diagonalModulation f v b) b = v := by
  apply PiLp.ext
  intro k
  change (v k * character (f k) b) * character (-f k) b = v k
  rw [mul_assoc,character_mul]
  simp [character]

/-- Exact dominant coordinates for a finite normalized prediction. The
rotation may be the inverse of the actual path carrier. -/
theorem source_path_prediction_identity
    (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (i₀ : ι) (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    {p μ : ℝ} (hp : 0 < p) (hl : 0 < l i₀) (hlam : lam i₀ ≠ 0) :
    let Y := (l i₀)^(1/p) • U (X i₀)
    let C := (l i₀)^(1-μ-1/p)*‖lam i₀‖
    let R := ∑ i : RemainderIndex i₀, l i*‖X i‖^p
    let Z := (scalarPhase (lam i₀))⁻¹ • U
      (∑ i : RemainderIndex i₀, (((l i)^(1-μ):ℝ):ℂ) • (lam i • X i))
    energyRatio p (1+∑ i, l i*‖X i‖^p)
      (∑ i, (((l i)^(1-μ):ℝ):ℂ) • (lam i • X i)) =
      energyRatio p (1+‖Y‖^p+R) (C • Y+Z) := by
  classical
  dsimp only
  have hscale : ((l i₀)^(1-μ-1/p)*‖lam i₀‖)*(l i₀)^(1/p) =
      (l i₀)^(1-μ)*‖lam i₀‖ := by
    calc
      _ = ((l i₀)^(1-μ-1/p)*(l i₀)^(1/p))*‖lam i₀‖ := by ring
      _ = (l i₀)^((1-μ-1/p)+(1/p))*‖lam i₀‖ := by rw [← Real.rpow_add hl]
      _ = _ := by congr 2; ring
  have hpath : (scalarPhase (lam i₀))⁻¹ •
      U ((((l i₀)^(1-μ):ℝ):ℂ) • (lam i₀ • X i₀)) =
      ((l i₀)^(1-μ-1/p)*‖lam i₀‖) • ((l i₀)^(1/p) • U (X i₀)) := by
    rw [U.map_smul,U.map_smul]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul]
    congr 1
    calc
      _ = (((l i₀)^(1-μ):ℝ):ℂ)*((scalarPhase (lam i₀))⁻¹*lam i₀) := by ring
      _ = _ := by
        rw [phase_inverse_mul _ hlam]
        apply Complex.ext <;> simp only [RCLike.ofReal_eq_complex_ofReal,Complex.mul_re,Complex.mul_im,
          Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero]
        exact hscale.symm
  have hvector :
      ((l i₀)^(1-μ-1/p)*‖lam i₀‖) • ((l i₀)^(1/p) • U (X i₀))+
        (scalarPhase (lam i₀))⁻¹ • U
          (∑ i : RemainderIndex i₀, (((l i)^(1-μ):ℝ):ℂ) • (lam i • X i)) =
      (scalarPhase (lam i₀))⁻¹ • U
        (∑ i, (((l i)^(1-μ):ℝ):ℂ) • (lam i • X i)) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀,U.map_add,smul_add,hpath]
  have hden : 1+∑ i, l i*‖X i‖^p =
      1+‖(l i₀)^(1/p) • U (X i₀)‖^p+
        ∑ i : RemainderIndex i₀, l i*‖X i‖^p := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀,
      norm_weighted_smul_rpow hp hl.le,U.norm_map]
    ring
  rw [hden,hvector]
  unfold energyRatio
  simp only [norm_smul,norm_inv,norm_scalarPhase hlam,inv_one,one_mul,U.norm_map]

/-- The scaled source amplitude is the actual path vector, including
its child fraction. No lower bound on that fraction is needed. -/
theorem source_path_vector_motion {n n' c c' p μ ε K : ℝ}
    (hn : 0 < n) (hn' : 0 < n') (hc : 0 < c) (hc' : 0 < c')
    (hcn : c ≤ n) (hp : 0 < p) (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hK : n^μ ≤ K) (f : κ → ℝ) (b : ℝ) (A A' : EuclideanSpace ℂ κ)
    (hscaled : ‖massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A'-
      diagonalModulation f (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b‖ ≤
      ε*(c/n)^(1/p)*c^μ) :
    ‖(c'/n')^(1/p) • diagonalModulation (fun k => -f k) (c'^(μ-1) • A') b-
      (c/n)^(1/p) • (c^(μ-1) • A)‖ ≤ ε*K := by
  have hnrm : ‖diagonalModulation (fun k => -f k)
      (massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A') b-
      massPowerScale n c (-(1/p)) (μ-1+1/p) • A‖ =
      ‖massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A'-
        diagonalModulation f (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b‖ := by
    calc
      _ = ‖diagonalModulation (fun k => -f k)
          (massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A') b-
          diagonalModulation (fun k => -f k)
            (diagonalModulation f (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b) b‖ := by
        rw [diagonalModulation_inverse]
      _ = ‖diagonalModulation (fun k => -f k)
          (massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A'-
            diagonalModulation f (massPowerScale n c (-(1/p)) (μ-1+1/p) • A) b) b‖ := by
        exact congrArg norm ((diagonalModulationIsometry (fun k => -f k) b).map_sub _ _).symm
      _ = _ := norm_diagonalModulation _ _ _
  have hfrac : (c/n)^(1/p) ≤ 1 := Real.rpow_le_one
    (div_pos hc hn).le ((div_le_one hn).mpr hcn) (by positivity)
  have hpower : c^μ ≤ K := (Real.rpow_le_rpow hc.le hcn hμ).trans hK
  calc
    _ = ‖diagonalModulation (fun k => -f k)
        (massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A') b-
        massPowerScale n c (-(1/p)) (μ-1+1/p) • A‖ := by
      rw [prediction_mass_scale_factor hn hc, prediction_mass_scale_factor hn' hc']
      rw [mul_smul,mul_smul]
      have hmap : diagonalModulation (fun k => -f k)
          ((c'/n')^(1/p) • (c'^(μ-1) • A')) b =
          (c'/n')^(1/p) • diagonalModulation (fun k => -f k) (c'^(μ-1) • A') b :=
        (diagonalModulationRealIsometry (fun k => -f k) b).map_smul _ _
      rw [hmap]
    _ ≤ ε*(c/n)^(1/p)*c^μ := hnrm.le.trans hscaled
    _ ≤ ε*1*K := mul_le_mul
      (mul_le_mul_of_nonneg_left hfrac hε) hpower
      (Real.rpow_nonneg hc.le μ) (by positivity)
    _ = ε*K := by ring

/-- Snapshot path size and its moved counterpart use the same parent
mass scale as the off-path coefficient budget. -/
theorem source_path_vector_size {n c p μ C K : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hcn : c ≤ n) (hp : 0 < p)
    (hμ : 0 ≤ μ) (hC : 0 ≤ C) (hsize : C*n^μ ≤ K)
    (A : EuclideanSpace ℂ κ) (hA : ‖A‖ ≤ C*c) :
    ‖(c/n)^(1/p) • (c^(μ-1) • A)‖ ≤ K := by
  have hx : ‖c^(μ-1) • A‖ ≤ C*n^μ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hc.le _)]
    calc
      _ ≤ c^(μ-1)*(C*c) := mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hc.le _)
      _ = C*c^μ := by
        rw [Real.rpow_sub hc,Real.rpow_one]
        field_simp
      _ ≤ C*n^μ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le hcn hμ) hC
  have hf : (c/n)^(1/p) ≤ 1 := Real.rpow_le_one (div_pos hc hn).le
    ((div_le_one hn).mpr hcn) (by positivity)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (div_pos hc hn).le _)]
  calc
    _ ≤ 1*(C*n^μ) := mul_le_mul hf hx (norm_nonneg _) zero_le_one
    _ ≤ K := by simpa only [one_mul] using hsize

/-- The one-sided source shrink bounds add over precisely the complementary
children; no comparison of the full path denominator is assumed. -/
theorem source_off_path_residual_order
    {n n' p μ ε : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hp : 0 < p) (hε : 0 ≤ ε) (f : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (f i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ) :
    (∑ i, (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p) ≤
      ∑ i, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p := by
  have hb := source_prediction_denominator_sum_shrink hn hn' c c' hc hc' hp hε f b A A' hscaled
  linarith

theorem source_numerator_term_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n c μ C : ℝ} (hn : 0 < n) (_hc : 0 < c) (_hC : 0 ≤ C)
    (A : E) (lam : ℂ) (hA : ‖A‖ ≤ C*c) (hlam : ‖lam‖ ≤ 1) :
    ‖((n^(μ-1):ℝ):ℂ) • (lam • A)‖ ≤ (C*n^μ)*(c/n) := by
  rw [norm_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn.le _)]
  calc
    _ ≤ n^(μ-1)*(1*(C*c)) := mul_le_mul_of_nonneg_left
      (mul_le_mul hlam hA (norm_nonneg _) zero_le_one) (Real.rpow_nonneg hn.le _)
    _ = C*(n^(μ-1)*c) := by ring
    _ = _ := by rw [prediction_numerator_scale_identity hn]; ring

/-- The removed path phase and carrier do not change the off-path size. -/
theorem source_off_path_coordinate_size {n μ ε K C u : ℝ}
    (hn : 0 < n) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hC : 0 ≤ C) (hsize : C*n^μ ≤ K)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (hmass : ∑ i, c i/n ≤ u)
    (f : ι → κ → ℝ) (b : ℝ) (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1) (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (pathLam : ℂ) (hpath : pathLam ≠ 0) :
    ‖(scalarPhase pathLam)⁻¹ • U (∑ i, ((n^(μ-1):ℝ):ℂ) •
      (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b))‖ ≤ K*u := by
  have hterm (i : ι) : ‖((n^(μ-1):ℝ):ℂ) •
      (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b)‖ ≤ K*(c i/n) := by
    have ha : ‖diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b‖ ≤ C*c i := by
      rw [norm_diagonalModulation]
      exact (norm_radialShrink_le (mul_nonneg (mul_nonneg (by norm_num) hε) (hc i).le) _).trans (hA i)
    exact (source_numerator_term_bound hn (hc i) hC _ _ ha (hlam i)).trans
      (mul_le_mul_of_nonneg_right hsize (div_pos (hc i) hn).le)
  rw [norm_smul,norm_inv,norm_scalarPhase hpath,inv_one,one_mul,U.norm_map]
  calc
    _ ≤ ∑ i, ‖((n^(μ-1):ℝ):ℂ) •
        (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b)‖ := norm_sum_le _ _
    _ ≤ ∑ i, K*(c i/n) := Finset.sum_le_sum fun i _ => hterm i
    _ = K*(∑ i, c i/n) := (Finset.mul_sum ..).symm
    _ ≤ K*u := mul_le_mul_of_nonneg_left hmass hK

/-- Simultaneously rotate all complementary children into the path frame.
The coefficient of the error still vanishes with their total mass. -/
theorem source_off_path_coordinate_motion
    {n n' μ ε K C q u : ℝ} (hn : 0 < n) (_hn' : 0 < n')
    (hε : 0 ≤ ε) (hK : 0 ≤ K) (_hC : 0 ≤ C) (hpower : n^μ ≤ K)
    (hsize : C*n^μ ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (hmass : ∑ i, c i/n ≤ u)
    (f : ι → κ → ℝ) (b : ℝ) (U : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1) (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (hmove : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (f i) (A i) b)‖ ≤
        ε*K*(c i/n))
    (pathLam pathLam' : ℂ) (hpath : pathLam ≠ 0)
    (hphase : ‖pathLam'-pathLam‖ ≤ q*‖pathLam‖) :
    ‖(scalarPhase pathLam')⁻¹ •
        U (∑ i, ((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i))-
      (scalarPhase pathLam)⁻¹ •
        U (∑ i, ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (f i)
          (radialShrink (2*ε*c i) (A i)) b))‖ ≤ (3*ε+2*q)*K*u := by
  let W := fun i => U (((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (f i)
    (radialShrink (2*ε*c i) (A i)) b))
  let W' := fun i => U (((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i))
  have hterm (i : ι) : ‖W' i-W i‖ ≤ (3*ε)*K*(c i/n) := by
    dsimp only [W,W']
    rw [← U.map_sub,U.norm_map]
    simpa only [diagonalModulationIsometry_apply,mul_assoc] using source_prediction_shrunk_numerator hn (hc i).le hε hpower
      (diagonalModulationIsometry (f i) b) (A i)
      (((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)) (lam i) (hlam i) (hmove i)
  have hnorm (i : ι) : ‖W i‖ ≤ K*(c i/n) := by
    have hs : ‖radialShrink (2*ε*c i) (A i)‖ ≤ ‖A i‖ :=
      norm_radialShrink_le (mul_nonneg (mul_nonneg (by norm_num) hε) (hc i).le) _
    dsimp only [W]
    rw [U.norm_map,norm_smul,norm_smul,norm_diagonalModulation,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hn.le _)]
    calc
      _ ≤ n^(μ-1)*(1*(C*c i)) := mul_le_mul_of_nonneg_left
        (mul_le_mul (hlam i) (hs.trans (hA i)) (norm_nonneg _) zero_le_one)
        (Real.rpow_nonneg hn.le _)
      _ = C*(n^(μ-1)*c i) := by ring
      _ = (C*n^μ)*(c i/n) := by rw [prediction_numerator_scale_identity hn]; ring
      _ ≤ K*(c i/n) := mul_le_mul_of_nonneg_right hsize (div_pos (hc i) hn).le
  have hb := finite_rotated_off_path_motion Finset.univ (fun i => c i/n) W W'
    hpath hq0 hq1 (show 0 ≤ 3*ε by positivity) hK hphase hmass
    (fun i _ => hnorm i) (fun i _ => hterm i)
  simpa only [W,W',map_sum] using hb

/-- The original child-mass error bounds imply all dominant-path errors
at once, with no assumed residual ordering. The scalar-coefficient bounds
are supplied by the complementary-mass theorem. -/
theorem source_dominant_coordinate_control
    {n n' p μ ε K C q u : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (hp : 0 < p) (hμ : 0 ≤ μ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hpower : n^μ ≤ K) (hsize : C*n^μ ≤ K)
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (i₀ : ι) (hcn : c i₀ ≤ n)
    (hmass : ∑ i : RemainderIndex i₀, c i/n ≤ u)
    (f : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1) (hpath : lam i₀ ≠ 0)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hqε : q ≤ ε)
    (hphase : ‖lam' i₀-lam i₀‖ ≤ q*‖lam i₀‖)
    (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (f i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ)
    (hmove : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (f i) (A i) b)‖ ≤
        ε*K*(c i/n)) :
    let U := diagonalModulationIsometry (fun k => -f i₀ k) b
    let Y := (c i₀/n)^(1/p) • ((c i₀)^(μ-1) • A i₀)
    let Y' := (c' i₀/n')^(1/p) • U ((c' i₀)^(μ-1) • A' i₀)
    let R := ∑ i : RemainderIndex i₀,
      (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p
    let R' := ∑ i : RemainderIndex i₀, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p
    let Z := (scalarPhase (lam i₀))⁻¹ • U
      (∑ i : RemainderIndex i₀, ((n^(μ-1):ℝ):ℂ) •
        (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b))
    let Z' := (scalarPhase (lam' i₀))⁻¹ • U
      (∑ i : RemainderIndex i₀, ((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i))
    ‖Y‖ ≤ K ∧ ‖Y'‖ ≤ 2*K ∧ ‖Y'-Y‖ ≤ ε*K ∧ R ≤ R' ∧
      ‖Z'-Z‖ ≤ 5*ε*K*u ∧ ‖Z‖ ≤ K*u := by
  dsimp only
  have hy := source_path_vector_size hn (hc i₀) hcn hp hμ hC hsize (A i₀) (hA i₀)
  have hmoveY := source_path_vector_motion hn hn' (hc i₀) (hc' i₀) hcn hp hμ hε0
    hpower (f i₀) b (A i₀) (A' i₀) (hscaled i₀)
  have hy' : ‖(c' i₀/n')^(1/p) • diagonalModulation (fun k => -f i₀ k)
      ((c' i₀)^(μ-1) • A' i₀) b‖ ≤ 2*K := by
    have ht := norm_sub_le_norm_sub_add_norm_sub
      ((c' i₀/n')^(1/p) • diagonalModulation (fun k => -f i₀ k)
        ((c' i₀)^(μ-1) • A' i₀) b)
      ((c i₀/n)^(1/p) • ((c i₀)^(μ-1) • A i₀)) 0
    simp only [sub_zero] at ht
    have he := mul_le_mul_of_nonneg_right hε1 hK
    linarith
  have hr := source_off_path_residual_order hn hn' (fun i : RemainderIndex i₀ => c i)
    (fun i : RemainderIndex i₀ => c' i) (fun i => hc i) (fun i => hc' i)
    hp hε0 (fun i => f i) b (fun i => A i) (fun i => A' i) (fun i => hscaled i)
  have hz := source_off_path_coordinate_motion hn hn' hε0 hK hC hpower hsize hq0 hq1
    (fun i : RemainderIndex i₀ => c i) (fun i => hc i) hmass (fun i => f i) b
    (diagonalModulationIsometry (fun k => -f i₀ k) b) (fun i => A i) (fun i => A' i)
    (fun i => lam i) (fun i => lam' i) (fun i => hlam i) (fun i => hA i)
    (fun i => hmove i) (lam i₀) (lam' i₀) hpath hphase
  have hs0 : 0 ≤ ∑ i : RemainderIndex i₀, c i/n :=
    Finset.sum_nonneg (fun i _ => (div_pos (hc i) hn).le)
  have hu : 0 ≤ u := hs0.trans hmass
  refine ⟨hy,hy',hmoveY,hr,hz.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 3*ε+2*q ≤ 5*ε) hK) hu
  · exact source_off_path_coordinate_size hn hε0 hK hC hsize
      (fun i : RemainderIndex i₀ => c i) (fun i => hc i) hmass (fun i => f i) b
      (diagonalModulationIsometry (fun k => -f i₀ k) b) (fun i => A i)
      (fun i => lam i) (fun i => hlam i) (fun i => hA i) (lam i₀) hpath

end LipschitzHilbert

end

end OAI
