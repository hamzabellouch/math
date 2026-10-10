import OAI.Dynamics.ThreeTorus.TrackedPackets

namespace OAI

/-! Block transfer, cofinal frequency trees, color-density products, finite iteration, and actual anchored blocks. -/

section

/-! Uniform-in-frequency estimator bounds and the correct parameter order for
transferring both block tests to actual densities. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def blockModelColors {m n : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (q : UnitAddCircle → ℂ) (ell : ℝ) (L : Fin n → ℤ) : Fin m → UnitAddCircle → ℝ :=
  fun r z => p r z*blockProduct n ell (b r-q z) (fun i => L i • z)

def blockDiagonalEstimator {n : ℕ} (q : UnitAddCircle → ℂ) (ell : ℝ)
    (L : Fin n → ℤ) (z : UnitAddCircle) : ℂ :=
  blockPhaseEstimator q n ell z (fun i => L i • z)

lemma continuous_blockPhaseEstimator_diagonal {n : ℕ} {q : UnitAddCircle → ℂ}
    (hq : Continuous q) (ell : ℝ) (L : Fin n → ℤ) :
    Continuous (blockDiagonalEstimator q ell L) := by
  unfold blockDiagonalEstimator blockPhaseEstimator
  fun_prop

lemma continuous_blockModelColors {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {q : UnitAddCircle → ℂ}
    (hq : Continuous q) (ell : ℝ) (L : Fin n → ℤ) (r : Fin m) :
    Continuous (blockModelColors p b q ell L r) := by
  unfold blockModelColors blockProduct blockFactor
  fun_prop

lemma blockModelColors_nonneg {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    {q : UnitAddCircle → ℂ} (hq : ∀ z, ‖q z‖ ≤ 2) {ell : ℝ} (he : 0 ≤ ell)
    (hes : 6*ell ≤ 1) (L : Fin n → ℤ) (r : Fin m) (z : UnitAddCircle) :
    0 ≤ blockModelColors p b q ell L r z := by
  apply mul_nonneg (hp r z)
  apply blockProduct_nonneg n he (b r-q z) _ (fun i => L i • z)
  calc
    2*ell*‖b r-q z‖ ≤ 2*ell*(1+2) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add (hb r) (hq z))
    _ ≤ 1 := by linarith

lemma blockPhaseEstimator_norm {n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell)
    {q : UnitAddCircle → ℂ} (hq : ∀ z, ‖q z‖ ≤ 2)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) :
    ‖blockPhaseEstimator q n ell z y‖ ≤ 2+1/ell := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hsum : ‖∑ i, fourier 1 (y i)‖ ≤ (n:ℝ) := by
    calc
      _ ≤ ∑ i, ‖fourier 1 (y i)‖ := norm_sum_le _ _
      _ = n := by simp only [fourier_apply, Circle.norm_coe, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hi : ‖((n:ℂ)*(ell:ℂ))⁻¹‖ = ((n:ℝ)*ell)⁻¹ := by
    rw [norm_inv,norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he]
  calc
    _ ≤ ‖q z‖+‖((n:ℂ)*(ell:ℂ))⁻¹*∑ i, fourier 1 (y i)‖ := norm_add_le _ _
    _ ≤ 2+((n:ℝ)*ell)⁻¹*(n:ℝ) := by
      rw [norm_mul,hi]
      exact add_le_add (hq z) (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (mul_nonneg hnR.le he.le)))
    _ = 2+1/ell := by field_simp

lemma block_estimator_weight_bound {m n : ℕ} (hn : 0 < n) {ell : ℝ} (he : 0 < ell)
    {q A : UnitAddCircle → ℂ} (hq : ∀ z, ‖q z‖ ≤ 2) {C : ℝ}
    (hA : ∀ z, ‖A z‖ ≤ C) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    (k : ℕ) (L : Fin n → ℤ) (r : Fin m) (z : UnitAddCircle) :
    ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*b r‖^2 ≤
      (C+2+1/ell+(k:ℝ)+1)^2 := by
  have hk : ‖((k:ℂ)+1)*b r‖ ≤ (k:ℝ)+1 := by
    rw [norm_mul]
    have heq : (k:ℂ)+1 = ((k:ℝ)+1:ℝ) := by push_cast; rfl
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    simpa using mul_le_mul_of_nonneg_left (hb r) (show 0 ≤ (k:ℝ)+1 by positivity)
  have hnorm : ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*b r‖ ≤
      C+2+1/ell+(k:ℝ)+1 := by
    calc
      _ ≤ ‖A z+blockDiagonalEstimator q ell L z‖+‖((k:ℂ)+1)*b r‖ := norm_sub_le _ _
      _ ≤ ‖A z‖+‖blockDiagonalEstimator q ell L z‖+‖((k:ℂ)+1)*b r‖ := by gcongr; exact norm_add_le _ _
      _ ≤ C+(2+1/ell)+((k:ℝ)+1) := add_le_add
        (add_le_add (hA z) (blockPhaseEstimator_norm hn he hq z _)) hk
      _ = _ := by ring
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

lemma integral_blockErrorTest_diagonal {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {q A : UnitAddCircle → ℂ}
    (hq : Continuous q) (hA : Continuous A) (k : ℕ) (ell : ℝ) (L : Fin n → ℤ) :
    (∫ z, blockErrorTest p b q A k n ell z (fun i => L i • z) ∂phaseHaar) =
    ∑ r, ∫ z, blockModelColors p b q ell L r z*
      ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*b r‖^2 ∂phaseHaar := by
  apply integral_finsetSum
  intro r _
  apply continuous_circle_integrable
  exact (continuous_blockModelColors hp b hq ell L r).mul
    (((hA.add (continuous_blockPhaseEstimator_diagonal hq ell L)).sub continuous_const).norm.pow 2)

/-- The analytic tolerance is fixed before all diagonal frequency choices.
The conclusion applies to any actual nonnegative continuous densities with
that total color error. It makes no assertion that geometry realizes them. -/
theorem block_diagonal_transfer {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    (hb : ∀ r, ‖b r‖ ≤ 1) {q A : UnitAddCircle → ℂ} (hq : Continuous q)
    (hqB : ∀ z, ‖q z‖ ≤ 2) (hA : Continuous A) (k : ℕ)
    {ell delta nu : ℝ} (hell : 0 < ell) (hs : 6*ell ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1/100)
    (hn0 : delta/2 ≤ (n:ℝ)*ell^2) (hn1 : (n:ℝ)*ell^2 ≤ delta)
    (hmass : (∫ z, blockTotal p z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p b z-q z‖^2 ∂phaseHaar) ≤ delta)
    (hnu : 0 < nu) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ B : (j : ℕ) → (Fin j → ℤ) → ℤ,
      ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
        (∀ j : Fin n, B j (fun i => L ⟨i.val, i.isLt.trans j.isLt⟩) < L j) ∧
        ∀ g : Fin m → UnitAddCircle → ℝ,
          (∀ r, Continuous (g r)) → (∀ r z, 0 ≤ g r z) →
          colorL1Distance (blockModelColors p b q ell L) g ≤ e0 →
          ((∫ z, Real.sqrt (blockTotal p z) ∂phaseHaar)-300*delta^2-nu ≤
             ∫ z, Real.sqrt (blockTotal g z) ∂phaseHaar) ∧
          ((∑ r, ∫ z, g r z*
              ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*b r‖^2 ∂phaseHaar) ≤
            (∫ z, blockPreviousError p b A k z ∂phaseHaar)+4/delta+nu) := by
  have hn : 0 < n := by
    by_contra hh
    have hz : n = 0 := Nat.eq_zero_of_not_pos hh
    simp only [hz,Nat.cast_zero,zero_mul] at hn0
    linarith
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hA.continuousOn
  have hAb : ∀ z, ‖A z‖ ≤ C := fun z => hC z (mem_univ z)
  let W : ℝ := (C+2+1/ell+(k:ℝ)+1)^2
  have hW : 0 ≤ W := sq_nonneg _
  let e0 : ℝ := min ((nu/2)^2) ((nu/2)/(W+1))
  have he0 : 0 < e0 := lt_min (sq_pos_of_pos (by linarith))
    (div_pos (by linarith) (by linarith))
  refine ⟨e0,he0,?_⟩
  intro B
  obtain ⟨L,hL,hB,hS,hE⟩ := block_model_diagonal hp hc b hb hq hqB
    (CircleBounded.continuous hA) k hell hs hd hd1 hn0 hn1 hmass hcenter
    (show 0 < nu/2 by linarith) B
  refine ⟨L,hL,hB,?_⟩
  intro g hgc hg hclose
  have hmodels := continuous_blockModelColors hc b hq ell L
  have hmodel0 := blockModelColors_nonneg hp hb hqB hell.le hs L
  have hsqrt : Real.sqrt (colorL1Distance (blockModelColors p b q ell L) g) ≤ nu/2 := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by linarith, hclose.trans (min_le_left _ _)⟩
  have hweight : W*colorL1Distance (blockModelColors p b q ell L) g ≤ nu/2 := by
    have he := hclose.trans (min_le_right _ _)
    have hprod := (le_div_iff₀ (show 0 < W+1 by linarith)).1 he
    have hnE := colorL1Distance_nonneg (blockModelColors p b q ell L) g
    nlinarith
  constructor
  · have hstab := color_hellinger_stability hmodel0 hg hmodels hgc
    have heq : blockTotal (blockModelColors p b q ell L) =
        fun z => blockModelDensity p b q n ell z (fun i => L i • z) := rfl
    rw [heq] at hstab
    linarith
  · let w : Fin m → UnitAddCircle → ℝ := fun r z =>
      ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*b r‖^2
    have hwc (r : Fin m) : Continuous (w r) := by
      exact (((hA.add (continuous_blockPhaseEstimator_diagonal hq ell L)).sub continuous_const).norm.pow 2)
    have hwb (r : Fin m) (z : UnitAddCircle) : 0 ≤ w r z ∧ w r z ≤ W :=
      ⟨sq_nonneg _,block_estimator_weight_bound hn hell hqB hAb hb k L r z⟩
    have hstab := color_weighted_stability hmodels hgc hwc hwb
    rw [integral_blockErrorTest_diagonal hc b hq hA k ell L] at hE
    change (∑ r, ∫ z, g r z*w r z ∂phaseHaar) ≤ _
    change (∑ r, ∫ z, blockModelColors p b q ell L r z*w r z ∂phaseHaar) ≤ _ at hE
    linarith

end ThreeTorus
end
end

section

/-! A finite tree of actual constructions with cofinal next integers admits
successive lower bounds of exactly the form required by the fixed phase tests.
This is dependent choice on a finite tree, not independence of the diagonal. -/
noncomputable section
open Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma finite_frequency_tree {n : ℕ}
    (R : (k : ℕ) → (Fin k → ℤ) → Prop)
    (hzero : R 0 (fun i => Fin.elim0 i))
    (hstep : ∀ k (v : Fin k → ℤ), k < n → R k v →
      ∀ᶠ N : ℤ in atTop, R (k+1) (Fin.snoc v N)) :
    ∃ B : (k : ℕ) → (Fin k → ℤ) → ℤ,
      ∀ L : Fin n → ℤ,
        (∀ j : Fin n, B j (fun i => L ⟨i.val,i.isLt.trans j.isLt⟩) < L j) → R n L := by
  classical
  have hbound : ∀ k (v : Fin k → ℤ), ∃ b : ℤ,
      ∀ N : ℤ, b < N → k < n → R k v → R (k+1) (Fin.snoc v N) := by
    intro k v
    by_cases hh : k < n ∧ R k v
    · obtain ⟨b,hb⟩ := eventually_atTop.1 (hstep k v hh.1 hh.2)
      exact ⟨b,fun N hN _ _ => hb N hN.le⟩
    · exact ⟨0,fun _ _ hk hv => (hh ⟨hk,hv⟩).elim⟩
  choose B hB using hbound
  refine ⟨B,?_⟩
  intro L hL
  have hind : ∀ k (hk : k ≤ n), R k (fun i => L ⟨i.val,i.isLt.trans_le hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      convert hzero using 1
    | succ k ih =>
      intro hk
      have hk' : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hh := hB k (fun i => L ⟨i.val,i.isLt.trans hk'⟩)
        (L ⟨k,hk'⟩) (hL ⟨k,hk'⟩) hk' (ih hk'.le)
      convert hh using 1
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp
  simpa only [Fin.eta] using hind n le_rfl

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def colorMass {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) : ℝ :=
  ∑ r, ∫ z, p r z ∂phaseHaar

def colorModel {m k : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (a : Fin m → UnitAddCircle → ℂ) (ell : ℝ) (L : Fin k → ℤ)
    (r : Fin m) (z : UnitAddCircle) : ℝ :=
  p r z*∏ j, colorFactor a ell (L j) r z

lemma colorFactor_bounds {m : ℕ} {a : Fin m → UnitAddCircle → ℂ}
    (ha : ∀ r z, ‖a r z‖ ≤ 3) {ell : ℝ} (he : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (N : ℤ) (r : Fin m) (z : UnitAddCircle) :
    0 ≤ colorFactor a ell N r z ∧ colorFactor a ell N r z ≤ 2 := by
  have hh := blockFactor_bounds he (a r z) (N • z)
  have hm := mul_le_mul_of_nonneg_left (ha r z) (show 0 ≤ 2*ell by positivity)
  have hEq : colorFactor a ell N r z = blockFactor ell (a r z) (N • z) := by
    unfold colorFactor blockFactor
    rw [mul_comm (fourier (-1) _) (a r z),fourier_neg]
  rw [hEq]
  constructor <;> linarith [hh.1,hh.2]

lemma continuous_colorModel {m k : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) {a : Fin m → UnitAddCircle → ℂ}
    (ha : ∀ r, Continuous (a r)) (ell : ℝ) (L : Fin k → ℤ) (r : Fin m) :
    Continuous (colorModel p a ell L r) := by
  apply (hp r).mul
  exact continuous_finsetProd _ (fun j _ => continuous_colorFactor ha ell (L j) r)

lemma colorModel_zero {m : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (a : Fin m → UnitAddCircle → ℂ) (ell : ℝ) (L : Fin 0 → ℤ) :
    colorModel p a ell L = p := by
  funext r z
  simp [colorModel]

lemma colorModel_snoc {m k : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (a : Fin m → UnitAddCircle → ℂ) (ell : ℝ) (L : Fin k → ℤ) (N : ℤ) :
    colorModel p a ell (Fin.snoc L N) =
      fun r z => colorModel p a ell L r z*colorFactor a ell N r z := by
  funext r z
  simp only [colorModel,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
  ring

lemma colorModel_bounds {m k : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {a : Fin m → UnitAddCircle → ℂ}
    (ha : ∀ r z, ‖a r z‖ ≤ 3) {ell : ℝ} (he : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (L : Fin k → ℤ) (r : Fin m) (z : UnitAddCircle) :
    0 ≤ colorModel p a ell L r z ∧ colorModel p a ell L r z ≤ p r z*2^k := by
  have h0 := fun j => (colorFactor_bounds ha he hs (L j) r z).1
  have h2 := fun j => (colorFactor_bounds ha he hs (L j) r z).2
  constructor
  · exact mul_nonneg (hp r z) (Finset.prod_nonneg (fun j _ => h0 j))
  · apply mul_le_mul_of_nonneg_left _ (hp r z)
    simpa using Finset.prod_le_prod₀ (s := Finset.univ) (fun j _ => h0 j) (fun j _ => h2 j)

lemma colorMass_le_add_distance {m : ℕ} {p g : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (hg : ∀ r, Continuous (g r)) :
    colorMass g ≤ colorMass p+colorL1Distance p g := by
  have hh r : (∫ z, g r z ∂phaseHaar) ≤ (∫ z, p r z ∂phaseHaar)+
      (∫ z, |p r z-g r z| ∂phaseHaar) := by
    have ht := integral_mono (continuous_circle_integrable (hg r))
      (continuous_circle_integrable ((hp r).add ((hp r).sub (hg r)).abs))
      (fun z => by
        change g r z ≤ p r z+|p r z-g r z|
        linarith [neg_le_abs (p r z-g r z)])
    change (∫ z, g r z ∂phaseHaar) ≤ ∫ z, p r z+|p r z-g r z| ∂phaseHaar at ht
    erw [integral_add (continuous_circle_integrable (hp r))
      (continuous_circle_integrable ((hp r).sub (hg r)).abs)] at ht
    exact ht
  simpa only [colorMass,colorL1Distance,Finset.sum_add_distrib] using
    Finset.sum_le_sum (s := Finset.univ) (fun r _ => hh r)

lemma colorModel_mass_bound {m k : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (hp0 : ∀ r z, 0 ≤ p r z)
    {a : Fin m → UnitAddCircle → ℂ} (ha : ∀ r, Continuous (a r))
    (ha3 : ∀ r z, ‖a r z‖ ≤ 3) {ell : ℝ} (he : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (L : Fin k → ℤ) : colorMass (colorModel p a ell L) ≤ colorMass p*2^k := by
  have hh r : (∫ z, colorModel p a ell L r z ∂phaseHaar) ≤ (∫ z, p r z ∂phaseHaar)*2^k := by
    have ht := integral_mono (continuous_circle_integrable (continuous_colorModel hp ha ell L r))
      ((continuous_circle_integrable (hp r)).mul_const _)
      (fun z => (colorModel_bounds hp0 ha3 he hs L r z).2)
    simpa only [integral_mul_const] using ht
  simpa only [colorMass,Finset.sum_mul] using Finset.sum_le_sum (s := Finset.univ) (fun r _ => hh r)

lemma colorL1Distance_symm {m : ℕ} (p g : Fin m → UnitAddCircle → ℝ) :
    colorL1Distance p g = colorL1Distance g p := by
  unfold colorL1Distance
  simp_rw [abs_sub_comm]

lemma colorModel_step_error {m k : ℕ} {p g h : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (hg : ∀ r, Continuous (g r))
    (hh : ∀ r, Continuous (h r)) {a : Fin m → UnitAddCircle → ℂ}
    (ha : ∀ r, Continuous (a r)) (ha3 : ∀ r z, ‖a r z‖ ≤ 3)
    {ell : ℝ} (he : 0 ≤ ell) (hs : 6*ell ≤ 1) (L : Fin k → ℤ) (N : ℤ) :
    colorL1Distance (colorModel p a ell (Fin.snoc L N)) h ≤
      2*colorL1Distance (colorModel p a ell L) g+
        colorL1Distance (fun r z => g r z*colorFactor a ell N r z) h := by
  rw [colorModel_snoc]
  apply (colorL1Distance_triangle
    (fun r => (continuous_colorModel hp ha ell L r).mul (continuous_colorFactor ha ell N r))
    (fun r => (hg r).mul (continuous_colorFactor ha ell N r)) hh).trans
  apply add_le_add _ le_rfl
  apply colorL1Distance_mul_bound (fun r => continuous_colorModel hp ha ell L r) hg
    (fun r => continuous_colorFactor ha ell N r)
  intro r z
  rw [abs_of_nonneg (colorFactor_bounds ha3 he hs N r z).1]
  exact (colorFactor_bounds ha3 he hs N r z).2

lemma colorModel_initial_error {m k : ℕ} {p g : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) (hg : ∀ r, Continuous (g r))
    {a : Fin m → UnitAddCircle → ℂ} (ha : ∀ r, Continuous (a r))
    (ha3 : ∀ r z, ‖a r z‖ ≤ 3) {ell : ℝ} (he : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (L : Fin k → ℤ) :
    colorL1Distance (colorModel p a ell L) (colorModel g a ell L) ≤
      2^k*colorL1Distance p g := by
  apply colorL1Distance_mul_bound hp hg
    (fun r => continuous_finsetProd _ (fun j _ => continuous_colorFactor ha ell (L j) r))
  intro r z
  have hh := colorModel_bounds (p := fun _ _ => 1) (by intros; norm_num) ha3 he hs L r z
  simp only [colorModel, one_mul] at hh
  rw [abs_of_nonneg hh.1]
  exact hh.2

lemma colorModel_eq_blockModelColors {m k : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (b : Fin m → ℂ) (q : UnitAddCircle → ℂ) (ell : ℝ) (L : Fin k → ℤ) :
    colorModel p (fun r z => b r-q z) ell L = blockModelColors p b q ell L := by
  funext r z
  unfold colorModel blockModelColors blockProduct
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  unfold colorFactor blockFactor
  rw [fourier_neg,mul_comm (starRingEnd ℂ _) (b r-q z)]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma ColoredPair.physicalError_chart {R : Type} {C : ColoredState R} {N : ℕ}
    (s : ColoredPair C N) (f g : TripleTorus → ℂ) :
    physicalError (f ∘ s.chart) (g ∘ s.chart) = physicalError f g := by
  change physicalError ((f ∘ passageChart (s.transmit.H N)) ∘ passageChart (s.refresh.H s.n))
    ((g ∘ passageChart (s.transmit.H N)) ∘ passageChart (s.refresh.H s.n)) = _
  rw [ThreeTorus.physicalError_chart (s.refresh.Hcontinuous s.n).measurable,
    ThreeTorus.physicalError_chart (s.transmit.Hcontinuous N).measurable]

/-- A finite trace contains actual neutral--signal pairs, including their
smooth geometry and exact intermediate speeds. -/
inductive ColoredPath {R : Type} (C : ColoredState R) :
    {k : ℕ} → (Fin k → ℤ) → ColoredState R → Equiv.Perm TripleTorus → Prop
  | nil : ColoredPath C (fun i => Fin.elim0 i) C (Equiv.refl TripleTorus)
  | snoc {k : ℕ} {L : Fin k → ℤ} {D : ColoredState R} {α : Equiv.Perm TripleTorus}
      (h : ColoredPath C L D α) {N : ℕ} (s : ColoredPair D N) :
      ColoredPath C (Fin.snoc L (N:ℤ)) s.output (α.trans s.chart)

namespace ColoredPath
variable {R : Type} {C D : ColoredState R} {k : ℕ} {L : Fin k → ℤ}
    {α : Equiv.Perm TripleTorus} (h : ColoredPath C L D α)
include h
lemma continuous : Continuous α := by
  induction h with
  | nil => exact continuous_id
  | snoc h s ih => exact s.chart_continuous.comp ih
lemma preserves : MeasurePreserving α tripleVolume tripleVolume := by
  induction h with
  | nil => exact MeasurePreserving.id tripleVolume
  | snoc h s ih => exact s.chart_preserves.comp ih
lemma physicalError_eq (f g : TripleTorus → ℂ) :
    physicalError (f ∘ α) (g ∘ α) = physicalError f g := by
  induction h generalizing f g with
  | nil => rfl
  | @snoc k L D α h N s ih =>
    change physicalError ((f ∘ s.chart) ∘ α) ((g ∘ s.chart) ∘ α) = _
    rw [ih,s.physicalError_chart]
end ColoredPath

lemma eventually_int_of_eventually_nat {P : ℤ → Prop}
    (h : ∀ᶠ n : ℕ in atTop, P (n:ℤ)) : ∀ᶠ n : ℤ in atTop, P n := by
  obtain ⟨b,hb⟩ := eventually_atTop.1 h
  filter_upwards [eventually_ge_atTop (b:ℤ)] with N hN
  have hN0 : 0 ≤ N := (Int.natCast_nonneg b).trans hN
  have hbN : b ≤ N.toNat := by omega
  simpa only [Int.toNat_of_nonneg hN0] using hb N.toNat hbN

end ThreeTorus
end
end

section
noncomputable section
open scoped BigOperators
namespace ThreeTorus

def iterationError (t : ℝ) (k : ℕ) : ℝ := ((k:ℝ)+1)*2^k*t

lemma iterationError_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : 0 ≤ iterationError t k := by
  unfold iterationError
  positivity

lemma iterationError_step {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    2*iterationError t k+t ≤ iterationError t (k+1) := by
  have hp : (1:ℝ) ≤ 2^(k+1) := one_le_pow₀ (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hp ht
  unfold iterationError
  rw [pow_succ] at hh ⊢
  push_cast
  nlinarith

/-- Choices are uniform over the future actual packet states. -/
lemma finite_iteration_budget (n : ℕ) {M γ ε : ℝ} (hM : 0 ≤ M) (hγ : 0 < γ)
    (hε : 0 < ε) :
    ∃ t ω U : ℝ, 0 < t ∧ 0 < ω ∧ 0 < U ∧ iterationError t n < ε ∧
      (∀ k ≤ n, M*2^k+iterationError t k ≤ U) ∧
      ∀ k ≤ n, 2*γ*(((k:ℝ)+1)*ω)*U ≤ t/2 := by
  let v : ℝ := ((n:ℝ)+1)*2^n
  have hv : 0 < v := by dsimp [v]; positivity
  let t := ε/(2*v)
  have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hv)
  have htEq : v*t = ε/2 := by dsimp [t]; field_simp
  let U := 2^n*(M+((n:ℝ)+1)*t)+1
  have hU : 0 < U := by dsimp [U]; positivity
  let ω := (t/2)/(2*γ*((n:ℝ)+1)*(U+1))
  have hω : 0 < ω := by dsimp [ω]; positivity
  refine ⟨t,ω,U,ht,hω,hU,?_,?_,?_⟩
  · change v*t < ε
    rw [htEq]
    linarith
  · intro k hk
    have hk' : (k:ℝ)+1 ≤ (n:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hk
    have hp : (2:ℝ)^k ≤ 2^n := pow_le_pow_right₀ (by norm_num) hk
    have h1 := mul_le_mul_of_nonneg_left hp hM
    have h2 : ((k:ℝ)+1)*2^k*t ≤ ((n:ℝ)+1)*2^n*t := by gcongr
    dsimp [iterationError,U]
    nlinarith
  · intro k hk
    have hk' : (k:ℝ)+1 ≤ (n:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hk
    calc
      _ ≤ 2*γ*(((n:ℝ)+1)*ω)*(U+1) := by gcongr; linarith
      _ = t/2 := by
        dsimp [ω]
        have hn : (n:ℝ)+1 ≠ 0 := by positivity
        have hU' : U+1 ≠ 0 := by positivity
        field_simp

lemma finite_color_tolerance (m : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ e : ℝ, 0 < e ∧ e ≤ t/2 ∧ (m:ℝ)*e < t/2 := by
  have hm : 0 < (m:ℝ)+1 := by positivity
  let e := (t/2)/((m:ℝ)+1)
  have he : 0 < e := div_pos (half_pos ht) hm
  have heq : e*((m:ℝ)+1) = t/2 := div_mul_cancel₀ _ (ne_of_gt hm)
  refine ⟨e,he,?_,?_⟩
  · have h := mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) he.le
    nlinarith
  · nlinarith

end ThreeTorus
end
end

section

/-! Concrete finite colored iteration. The cofinal-frequency tree is built
from actual neutral--signal pairs. The error budget is fixed before the
initial anchor state and before any future packet index type is known. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def ColoredSignalRealizes (b D : ℝ) (d : ℝ → ℂ) (γ ell : ℝ) : Prop :=
  ∀ (R : Type) [DecidableEq R], ∀ (C : ColoredState R),
    ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
    ∀ (a : R → UnitAddCircle → ℂ), (∀ r, Continuous (a r)) →
    ∀ ω : ℝ, 0 ≤ ω → C.Matches d a ω →
    ∀ ε η : ℝ, 0 < ε → 0 < η →
    ∀ᶠ N : ℕ in atTop, ∃ s : ColoredPair C N, s.Tracks η ∧ ∀ r,
      physicalError (C.vector r) (s.output.vector r ∘ s.chart) < ε ∧
      (∫ z, |s.output.density r z-C.density r z*colorFactor a ell (N:ℤ) r z| ∂phaseHaar) <
        2*γ*ω*(∫ z, C.density r z ∂phaseHaar)+ε

/-- The interface is discharged by the actual geometric construction. -/
theorem exists_concrete_colored_signal {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ColoredSignalRealizes b D d γ (refreshedStrength (signalPrimeProduct L) γ) :=
  exists_colored_signal hb hbD hd hdc hdr hd0 hds

/-- Fixed data and a small coefficient tolerance first; the threshold tree is
chosen on the actual initial state; ALL diagonals above that tree are realized
with small product-model and physical errors. No independence of the diagonal,
modeled next state, or unproved packet producer is used. -/
theorem ColoredSignalRealizes.iterate {b D γ ell : ℝ} {d : ℝ → ℂ}
    (hsignal : ColoredSignalRealizes b D d γ ell)
    (hd : Continuous d) (hdc : HasCompactSupport d) (hγ : 0 < γ)
    (hell : 0 ≤ ell) (hells : 6*ell ≤ 1)
    (m n : ℕ) (a : Fin m → UnitAddCircle → ℂ)
    (ha : ∀ r, Continuous (a r)) (ha3 : ∀ r z, ‖a r z‖ ≤ 3)
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ C : ColoredState (Fin m),
      colorMass C.density ≤ M → ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
      C.Matches d a ω →
      ∃ B : (j : ℕ) → (Fin j → ℤ) → ℤ, ∀ L : Fin n → ℤ,
        (∀ j : Fin n, B j (fun i => L ⟨i.val,i.isLt.trans j.isLt⟩) < L j) →
        ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
          ColoredPath C L E α ∧
          colorL1Distance (colorModel C.density a ell L) E.density < ε ∧
          (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < ε) ∧
          ∃ μ : ℝ, 0 < μ ∧ E.InBand b D μ ∧ E.Matches d a (((n:ℝ)+1)*ω) := by
  classical
  obtain ⟨t,ω,U,ht,hω,hU,hfinal,hmassBound,hsubstitution⟩ := finite_iteration_budget n hM hγ hε
  obtain ⟨e,he,het,hem⟩ := finite_color_tolerance m ht
  refine ⟨ω,hω,?_⟩
  intro C hmass margin hmargin hband hmatch
  let Reach (k : ℕ) (L : Fin k → ℤ) : Prop :=
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus, ∃ μ : ℝ,
      0 < μ ∧ ColoredPath C L E α ∧ E.InBand b D μ ∧
      E.Matches d a (((k:ℝ)+1)*ω) ∧
      colorL1Distance (colorModel C.density a ell L) E.density ≤ iterationError t k ∧
      ∀ r, physicalError (C.vector r) (E.vector r ∘ α) ≤ iterationError t k
  have hzero : Reach 0 (fun i => Fin.elim0 i) := by
    refine ⟨C,Equiv.refl _,margin,hmargin,ColoredPath.nil,hband,?_,?_,?_⟩
    · simpa using hmatch
    · rw [colorModel_zero]
      simpa [colorL1Distance,iterationError] using ht.le
    · intro r
      simpa [physicalError,iterationError] using ht.le
  have hstep : ∀ k (L : Fin k → ℤ), k < n → Reach k L →
      ∀ᶠ N : ℤ in atTop, Reach (k+1) (Fin.snoc L N) := by
    intro k L hk hreach
    obtain ⟨E,α,μ,hμ,hpath,hbandE,hmatchE,herror,hphysical⟩ := hreach
    have hmassE : colorMass E.density ≤ U := by
      have hmodel := colorModel_mass_bound C.density_continuous C.density_nonneg ha ha3 hell hells L
      have hbase := mul_le_mul_of_nonneg_right hmass (show (0:ℝ) ≤ 2^k by positivity)
      exact (colorMass_le_add_distance
        (continuous_colorModel C.density_continuous ha ell L) E.density_continuous).trans
        ((add_le_add (hmodel.trans hbase) herror).trans (hmassBound k hk.le))
    obtain ⟨η₀,hη₀,hcoeff⟩ := core_coefficient_drift_budget E.packets hd hdc
      (fun i => a (E.color i)) (fun i => ha (E.color i)) hω hmatchE
    let η := min η₀ (μ/2)
    have hη : 0 < η := lt_min hη₀ (half_pos hμ)
    have hωk : 0 ≤ ((k:ℝ)+1)*ω := by positivity
    have hready := hsignal (Fin m) E μ hμ hbandE a ha (((k:ℝ)+1)*ω) hωk hmatchE e η he hη
    apply eventually_int_of_eventually_nat
    filter_upwards [hready] with N hN
    obtain ⟨s,htrack,hcolor⟩ := hN
    have hbandNext : s.output.InBand b D (μ/2) :=
      htrack.band_margin hbandE (min_le_right _ _)
    have hcoeffNext : s.output.Matches d a ((((k+1:ℕ):ℝ)+1)*ω) := by
      intro i y _hy
      have hh := hcoeff _ s.final (Sigma.fst ∘ Sigma.fst) s.output.scale
        (htrack.mono (min_le_left _ _)) i y
      change ‖d ((s.final.m i:ℝ)/s.output.scale)-
        a (E.color ((Sigma.fst ∘ Sigma.fst) i))
          ((s.final.m i:ℝ)*s.final.V y:UnitAddCircle)‖ ≤ _
      have heq : ((((k+1:ℕ):ℝ)+1)*ω) = ((k:ℝ)+1)*ω+ω := by push_cast; ring
      rw [heq]
      exact hh
    have hdensityStep : colorL1Distance
        (fun r z => E.density r z*colorFactor a ell (N:ℤ) r z) s.output.density ≤ t := by
      rw [colorL1Distance_symm]
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun r _ => (hcolor r).2.le)
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
      change colorL1Distance s.output.density
        (fun r z => E.density r z*colorFactor a ell (N:ℤ) r z) ≤
          2*γ*(((k:ℝ)+1)*ω)*colorMass E.density+(m:ℝ)*e at hh
      have hb := mul_le_mul_of_nonneg_left hmassE (show 0 ≤ 2*γ*(((k:ℝ)+1)*ω) by positivity)
      have hs := hsubstitution k hk.le
      linarith
    refine ⟨s.output,α.trans s.chart,μ/2,half_pos hμ,hpath.snoc s,hbandNext,hcoeffNext,?_,?_⟩
    · have hh := colorModel_step_error C.density_continuous E.density_continuous
        s.output.density_continuous ha ha3 hell hells L (N:ℤ)
      have hs := iterationError_step ht.le k
      linarith
    · intro r
      have htwo := hpath.physicalError_eq (E.vector r) (s.output.vector r ∘ s.chart)
      have hh := physicalError_triangle (C.vector_continuous r)
        ((E.vector_continuous r).comp hpath.continuous)
        ((s.output.vector_continuous r).comp (s.chart_continuous.comp hpath.continuous))
      change physicalError (C.vector r) (s.output.vector r ∘ (α.trans s.chart)) ≤
        2*physicalError (C.vector r) (E.vector r ∘ α)+
          2*physicalError (E.vector r ∘ α) ((s.output.vector r ∘ s.chart) ∘ α) at hh
      rw [htwo] at hh
      have hs := iterationError_step ht.le k
      have hp := hphysical r
      have hp' := (hcolor r).1
      linarith
  obtain ⟨B,hB⟩ := finite_frequency_tree Reach hzero hstep
  refine ⟨B,?_⟩
  intro L hL
  obtain ⟨E,α,μ,hμ,hpath,hbandE,hmatchE,herr,hphys⟩ := hB L hL
  exact ⟨E,α,hpath,herr.trans_lt hfinal,fun r => (hphys r).trans_lt hfinal,
    μ,hμ,hbandE,hmatchE⟩

end ThreeTorus
end
end

section

/-! The fixed pre-anchor model tests are achieved by the actual packet family
constructed along a dependent finite path. This does not assume independent
phases for the realized packets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma colorMass_eq_integral_total {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) :
    colorMass p = ∫ z, blockTotal p z ∂phaseHaar := by
  unfold colorMass blockTotal
  rw [integral_finsetSum]
  intro r _
  exact continuous_circle_integrable (hp r)

/-- Accuracy requirements for the actual anchor are fixed BEFORE that anchor
is made. Given any such actual anchor, the two block tests are achieved on one
actual endpoint of a sequence of neutral/signal pairs. -/
theorem ColoredSignalRealizes.block {b D γ ell : ℝ} {d : ℝ → ℂ}
    (hsignal : ColoredSignalRealizes b D d γ ell)
    (hdc : Continuous d) (hds : HasCompactSupport d) (hγ : 0 < γ)
    {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (tags : Fin m → ℂ)
    (htags : ∀ r, ‖tags r‖ ≤ 1) {q A : UnitAddCircle → ℂ} (hq : Continuous q)
    (hqB : ∀ z, ‖q z‖ ≤ 2) (hA : Continuous A) (k : ℕ)
    {delta nu ε : ℝ} (hell : 0 < ell) (hells : 6*ell ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1/100)
    (hn0 : delta/2 ≤ (n:ℝ)*ell^2) (hn1 : (n:ℝ)*ell^2 ≤ delta)
    (hmass : (∫ z, blockTotal p z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p tags z-q z‖^2 ∂phaseHaar) ≤ delta)
    (hnu : 0 < nu) (hε : 0 < ε) :
    ∃ e ω : ℝ, 0 < e ∧ 0 < ω ∧
      ∀ C : ColoredState (Fin m), colorL1Distance p C.density ≤ e →
      ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
      C.Matches d (fun r z => tags r-q z) ω →
      ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
        ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
          ColoredPath C L E α ∧
          (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < ε) ∧
          ((∫ z, Real.sqrt (blockTotal p z) ∂phaseHaar)-300*delta^2-nu ≤
            ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
          ((∑ r, ∫ z, E.density r z*
            ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*tags r‖^2 ∂phaseHaar) ≤
            (∫ z, blockPreviousError p tags A k z ∂phaseHaar)+4/delta+nu) := by
  obtain ⟨e0,he0,htests⟩ := block_diagonal_transfer hp hc tags htags hq hqB hA k
    hell hells hd hd1 hn0 hn1 hmass hcenter hnu
  let a : Fin m → UnitAddCircle → ℂ := fun r z => tags r-q z
  have ha : ∀ r, Continuous (a r) := fun r => continuous_const.sub hq
  have ha3 : ∀ r z, ‖a r z‖ ≤ 3 := fun r z =>
    (norm_sub_le _ _).trans (by linarith [htags r,hqB z])
  obtain ⟨ω,hω,hiteration⟩ := hsignal.iterate hdc hds hγ hell.le hells m n a ha ha3
    (M := 3) (by norm_num) (lt_min (half_pos he0) hε)
  let e : ℝ := min 1 (e0/(2*2^n))
  have he : 0 < e := lt_min zero_lt_one (div_pos he0 (by positivity))
  refine ⟨e,ω,he,hω,?_⟩
  intro C hclose margin hmargin hband hmatch
  have hmassC : colorMass C.density ≤ 3 := by
    have h0 := colorMass_le_add_distance hc C.density_continuous
    rw [colorMass_eq_integral_total hc] at h0
    have he1 : e ≤ 1 := min_le_left _ _
    linarith
  obtain ⟨B,hB⟩ := hiteration C hmassC margin hmargin hband hmatch
  obtain ⟨L,hL,hLB,htest⟩ := htests B
  obtain ⟨E,α,hpath,hdensity,hphysical,_hend⟩ := hB L hLB
  have hinitial := colorModel_initial_error hc C.density_continuous ha ha3 hell.le hells L
  have hsmall : 2^n*colorL1Distance p C.density ≤ e0/2 := by
    have he2 : e ≤ e0/(2*2^n) := min_le_right _ _
    have hprod := (le_div_iff₀ (show (0:ℝ) < 2*2^n by positivity)).1 (hclose.trans he2)
    nlinarith
  have hmodels := colorL1Distance_triangle (continuous_colorModel hc ha ell L)
    (continuous_colorModel C.density_continuous ha ell L) E.density_continuous
  have herr : colorL1Distance (blockModelColors p tags q ell L) E.density ≤ e0 := by
    rw [← colorModel_eq_blockModelColors]
    change colorL1Distance (colorModel p a ell L) E.density ≤ e0
    have hi := hinitial.trans hsmall
    have hd' := lt_of_lt_of_le hdensity (min_le_left (e0/2) ε)
    linarith
  obtain ⟨hsqrt,hpred⟩ := htest E.density E.density_continuous E.density_nonneg herr
  exact ⟨L,hL,E,α,hpath,(fun r => (hphysical r).trans_le (min_le_right _ _)),hsqrt,hpred⟩

end ThreeTorus
end
end

section

/-! The pre-anchor smooth signal is chosen before the anchor integer and
before its accuracy tolerances. This is source 04, the band-function step. -/
noncomputable section
open Set Function Filter MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Smooth interpolation near a finite pairwise disjoint compact family off
zero, with the exact reflection required by the real signal law. -/
theorem exists_symmetric_anchor_band {ι : Type*} [Fintype ι]
    (K : ι → Set ℝ) (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise (Disjoint on K)) (h0 : ∀ i, 0 ∉ K i)
    (τ : ι → ι) (hKr : ∀ i x, x ∈ K i → -x ∈ K (τ i))
    (b : ι → ℂ) (hbr : ∀ i, b (τ i) = conj (b i))
    {q : UnitAddCircle → ℂ}
    (hqs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x:UnitAddCircle)))
    (hqr : ∀ z, q (-z) = conj (q z)) :
    ∃ d : ℝ → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d ∧ HasCompactSupport d ∧
      d 0 = 0 ∧ (∀ x, d (-x) = conj (d x)) ∧
      ∀ i x, x ∈ K i → d =ᶠ[𝓝 x] (fun y => b i-q (y:UnitAddCircle)) := by
  classical
  obtain ⟨χ,hχ,hχd⟩ := finite_disjoint_frequency_cutoffs K (fun _ => ({0}:Set ℝ)ᶜ)
    hK (fun _ => isOpen_compl_singleton) (fun i x hx he => h0 i (he ▸ hx)) hdisj
  let f (x : ℝ) : ℂ := ∑ i, (χ i x:ℂ)*(b i-q (x:UnitAddCircle))
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
    ContDiff.sum (fun i _ => (Complex.ofRealCLM.contDiff.comp (hχ i).1).mul (contDiff_const.sub hqs))
  have hfc : HasCompactSupport f := by
    have hh i : HasCompactSupport (fun x => (χ i x:ℂ)*(b i-q (x:UnitAddCircle))) :=
      ((hχ i).2.1.comp_left (show ((0:ℝ):ℂ) = 0 from rfl)).mul_right
    have he : f = ∑ i, (fun x => (χ i x:ℂ)*(b i-q (x:UnitAddCircle))) := by
      funext x
      simp only [f,Finset.sum_apply]
    rw [he]
    exact HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => hh i)
  have hf0 : f 0 = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hc0 : χ i 0 = 0 := by
      by_contra hn
      exact (hχ i).2.2.1 (subset_tsupport _ hn) rfl
    simp only [hc0,Complex.ofReal_zero,zero_mul]
  have hflocal i x (hx : x ∈ K i) : f =ᶠ[𝓝 x] (fun y => b i-q (y:UnitAddCircle)) := by
    filter_upwards [(hχ i).2.2.2.2 x hx] with y hy
    unfold f
    rw [Finset.sum_eq_single i]
    · simp only [Pi.one_apply] at hy
      rw [hy,Complex.ofReal_one,one_mul]
    · intro j _ hji
      have hz : χ j y = 0 := by
        by_contra hn
        have hi : χ i y ≠ 0 := by rw [hy]; exact one_ne_zero
        exact Set.disjoint_left.mp (hχd hji) (subset_tsupport _ hn) (subset_tsupport _ hi)
      rw [hz,Complex.ofReal_zero,zero_mul]
    · simp
  let d (x : ℝ) := (f x+conj (f (-x)))/2
  have hds : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d :=
    (hfs.add (Complex.conjCLE.contDiff.comp (hfs.comp contDiff_neg))).div_const _
  have hdc : HasCompactSupport d := by
    have hh : HasCompactSupport (fun x : ℝ => conj (f (-x))) :=
      (hfc.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (map_zero _)
    exact (hfc.add hh).mul_right
  refine ⟨d,hds,hdc,by simp [d,hf0],?_,?_⟩
  · intro x
    simp only [d,neg_neg,map_div₀,map_add,starRingEnd_self_apply,map_ofNat]
    ring
  · intro i x hx
    have h₂ := (hflocal (τ i) (-x) (hKr i x hx)).comp_tendsto (continuous_neg.tendsto x)
    filter_upwards [hflocal i x hx,h₂] with y hy hz
    simp only [Function.comp_apply] at hz
    dsimp only [d] at *
    rw [hy,hz,hbr,AddCircle.coe_neg,hqr]
    simp only [map_sub,starRingEnd_self_apply]
    ring

end ThreeTorus
end
end

section

/-! Uniform open room for actual anchors, and their exact temporal deviation.
These bounds do not take a model density or a later passage as input. -/
noncomputable section
open Set Function Filter MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma finite_positive_lower {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) : ∃ e : ℝ, 0 < e ∧ ∀ i, e ≤ a i := by
  classical
  have hh : ∀ s : Finset ι, ∃ e : ℝ, 0 < e ∧ ∀ i ∈ s, e ≤ a i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨e,he,hs⟩ := ih
      refine ⟨min e (a i),lt_min he (ha i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs j hj)
  obtain ⟨e,he,hs⟩ := hh Finset.univ
  exact ⟨e,he,fun i => hs i (Finset.mem_univ _)⟩

/-- A single positive enlargement works for every compact frequency image.
The band bounds also contain the entire compact signal support. -/
theorem anchor_uniform_room {ι : Type*} [Fintype ι]
    (K : ι → Set ℝ) (hK : ∀ i, IsCompact (K i)) (h0 : ∀ i, 0 ∉ K i)
    {d : ℝ → ℂ} (hdc : HasCompactSupport d)
    (a : ι → ℝ → ℂ) (hl : ∀ i x, x ∈ K i → d =ᶠ[𝓝 x] a i) :
    ∃ b D μ τ : ℝ, 0 < b ∧ b < D ∧ 0 < μ ∧ 0 < τ ∧
      support d ⊆ Icc (-D) D ∧
      ∀ i x, x ∈ K i → ∀ y, |y-x| < τ →
        d y = a i y ∧ b+μ ≤ |y| ∧ |y| ≤ D-μ := by
  classical
  let E := ⋃ i, K i
  have hEc : IsCompact E := isCompact_iUnion hK
  have hE0 : E ⊆ ({0}:Set ℝ)ᶜ := by
    intro x hx hzero
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact h0 i (hzero ▸ hi)
  obtain ⟨r,hr,hroom⟩ := hEc.exists_thickening_subset_open isOpen_compl_singleton hE0
  have hlow i x (hx : x ∈ K i) : r ≤ |x| := by
    by_contra h
    have hh : (0:ℝ) ∈ Metric.thickening r E := Metric.mem_thickening_iff.mpr
      ⟨x,mem_iUnion.mpr ⟨i,hx⟩,by simpa only [dist_zero_left,Real.norm_eq_abs] using lt_of_not_ge h⟩
    exact hroom hh rfl
  have hlocal i : K i ⊆ interior {x | d x = a i x} := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr (hl i x hx)
  choose t ht hsub using fun i => (hK i).exists_thickening_subset_open isOpen_interior (hlocal i)
  obtain ⟨t₀,ht₀,htall⟩ := finite_positive_lower t ht
  obtain ⟨M,hM⟩ := (hEc.union hdc).isBounded.exists_norm_le
  let R := max M 0
  let τ := min t₀ (min (r/4) (1/2))
  have hτ : 0 < τ := lt_min ht₀ (lt_min (by positivity) (by norm_num))
  refine ⟨r/4,R+r+2,r/4,τ,by positivity,by dsimp [R]; linarith [le_max_right M 0],
    by positivity,hτ,?_,?_⟩
  · intro x hx
    have hb : |x| ≤ R := (hM x (Or.inr (subset_tsupport d hx))).trans (le_max_left _ _)
    have ha := abs_le.mp hb
    dsimp [R] at *
    constructor <;> linarith
  · intro i x hx y hxy
    have he : y ∈ Metric.thickening (t i) (K i) := Metric.mem_thickening_iff.mpr
      ⟨x,hx,by simpa only [Real.dist_eq] using hxy.trans_le ((min_le_left _ _).trans (htall i))⟩
    have hyx : |y-x| < r/4 := hxy.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hyx' : |y-x| < 1/2 := hxy.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hxlo := hlow i x hx
    have hxhi : |x| ≤ R := (hM x (Or.inl (mem_iUnion.mpr ⟨i,hx⟩))).trans (le_max_left _ _)
    have hlower := (abs_le.mp (abs_abs_sub_abs_le_abs_sub y x)).1
    have hupper := (abs_le.mp (abs_abs_sub_abs_le_abs_sub y x)).2
    have heq : y ∈ {x | d x = a i x} := interior_subset (hsub i he)
    refine ⟨heq,?_,?_⟩ <;> dsimp [R] at * <;> linarith

lemma anchor_temporal_deviation {j : ℤ} {n : ℕ} (hn : 0 < n) (J : ℝ)
    {D R : ℝ} (hj : |(j:ℝ)/(n:ℝ)| ≤ D) (hJ : |J| ≤ R) :
    dist ((j:ℝ)*((1+J/(n:ℝ))/(n:ℝ)):UnitAddCircle) ((j:ℝ)/(n:ℝ):UnitAddCircle) ≤ D*R/(n:ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  calc
    _ ≤ |(j:ℝ)*((1+J/(n:ℝ))/(n:ℝ))-(j:ℝ)/(n:ℝ)| := circle_dist_le_real _ _
    _ = |(j:ℝ)/(n:ℝ)| *|J|/(n:ℝ) := by
      have he : (j:ℝ)*((1+J/(n:ℝ))/(n:ℝ))-(j:ℝ)/(n:ℝ) = ((j:ℝ)/(n:ℝ))*J/(n:ℝ) := by ring
      rw [he,abs_div,abs_mul,abs_of_pos hnR]
    _ ≤ D*R/(n:ℝ) := div_le_div_of_nonneg_right
      (mul_le_mul hj hJ (abs_nonneg _) ((abs_nonneg _).trans hj)) hnR.le

/-- Coefficient substitution on EVERY new speed point (not only a nonzero
spectral-density set). This is what the next real packet passage needs. -/
theorem anchor_coefficient_budget {ι : Type*} [Fintype ι]
    {q : UnitAddCircle → ℂ} (hq : Continuous q)
    {d : ℝ → ℂ} (a : ι → ℂ) {D ω : ℝ} (hω : 0 < ω) :
    ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, 0 < n ∧
      ∀ (j : ℤ) (i : ι) (J : ℝ), |(j:ℝ)/(n:ℝ)| ≤ D → |J| ≤ R →
        d ((j:ℝ)/(n:ℝ)) = a i-q ((j:ℝ)/(n:ℝ):UnitAddCircle) →
        ‖d ((j:ℝ)/(n:ℝ))-(a i-q ((j:ℝ)*((1+J/(n:ℝ))/(n:ℝ)):UnitAddCircle))‖ < ω := by
  obtain ⟨η,hη,hU⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hq) ω hω
  intro R
  have ht : ∀ᶠ n : ℕ in atTop, D*R/(n:ℝ) < η :=
    ((tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hη))
  filter_upwards [ht,eventually_gt_atTop (0:ℕ)] with n hn hnp
  refine ⟨hnp,?_⟩
  intro j i J hj hJ he
  rw [he]
  have hh := hU ((anchor_temporal_deviation hnp J hj hJ).trans_lt hn)
  rw [dist_eq_norm] at hh
  convert hh using 1
  congr 1
  ring

end ThreeTorus
end
end

section

/-! The correctly ordered anchor constructs the literal finite output state,
with coefficient matching valid on every next packet core. -/
noncomputable section
open Set Function Filter MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Carrier first; signal, band and all block tolerances afterwards; anchor
integer last and still arbitrarily large. No modeled next densities occur. -/
theorem eventually_anchor_state {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent) :
    ∀ᶠ c : ℕ in atTop,
      ∀ (d : ℝ → ℂ) (q : UnitAddCircle → ℂ) (a : ι → ℂ), Continuous q →
      ∀ b D margin τ : ℝ, 0 < τ →
      (∀ i x, x ∈ F.core i → ∀ s,
        |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < τ →
        d s = a i-q (s:UnitAddCircle) ∧ b+margin ≤ |s| ∧ |s| ≤ D-margin) →
      ∀ ε ω κ : ℝ, 0 < ε → 0 < ω → 0 < κ →
      ∃ g : PassageGeometryFamily F.V, g.c = c ∧
      ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ L : ℝ,
        0 < δ ∧ δ < κ ∧ 0 < L ∧ g.J₀ = neutralJitterReal cut L 0 ∧
      ∃ S : ℕ → ι → Finset ℤ, ∀ᶠ n : ℕ in atTop, 0 < n ∧
        ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z| ∂phaseHaar) < ε) ∧
          (∀ i, b+margin ≤ |(G.m i:ℝ)/n| ∧ |(G.m i:ℝ)/n| ≤ D-margin) ∧
          ∀ i y, ‖d ((G.m i:ℝ)/n)-
            (a i.1-q ((G.m i:ℝ)*G.V y:UnitAddCircle))‖ < ω := by
  filter_upwards [eventually_neutral_anchor_family F hi hmod] with c hc
  intro d q a hq b D margin τ hτ hroom ε ω κ hε hω hκ
  obtain ⟨hcp,δ,cut,L,χ,Δ,H,hδ,_hδ',hδκ,hL,hχ,_hχd,hΔ,hΔt,hHc,hHe,
    hgeo,hgraph,hlimit,S,_hSd,hS,hgood⟩ := hc 1 (by norm_num) ε τ κ hε hτ hκ
  let g : PassageGeometryFamily F.V :=
    ⟨c,hcp,Δ,H,neutralJitter cut L 0,neutralJitterReal cut L 0,(fun _ => rfl),
      continuous_neutralJitter cut L 0,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit⟩
  obtain ⟨R,_hR,hRJ⟩ := periodic_real_bound (neutralJitterReal_smooth cut L 0).continuous
    (neutralJitterReal_periodic cut L 0)
  have hbudget := anchor_coefficient_budget (d := d) (D := D-margin) hq a hω R
  refine ⟨g,rfl,δ,cut,L,hδ,hδκ,hL,rfl,S,?_⟩
  filter_upwards [hgood,hbudget] with n hn hnω
  obtain ⟨hnp,haul,G,hGi,hGmod,hGV,hGm,hGA,_hGden,hgroup⟩ := hn
  have hloc (i : PassageOutputIndex (S n)) :
      d ((G.m i:ℝ)/n) = a i.1-q (((G.m i:ℝ)/(n:ℝ)):UnitAddCircle) ∧
      b+margin ≤ |(G.m i:ℝ)/n| ∧ |(G.m i:ℝ)/n| ≤ D-margin := by
    obtain ⟨x,hx,hx'⟩ := (hχ i.1).2.2.2.2 _
      (subset_tsupport _ ((hS n hnp i.1 _).mp i.2.property))
    rw [hGm]
    exact hroom i.1 x hx _ hx'
  refine ⟨hnp,G,hGi,hGmod,hGV,hGm,?_,fun i => (hloc i).2,?_⟩
  · intro i
    have hv := outputVector_eq_retained F G (neutralCircleCutoff cut) (fun i s _ => χ i s)
      H n hGm hGA i
    have hp : exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0)
        (neutralCircleCutoff cut) (fun s _ => χ i s) (F.m i) H (F.A i) (S n i) n =
        outputDensity G i := by
      have hh := hgroup i (fun _ => True)
      change _ = fun z => ∑ j : ↥(S n i), G.density ⟨i,j⟩ z
      simpa only [Finset.filter_true,ite_true] using hh
    have hh := haul i
    dsimp only at hh
    rw [← hv,hp] at hh
    exact ⟨hh.1,hh.2.1⟩
  · intro i y
    rw [hGV]
    exact hnω.2 (G.m i) i.1 (neutralJitterReal cut L 0 y) (hloc i).2.2 (hRJ y) (hloc i).1

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma colorVector_output {ι R : Type*} [Fintype ι] [DecidableEq R]
    {S : ι → Finset ℤ} (G : PassagePackets (PassageOutputIndex S))
    (c : ι → R) (r : R) (x : TripleTorus) :
    colorVector G (c ∘ Sigma.fst) r x =
      ∑ i, if c i = r then outputVector G i x else 0 := by
  unfold colorVector outputVector
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = r
  · simp only [Function.comp_apply,h,ite_true]
  · simp only [Function.comp_apply,h,ite_false,Finset.sum_const_zero]

lemma colorDensity_output {ι R : Type*} [Fintype ι] [DecidableEq R]
    {S : ι → Finset ℤ} (G : PassagePackets (PassageOutputIndex S))
    (c : ι → R) (r : R) (z : UnitAddCircle) :
    colorDensity G (c ∘ Sigma.fst) r z =
      ∑ i, if c i = r then outputDensity G i z else 0 := by
  unfold colorDensity outputDensity
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = r
  · simp only [Function.comp_apply,h,ite_true]
  · simp only [Function.comp_apply,h,ite_false,Finset.sum_const_zero]

structure ColoredAnchor {R : Type} (C : ColoredState R) (n : ℕ) where
  geometry : PassageGeometryFamily C.packets.V
  indices : C.Index → Finset ℤ
  n_pos : 0 < n
  final : PassagePackets (PassageOutputIndex indices)
  final_injective : Injective final.m
  final_spare : final.SpareIndependent
  final_speed : final.V = fun x => (1+geometry.J₀ x/n)/n
  final_index : ∀ i, final.m i = i.2.val

namespace ColoredAnchor
variable {R : Type} {C : ColoredState R} {n : ℕ} (s : ColoredAnchor C n)
def output : ColoredState R where
  Index := PassageOutputIndex s.indices
  finite := inferInstance
  packets := s.final
  injective := s.final_injective
  spare := s.final_spare
  color := C.color ∘ Sigma.fst
  scale := n
  scale_pos := by exact_mod_cast s.n_pos

def chart : Equiv.Perm TripleTorus := passageChart (s.geometry.H n)
lemma chart_continuous : Continuous s.chart := continuous_passageChart (s.geometry.Hcontinuous n)
lemma chart_preserves : MeasurePreserving s.chart tripleVolume tripleVolume :=
  measurePreserving_passageChart (s.geometry.Hcontinuous n).measurable
end ColoredAnchor

/-- The carrier precedes the block signal and every block accuracy requirement.
The output retains the literal actual geometry and finite amplitudes. -/
theorem eventually_colored_anchor {m : ℕ} (C : ColoredState (Fin m)) :
    ∀ᶠ c : ℕ in atTop,
      ∀ (d : ℝ → ℂ) (q : UnitAddCircle → ℂ) (tags : Fin m → ℂ), Continuous q →
      ∀ b D margin τ : ℝ, 0 < τ →
      (∀ i x, x ∈ C.packets.core i → ∀ s,
        |s-(C.packets.m i:ℝ)*((c:ℝ)+C.packets.V x)| < τ →
        d s = tags (C.color i)-q (s:UnitAddCircle) ∧ b+margin ≤ |s| ∧ |s| ≤ D-margin) →
      ∀ ε e ω κ : ℝ, 0 < ε → 0 < e → 0 < ω → 0 < κ →
      ∀ᶠ n : ℕ in atTop, ∃ s : ColoredAnchor C n,
        s.geometry.c = c ∧
        (∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ K : ℝ,
          0 < δ ∧ δ < κ ∧ 0 < K ∧ s.geometry.J₀ = neutralJitterReal cut K 0) ∧
        (∀ r, physicalError (C.vector r) (s.output.vector r ∘ s.chart) < ε) ∧
        colorL1Distance C.density s.output.density < e ∧
        s.output.InBand b D margin ∧
        s.output.Matches d (fun r z => tags r-q z) ω := by
  classical
  filter_upwards [eventually_anchor_state C.packets C.injective C.spare] with c hc
  intro d q tags hq b D margin τ hτ hroom ε e ω κ hε he hω hκ
  let K : ℝ := Fintype.card C.Index
  have hK : 0 ≤ K := Nat.cast_nonneg _
  let e' : ℝ := min (ε/(K^2+1)) (e/((m:ℝ)*K+1))
  have he' : 0 < e' := lt_min (div_pos hε (by positivity)) (div_pos he (by positivity))
  have hphysicalBudget : K^2*e' < ε := by
    have he1 : e' ≤ ε/(K^2+1) := min_le_left _ _
    have hp := (le_div_iff₀ (show 0 < K^2+1 by positivity)).1 he1
    nlinarith
  have hdensityBudget : (m:ℝ)*K*e' < e := by
    have he1 : e' ≤ e/((m:ℝ)*K+1) := min_le_right _ _
    have hp := (le_div_iff₀ (show 0 < (m:ℝ)*K+1 by positivity)).1 he1
    nlinarith
  obtain ⟨g,hgc,δ,cut,L,hδ,hδκ,hL,hgJ,S,hready⟩ := hc d q (tags ∘ C.color) hq
    b D margin τ hτ hroom e' ω κ he' hω hκ
  filter_upwards [hready] with n hn
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,herror,hband,hmatch⟩ := hn
  let s : ColoredAnchor C n := ⟨g,S n,hnp,G,hGi,hGmod,hGV,hGm⟩
  refine ⟨s,hgc,⟨δ,cut,L,hδ,hδκ,hL,hgJ⟩,?_,?_,hband,?_⟩
  · intro r
    have hh := colored_physical_bound
      (fun i => continuous_packet (C.packets.continuous_amplitude i))
      (fun i => (continuous_outputVector G i).comp (continuous_passageChart (g.Hcontinuous n)))
      C.color r he'.le (fun i => (herror i).1.le) hphysicalBudget
    change physicalError (C.vector r) _ < ε at hh
    have heq : (s.output.vector r ∘ s.chart) =
        (fun x => ∑ i, if C.color i = r then outputVector G i (passageChart (g.H n) x) else 0) := by
      funext x
      exact colorVector_output G C.color r _
    rw [heq]
    exact hh
  · have hcolor r : (∫ z, |C.density r z-s.output.density r z| ∂phaseHaar) ≤ K*e' := by
      have hh := colored_density_bound
        (fun i => continuous_outputDensity G i) C.packets.density_continuous C.color r
        (fun _ => 0) (γ := 0) (ω := 0) he'.le (fun i => by simpa using (herror i).2.le)
      simp only [zero_mul,zero_add] at hh
      have heq : (fun z => ∑ i, if C.color i = r then outputDensity G i z else 0) =
          s.output.density r := by
        funext z
        exact (colorDensity_output G C.color r z).symm
      change (∫ z, |(fun z => ∑ i, if C.color i = r then outputDensity G i z else 0) z-
        C.density r z| ∂phaseHaar) ≤ K*e' at hh
      rw [heq] at hh
      simpa only [abs_sub_comm] using hh
    apply (Finset.sum_le_sum (s := Finset.univ) (fun r _ => hcolor r)).trans_lt
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hdensityBudget
  · intro i y _hy
    exact (hmatch i y).le

end ThreeTorus
end
end

section

/-! A complete pre-anchor-to-endpoint actual block construction. This is the
connected geometric/analytic core; symmetry propagation and global smooth
neighborhood budgeting are separate remaining obligations for prediction. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma exists_block_length {ell delta : ℝ} (he : 0 < ell) (hd : 0 < delta)
    (hes : ell^2 ≤ delta/2) :
    ∃ n : ℕ, 0 < n ∧ delta/2 ≤ (n:ℝ)*ell^2 ∧ (n:ℝ)*ell^2 ≤ delta := by
  let n := ⌊delta/ell^2⌋₊
  have hsq : 0 < ell^2 := sq_pos_of_pos he
  have hu : (n:ℝ)*ell^2 ≤ delta :=
    (le_div_iff₀ hsq).mp (Nat.floor_le (by positivity))
  have hl : delta < ((n:ℝ)+1)*ell^2 :=
    (div_lt_iff₀ hsq).mp (Nat.lt_floor_add_one (delta/ell^2))
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := Nat.eq_zero_of_not_pos h
    simp only [hz,Nat.cast_zero,zero_add,one_mul] at hl
    linarith
  exact ⟨n,hn,by nlinarith,hu⟩

/-- All signal parameters and tolerances are fixed before the anchor. The
endpoint is a genuine actual state linked by its anchor and finite passage
path, and satisfies both prescribed source block inequalities. The input
reflection hypotheses are the ordinary packet reality conditions needed to
construct the real-symmetric band signal. -/
theorem actual_block_of_center {m : ℕ} (C : ColoredState (Fin m))
    (τ : C.Index → C.Index)
    (hmr : ∀ i, C.packets.m (τ i) = -C.packets.m i)
    (hcore : ∀ i, C.packets.core i ⊆ C.packets.core (τ i))
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htr : ∀ i, tags (C.color (τ i)) = conj (tags (C.color i)))
    {q A : UnitAddCircle → ℂ} (hq : Continuous q)
    (hqs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x:UnitAddCircle)))
    (hqr : ∀ z, q (-z) = conj (q z)) (hqB : ∀ z, ‖q z‖ ≤ 2)
    (hA : Continuous A) (k : ℕ) {delta nu ε κ : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1/100) (hnu : 0 < nu) (hε : 0 < ε) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal C.density z)*
      ‖blockTagMean C.density tags z-q z‖^2 ∂phaseHaar) ≤ delta) :
    ∃ n : ℕ, ∃ ell : ℝ, 0 < n ∧ 0 < ell ∧ 6*ell ≤ 1 ∧
      delta/2 ≤ (n:ℝ)*ell^2 ∧ (n:ℝ)*ell^2 ≤ delta ∧
      ∃ N : ℕ, ∃ s : ColoredAnchor C N,
        (∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ K : ℝ,
          0 < δ ∧ δ < κ ∧ 0 < K ∧ s.geometry.J₀ = neutralJitterReal cut K 0) ∧
        ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
          ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
            ColoredPath s.output L E α ∧
            (∀ r, physicalError (C.vector r) (E.vector r ∘ s.chart.trans α) < ε) ∧
            ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-300*delta^2-nu ≤
              ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
            ((∑ r, ∫ z, E.density r z*
              ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*tags r‖^2 ∂phaseHaar) ≤
              (∫ z, blockPreviousError C.density tags A k z ∂phaseHaar)+4/delta+nu) := by
  classical
  obtain ⟨c,hsep,hanchor⟩ := ((eventually_integral_speed_separation C.packets.m
    C.packets.periodic.lift C.packets.nonzero C.packets.speed_continuous).and
    (eventually_colored_anchor C)).exists
  let K : C.Index → Set ℝ := fun i =>
    (fun x => (C.packets.m i:ℝ)*((c:ℝ)+C.packets.V x)) '' C.packets.core i
  have hK i : IsCompact (K i) := (C.packets.core_compact i).image
    (continuous_const.mul (continuous_const.add C.packets.smooth_speed.continuous))
  have hK0 i : 0 ∉ K i := by
    rintro ⟨x,_hx,he⟩
    exact hsep.2.1 i (x:UnitAddCircle) he
  have hKd : Pairwise (Disjoint on K) := by
    intro i j hij
    change Disjoint (K i) (K j)
    rw [Set.disjoint_left]
    rintro z ⟨x,_hx,rfl⟩ ⟨y,_hy,he⟩
    exact hij (C.injective (hsep.2.2 i j (x:UnitAddCircle) (y:UnitAddCircle) he.symm))
  have hKr i x (hx : x ∈ K i) : -x ∈ K (τ i) := by
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨y,hcore i hy,?_⟩
    simp only [hmr,Int.cast_neg,neg_mul]
  obtain ⟨d,hds,hdcompact,hd0,hdr,hdlocal⟩ := exists_symmetric_anchor_band K hK hKd hK0
    τ hKr (tags ∘ C.color) htr hqs hqr
  obtain ⟨b,D,μ,t,hb,hbD,hμ,ht,hdsupport,hroom⟩ := anchor_uniform_room K hK hK0 hdcompact
    (fun i y => tags (C.color i)-q (y:UnitAddCircle)) hdlocal
  obtain ⟨P,γ₀,_hP,_hPD,hγ₀,hsignal⟩ := exists_concrete_colored_signal hb hbD hds hdcompact hdr hd0 hdsupport
  let γ : ℝ := min γ₀ (delta/2)/2
  have hγ : 0 < γ := half_pos (lt_min hγ₀ (half_pos hd))
  have hγ₀' : γ ≤ γ₀ := by
    have hh := min_le_left γ₀ (delta/2)
    dsimp [γ]
    linarith [lt_min hγ₀ (half_pos hd)]
  have hγd : γ ≤ delta/2 := by
    have hh := min_le_right γ₀ (delta/2)
    dsimp [γ]
    linarith [lt_min hγ₀ (half_pos hd)]
  let ell := refreshedStrength (signalPrimeProduct P) γ
  have hell : 0 < ell := refreshedStrength_pos _ hγ
  have helg : ell ≤ γ := refreshedStrength_le _ hγ.le
  have hells : 6*ell ≤ 1 := by linarith
  have helld : ell^2 ≤ delta/2 := by
    have hel1 : ell ≤ 1 := by linarith
    nlinarith
  obtain ⟨n,hn,hn0,hn1⟩ := exists_block_length hell hd helld
  obtain ⟨_hbound,hsig⟩ := hsignal γ hγ hγ₀'
  obtain ⟨e,ω,he,hω,hblock⟩ := hsig.block hds.continuous hdcompact hγ C.density_nonneg
    C.density_continuous tags htags hq hqB hA k hell hells hd hd1 hn0 hn1 hmass hcenter hnu
    (show 0 < ε/4 by positivity)
  have hanchorReady := hanchor d q tags hq b D μ t ht
    (fun i x hx s hs => hroom i _ ⟨x,hx,rfl⟩ s hs)
    (ε/4) e ω κ (by positivity) he hω hκ
  obtain ⟨N,s,_hsc,hjitter,hphysical,hclose,hband,hmatch⟩ := hanchorReady.exists
  obtain ⟨L,hL,E,α,hpath,hmovement,hsqrt,hpred⟩ := hblock s.output hclose.le μ hμ hband hmatch
  refine ⟨n,ell,hn,hell,hells,hn0,hn1,N,s,hjitter,L,hL,E,α,hpath,?_,hsqrt,hpred⟩
  intro r
  have hmove : physicalError (s.output.vector r ∘ s.chart)
      ((E.vector r ∘ α) ∘ s.chart) < ε/4 := by
    change physicalError (s.output.vector r ∘ passageChart (s.geometry.H N))
      ((E.vector r ∘ α) ∘ passageChart (s.geometry.H N)) < ε/4
    rw [physicalError_chart (s.geometry.Hcontinuous N).measurable]
    exact hmovement r
  have htriangle := physicalError_triangle (C.vector_continuous r)
    ((s.output.vector_continuous r).comp s.chart_continuous)
    (((E.vector_continuous r).comp hpath.continuous).comp s.chart_continuous)
  change physicalError (C.vector r) ((E.vector r ∘ α) ∘ s.chart) < ε
  have hfirst := hphysical r
  linarith

end ThreeTorus
end
end

end OAI
