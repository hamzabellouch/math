import OAI.Dynamics.ThreeTorus.BlockMoments

namespace OAI

/-! Block tests, diagonal predictions, centering, and stability of finite-color models. -/

section

/-! Actual Laurent tests for source 04, using the fixed pre-block densities,
centering function and previous estimator. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma PhaseLaurent.coordinate {n : ℕ} (i : Fin n) :
    PhaseLaurent (fun (_ : UnitAddCircle) y => fourier 1 (y i)) := by
  simpa only [UnitAddTorus.mFourier_single] using
    PhaseLaurent.character (Pi.single i 1)

lemma PhaseLaurent.blockFactor {n : ℕ} {a : UnitAddCircle → ℂ}
    (ha : CircleBounded a) (ell : ℝ) (i : Fin n) :
    PhaseLaurent (fun z y => (blockFactor ell (a z) (y i) : ℂ)) := by
  have hZ := PhaseLaurent.coordinate i
  have ha' := PhaseLaurent.coeff (n := n) ha
  have hl := PhaseLaurent.coeff (n := n) (CircleBounded.const (ell : ℂ))
  have h1 := PhaseLaurent.coeff (n := n) (CircleBounded.const 1)
  simpa only [blockFactor_cast,blockFactorC,fourier_neg] using
    (h1.add ((hl.mul ha').mul hZ.conj)).add ((hl.mul ha'.conj).mul hZ)

lemma PhaseLaurent.blockProduct {n : ℕ} {a : UnitAddCircle → ℂ}
    (ha : CircleBounded a) (ell : ℝ) :
    PhaseLaurent (fun z y => (blockProduct n ell (a z) y : ℂ)) := by
  simpa only [ThreeTorus.blockProduct,Complex.ofReal_prod] using
    PhaseLaurent.prod Finset.univ (fun i _ => PhaseLaurent.blockFactor ha ell i)

lemma CircleBounded.neg {f : UnitAddCircle → ℂ} (hf : CircleBounded f) :
    CircleBounded (fun z => -f z) := by
  simpa only [neg_one_mul] using (CircleBounded.const (-1)).mul hf

lemma CircleBounded.sub {f g : UnitAddCircle → ℂ} (hf : CircleBounded f)
    (hg : CircleBounded g) : CircleBounded (fun z => f z-g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma circleBounded_ofReal {f : UnitAddCircle → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ z, |f z| ≤ C) :
    CircleBounded (fun z => (f z : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.measurable.comp hf,C,hC,?_⟩
  intro z
  simpa only [Complex.norm_real,Real.norm_eq_abs] using hB z

def blockTotal {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (z : UnitAddCircle) : ℝ :=
  ∑ r, p r z

def blockWeights {m : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (r : Fin m) (z : UnitAddCircle) : ℝ := p r z / blockTotal p z

def blockTagMean {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (z : UnitAddCircle) : ℂ := ∑ r, (blockWeights p r z : ℂ)*b r

lemma blockTotal_nonneg {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (z : UnitAddCircle) : 0 ≤ blockTotal p z :=
  Finset.sum_nonneg (fun r _ => hp r z)

lemma continuous_blockTotal {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r, Continuous (p r)) : Continuous (blockTotal p) := by
  exact continuous_finsetSum _ (fun r _ => hp r)

lemma blockWeights_bounds {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (r : Fin m) (z : UnitAddCircle) :
    0 ≤ blockWeights p r z ∧ blockWeights p r z ≤ 1 := by
  have htot := blockTotal_nonneg hp z
  have hr : p r z ≤ blockTotal p z :=
    Finset.single_le_sum (fun r _ => hp r z) (Finset.mem_univ r)
  refine ⟨div_nonneg (hp r z) htot,?_⟩
  by_cases h : blockTotal p z = 0
  · simp [blockWeights,h]
  · exact (div_le_one (lt_of_le_of_ne htot (Ne.symm h))).2 hr

lemma sum_blockWeights {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    {z : UnitAddCircle} (h : blockTotal p z ≠ 0) : ∑ r, blockWeights p r z = 1 := by
  simp only [blockWeights,← Finset.sum_div]
  exact div_self h

lemma circleBounded_blockWeights {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (r : Fin m) :
    CircleBounded (fun z => (blockWeights p r z : ℂ)) := by
  apply circleBounded_ofReal ((hc r).measurable.div (continuous_blockTotal hc).measurable)
    (by norm_num : (0:ℝ) ≤ 1)
  intro z
  change |blockWeights p r z| ≤ 1
  rw [abs_of_nonneg (blockWeights_bounds hp r z).1]
  exact (blockWeights_bounds hp r z).2

/-- The exact polynomial lower bound, not the non-polynomial square root. -/
def blockSqrtTest {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (q : UnitAddCircle → ℂ) (n : ℕ) (ell : ℝ)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) : ℝ :=
  let R := blockMixture (fun r => blockWeights p r z) (fun r => b r-q z) n ell y
  Real.sqrt (blockTotal p z) * (1+(R-1)/2-(R-1)^2)

def blockPhaseEstimator (q : UnitAddCircle → ℂ) (n : ℕ) (ell : ℝ)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) : ℂ :=
  q z+((n:ℂ)*(ell:ℂ))⁻¹*∑ i, fourier 1 (y i)

def blockErrorTest {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (q A : UnitAddCircle → ℂ) (k n : ℕ) (ell : ℝ)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) : ℝ :=
  ∑ r, p r z * blockProduct n ell (b r-q z) y *
    ‖A z+blockPhaseEstimator q n ell z y-((k:ℂ)+1)*b r‖^2

lemma phaseLaurent_blockMixture {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    {q : UnitAddCircle → ℂ} (hq : CircleBounded q) (ell : ℝ) :
    PhaseLaurent (fun z y => (blockMixture (fun r => blockWeights p r z)
      (fun r => b r-q z) n ell y : ℂ)) := by
  have hr (r : Fin m) := (PhaseLaurent.coeff (n := n) (circleBounded_blockWeights hp hc r)).mul
    (PhaseLaurent.blockProduct ((CircleBounded.const (b r)).sub hq) ell)
  simpa only [blockMixture,Complex.ofReal_sum,Complex.ofReal_mul] using
    PhaseLaurent.sum Finset.univ (fun r _ => hr r)

lemma phaseLaurent_blockSqrtTest {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    {q : UnitAddCircle → ℂ} (hq : CircleBounded q) (ell : ℝ) :
    PhaseLaurent (fun z y => (blockSqrtTest p b q n ell z y : ℂ)) := by
  have hR := phaseLaurent_blockMixture (n := n) hp hc b hq ell
  have h1 := PhaseLaurent.coeff (n := n) (CircleBounded.const 1)
  have hp' : CircleBounded (fun z => (Real.sqrt (blockTotal p z) : ℂ)) :=
    CircleBounded.continuous (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (continuous_blockTotal hc)))
  have hR1 := hR.sub h1
  have hhalf := PhaseLaurent.coeff (n := n) (CircleBounded.const (1/2))
  convert (PhaseLaurent.coeff hp').mul ((h1.add (hR1.mul hhalf)).sub (hR1.mul hR1)) using 1
  ext z y
  simp only [blockSqrtTest,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_pow]
  ring

lemma phaseLaurent_blockPhaseEstimator {n : ℕ} {q : UnitAddCircle → ℂ}
    (hq : CircleBounded q) (ell : ℝ) : PhaseLaurent (blockPhaseEstimator q n ell) := by
  exact (PhaseLaurent.coeff hq).add
    ((PhaseLaurent.coeff (CircleBounded.const (((n:ℂ)*(ell:ℂ))⁻¹))).mul
      (PhaseLaurent.sum Finset.univ (fun i _ => PhaseLaurent.coordinate i)))

lemma phaseLaurent_blockErrorTest {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {q A : UnitAddCircle → ℂ}
    (hq : CircleBounded q) (hA : CircleBounded A) (k : ℕ) (ell : ℝ) :
    PhaseLaurent (fun z y => (blockErrorTest p b q A k n ell z y : ℂ)) := by
  have hr (r : Fin m) :=
    ((PhaseLaurent.coeff (n := n) (CircleBounded.continuous
      (Complex.continuous_ofReal.comp (hc r)))).mul
      (PhaseLaurent.blockProduct ((CircleBounded.const (b r)).sub hq) ell)).mul
      (((PhaseLaurent.coeff hA).add (phaseLaurent_blockPhaseEstimator hq ell)).sub
        (PhaseLaurent.coeff (CircleBounded.const (((k:ℂ)+1)*b r)))).norm_sq
  simpa only [blockErrorTest,Complex.ofReal_sum,Complex.ofReal_mul,Function.comp_apply] using
    PhaseLaurent.sum Finset.univ (fun r _ => hr r)

end ThreeTorus
end
end

section

/-! Transfer of the two actual block tests to a common temporal diagonal. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma CircleBounded.sum {ι : Type*} (S : Finset ι)
    {f : ι → UnitAddCircle → ℂ} (hf : ∀ i ∈ S, CircleBounded (f i)) :
    CircleBounded (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using CircleBounded.const 0
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma PhaseLaurent.diagonal_bounded {n : ℕ}
    {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) (L : Fin n → ℤ) :
    CircleBounded (fun z => F z (fun i => L i • z)) := by
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  let _ := fi
  simp only [hF,phaseTest]
  apply CircleBounded.sum
  intro i _
  apply (hc i).mul (CircleBounded.continuous ?_)
  exact (UnitAddTorus.mFourier (ν i)).continuous.comp (by fun_prop)

lemma integral_phaseTest_pointwise {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → UnitAddCircle → ℂ) (ν : ι → Fin n → ℤ) (z : UnitAddCircle) :
    (∫ y, phaseTest c ν z y ∂phaseProduct n) =
      ∑ i, if ν i = 0 then c i z else 0 := by
  classical
  have hm (i : ι) : Integrable (UnitAddTorus.mFourier (ν i)) (phaseProduct n) :=
    (UnitAddTorus.mFourier (ν i)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [phaseTest]
  rw [integral_finsetSum _ (fun i _ => (hm i).const_mul (c i z))]
  simp_rw [integral_const_mul]
  have hν (i : ι) : (∫ y, UnitAddTorus.mFourier (ν i) y ∂phaseProduct n) =
      if ν i = 0 then 1 else 0 := by
    simpa only using! phase_integral_mFourier (ν i)
  simp_rw [hν]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma PhaseLaurent.independent_bounded {n : ℕ}
    {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℂ}
    (hF : PhaseLaurent F) :
    CircleBounded (fun z => ∫ y, F z y ∂phaseProduct n) := by
  classical
  obtain ⟨ι,fi,c,ν,hc,hF⟩ := hF
  let _ := fi
  simp only [hF,integral_phaseTest_pointwise]
  apply CircleBounded.sum
  intro i _
  split_ifs
  · exact hc i
  · exact CircleBounded.const 0

lemma PhaseLaurent.diagonal_integrable_real {n : ℕ}
    {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℝ}
    (hF : PhaseLaurent (fun z y => (F z y : ℂ))) (L : Fin n → ℤ) :
    Integrable (fun z => F z (fun i => L i • z)) phaseHaar := by
  simpa only [RCLike.ofReal_re] using! (hF.diagonal_bounded L).integrable.re

lemma PhaseLaurent.independent_integrable_real {n : ℕ}
    {F : UnitAddCircle → (Fin n → UnitAddCircle) → ℝ}
    (hF : PhaseLaurent (fun z y => (F z y : ℂ))) :
    Integrable (fun z => ∫ y, F z y ∂phaseProduct n) phaseHaar := by
  simpa only [integral_complex_ofReal,RCLike.ofReal_re] using! hF.independent_bounded.integrable.re

lemma blockMixture_polynomial_integral {m n : ℕ} (t : Fin m → ℝ) (a : Fin m → ℂ)
    (ell : ℝ) (ht : ∑ r, t r = 1) :
    (∫ y, 1+(blockMixture t a n ell y-1)/2-
      (blockMixture t a n ell y-1)^2 ∂phaseProduct n) =
      1-(∫ y, (blockMixture t a n ell y-1)^2 ∂phaseProduct n) := by
  have hc := continuous_blockMixture t a n ell
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := phaseProduct n)
  have hiv := ((hc.sub (continuous_const (y := (1:ℝ)))).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := phaseProduct n)
  rw [integral_sub (f := fun y => 1+(blockMixture t a n ell y-1)/2)
    (g := fun y => (blockMixture t a n ell y-1)^2) ((integrable_const (1:ℝ)).add
    ((hi.sub (integrable_const (1:ℝ))).div_const 2)) hiv,
    integral_add (f := fun _ => (1:ℝ)) (g := fun y => (blockMixture t a n ell y-1)/2)
    (integrable_const (1:ℝ)) ((hi.sub (integrable_const (1:ℝ))).div_const 2),
    integral_div,integral_sub (f := blockMixture t a n ell) (g := fun _ => (1:ℝ))
    hi (integrable_const (1:ℝ)),integral_blockMixture,ht]
  simp

lemma blockTagMean_centered {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (b : Fin m → ℂ) (q : UnitAddCircle → ℂ) {z : UnitAddCircle}
    (h : blockTotal p z ≠ 0) :
    (∑ r, (blockWeights p r z : ℂ)*(b r-q z)) = blockTagMean p b z-q z := by
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,blockTagMean]
  have hs : (∑ r, (blockWeights p r z : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum,sum_blockWeights h]
    rfl
  rw [hs,one_mul]

lemma blockSqrtTest_independent_bound {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (b : Fin m → ℂ) (q : UnitAddCircle → ℂ)
    (ha : ∀ r z, ‖b r-q z‖ ≤ 3) {ell delta : ℝ}
    (hd : 0 ≤ delta) (hn : (n:ℝ)*ell^2 ≤ delta) (z : UnitAddCircle) :
    Real.sqrt (blockTotal p z) * (1-2*delta*‖blockTagMean p b z-q z‖^2-
      162*Real.exp (18*delta)*delta^2) ≤
      ∫ y, blockSqrtTest p b q n ell z y ∂phaseProduct n := by
  simp only [blockSqrtTest]
  rw [integral_const_mul]
  by_cases hz : blockTotal p z = 0
  · simp [hz]
  rw [blockMixture_polynomial_integral _ _ ell (sum_blockWeights hz)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have h := blockMixture_variance_bound (n := n) (fun r => blockWeights p r z)
    (fun r => b r-q z) (fun r => (blockWeights_bounds hp r z).1)
    (sum_blockWeights hz) (fun r => ha r z) hd hn
  rw [blockTagMean_centered b q hz] at h
  linarith

lemma blockPhaseEstimator_noise {n : ℕ} (q : UnitAddCircle → ℂ) (ell : ℝ)
    (b : ℂ) (hn : n ≠ 0) (he : ell ≠ 0) (z : UnitAddCircle)
    (y : Fin n → UnitAddCircle) :
    blockPhaseEstimator q n ell z y = b+blockEstimatorNoise n ell (b-q z) y := by
  have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  have he' : (ell:ℂ) ≠ 0 := by exact_mod_cast he
  simp only [blockPhaseEstimator,blockEstimatorNoise,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  ring

lemma blockErrorTest_independent_exact {m n : ℕ} (p : Fin m → UnitAddCircle → ℝ)
    (b : Fin m → ℂ) (q A : UnitAddCircle → ℂ) (k : ℕ) (ell : ℝ)
    (hn : n ≠ 0) (he : ell ≠ 0) (z : UnitAddCircle) :
    (∫ y, blockErrorTest p b q A k n ell z y ∂phaseProduct n) =
      ∑ r, p r z * (‖A z-(k:ℂ)*b r‖^2+
        (1-ell^2*‖b r-q z‖^2)/((n:ℝ)*ell^2)) := by
  simp only [blockErrorTest]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    simp_rw [mul_assoc,integral_const_mul,blockPhaseEstimator_noise q ell (b r) hn he]
    have heq (y : Fin n → UnitAddCircle) :
        A z+(b r+blockEstimatorNoise n ell (b r-q z) y)-((k:ℂ)+1)*b r =
          (A z-(k:ℂ)*b r)+blockEstimatorNoise n ell (b r-q z) y := by ring
    simp_rw [heq]
    rw [block_estimator_previous_error ell (b r-q z) (A z-(k:ℂ)*b r) hn he]
  · intro r _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply Continuous.mul
    · exact continuous_const.mul (continuous_blockProduct n ell (b r-q z))
    · apply Continuous.pow
      apply Continuous.norm
      unfold blockPhaseEstimator
      fun_prop

lemma CircleBounded.norm_sq {f : UnitAddCircle → ℂ} (hf : CircleBounded f) :
    CircleBounded (fun z => (‖f z‖^2:ℝ)) := by
  simpa only [Complex.mul_conj',Complex.ofReal_pow] using hf.mul hf.conj

lemma integrable_real_of_circleBounded {f : UnitAddCircle → ℝ}
    (hf : CircleBounded (fun z => (f z : ℂ))) : Integrable f phaseHaar := by
  simpa only [RCLike.ofReal_re] using! hf.integrable.re

lemma circleBounded_blockTagMean {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) :
    CircleBounded (blockTagMean p b) :=
  CircleBounded.sum Finset.univ (fun r _ =>
    (circleBounded_blockWeights hp hc r).mul (CircleBounded.const (b r)))

lemma integral_sqrt_le_sqrt_two {p : UnitAddCircle → ℝ}
    (hp : Continuous p) (hp0 : ∀ z, 0 ≤ p z) (hmass : (∫ z, p z ∂phaseHaar) ≤ 2) :
    (∫ z, Real.sqrt (p z) ∂phaseHaar) ≤ Real.sqrt 2 := by
  let sIntegral := ∫ z, Real.sqrt (p z) ∂phaseHaar
  have hs := Real.continuous_sqrt.comp hp
  have hi := hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := phaseHaar)
  have his := hs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := phaseHaar)
  have hnon := integral_nonneg (μ := phaseHaar)
    (f := fun z : UnitAddCircle => (Real.sqrt (p z)-sIntegral)^2)
    (fun z => sq_nonneg (Real.sqrt (p z)-sIntegral))
  have heq (z : UnitAddCircle) : (Real.sqrt (p z)-sIntegral)^2 = p z-2*sIntegral*Real.sqrt (p z)+sIntegral^2 := by
    nlinarith [Real.sq_sqrt (hp0 z)]
  simp_rw [heq] at hnon
  erw [integral_add (hi.sub (his.const_mul (2*sIntegral))) (integrable_const _),
    integral_sub hi (his.const_mul (2*sIntegral)),integral_const_mul] at hnon
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hnon
  have hI : 0 ≤ sIntegral := integral_nonneg (fun z => Real.sqrt_nonneg (p z))
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp2 := Real.sqrt_nonneg (2:ℝ)
  change sIntegral ≤ Real.sqrt 2
  change 0 ≤ (∫ z, p z ∂phaseHaar)-2*sIntegral*sIntegral+sIntegral^2 at hnon
  nlinarith

lemma blockSqrtTest_integral_bound {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    {q : UnitAddCircle → ℂ} (hq : CircleBounded q) (ha : ∀ r z, ‖b r-q z‖ ≤ 3)
    {ell delta : ℝ} (hd : 0 ≤ delta) (hd1 : delta ≤ 1/100)
    (hn : (n:ℝ)*ell^2 ≤ delta) (hmass : (∫ z, blockTotal p z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p b z-q z‖^2 ∂phaseHaar) ≤ delta) :
    (∫ z, Real.sqrt (blockTotal p z) ∂phaseHaar)-300*delta^2 ≤
      ∫ z, ∫ y, blockSqrtTest p b q n ell z y ∂phaseProduct n ∂phaseHaar := by
  let C := 162*Real.exp (18*delta)*delta^2
  have hs : CircleBounded (fun z => (Real.sqrt (blockTotal p z):ℂ)) :=
    CircleBounded.continuous (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (continuous_blockTotal hc)))
  have he : CircleBounded (fun z =>
      ((Real.sqrt (blockTotal p z)*‖blockTagMean p b z-q z‖^2:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_mul] using
      hs.mul ((circleBounded_blockTagMean hp hc b).sub hq).norm_sq
  have his := integrable_real_of_circleBounded hs
  have hie := integrable_real_of_circleBounded he
  have hilower := (his.sub (hie.const_mul (2*delta))).sub (his.const_mul C)
  have hiP := (phaseLaurent_blockSqrtTest (n := n) hp hc b hq ell).independent_integrable_real
  have hbound := integral_mono hilower hiP (fun z => ?_)
  · simp only [Pi.sub_apply] at hbound
    erw [integral_sub (his.sub (hie.const_mul (2*delta))) (his.const_mul C),
      integral_sub his (hie.const_mul (2*delta)),integral_const_mul,integral_const_mul] at hbound
    have hfirst := mul_le_mul_of_nonneg_left hcenter (by positivity : 0 ≤ 2*delta)
    have hmass' := integral_sqrt_le_sqrt_two (continuous_blockTotal hc)
      (blockTotal_nonneg hp) hmass
    have hsecond := mul_le_mul_of_nonneg_left hmass' (by dsimp [C]; positivity : 0 ≤ C)
    have hconstant := block_hellinger_numerical_constant hd hd1
    dsimp [C] at hbound hsecond
    nlinarith
  · dsimp only [Pi.sub_apply]
    dsimp [C]
    nlinarith only [blockSqrtTest_independent_bound hp b q ha hd hn z]

def blockPreviousError {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (A : UnitAddCircle → ℂ) (k : ℕ) (z : UnitAddCircle) : ℝ :=
  ∑ r, p r z*‖A z-(k:ℂ)*b r‖^2

lemma integrable_blockPreviousError {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {A : UnitAddCircle → ℂ}
    (hA : CircleBounded A) (k : ℕ) : Integrable (blockPreviousError p b A k) phaseHaar := by
  apply integrable_real_of_circleBounded
  have hr (r : Fin m) := (CircleBounded.continuous (Complex.continuous_ofReal.comp (hc r))).mul
    (hA.sub (CircleBounded.const ((k:ℂ)*b r))).norm_sq
  simpa only [blockPreviousError,Complex.ofReal_sum,Complex.ofReal_mul,Function.comp_apply] using
    CircleBounded.sum Finset.univ (fun r _ => hr r)

lemma blockErrorTest_integral_bound {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    {q A : UnitAddCircle → ℂ} (hq : CircleBounded q) (hA : CircleBounded A) (k : ℕ)
    {ell delta : ℝ} (hd : 0 < delta) (hn : delta/2 ≤ (n:ℝ)*ell^2)
    (hmass : (∫ z, blockTotal p z ∂phaseHaar) ≤ 2) :
    (∫ z, ∫ y, blockErrorTest p b q A k n ell z y ∂phaseProduct n ∂phaseHaar) ≤
      (∫ z, blockPreviousError p b A k z ∂phaseHaar)+4/delta := by
  have hn0 : n ≠ 0 := by intro h; simp only [h,Nat.cast_zero,zero_mul] at hn; linarith
  have he0 : ell ≠ 0 := by intro h; simp only [h,zero_pow (by norm_num : 2 ≠ 0),mul_zero] at hn; linarith
  have bound (z : UnitAddCircle) :
      (∫ y, blockErrorTest p b q A k n ell z y ∂phaseProduct n) ≤
        blockPreviousError p b A k z+blockTotal p z*(2/delta) := by
    rw [blockErrorTest_independent_exact p b q A k ell hn0 he0 z]
    simp only [blockPreviousError,blockTotal,Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    have h := mul_le_mul_of_nonneg_left
      (block_estimator_variance_bound (b r-q z) hd hn) (hp r z)
    nlinarith
  have hiP := (phaseLaurent_blockErrorTest (n := n) hc b hq hA k ell).independent_integrable_real
  have hiE := integrable_blockPreviousError hc b hA k
  have hit := (continuous_blockTotal hc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := phaseHaar)
  have h := integral_mono hiP (hiE.add (hit.mul_const (2/delta))) bound
  simp only [Pi.add_apply] at h
  erw [integral_add hiE (hit.mul_const (2/delta)),integral_mul_const] at h
  have hm := mul_le_mul_of_nonneg_right hmass (by positivity : 0 ≤ 2/delta)
  have heq : (2:ℝ)*(2/delta) = 4/delta := by ring
  linarith

end ThreeTorus
end
end

section

/-! Exact finite-frequency model step for source 04.  Both phase tests are
selected simultaneously from the actual pre-block data; no probability law
for the whole diagonal is assumed. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def blockModelDensity {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (q : UnitAddCircle → ℂ) (n : ℕ) (ell : ℝ)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) : ℝ :=
  ∑ r, p r z*blockProduct n ell (b r-q z) y

lemma blockTotal_mul_blockWeights {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (r : Fin m) (z : UnitAddCircle) :
    blockTotal p z*blockWeights p r z = p r z := by
  have hr : p r z ≤ blockTotal p z :=
    Finset.single_le_sum (fun r _ => hp r z) (Finset.mem_univ r)
  by_cases ht : blockTotal p z = 0
  · have hz : p r z = 0 := le_antisymm (ht ▸ hr) (hp r z)
    simp [ht,hz]
  · dsimp [blockWeights]
    field_simp

lemma blockModelDensity_eq {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (b : Fin m → ℂ) (q : UnitAddCircle → ℂ)
    (ell : ℝ) (z : UnitAddCircle) (y : Fin n → UnitAddCircle) :
    blockModelDensity p b q n ell z y = blockTotal p z *
      blockMixture (fun r => blockWeights p r z) (fun r => b r-q z) n ell y := by
  simp only [blockModelDensity,blockMixture,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [← mul_assoc,blockTotal_mul_blockWeights hp r z]

lemma blockModelDensity_nonneg {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (b : Fin m → ℂ) (q : UnitAddCircle → ℂ)
    (ha : ∀ r z, ‖b r-q z‖ ≤ 3) {ell : ℝ} (hell : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) :
    0 ≤ blockModelDensity p b q n ell z y := by
  apply Finset.sum_nonneg
  intro r _
  apply mul_nonneg (hp r z)
  exact blockProduct_nonneg n hell (b r-q z) (by nlinarith [ha r z]) y

lemma blockSqrtTest_le_model_sqrt {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (b : Fin m → ℂ) (q : UnitAddCircle → ℂ)
    (ha : ∀ r z, ‖b r-q z‖ ≤ 3) {ell : ℝ} (hell : 0 ≤ ell) (hs : 6*ell ≤ 1)
    (z : UnitAddCircle) (y : Fin n → UnitAddCircle) :
    blockSqrtTest p b q n ell z y ≤ Real.sqrt (blockModelDensity p b q n ell z y) := by
  rw [blockModelDensity_eq hp b q ell z y,Real.sqrt_mul (blockTotal_nonneg hp z)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply square_root_polynomial_bound
  exact blockMixture_nonneg (fun r => blockWeights p r z) (fun r => b r-q z)
    hell (fun r => (blockWeights_bounds hp r z).1) (fun r => by nlinarith [ha r z]) y

lemma continuous_blockModel_diagonal {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) {q : UnitAddCircle → ℂ}
    (hq : Continuous q) (ell : ℝ) (L : Fin n → ℤ) :
    Continuous (fun z => blockModelDensity p b q n ell z (fun i => L i • z)) := by
  unfold blockModelDensity blockProduct blockFactor
  fun_prop

/-- The exact Hellinger and previous-estimator estimates of source 04 on
one common actual diagonal, with arbitrary successive geometric lower bounds.
This is the analytic model step, not the geometric prediction proposition. -/
theorem block_model_diagonal {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    (hb : ∀ r, ‖b r‖ ≤ 1) {q A : UnitAddCircle → ℂ} (hq : Continuous q)
    (hqB : ∀ z, ‖q z‖ ≤ 2) (hA : CircleBounded A) (k : ℕ)
    {ell delta eta : ℝ} (hell : 0 < ell) (hs : 6*ell ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1/100)
    (hn0 : delta/2 ≤ (n:ℝ)*ell^2) (hn1 : (n:ℝ)*ell^2 ≤ delta)
    (hmass : (∫ z, blockTotal p z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p b z-q z‖^2 ∂phaseHaar) ≤ delta)
    (heta : 0 < eta) (B : (j : ℕ) → (Fin j → ℤ) → ℤ) :
    ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
      (∀ j : Fin n, B j (fun i => L ⟨i.val, i.isLt.trans j.isLt⟩) < L j) ∧
      ((∫ z, Real.sqrt (blockTotal p z) ∂phaseHaar)-300*delta^2-eta ≤
        ∫ z, Real.sqrt (blockModelDensity p b q n ell z (fun i => L i • z)) ∂phaseHaar) ∧
      ((∫ z, blockErrorTest p b q A k n ell z (fun i => L i • z) ∂phaseHaar) ≤
        (∫ z, blockPreviousError p b A k z ∂phaseHaar)+4/delta+eta) := by
  have hqb := CircleBounded.continuous hq
  have ha (r : Fin m) (z : UnitAddCircle) : ‖b r-q z‖ ≤ 3 := by
    calc
      _ ≤ ‖b r‖+‖q z‖ := norm_sub_le _ _
      _ ≤ 1+2 := add_le_add (hb r) (hqB z)
      _ = 3 := by norm_num
  let F : Bool → UnitAddCircle → (Fin n → UnitAddCircle) → ℂ := fun t z y =>
    if t then (blockErrorTest p b q A k n ell z y : ℂ) else (blockSqrtTest p b q n ell z y : ℂ)
  have hF (t : Bool) : PhaseLaurent (F t) := by
    cases t with
    | false => exact phaseLaurent_blockSqrtTest hp hc b hqb ell
    | true => exact phaseLaurent_blockErrorTest hc b hqb hA k ell
  obtain ⟨L,hL,hB,htest⟩ := PhaseLaurent.finite_tests hF heta B
  have hS : |(∫ z, blockSqrtTest p b q n ell z (fun i => L i • z) ∂phaseHaar)-
      (∫ z, ∫ y, blockSqrtTest p b q n ell z y ∂phaseProduct n ∂phaseHaar)| < eta := by
    have h := htest false
    change ‖(∫ z, (blockSqrtTest p b q n ell z (fun i => L i • z):ℂ) ∂phaseHaar)-
      (∫ z, ∫ y, (blockSqrtTest p b q n ell z y:ℂ) ∂phaseProduct n ∂phaseHaar)‖ < eta at h
    simpa only [integral_complex_ofReal,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h
  have hE : |(∫ z, blockErrorTest p b q A k n ell z (fun i => L i • z) ∂phaseHaar)-
      (∫ z, ∫ y, blockErrorTest p b q A k n ell z y ∂phaseProduct n ∂phaseHaar)| < eta := by
    have h := htest true
    change ‖(∫ z, (blockErrorTest p b q A k n ell z (fun i => L i • z):ℂ) ∂phaseHaar)-
      (∫ z, ∫ y, (blockErrorTest p b q A k n ell z y:ℂ) ∂phaseProduct n ∂phaseHaar)‖ < eta at h
    simpa only [integral_complex_ofReal,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h
  refine ⟨L,hL,hB,?_,?_⟩
  · have his := (phaseLaurent_blockSqrtTest (n := n) hp hc b hqb ell).diagonal_integrable_real L
    have him := (Real.continuous_sqrt.comp (continuous_blockModel_diagonal hc b hq ell L)).integrable_of_hasCompactSupport
       (HasCompactSupport.of_compactSpace _) (μ := phaseHaar)
    have hm := integral_mono his him (fun z => blockSqrtTest_le_model_sqrt hp b q ha hell.le hs z _)
    dsimp only [Function.comp_def] at hm
    have hpS := blockSqrtTest_integral_bound (n := n) hp hc b hqb ha hd.le hd1 hn1 hmass hcenter
    have hlow := (abs_lt.mp hS).1
    linarith
  · have hpE := blockErrorTest_integral_bound (n := n) hp hc b hqb hA k hd hn0 hmass
    have hhigh := (abs_lt.mp hE).2
    linarith

end ThreeTorus
end
end

section

/-! Explicit smooth centering of the actual pre-block tag field.  Positive
regularization avoids any regularity assumption on the quotient at its zero set. -/
noncomputable section
open MeasureTheory Complex Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def blockNumerator {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (z : UnitAddCircle) : ℂ := ∑ r, (p r z:ℂ)*b r

def blockCenter {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (epsilon : ℝ) (z : UnitAddCircle) : ℂ :=
  blockNumerator p b z / (blockTotal p z+epsilon:ℝ)

lemma blockNumerator_norm {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    (z : UnitAddCircle) : ‖blockNumerator p b z‖ ≤ blockTotal p z := by
  calc
    _ ≤ ∑ r, ‖(p r z:ℂ)*b r‖ := norm_sum_le _ _
    _ ≤ ∑ r, p r z := Finset.sum_le_sum (fun r _ => by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp r z)]
      simpa using mul_le_mul_of_nonneg_left (hb r) (hp r z))
    _ = _ := rfl

lemma blockTagMean_eq {m : ℕ} (p : Fin m → UnitAddCircle → ℝ) (b : Fin m → ℂ)
    (z : UnitAddCircle) : blockTagMean p b z = blockNumerator p b z/(blockTotal p z:ℂ) := by
  unfold blockTagMean blockWeights blockNumerator
  simp_rw [Complex.ofReal_div,div_mul_eq_mul_div]
  rw [Finset.sum_div]

lemma blockTagMean_norm {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    (z : UnitAddCircle) : ‖blockTagMean p b z‖ ≤ 1 := by
  rw [blockTagMean_eq,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (blockTotal_nonneg hp z)]
  by_cases ht : blockTotal p z = 0
  · simp [ht]
  · exact (div_le_one₀ (lt_of_le_of_ne (blockTotal_nonneg hp z) (Ne.symm ht))).2
      (blockNumerator_norm hp hb z)

lemma blockCenter_norm {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    {epsilon : ℝ} (he : 0 < epsilon) (z : UnitAddCircle) :
    ‖blockCenter p b epsilon z‖ ≤ 1 := by
  have ht := blockTotal_nonneg hp z
  have hte : 0 < blockTotal p z+epsilon := by linarith
  rw [blockCenter,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hte.le]
  apply (div_le_one₀ hte).2
  exact (blockNumerator_norm hp hb z).trans (by linarith)

lemma blockCenter_error_eq {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (b : Fin m → ℂ) {epsilon : ℝ} (he : 0 < epsilon)
    (z : UnitAddCircle) : blockTagMean p b z-blockCenter p b epsilon z =
      blockTagMean p b z*(epsilon/(blockTotal p z+epsilon):ℝ) := by
  have ht := blockTotal_nonneg hp z
  have hte : (blockTotal p z+epsilon:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < blockTotal p z+epsilon by linarith))
  by_cases hz : blockTotal p z = 0
  · have hnum : blockNumerator p b z = 0 := by
      unfold blockNumerator
      apply Finset.sum_eq_zero
      intro r _
      have hr := Finset.single_le_sum (fun r _ => hp r z) (Finset.mem_univ r)
      change p r z ≤ blockTotal p z at hr
      have hpz : p r z = 0 := le_antisymm (hz ▸ hr) (hp r z)
      simp [hpz]
    simp [blockTagMean_eq,blockCenter,hnum]
  · have hz' : (blockTotal p z:ℂ) ≠ 0 := by exact_mod_cast hz
    rw [blockTagMean_eq,blockCenter]
    push_cast
    field_simp
    ring

lemma blockCenter_error_bound {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1)
    {epsilon : ℝ} (he : 0 < epsilon) (z : UnitAddCircle) :
    ‖blockTagMean p b z-blockCenter p b epsilon z‖ ≤ epsilon/(blockTotal p z+epsilon) := by
  rw [blockCenter_error_eq hp b he z,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg he.le (add_nonneg (blockTotal_nonneg hp z) he.le))]
  simpa using mul_le_mul_of_nonneg_right (blockTagMean_norm hp hb z)
    (div_nonneg he.le (add_nonneg (blockTotal_nonneg hp z) he.le))

lemma sqrt_weighted_regularization_bound {t epsilon : ℝ} (ht : 0 ≤ t) (he : 0 < epsilon)
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ epsilon/(t+epsilon)) :
    Real.sqrt t*x^2 ≤ Real.sqrt epsilon/2 := by
  have hte : 0 < t+epsilon := by linarith
  have hratio : epsilon/(t+epsilon) ≤ 1 := (div_le_one₀ hte).2 (by linarith)
  have hx1 : x ≤ 1 := hx.trans hratio
  have hx2 : x^2 ≤ x := by nlinarith
  have hs := Real.sqrt_nonneg t
  have he' := Real.sqrt_nonneg epsilon
  have hs2 := Real.sq_sqrt ht
  have he2 := Real.sq_sqrt he.le
  have hprod : Real.sqrt t*epsilon ≤ Real.sqrt epsilon/2*(t+epsilon) := by
    nlinarith [mul_nonneg he' (sq_nonneg (Real.sqrt t-Real.sqrt epsilon))]
  calc
    _ ≤ Real.sqrt t*x := mul_le_mul_of_nonneg_left hx2 hs
    _ ≤ Real.sqrt t*(epsilon/(t+epsilon)) := mul_le_mul_of_nonneg_left hx hs
    _ = (Real.sqrt t*epsilon)/(t+epsilon) := by ring
    _ ≤ Real.sqrt epsilon/2 := (div_le_iff₀ hte).2 hprod

lemma continuous_blockNumerator {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ) : Continuous (blockNumerator p b) := by
  unfold blockNumerator
  fun_prop

lemma continuous_blockCenter {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (b : Fin m → ℂ)
    {epsilon : ℝ} (he : 0 < epsilon) : Continuous (blockCenter p b epsilon) := by
  apply (continuous_blockNumerator hc b).div
    (Complex.continuous_ofReal.comp ((continuous_blockTotal hc).add continuous_const))
  intro z
  dsimp only [Function.comp_def,Pi.add_apply]
  exact_mod_cast (ne_of_gt (show 0 < blockTotal p z+epsilon from add_pos_of_nonneg_of_pos
    (blockTotal_nonneg hp z) he))

lemma blockCenter_integral_error {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) {b : Fin m → ℂ}
    (hb : ∀ r, ‖b r‖ ≤ 1) {epsilon : ℝ} (he : 0 < epsilon) :
    (∫ z, Real.sqrt (blockTotal p z)*
      ‖blockTagMean p b z-blockCenter p b epsilon z‖^2 ∂phaseHaar) ≤ Real.sqrt epsilon/2 := by
  have hs : CircleBounded (fun z => (Real.sqrt (blockTotal p z):ℂ)) :=
    CircleBounded.continuous (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp (continuous_blockTotal hc)))
  have hec := ((circleBounded_blockTagMean hp hc b).sub
    (CircleBounded.continuous (continuous_blockCenter hp hc b he))).norm_sq
  have hi : Integrable (fun z => Real.sqrt (blockTotal p z)*
      ‖blockTagMean p b z-blockCenter p b epsilon z‖^2) phaseHaar := by
    apply integrable_real_of_circleBounded
    simpa only [Complex.ofReal_mul] using hs.mul hec
  have hi' := integral_mono hi (integrable_const (Real.sqrt epsilon/2))
    (fun z => sqrt_weighted_regularization_bound (blockTotal_nonneg hp z) he
        (norm_nonneg _) (blockCenter_error_bound hp hb he z))
  simpa only [integral_const,probReal_univ,one_smul] using hi'

lemma exists_block_center {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) {b : Fin m → ℂ}
    (hb : ∀ r, ‖b r‖ ≤ 1) {delta : ℝ} (hd : 0 < delta) :
    ∃ q : UnitAddCircle → ℂ, Continuous q ∧ (∀ z, ‖q z‖ ≤ 1) ∧
      (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p b z-q z‖^2 ∂phaseHaar) < delta := by
  have hd2 : 0 < delta^2 := sq_pos_of_pos hd
  refine ⟨blockCenter p b (delta^2),continuous_blockCenter hp hc b hd2,
    blockCenter_norm hp hb hd2, ?_⟩
  have h := blockCenter_integral_error hp hc hb hd2
  rw [Real.sqrt_sq hd.le] at h
  linarith

/-- The regularized center is genuinely smooth as a circle function whenever
its finite color densities are smooth; no regularity of beta is needed at zeros. -/
lemma contDiff_blockCenter_lift {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z)
    (hs : ∀ r, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p r (x : UnitAddCircle)))
    (b : Fin m → ℂ) {epsilon : ℝ} (he : 0 < epsilon) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => blockCenter p b epsilon (x : UnitAddCircle)) := by
  have ht : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => blockTotal p (x : UnitAddCircle)) := by
    unfold blockTotal
    exact ContDiff.sum (fun r _ => hs r)
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => blockNumerator p b (x : UnitAddCircle)) := by
    unfold blockNumerator
    exact ContDiff.sum (fun r _ => (Complex.ofRealCLM.contDiff.comp (hs r)).mul contDiff_const)
  have hf := (ht.add contDiff_const).inv (fun x =>
    ne_of_gt (add_pos_of_nonneg_of_pos (blockTotal_nonneg hp (x : UnitAddCircle)) he))
  convert hf.smul hn using 1
  ext x
  simp [blockCenter,div_eq_mul_inv,mul_comm]

lemma blockTotal_reflection {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (e : Equiv.Perm (Fin m)) (hp : ∀ r z, p (e r) (-z) = p r z)
    (z : UnitAddCircle) : blockTotal p (-z) = blockTotal p z := by
  unfold blockTotal
  rw [← Equiv.sum_comp e (fun r => p r (-z))]
  simp only [hp]

lemma blockNumerator_reflection {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    {b : Fin m → ℂ} (e : Equiv.Perm (Fin m))
    (hp : ∀ r z, p (e r) (-z) = p r z) (hb : ∀ r, b (e r) = conj (b r))
    (z : UnitAddCircle) : blockNumerator p b (-z) = conj (blockNumerator p b z) := by
  unfold blockNumerator
  rw [← Equiv.sum_comp e (fun r => (p r (-z):ℂ)*b r)]
  simp only [hp,hb,map_sum,map_mul,Complex.conj_ofReal]

lemma blockCenter_reflection {m : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    {b : Fin m → ℂ} (e : Equiv.Perm (Fin m))
    (hp : ∀ r z, p (e r) (-z) = p r z) (hb : ∀ r, b (e r) = conj (b r))
    (epsilon : ℝ) (z : UnitAddCircle) :
    blockCenter p b epsilon (-z) = conj (blockCenter p b epsilon z) := by
  simp only [blockCenter,blockTotal_reflection e hp,
    blockNumerator_reflection e hp hb,map_div₀,Complex.conj_ofReal]

/-- Source 04 centering with its smoothness, norm, and conjugation requirements.
The explicit center even has norm at most one (the source permits two). -/
theorem exists_smooth_symmetric_block_center {m : ℕ}
    {p : Fin m → UnitAddCircle → ℝ} (hp : ∀ r z, 0 ≤ p r z)
    (hc : ∀ r, Continuous (p r))
    (hs : ∀ r, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p r (x : UnitAddCircle)))
    {b : Fin m → ℂ} (hb : ∀ r, ‖b r‖ ≤ 1) (e : Equiv.Perm (Fin m))
    (hpr : ∀ r z, p (e r) (-z) = p r z) (hbr : ∀ r, b (e r) = conj (b r))
    {delta : ℝ} (hd : 0 < delta) :
    ∃ q : UnitAddCircle → ℂ, Continuous q ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x : UnitAddCircle)) ∧
      (∀ z, ‖q z‖ ≤ 2) ∧ (∀ z, q (-z) = conj (q z)) ∧
      (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p b z-q z‖^2 ∂phaseHaar) < delta := by
  have he : 0 < delta^2 := sq_pos_of_pos hd
  refine ⟨blockCenter p b (delta^2),continuous_blockCenter hp hc b he,
    contDiff_blockCenter_lift hp hs b he,?_,blockCenter_reflection e hpr hbr (delta^2),?_⟩
  · intro z
    exact (blockCenter_norm hp hb he z).trans (by norm_num)
  · have h := blockCenter_integral_error hp hc hb he
    rw [Real.sqrt_sq hd.le] at h
    linarith

end ThreeTorus
end
end

section

/-! Quantitative passage from the fixed pre-block model to actual color
 densities, source 04:239--286 and 409--437. No geometric approximation oracle
 is introduced: these are deterministic L1 stability estimates. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def colorL1Distance {m : ℕ} (p g : Fin m → UnitAddCircle → ℝ) : ℝ :=
  ∑ r, ∫ z, |p r z-g r z| ∂phaseHaar

lemma colorL1Distance_nonneg {m : ℕ} (p g : Fin m → UnitAddCircle → ℝ) :
    0 ≤ colorL1Distance p g :=
  Finset.sum_nonneg (fun _r _ => integral_nonneg (fun _ => abs_nonneg _))

lemma continuous_circle_integrable {f : UnitAddCircle → ℝ} (hf : Continuous f) :
    Integrable f phaseHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integral_sqrt_le_sqrt_integral {p : UnitAddCircle → ℝ}
    (hp : Continuous p) (hp0 : ∀ z, 0 ≤ p z) :
    (∫ z, Real.sqrt (p z) ∂phaseHaar) ≤ Real.sqrt (∫ z, p z ∂phaseHaar) := by
  let sIntegral := ∫ z, Real.sqrt (p z) ∂phaseHaar
  have hi := continuous_circle_integrable hp
  have his := continuous_circle_integrable (Real.continuous_sqrt.comp hp)
  have hnon := integral_nonneg (μ := phaseHaar)
    (f := fun z : UnitAddCircle => (Real.sqrt (p z)-sIntegral)^2)
    (fun z => sq_nonneg (Real.sqrt (p z)-sIntegral))
  have heq (z : UnitAddCircle) : (Real.sqrt (p z)-sIntegral)^2 =
      p z-2*sIntegral*Real.sqrt (p z)+sIntegral^2 := by
    nlinarith [Real.sq_sqrt (hp0 z)]
  simp_rw [heq] at hnon
  erw [integral_add (hi.sub (his.const_mul (2*sIntegral))) (integrable_const _),
    integral_sub hi (his.const_mul (2*sIntegral)),integral_const_mul] at hnon
  simp only [integral_const,probReal_univ,one_smul] at hnon
  have hm : 0 ≤ ∫ z, p z ∂phaseHaar := integral_nonneg hp0
  have hs := Real.sqrt_nonneg (∫ z, p z ∂phaseHaar)
  have hsq := Real.sq_sqrt hm
  change sIntegral ≤ _
  change 0 ≤ (∫ z, p z ∂phaseHaar)-2*sIntegral*sIntegral+sIntegral^2 at hnon
  nlinarith

lemma sqrt_le_sqrt_add_sqrt_error {a b e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : 0 ≤ e) (hab : a-b ≤ e) : Real.sqrt a ≤ Real.sqrt b+Real.sqrt e := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hse := Real.sq_sqrt he
  have hna := Real.sqrt_nonneg a
  have hnb := Real.sqrt_nonneg b
  have hne := Real.sqrt_nonneg e
  nlinarith [mul_nonneg hnb hne]

/-- Total Hellinger loss is bounded by the square root of total color L1 loss. -/
theorem color_hellinger_stability {m : ℕ} {p g : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hg : ∀ r z, 0 ≤ g r z)
    (hcp : ∀ r, Continuous (p r)) (hcg : ∀ r, Continuous (g r)) :
    (∫ z, Real.sqrt (blockTotal p z) ∂phaseHaar) ≤
      (∫ z, Real.sqrt (blockTotal g z) ∂phaseHaar)+Real.sqrt (colorL1Distance p g) := by
  let E : UnitAddCircle → ℝ := fun z => ∑ r, |p r z-g r z|
  have hE : Continuous E := by unfold E; fun_prop
  have hE0 : ∀ z, 0 ≤ E z := fun z => Finset.sum_nonneg (fun r _ => abs_nonneg _)
  have hEt : (∫ z, E z ∂phaseHaar) = colorL1Distance p g := by
    exact integral_finsetSum _ (fun r _ => continuous_circle_integrable ((hcp r).sub (hcg r)).abs)
  have hi := integral_mono
    (continuous_circle_integrable (Real.continuous_sqrt.comp (continuous_blockTotal hcp)))
    ((continuous_circle_integrable (Real.continuous_sqrt.comp (continuous_blockTotal hcg))).add
      (continuous_circle_integrable (Real.continuous_sqrt.comp hE)))
    (fun z => sqrt_le_sqrt_add_sqrt_error (blockTotal_nonneg hp z)
      (blockTotal_nonneg hg z) (hE0 z) (by
        unfold blockTotal
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_le_sum (fun r _ => le_abs_self _)))
  erw [integral_add
    (continuous_circle_integrable (Real.continuous_sqrt.comp (continuous_blockTotal hcg)))
    (continuous_circle_integrable (Real.continuous_sqrt.comp hE))] at hi
  have hsq := integral_sqrt_le_sqrt_integral hE hE0
  rw [hEt] at hsq
  dsimp only [Function.comp_def] at hi
  linarith

/-- Bounded weights transfer the model prediction integral to actual densities. -/
theorem color_weighted_stability {m : ℕ} {p g w : Fin m → UnitAddCircle → ℝ}
    (hcp : ∀ r, Continuous (p r)) (hcg : ∀ r, Continuous (g r))
    (hcw : ∀ r, Continuous (w r)) {W : ℝ}
    (hw : ∀ r z, 0 ≤ w r z ∧ w r z ≤ W) :
    (∑ r, ∫ z, g r z*w r z ∂phaseHaar) ≤
      (∑ r, ∫ z, p r z*w r z ∂phaseHaar)+W*colorL1Distance p g := by
  have h (r : Fin m) : (∫ z, g r z*w r z ∂phaseHaar) ≤
      (∫ z, p r z*w r z ∂phaseHaar)+W*(∫ z, |p r z-g r z| ∂phaseHaar) := by
    have hpoint (z : UnitAddCircle) : g r z*w r z ≤
        p r z*w r z+W*|p r z-g r z| := by
      have h1 : (g r z-p r z)*w r z ≤ |p r z-g r z| * w r z := by
        apply mul_le_mul_of_nonneg_right _ (hw r z).1
        simpa only [abs_sub_comm] using le_abs_self (g r z-p r z)
      have h2 := mul_le_mul_of_nonneg_left (hw r z).2 (abs_nonneg (p r z-g r z))
      nlinarith
    have hi := integral_mono (continuous_circle_integrable ((hcg r).mul (hcw r)))
      (continuous_circle_integrable (((hcp r).mul (hcw r)).add
        (continuous_const.mul (((hcp r).sub (hcg r)).abs)))) hpoint
    erw [integral_add (continuous_circle_integrable ((hcp r).mul (hcw r)))
      (continuous_circle_integrable (continuous_const.mul (((hcp r).sub (hcg r)).abs))),
      integral_const_mul] at hi
    exact hi
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ => h r)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,colorL1Distance] using hs

lemma colorL1Distance_triangle {m : ℕ} {p g h : Fin m → UnitAddCircle → ℝ}
    (hcp : ∀ r, Continuous (p r)) (hcg : ∀ r, Continuous (g r))
    (hch : ∀ r, Continuous (h r)) :
    colorL1Distance p h ≤ colorL1Distance p g+colorL1Distance g h := by
  have hh (r : Fin m) : (∫ z, |p r z-h r z| ∂phaseHaar) ≤
      (∫ z, |p r z-g r z| ∂phaseHaar)+(∫ z, |g r z-h r z| ∂phaseHaar) := by
    have hi := integral_mono (continuous_circle_integrable (((hcp r).sub (hch r)).abs))
      (continuous_circle_integrable ((((hcp r).sub (hcg r)).abs).add
        (((hcg r).sub (hch r)).abs))) (fun z => abs_sub_le (p r z) (g r z) (h r z))
    erw [integral_add (continuous_circle_integrable (((hcp r).sub (hcg r)).abs))
      (continuous_circle_integrable (((hcg r).sub (hch r)).abs))] at hi
    exact hi
  simpa only [colorL1Distance,Finset.sum_add_distrib] using
    Finset.sum_le_sum (s := Finset.univ) (fun r _ => hh r)

lemma colorL1Distance_mul_bound {m : ℕ} {p g f : Fin m → UnitAddCircle → ℝ}
    (hcp : ∀ r, Continuous (p r)) (hcg : ∀ r, Continuous (g r))
    (hcf : ∀ r, Continuous (f r)) {M : ℝ} (hM : ∀ r z, |f r z| ≤ M) :
    colorL1Distance (fun r z => p r z*f r z) (fun r z => g r z*f r z) ≤
      M*colorL1Distance p g := by
  have hh (r : Fin m) : (∫ z, |p r z*f r z-g r z*f r z| ∂phaseHaar) ≤
      M*(∫ z, |p r z-g r z| ∂phaseHaar) := by
    have hi := integral_mono
      (continuous_circle_integrable ((((hcp r).mul (hcf r)).sub ((hcg r).mul (hcf r))).abs))
      (continuous_circle_integrable (continuous_const.mul (((hcp r).sub (hcg r)).abs)))
      (fun z => by
        change |p r z*f r z-g r z*f r z| ≤ M*|p r z-g r z|
        rw [← sub_mul,abs_mul,mul_comm M]
        exact mul_le_mul_of_nonneg_left (hM r z) (abs_nonneg _))
    erw [integral_const_mul] at hi
    exact hi
  simpa only [colorL1Distance,Finset.mul_sum] using
    Finset.sum_le_sum (s := Finset.univ) (fun r _ => hh r)

/-- The geometric amplification is finite and fixed before choosing any anchor
accuracy, even when the block length is very large. -/
lemma finite_error_propagation {E : ℕ → ℝ} {M t : ℝ} (hM : 1 ≤ M) (ht : 0 ≤ t)
    (h0 : E 0 ≤ t) (hstep : ∀ i, E (i+1) ≤ M*E i+t) (n : ℕ) :
    E n ≤ ((n:ℝ)+1)*M^n*t := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hMn : 1 ≤ M^(n+1) := one_le_pow₀ hM
    have hM0 : 0 ≤ M := le_trans (by norm_num) hM
    have hMul := mul_le_mul_of_nonneg_left ih hM0
    have htn := mul_le_mul_of_nonneg_right hMn ht
    have heq : M*(((n:ℝ)+1)*M^n*t) = ((n:ℝ)+1)*M^(n+1)*t := by
      rw [pow_succ]; ring
    rw [heq] at hMul
    have hs := hstep n
    push_cast
    nlinarith

end ThreeTorus
end
end

end OAI
