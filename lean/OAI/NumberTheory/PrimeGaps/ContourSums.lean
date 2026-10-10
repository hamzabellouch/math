import OAI.NumberTheory.PrimeGaps.EulerChoices

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

noncomputable def fourierCoordinateSum (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  ∑ i, EuclideanSpace.proj i

@[simp] theorem fourierCoordinateSum_apply {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    fourierCoordinateSum ι v = ∑ i, v i := by simp [fourierCoordinateSum]

noncomputable def divisorLogVector {ι : Type*} (L : ℝ) (d : ι → ℕ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.log (d i)/L)

@[simp] theorem divisorLogVector_apply {ι : Type*} (L : ℝ) (d : ι → ℕ) (i : ι) :
    divisorLogVector L d i = Real.log (d i)/L := rfl

noncomputable def fourierContour {ι : Type*} (L : ℝ) (u : EuclideanSpace ℝ ι) (i : ι) : ℂ :=
  (1+Complex.I*(u i : ℂ))/(L:ℂ)

@[simp] theorem fourierContour_re {ι : Type*} (L : ℝ) (u : EuclideanSpace ℝ ι) (i : ι) :
    (fourierContour L u i).re = L⁻¹ := by
  simp [fourierContour, Complex.div_ofReal_re]

theorem tupleFourierCoefficient_norm_eq_of_re {ι : Type*} [Fintype ι] (δ : ℕ) (d : ι → ℕ)
    (z w : ι → ℂ) (h : ∀ i, (z i).re=(w i).re) :
    ‖tupleFourierCoefficient δ d z‖ = ‖tupleFourierCoefficient δ d w‖ := by
  simp only [tupleFourierCoefficient, norm_mul, Complex.norm_exp, Complex.neg_re,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, h]

theorem tupleFourierCoefficient_contour_norm {ι : Type*} [Fintype ι] (δ : ℕ) (d : ι → ℕ)
    (L : ℝ) (u : EuclideanSpace ℝ ι) :
    ‖tupleFourierCoefficient δ d (fourierContour L u)‖ =
      ‖tupleFourierCoefficient δ d (fun _ => (L⁻¹:ℝ))‖ := by
  apply tupleFourierCoefficient_norm_eq_of_re
  intro i
  simp

theorem continuous_tupleFourierCoefficient_contour {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) :
    Continuous (fun u : EuclideanSpace ℝ ι => tupleFourierCoefficient δ d (fourierContour L u)) := by
  unfold tupleFourierCoefficient fourierContour
  fun_prop

theorem contour_sum_log_eq {ι : Type*} [Fintype ι] (L : ℝ) (d : ι → ℕ)
    (u : EuclideanSpace ℝ ι) :
    (∑ i, (Real.log (d i):ℂ)*fourierContour L u i) =
      (fourierCoordinateSum ι (divisorLogVector L d) : ℂ) +
        Complex.I*(inner ℝ u (divisorLogVector L d) : ℂ) := by
  simp only [fourierCoordinateSum_apply, Complex.ofReal_sum, PiLp.inner_apply,
    Real.inner_apply, divisorLogVector_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [fourierContour, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem integral_sourceFourier_tupleCoefficient {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    (∫ u : EuclideanSpace ℝ ι, sourceFourier (fourierCoordinateSum ι) F hF hFs u *
      tupleFourierCoefficient δ d (fourierContour L u)) =
    tuplePrimeDensity δ d * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      F (divisorLogVector L d) := by
  simp only [tupleFourierCoefficient, contour_sum_log_eq, neg_add_rev]
  rw [← sourceFourier_inversion (fourierCoordinateSum ι) F hF hFs (divisorLogVector L d),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sub_eq_add_neg]
  ring_nf

theorem integrable_sourceFourier_tupleCoefficient {ι : Type*} [Fintype ι]
    (δ : ℕ) (d : ι → ℕ) (L : ℝ) (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    Integrable (fun u => Φ u * tupleFourierCoefficient δ d (fourierContour L u)) := by
  apply Φ.integrable.mul_bdd (continuous_tupleFourierCoefficient_contour δ d L).aestronglyMeasurable
  filter_upwards [] with u
  exact (tupleFourierCoefficient_contour_norm δ d L u).le

noncomputable def analyticDensity {ι : Type*} [Fintype ι] (δ : ℕ)
    (A : ℕ → Finset (Finset ι)) (L : ℝ) (F : EuclideanSpace ℝ ι → ℂ) : ℂ :=
  ∑' d : AllowedDivisorTuple A,
    tuplePrimeDensity δ d.val * (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      F (divisorLogVector L d.val)

theorem analyticDensity_eq_integral {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    analyticDensity δ A L F =
      ∫ u : EuclideanSpace ℝ ι, sourceFourier (fourierCoordinateSum ι) F hF hFs u *
        ∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u) := by
  let : Countable (AllowedDivisorTuple A) := by unfold AllowedDivisorTuple; infer_instance
  let Φ := sourceFourier (fourierCoordinateSum ι) F hF hFs
  have hs := tupleFourier_summable_norm hδ A (fun _ => (L⁻¹:ℝ)) (inv_pos.mpr hL)
    hA hR (fun _ => le_rfl)
  have hint (d : AllowedDivisorTuple A) :
      Integrable (fun u => Φ u * tupleFourierCoefficient δ d.val (fourierContour L u)) :=
    integrable_sourceFourier_tupleCoefficient δ d.val L Φ
  have hsum : Summable (fun d : AllowedDivisorTuple A =>
      ∫ u : EuclideanSpace ℝ ι, ‖Φ u*tupleFourierCoefficient δ d.val (fourierContour L u)‖) := by
    simp_rw [norm_mul, tupleFourierCoefficient_contour_norm, integral_mul_const]
    exact hs.mul_left _
  have he := (hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq
  simp only [integral_sourceFourier_tupleCoefficient, Φ] at he
  rw [analyticDensity, he]
  apply integral_congr_ae
  filter_upwards [] with u
  exact tsum_mul_left

theorem allowed_residue_iff {ι : Type*} [Fintype ι] (d b : ι → ℕ) :
    (∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈residueFamily (fun i => (b i:ℤ)) p) ↔ localCompatible d b := by
  constructor
  · intro h p hp _ i j hi hj
    have hm := h ⟨p,hp⟩ ⟨i,by simp [tuplePrimeSubset,hi]⟩
    rw [residueFamily, mem_fiberSubsetFamily_image] at hm
    have he := hm.2 i (by simp [tuplePrimeSubset,hi]) j (by simp [tuplePrimeSubset,hj])
    change b i % p = b j % p
    exact_mod_cast he
  · intro h p hp
    rw [residueFamily, mem_fiberSubsetFamily_image]
    refine ⟨hp,?_⟩
    intro i hi j hj
    have hi' : p.val∣d i := by simpa [tuplePrimeSubset] using hi
    have hj' : p.val∣d j := by simpa [tuplePrimeSubset] using hj
    have hq : p.val∣tupleModulus d := hi'.trans (Finset.dvd_lcm (Finset.mem_univ i))
    have he : b i % p.val=b j % p.val := h p.val p.property hq i j hi' hj'
    exact_mod_cast he

theorem allowed_marked_residue_iff {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) :
    (∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈markedResidueFamily (fun i => (b i:ℤ)) p a) ↔
      markedLocalCompatible d b a := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · apply (allowed_residue_iff d b).mp
      intro p hp
      have hm := (mem_markedResidueFamily _ _ _ _).mp (h p hp)
      rw [residueFamily,mem_fiberSubsetFamily_image]
      exact ⟨hm.1,hm.2.1⟩
    · intro p hp _ i hi he
      have hm := (mem_markedResidueFamily _ _ _ _).mp
        (h ⟨p,hp⟩ ⟨i,by simp [tuplePrimeSubset,hi]⟩)
      apply hm.2.2 i (by simp [tuplePrimeSubset,hi])
      change b i % p=a % p at he
      exact_mod_cast he
  · rintro ⟨h,hmark⟩ p hp
    rw [mem_markedResidueFamily]
    have hu := (allowed_residue_iff d b).mpr h p hp
    rw [residueFamily,mem_fiberSubsetFamily_image] at hu
    refine ⟨hu.1,hu.2,?_⟩
    intro i hi he
    have hi' : p.val∣d i := by simpa [tuplePrimeSubset] using hi
    apply hmark p.val p.property (hi'.trans (Finset.dvd_lcm (Finset.mem_univ i))) i hi'
    change b i % p.val=a % p.val
    exact_mod_cast he

theorem analyticDensity_eq_unmarked_tsum {n : ℕ} (X : ℕ)
    (F : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) :
    analyticDensity 0 (residueFamily (fun i => (b i:ℤ))) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) =
      ∑' d : Fin n → ℕ, ((divisorCoefficient X F d * tupleDensity d b : ℝ):ℂ) := by
  let P := fun d : Fin n → ℕ => (∀ i, Squarefree (d i)) ∧
    ∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈residueFamily (fun i => (b i:ℤ)) p
  change (∑' d : {d // P d}, tuplePrimeDensity 0 d.val *
    (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      (F (divisorLogVector (Real.log X) d.val).ofLp:ℂ)) = _
  refine (tsum_subtype {d | P d} (fun d => tuplePrimeDensity 0 d *
    (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (divisorLogVector (Real.log X) d).ofLp:ℂ))).trans ?_
  apply tsum_congr
  intro d
  by_cases hd : P d
  · rw [Set.indicator_of_mem (show d ∈ {d | P d} from hd), tuplePrimeDensity_zero hd.1]
    have hc := (tupleCompatible_iff_localCompatible hd.1).mpr ((allowed_residue_iff d b).mp hd.2)
    simp only [divisorCoefficient,tupleDensity,ite_eq_left hc,Complex.ofReal_mul,
      Complex.ofReal_prod,Complex.ofReal_intCast,Complex.ofReal_inv,Complex.ofReal_natCast]
    change (tupleModulus d : ℂ)⁻¹ * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (logCoordinates X d):ℂ) = _
    ring
  · rw [Set.indicator_of_notMem (show d ∉ {d | P d} from hd)]
    have hv : divisorCoefficient X F d * tupleDensity d b = 0 := by
      by_contra hv
      have hf := (divisorCoefficient_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1
      have hc : tupleCompatible d b := by
        by_contra hc
        exact (mul_ne_zero_iff.mp hv).2 (by simp [tupleDensity,hc])
      exact hd ⟨hf,(allowed_residue_iff d b).mpr
        ((tupleCompatible_iff_localCompatible hf).mp hc)⟩
    rw [hv,Complex.ofReal_zero]

theorem analyticDensity_eq_marked_tsum {n : ℕ} (X : ℕ)
    (F : (Fin n → ℝ) → ℝ) (b : Fin n → ℕ) (a : ℕ) :
    analyticDensity 1 (fun p => markedResidueFamily (fun i => (b i:ℤ)) p a) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) =
      ∑' d : Fin n → ℕ, ((divisorCoefficient X F d * markedTupleDensity d b a : ℝ):ℂ) := by
  let P := fun d : Fin n → ℕ => (∀ i, Squarefree (d i)) ∧
    ∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty →
      tuplePrimeSubset d p∈markedResidueFamily (fun i => (b i:ℤ)) p a
  change (∑' d : {d // P d}, tuplePrimeDensity 1 d.val *
    (∏ i, (ArithmeticFunction.moebius (d.val i):ℂ)) *
      (F (divisorLogVector (Real.log X) d.val).ofLp:ℂ)) = _
  refine (tsum_subtype {d | P d} (fun d => tuplePrimeDensity 1 d *
    (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (divisorLogVector (Real.log X) d).ofLp:ℂ))).trans ?_
  apply tsum_congr
  intro d
  by_cases hd : P d
  · rw [Set.indicator_of_mem (show d ∈ {d | P d} from hd), tuplePrimeDensity_one hd.1]
    have hc := (markedTupleCompatible_iff_local hd.1).mpr ((allowed_marked_residue_iff d b a).mp hd.2)
    simp only [divisorCoefficient,markedTupleDensity,ite_eq_left hc,Complex.ofReal_mul,
      Complex.ofReal_prod,Complex.ofReal_intCast,Complex.ofReal_inv,Complex.ofReal_natCast]
    change ((tupleModulus d).totient : ℂ)⁻¹ * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
      (F (logCoordinates X d):ℂ) = _
    ring
  · rw [Set.indicator_of_notMem (show d ∉ {d | P d} from hd)]
    have hv : divisorCoefficient X F d * markedTupleDensity d b a = 0 := by
      by_contra hv
      have hf := (divisorCoefficient_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1
      have hc : markedTupleCompatible d b a := by
        by_contra hc
        exact (mul_ne_zero_iff.mp hv).2 (by simp [markedTupleDensity,hc])
      exact hd ⟨hf,(allowed_marked_residue_iff d b a).mpr
        ((markedTupleCompatible_iff_local hf).mp hc)⟩
    rw [hv,Complex.ofReal_zero]

theorem divisorCoefficient_support {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho)
    {d : Fin n → ℕ} (hd : divisorCoefficient X F d≠0) :
    d ∈ positiveProductTuples n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ := by
  obtain ⟨hsq,hF⟩ := divisorCoefficient_ne_zero_iff.mp hd
  have hp : ∀ i, 0<d i := fun i => Nat.pos_of_ne_zero (hsq i).ne_zero
  refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_,?_⟩
  · intro i
    exact Finset.mem_Icc.mpr ⟨hp i,divisor_coordinate_bound hX hbudget hp hF i⟩
  · exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr (divisor_product_bound hX hbudget hp hF)

theorem analyticDensity_eq_unmarkedDensitySum {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho) (b : Fin n → ℕ) :
    analyticDensity 0 (residueFamily (fun i => (b i:ℤ))) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) = (unmarkedDensitySum X F rho b : ℂ) := by
  rw [analyticDensity_eq_unmarked_tsum,unmarkedDensitySum,Complex.ofReal_sum]
  apply tsum_eq_sum
  intro d hd
  have hc : divisorCoefficient X F d=0 := by
    by_contra hc
    exact hd (divisorCoefficient_support hX hbudget hc)
  simp only [hc,zero_mul,Complex.ofReal_zero]

theorem analyticDensity_eq_markedDensitySum {n X : ℕ} (hX : 2≤X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho) (b : Fin n → ℕ) (a : ℕ) :
    analyticDensity 1 (fun p => markedResidueFamily (fun i => (b i:ℤ)) p a) (Real.log X)
      (fun v => (F v.ofLp:ℂ)) = (markedDensitySum X F rho b a : ℂ) := by
  rw [analyticDensity_eq_marked_tsum,markedDensitySum,Complex.ofReal_sum]
  apply tsum_eq_sum
  intro d hd
  have hc : divisorCoefficient X F d=0 := by
    by_contra hc
    exact hd (Finset.mem_filter.mpr ⟨divisorCoefficient_support hX hbudget hc,
      (divisorCoefficient_ne_zero_iff.mp hc).1⟩)
  simp only [hc,zero_mul,Complex.ofReal_zero]

theorem schwartz_integral_tail_bound {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (K : EuclideanSpace ℝ ι → ℂ)
    {R B : ℝ} (hR : 0<R) (hB : 0≤B) (hKm : AEStronglyMeasurable K volume)
    (hK : ∀ u, ‖K u‖≤B) (k : ℕ) :
    ‖∫ u in {u | R<‖u‖}, Φ u*K u‖ ≤
      (B/R^k) * ∫ u, ‖u‖^k*‖Φ u‖ := by
  let S : Set (EuclideanSpace ℝ ι) := {u | R<‖u‖}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hp : Integrable (fun u => Φ u*K u) :=
    Φ.integrable.mul_bdd hKm (Filter.Eventually.of_forall hK)
  have ht : Integrable (fun u : EuclideanSpace ℝ ι => ‖u‖^k*‖Φ u‖) :=
    SchwartzMap.integrable_pow_mul volume Φ k
  have hm : ∀ᵐ u ∂volume.restrict S,
      ‖Φ u*K u‖ ≤ (B/R^k)*(‖u‖^k*‖Φ u‖) := by
    filter_upwards [ae_restrict_mem hS] with u hu
    have hpow : R^k≤‖u‖^k := pow_le_pow_left₀ hR.le hu.le k
    rw [norm_mul]
    have hpower : 1≤‖u‖^k/R^k := (one_le_div (pow_pos hR k)).mpr hpow
    calc
      ‖Φ u‖*‖K u‖ ≤ ‖Φ u‖*B := mul_le_mul_of_nonneg_left (hK u) (norm_nonneg _)
      _ ≤ (‖Φ u‖*B)*(‖u‖^k/R^k) := le_mul_of_one_le_right (by positivity) hpower
      _ = (B/R^k)*(‖u‖^k*‖Φ u‖) := by ring
  calc
    _ ≤ ∫ u in S, ‖Φ u*K u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in S, (B/R^k)*(‖u‖^k*‖Φ u‖) :=
      integral_mono_ae hp.integrableOn.norm ((ht.const_mul _).integrableOn) hm
    _ ≤ ∫ u, (B/R^k)*(‖u‖^k*‖Φ u‖) :=
      setIntegral_le_integral (ht.const_mul _) (by filter_upwards [] with u; positivity)
    _ = _ := integral_const_mul _ _

theorem continuous_tupleFourier_tsum {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) :
    Continuous (fun u : EuclideanSpace ℝ ι =>
      ∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u)) := by
  refine continuous_tsum (fun d => continuous_tupleFourierCoefficient_contour δ d.val L)
    (tupleFourier_summable_norm hδ A (fun _ => (L⁻¹:ℝ)) (inv_pos.mpr hL) hA hR
      (fun _ => by simp)) ?_
  intro d u
  exact (tupleFourierCoefficient_contour_norm δ d.val L u).le

theorem tupleFourier_tsum_norm_bound {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L : ℝ} (hL : 0<L)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (u : EuclideanSpace ℝ ι) :
    ‖∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u)‖ ≤
    Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re) := by
  exact (norm_tsum_le_tsum_norm (tupleFourier_summable_norm hδ A _ (inv_pos.mpr hL)
    hA hR (by intro i; simp))).trans
    (tupleFourier_norm_tsum_le hδ A _ (inv_pos.mpr hL) hA hR (by intro i; simp))

theorem tupleFourier_schwartz_tail {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) {L U : ℝ} (hL : 0<L) (hU : 0<U)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R)
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (k : ℕ) :
    ‖∫ u in {u | U<‖u‖}, Φ u *
      (∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u))‖ ≤
      (Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re)/U^k) *
        ∫ u, ‖u‖^k*‖Φ u‖ := by
  apply schwartz_integral_tail_bound Φ _ hU (Real.exp_pos _).le
    (continuous_tupleFourier_tsum hδ A hL hA hR).aestronglyMeasurable
    (tupleFourier_tsum_norm_bound hδ A hL hA hR)

theorem zeta_contour_majorant_polynomial :
    ∃ L₀>0, ∀ L : ℝ, L₀≤L → ∀ R : ℕ,
      Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re) ≤ ((3/2)*L)^(2*R) := by
  obtain ⟨c,hc,ε,hε,hpole⟩ := zeta_pole_two_sided
  refine ⟨1+ε⁻¹,by positivity,fun L hL R => ?_⟩
  have hL0 : 0<L := lt_of_lt_of_le (by positivity) hL
  have heL : L⁻¹<ε := (inv_lt_comm₀ hL0 hε).mpr (by linarith)
  have hnorm : ‖(L⁻¹:ℂ)‖=L⁻¹ := by
    rw [show (L⁻¹:ℂ)=((L⁻¹:ℝ):ℂ) by simp,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hL0)]
  have hb := (hpole (L⁻¹:ℂ) (inv_ne_zero (by exact_mod_cast hL0.ne')) (by rw [hnorm]; exact heL)).2.2
  rw [norm_mul,hnorm] at hb
  have hz : (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re ≤ (3/2)*L := by
    have hcast : ((1+L⁻¹:ℝ):ℂ)=1+(L⁻¹:ℂ) := by simp
    rw [hcast]
    apply (Complex.re_le_norm _).trans
    calc
      _ = L * (L⁻¹ * ‖riemannZeta (1+(L⁻¹:ℂ))‖) := by field_simp
      _ ≤ L*(3/2) := mul_le_mul_of_nonneg_left hb hL0.le
      _ = _ := by ring
  have hzpos : 0<(riemannZeta ((1+L⁻¹:ℝ):ℂ)).re :=
    riemannZeta_re_pos_of_one_lt (by linarith [inv_pos.mpr hL0])
  calc
    _ = (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re^(2*R) := by
      rw [show (2:ℝ)*R=((2*R:ℕ):ℝ) by norm_cast,Real.exp_nat_mul,Real.exp_log hzpos]
    _ ≤ _ := pow_le_pow_left₀ hzpos.le hz _

theorem tupleFourier_sqrt_tail_power_saving {ι : Type*} [Fintype ι]
    (Φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) (R N : ℕ) :
    ∃ L₀>0, ∀ L : ℝ, L₀≤L → ∀ δ : ℕ, δ≤1 →
      ∀ A : ℕ → Finset (Finset ι),
      (∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) →
      (∀ p : Nat.Primes, (A p).card≤R) →
      ‖∫ u in {u | Real.sqrt L<‖u‖}, Φ u *
        (∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val (fourierContour L u))‖ ≤
        ((3/2:ℝ)^(2*R) * ∫ u, ‖u‖^(2*(2*R+N))*‖Φ u‖) / L^N := by
  obtain ⟨L₀,hL₀,hz⟩ := zeta_contour_majorant_polynomial
  refine ⟨L₀,hL₀,fun L hL δ hδ A hA hR => ?_⟩
  have hL0 : 0<L := hL₀.trans_le hL
  have hI : 0≤∫ u, ‖u‖^(2*(2*R+N))*‖Φ u‖ :=
    integral_nonneg (fun _ => by positivity)
  have hs : (Real.sqrt L)^(2*(2*R+N))=L^(2*R+N) := by
    rw [pow_mul,Real.sq_sqrt hL0.le]
  calc
    _ ≤ (Real.exp ((2*R)*Real.log (riemannZeta ((1+L⁻¹:ℝ):ℂ)).re)/
        (Real.sqrt L)^(2*(2*R+N))) * ∫ u, ‖u‖^(2*(2*R+N))*‖Φ u‖ :=
      tupleFourier_schwartz_tail hδ A hL0 (Real.sqrt_pos.mpr hL0) hA hR Φ _
    _ ≤ (((3/2)*L)^(2*R)/(Real.sqrt L)^(2*(2*R+N))) *
        ∫ u, ‖u‖^(2*(2*R+N))*‖Φ u‖ := by
      gcongr
      exact hz L hL R
    _ = _ := by
      rw [hs,mul_pow,pow_add]
      field_simp

theorem nonemptySubsets_singleton {ι : Type*} (i : ι) :
    nonemptySubsets {i} = {{i}} := by
  classical
  ext S
  simp [nonemptySubsets,Finset.subset_singleton_iff]
  aesop

theorem nonemptySubsets_pair {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j) :
    nonemptySubsets {i,j} = {{i},{j},{i,j}} := by
  classical
  ext S
  simp only [nonemptySubsets, Finset.mem_erase, Finset.mem_powerset,
    Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hne,he⟩
    have h : S=∅ ∨ S={i} ∨ S={j} ∨ S={i,j} := by
      have hp := Finset.mem_powerset.mpr he
      simp [Finset.powerset_insert] at hp
      aesop
    exact h.resolve_left (hne)
  · rintro (rfl|rfl|rfl) <;> simp

theorem fiberKernel_singleton {ι : Type*} (i : ι) (w : ι → ℂ) :
    fiberKernel {i} w = w i := by
  simp [fiberKernel,nonemptySubsets_singleton]

theorem fiberKernel_pair {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j) (w : ι → ℂ) :
    fiberKernel {i,j} w = w i*w j/(w i+w j) := by
  rw [fiberKernel,nonemptySubsets_pair hij]
  have h1 : ({j} : Finset ι)≠{i,j} := by simp [Finset.ext_iff,hij]
  have h2 : ({i} : Finset ι)≠{j} := by simp [hij]
  have h3 : ({i} : Finset ι)≠{i,j} := by simp [Finset.ext_iff,hij.symm]
  simp [h1,h2,h3,hij,div_eq_mul_inv]
  ring

theorem integral_exp_neg_complex_Ioi {w : ℂ} (hw : 0<w.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-w*(y:ℂ))) = w⁻¹ := by
  simpa using integral_exp_mul_complex_Ioi (a := -w) (by simpa using hw) 0

theorem fiberKernel_pair_laplace {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j)
    (u : ι → ℝ) :
    fiberKernel {i,j} (fun i => frequencyW (u i)) =
    frequencyW (u i)*frequencyW (u j) *
      ∫ y : ℝ in Ioi 0, Complex.exp (-(frequencyW (u i)+frequencyW (u j))*(y:ℂ)) := by
  rw [fiberKernel_pair hij,integral_exp_neg_complex_Ioi (by simp [frequencyW])]
  rfl

@[simp] theorem primeReciprocalPrefix_eq (y : ℕ) :
    primeReciprocalPrefix y = ∑ p∈Nat.primesLE y, (1:ℝ)/p := by
  simp only [primeReciprocalPrefix,primePrefix,one_div]
  exact Finset.sum_subtype_of_mem (fun p : ℕ => (p:ℝ)⁻¹) (fun p hp => (Nat.mem_primesLE.mp hp).2)

theorem genericEulerConstant_mono : Monotone genericEulerConstant := by
  intro m n hmn
  unfold genericEulerConstant
  gcongr
  norm_num

theorem primeReciprocalPrefix_nonneg (y : ℕ) : 0≤primeReciprocalPrefix y := by
  unfold primeReciprocalPrefix
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem exp_sub_one_le_two_mul {x : ℝ} (hx : 0≤x) (hx1 : x≤1) :
    Real.exp x-1≤2*x := by
  have h := Real.norm_exp_sub_one_sub_id_le (x:=x) (by simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using hx1)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hx] at h
  have hh := (abs_le.mp h).2
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]

noncomputable def uniformEulerError (R : ℕ) (s : ℝ) (y : ℕ) : ℝ :=
  Real.exp (4*R*primeReciprocalPrefix y)*
    (Real.exp (2*R)*6*R*Real.log y*(y:ℝ)^(-s)*primeReciprocalPrefix y+
      2*(Real.exp (genericEulerConstant R/(y:ℝ))-1))

theorem eulerGlobal_uniform_error {ι : Type*} [Fintype ι] {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y R : ℕ} (hy : 2≤y)
    (hA : ∀ p : Nat.Primes, (A p).card≤R) (hB : B.card≤R)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) {s : ℝ}
    (hzsmall : ∑ i, ‖z i‖ ≤ (y:ℝ)^(-s)) :
    ‖eulerGlobal δ A B z-eulerGlobal δ A B (fun _ => 0)‖ ≤ uniformEulerError R s y := by
  apply (eulerGlobal_comparison hδ A B z hz hy hA hB hgen).trans
  unfold uniformEulerError
  have hlog : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤y))
  have hr := primeReciprocalPrefix_nonneg y
  have hK := genericEulerConstant_mono hB
  gcongr

end LargePrimeGaps

end OAI
