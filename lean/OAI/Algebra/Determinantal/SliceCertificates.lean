import OAI.Algebra.Determinantal.SmoothSlices

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma homogeneous_piece_certificate_all {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Fintype σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) :
    ∃ N : ℕ, ∀ D ≥ N, ∀ f : MvPolynomial σ K, f.IsHomogeneous D → f ∈ I := by
  classical
  choose M hM using variable_power_certificate I hz
  refine ⟨(∑ j, M j)+1, ?_⟩
  intro D hD f hf
  rw [← f.support_sum_monomial_coeff]
  apply I.sum_mem
  intro s hs
  apply monomial_mem_of_variable_powers I M hM
  have hd : s.degree = D := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hs)
  omega

lemma macaulay_surjective_zero {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι]
    (F : ι → MvPolynomial σ K) (e : ι → ℕ) (hh : ∀ i, (F i).IsHomogeneous (e i))
    (D : ℕ) (hM : Function.Surjective (macaulayMatrix (fun i => (e i : ℤ)) F D).mulVec)
    (y : σ → K) (hy : ∀ i, eval y (F i) = 0) : y = 0 := by
  have hI : Ideal.span (Set.range F) ≤ RingHom.ker (eval y) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hy i
  have h := (macaulay_surjective_iff _ _ (fun i => homogeneous_intWeight (hh i)) D).mp hM
  funext j
  have hm : (X j : MvPolynomial σ K)^D ∈ Ideal.span (Set.range F) := by
    apply h
    apply homogeneous_intWeight
    simpa using (isHomogeneous_X K j).pow D
  have he := hI hm
  change eval y ((X j)^D) = 0 at he
  rw [map_pow, eval_X] at he
  exact eq_zero_of_pow_eq_zero he

end PermanentBorder.SliceParameters
namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma good_certificate_all (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ)
    (e : ι → ℕ) (hh : ∀ i, (H i).IsHomogeneous (e i)) (hg : Good H l) :
    ∃ N : ℕ, ∀ D ≥ N, Function.Surjective
      (macaulayMatrix (fun i => (degrees e i : ℤ)) (bad H l) D).mulVec := by
  have hz : ∀ y ∈ zeroLocus ℂ (Ideal.span (Set.range (bad H l))), y = 0 := by
    intro y hy
    apply (good_iff_bad H l).mp hg y
    intro i
    exact hy _ Ideal.mem_span_range_self
  obtain ⟨N,hN⟩ := homogeneous_piece_certificate_all (Ideal.span (Set.range (bad H l))) hz
  refine ⟨N, fun D hD => ?_⟩
  apply (macaulay_surjective_iff _ _
    (fun i => homogeneous_intWeight (bad_homogeneous H l e hh i)) D).mpr
  intro f hf
  exact hN D hD f (intWeight_homogeneous hf)

lemma good_of_certificate (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ)
    (e : ι → ℕ) (hh : ∀ i, (H i).IsHomogeneous (e i)) (D : ℕ)
    (hM : Function.Surjective (macaulayMatrix (fun i => (degrees e i : ℤ)) (bad H l) D).mulVec) :
    Good H l := by
  apply (good_iff_bad H l).mpr
  exact macaulay_surjective_zero (bad H l) (degrees e) (bad_homogeneous H l e hh) D hM

end PermanentBorder.CI

namespace PermanentBorder.CI
open Polynomial Matrix
open scoped Classical

lemma matrix_right_inverse {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (A : Matrix α β K) (hA : Function.Surjective A.mulVec) :
    ∃ B : Matrix β α K, A * B = 1 := by
  choose b hb using fun i : α => hA (Pi.single i 1)
  refine ⟨fun j i => b i j, ?_⟩
  ext i j
  change (A.mulVec (b j)) i = (1 : Matrix α α K) i j
  rw [hb]
  simp [Matrix.one_apply, Pi.single_apply]

lemma rank_curve {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (A : Matrix α β K[X])
    (h0 : Function.Surjective (A.map (evalRingHom (0 : K))).mulVec)
    (h1 : Function.Surjective (A.map (evalRingHom (1 : K))).mulVec) :
    ∃ q : K[X], q.eval 0 = 1 ∧ q.eval 1 = 1 ∧
      ∀ t : K, q.eval t ≠ 0 → Function.Surjective (A.map (evalRingHom t)).mulVec := by
  obtain ⟨b0,hb0⟩ := matrix_right_inverse _ h0
  obtain ⟨b1,hb1⟩ := matrix_right_inverse _ h1
  let B : Matrix β α K[X] := fun i j => C (b0 i j) + X * (C (b1 i j) - C (b0 i j))
  have hB0 : B.map (evalRingHom (0 : K)) = b0 := by
    ext i j
    change (C (b0 i j) + X * (C (b1 i j) - C (b0 i j))).eval _ = _
    simp
  have hB1 : B.map (evalRingHom (1 : K)) = b1 := by
    ext i j
    change (C (b0 i j) + X * (C (b1 i j) - C (b0 i j))).eval _ = _
    simp
  refine ⟨(A*B).det, ?_, ?_, ?_⟩
  · rw [show ((A*B).det).eval 0 = ((A*B).map (evalRingHom (0 : K))).det from
      (evalRingHom (0 : K)).map_det (A*B)]
    rw [Matrix.map_mul, hB0, hb0, Matrix.det_one]
  · rw [show ((A*B).det).eval 1 = ((A*B).map (evalRingHom (1 : K))).det from
      (evalRingHom (1 : K)).map_det (A*B)]
    rw [Matrix.map_mul, hB1, hb1, Matrix.det_one]
  · intro t ht
    have hu : IsUnit ((A*B).map (evalRingHom t)) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      apply isUnit_iff_ne_zero.mpr
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ht
    have hs := Matrix.mulVec_surjective_iff_isUnit.mpr hu
    intro v
    obtain ⟨x,hx⟩ := hs v
    refine ⟨(B.map (evalRingHom t)).mulVec x, ?_⟩
    rw [Matrix.mulVec_mulVec]
    simpa only [Matrix.map_mul] using hx

lemma polynomial_nonzero_preconnected (q : ℂ[X]) (hq : q ≠ 0) :
    IsPreconnected {t : ℂ | q.eval t ≠ 0} := by
  have hs : {t : ℂ | q.eval t = 0}.Finite := q.finite_setOfPred_isRoot hq
  have hdim : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  exact (hs.countable.isPathConnected_compl_of_one_lt_rank hdim).isConnected.isPreconnected

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma map_linear {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (l : Option ι → R) : map φ (linear l) = linear (fun j => φ (l j)) := by
  simp [linear]

omit [Fintype ι] in
lemma map_square {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    (square H l).map (map φ) = square (fun i => map φ (H i)) (fun j => φ (l j)) := by
  ext i j
  cases i <;> simp [square, pderiv_map]

lemma map_bad {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) (i : Option ι) :
    map φ (bad H l i) = bad (fun i => map φ (H i)) (fun j => φ (l j)) i := by
  cases i with
  | none => simp only [bad, Option.elim'_none, map_mul, RingHom.map_det, RingHom.mapMatrix_apply, map_linear, map_square]
  | some i => rfl

noncomputable def Hline (H0 H1 : ι → MvPolynomial (Option ι) ℂ) :
    ι → MvPolynomial (Option ι) (Polynomial ℂ) := fun i =>
  map Polynomial.C (H0 i) + C Polynomial.X * (map Polynomial.C (H1 i) - map Polynomial.C (H0 i))
noncomputable def lline (l0 l1 : Option ι → ℂ) : Option ι → Polynomial ℂ := fun j =>
  Polynomial.C (l0 j) + Polynomial.X * (Polynomial.C (l1 j) - Polynomial.C (l0 j))
noncomputable def Htime (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (t : ℂ) :
    ι → MvPolynomial (Option ι) ℂ := fun i => H0 i + C t * (H1 i - H0 i)
noncomputable def ltime (l0 l1 : Option ι → ℂ) (t : ℂ) : Option ι → ℂ := fun j =>
  l0 j + t * (l1 j - l0 j)

omit [Fintype ι] in
@[simp] lemma Htime_zero (H0 H1 : ι → MvPolynomial (Option ι) ℂ) : Htime H0 H1 0 = H0 := by
  funext i; simp [Htime]
omit [Fintype ι] in
@[simp] lemma Htime_one (H0 H1 : ι → MvPolynomial (Option ι) ℂ) : Htime H0 H1 1 = H1 := by
  funext i; simp [Htime]
omit [Fintype ι] in
@[simp] lemma ltime_zero (l0 l1 : Option ι → ℂ) : ltime l0 l1 0 = l0 := by
  funext i; simp [ltime]
omit [Fintype ι] in
@[simp] lemma ltime_one (l0 l1 : Option ι → ℂ) : ltime l0 l1 1 = l1 := by
  funext i; simp [ltime]

omit [Fintype ι] in
lemma Hline_map (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (t : ℂ) (i : ι) :
    map (Polynomial.evalRingHom t) (Hline H0 H1 i) = Htime H0 H1 t i := by
  have hh : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
    ext x; simp
  simp [Hline, Htime, map_map, hh, MvPolynomial.map_id]
omit [Fintype ι] in
lemma lline_eval (l0 l1 : Option ι → ℂ) (t : ℂ) (j : Option ι) :
    (lline l0 l1 j).eval t = ltime l0 l1 t j := by simp [lline, ltime]

omit [Fintype ι] in
lemma Htime_homogeneous (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (e : ι → ℕ)
    (h0 : ∀ i, (H0 i).IsHomogeneous (e i)) (h1 : ∀ i, (H1 i).IsHomogeneous (e i))
    (t : ℂ) (i : ι) : (Htime H0 H1 t i).IsHomogeneous (e i) := by
  apply (h0 i).add
  simpa using (isHomogeneous_C (Option ι) t).mul ((h1 i).sub (h0 i))

lemma good_curve (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (l0 l1 : Option ι → ℂ)
    (e : ι → ℕ) (h0 : ∀ i, (H0 i).IsHomogeneous (e i))
    (h1 : ∀ i, (H1 i).IsHomogeneous (e i)) (hg0 : Good H0 l0) (hg1 : Good H1 l1) :
    ∃ q : Polynomial ℂ, q.eval 0 = 1 ∧ q.eval 1 = 1 ∧
      ∀ t, q.eval t ≠ 0 → Good (Htime H0 H1 t) (ltime l0 l1 t) := by
  obtain ⟨N0,hN0⟩ := good_certificate_all H0 l0 e h0 hg0
  obtain ⟨N1,hN1⟩ := good_certificate_all H1 l1 e h1 hg1
  let D := max N0 N1
  let A := macaulayMatrix (fun i => (degrees e i : ℤ)) (bad (Hline H0 H1) (lline l0 l1)) D
  have hA (t : ℂ) : A.map (Polynomial.evalRingHom t) =
      macaulayMatrix (fun i => (degrees e i : ℤ)) (bad (Htime H0 H1 t) (ltime l0 l1 t)) D := by
    rw [← macaulayMatrix_map]
    congr 1
    funext i
    rw [map_bad]
    congr 2
    · exact funext (Hline_map H0 H1 t)
    · exact funext (lline_eval l0 l1 t)
  have ha0 : Function.Surjective (A.map (Polynomial.evalRingHom (0 : ℂ))).mulVec := by
    rw [hA]; simp only [Htime_zero, ltime_zero]
    exact hN0 D (le_max_left _ _)
  have ha1 : Function.Surjective (A.map (Polynomial.evalRingHom (1 : ℂ))).mulVec := by
    rw [hA]; simp only [Htime_one, ltime_one]
    exact hN1 D (le_max_right _ _)
  obtain ⟨q,hq0,hq1,hq⟩ := rank_curve A ha0 ha1
  refine ⟨q,hq0,hq1,fun t ht => ?_⟩
  apply good_of_certificate _ _ e (Htime_homogeneous H0 H1 e h0 h1 t) D
  rw [← hA]
  exact hq t ht

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma linear_ltime (l0 l1 : Option ι → ℂ) (t : ℂ) :
    linear (ltime l0 l1 t) = linear l0 + C t * (linear l1 - linear l0) := by
  simp only [linear, ltime, map_add, map_mul, map_sub, add_mul, mul_sub, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [mul_assoc]

lemma normalized_time (H0 H1 : ι → MvPolynomial (Option ι) ℂ)
    (l0 l1 : Option ι → ℂ) (t : ℂ) (i : Option ι) :
    normalized (Htime H0 H1 t) (ltime l0 l1 t) i =
      normalized H0 l0 i + C t * (normalized H1 l1 i - normalized H0 l0 i) := by
  cases i with
  | none => simp only [normalized, Option.elim'_none, linear_ltime]; ring
  | some i => rfl

lemma contDiff_normalized_time (H0 H1 : ι → MvPolynomial (Option ι) ℂ)
    (l0 l1 : Option ι → ℂ) :
    ContDiff ℂ 1 (fun z : ℂ × (Option ι → ℂ) =>
      fun i => eval z.2 (normalized (Htime H0 H1 z.1) (ltime l0 l1 z.1) i)) := by
  apply contDiff_pi.mpr
  intro i
  simp only [normalized_time, map_add, map_mul, map_sub, eval_C]
  exact ((contDiff_eval (normalized H0 l0 i)).comp contDiff_snd).add
    (contDiff_fst.mul (((contDiff_eval (normalized H1 l1 i)).comp contDiff_snd).sub
      ((contDiff_eval (normalized H0 l0 i)).comp contDiff_snd)))

theorem good_card (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ)
    (e : ι → ℕ) (he : ∀ i, 0 < e i) (hh : ∀ i, (H i).IsHomogeneous (e i))
    (hg : Good H l) : Nat.card (Roots H l) = ∏ i, e i := by
  obtain ⟨q,hq0,hq1,hq⟩ := good_curve H (powers e) l coordinate e hh
    (powers_homogeneous e) hg (powers_good e he)
  have hqn : q ≠ 0 := by intro hz; simp [hz] at hq0
  let s : Set ℂ := {t | q.eval t ≠ 0}
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp
    (polynomial_nonzero_preconnected q hqn)
  let a : s := ⟨0,by simp [s,hq0]⟩
  let b : s := ⟨1,by simp [s,hq1]⟩
  have hc := normalized_count_constant (Htime H (powers e)) (ltime l coordinate) e
    (Htime_homogeneous H (powers e) e hh (powers_homogeneous e))
    (contDiff_normalized_time H (powers e) l coordinate) s hq a b
  simpa only [a,b,Htime_zero,Htime_one,ltime_zero,ltime_one,powers_card e he] using hc

end PermanentBorder.CI

namespace PermanentBorder.Polar
open MvPolynomial
open scoped TensorProduct

variable {K R L : Type*} [CommRing K] [CommRing R] [CommRing L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

noncomputable def extendDerivation [Algebra.FormallyEtale R L]
    (D : Derivation K R L) : Derivation K L L :=
  ((D.liftKaehlerDifferential.liftBaseChange L).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K R L).symm.toLinearMap).compDer
      (KaehlerDifferential.D K L)

lemma extendDerivation_algebraMap [Algebra.FormallyEtale R L]
    (D : Derivation K R L) (x : R) :
    extendDerivation D (algebraMap R L x) = D x := by
  simp [extendDerivation, LinearMap.compDer,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

section Generic
universe u v
variable (K : Type u) [Field K] [CharZero K] (ι : Type v)

abbrev GenericField := AlgebraicClosure (FractionRing (MvPolynomial ι K))

noncomputable def genericParameter (i : ι) : GenericField K ι :=
  algebraMap (MvPolynomial ι K) (GenericField K ι) (X i)

lemma generic_formallyEtale :
    Algebra.FormallyEtale (MvPolynomial ι K) (GenericField K ι) := by
  let R := MvPolynomial ι K
  let Q := FractionRing R
  have : Algebra.FormallyEtale R Q :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have : Algebra.FormallyEtale Q (GenericField K ι) :=
    Algebra.FormallyEtale.of_isSeparable Q (GenericField K ι)
  exact Algebra.FormallyEtale.comp R Q (GenericField K ι)

noncomputable def parameterDerivation (i : ι) :
    Derivation K (GenericField K ι) (GenericField K ι) := by
  classical
  letI := generic_formallyEtale K ι
  exact extendDerivation (MvPolynomial.mkDerivation K (Pi.single i 1))

lemma parameterDerivation_parameter [DecidableEq ι] (i j : ι) :
    parameterDerivation K ι i (genericParameter K ι j) = if i = j then 1 else 0 := by
  classical
  simp [parameterDerivation, genericParameter, extendDerivation_algebraMap, Pi.single_apply,
    eq_comm]

end Generic

section ChainRule
variable {K L σ : Type*} [CommRing K] [CommRing L] [Algebra K L] [Fintype σ]

lemma derivation_aeval (D : Derivation K L L) (x : σ → L) (f : MvPolynomial σ K) :
    D (aeval x f) = ∑ j, aeval x (pderiv j f) * D (x j) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f i hf =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hf,
      map_add, pderiv_X]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    simp [Pi.single_apply, mul_comm]

end ChainRule
end PermanentBorder.Polar

end OAI
