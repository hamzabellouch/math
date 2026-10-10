import OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalMajorants

namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def primePoolDensity (G : Ideal O) : ℂ :=
  ∏ P : primePool {G}, (1-(1:ℂ)/(Ideal.absNorm P.val:ℂ))

theorem principalTruncation_scaled (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (c X Z : ℝ) :
    (c:ℂ)*principalTruncation (fun P : primePool {G} => P.val) Finset.univ W X Z =
      ((c*X:ℝ):ℂ)*paperRadialFourier W 0*primePoolDensity G -
      paperRadialFourier W 0 * (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((c*X)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) -
      W 0 * (∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(c:ℂ) else 0) := by
  classical
  have hl : (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((c*X)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) =
      ((c*X:ℝ):ℂ)*(∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)/(Ideal.absNorm d:ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : Z < (Ideal.absNorm d:ℝ)
    · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_natCast]
      ring
    · simp only [hd,ite_false,mul_zero]
  have hs : (∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(c:ℂ) else 0) =
      (c:ℂ)*(∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : (Ideal.absNorm d:ℝ) ≤ Z <;> simp only [hd,ite_true,ite_false,mul_zero] ; ring
  rw [principalTruncation_eq_ideal_divisors G hG,hl,hs]
  unfold primePoolDensity
  push_cast
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedPrincipalDensity
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (R : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ((Real.sqrt (R/(Ideal.absNorm (rows i):ℝ)):ℝ):ℂ)*primePoolDensity (left j*right k)

def unrestrictedDualPrincipalTruncation (W : ℝ → ℂ)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    (((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) *
      principalTruncation (fun P : primePool {left j*right k} => P.val) Finset.univ W
        (Real.sqrt (F*(Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ)/
          (M*(Ideal.absNorm (rows i):ℝ)))) (Z i))

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedDualPrincipalTruncation_eq
    (W : ℝ → ℂ) (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, rows i ≠ 0) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k)) :
    unrestrictedDualPrincipalTruncation W rows left right a b M F Z =
      paperRadialFourier W 0*unrestrictedPrincipalDensity rows left right a b (M/F) -
      paperRadialFourier W 0*unrestrictedLargePrincipalSum rows left right a b M F Z -
      W 0*unrestrictedSmallPrincipalSum rows left right a b M F (fun d i => (Ideal.absNorm d:ℝ) ≤ Z i) := by
  classical
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  have ht (i : m) (j : n) (k : p) :
      unrestrictedPairTerm rows left right a b i j k *
        (((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) *
          principalTruncation (fun P : primePool {left j*right k} => P.val) Finset.univ W
            (Real.sqrt (F*(Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ)/
              (M*(Ideal.absNorm (rows i):ℝ)))) (Z i)) =
      paperRadialFourier W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i):ℝ)):ℝ):ℂ)*primePoolDensity (left j*right k)) -
      paperRadialFourier W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ∑ d ∈ idealDivisors (left j*right k), if Z i < (Ideal.absNorm d:ℝ) then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) -
      W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ∑ d ∈ idealDivisors (left j*right k), if (Ideal.absNorm d:ℝ) ≤ Z i then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) else 0) := by
    by_cases hc : IsCoprime (left j) (right k)
    · have hsq : Squarefree (left j*right k) :=
        squarefree_mul_iff.mpr ⟨hc.isRelPrime,(hleft j).2.1,(hright k).2.1⟩
      rw [principalTruncation_scaled _ hsq,dual_principal_prefactor_identity M F (Ideal.absNorm (rows i))
        (Ideal.absNorm (left j)) (Ideal.absNorm (right k)) hM hF
        (hpos _ (hrows i)) (hpos _ (hleft j).1) (hpos _ (hright k).1)]
      ring
    · have hz : unrestrictedPairTerm rows left right a b i j k = 0 := by
        simp only [unrestrictedPairTerm,hc,ite_false]
      simp only [hz,zero_mul,mul_zero,sub_zero]
  unfold unrestrictedDualPrincipalTruncation
  simp_rw [ht]
  simp only [unrestrictedPrincipalDensity,unrestrictedLargePrincipalSum,unrestrictedSmallPrincipalSum,
    Finset.sum_sub_distrib,Finset.mul_sum]

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson UnrestrictedIdealReindex GaussGeneratorTransport

theorem dualPrincipalIdeal_truncated_all_conductors
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (V : 𝓢(ℝ,ℂ)) (X Y Z lengthScale : ℝ) (hX : 0<X) :
    dualPrincipalIdeal I J V X = (6:ℂ)⁻¹ *
      (principalTruncation (fun P : primePool {I*J} => P.val) Finset.univ V X Z +
       middleTruncation (fun P : primePool {I*J} => P.val) Finset.univ V X Y Z lengthScale +
       truncationError (fun P : primePool {I*J} => P.val) Finset.univ V X Y Z lengthScale) := by
  let P := fun P : primePool {I*J} => P.val
  let f : O → ℂ := fun z => rowCoprimeMask P Finset.univ z *
    (if z=0 then 0 else V (‖eisEmbedding z‖^2/X))
  have hV : Summable (fun z : O => ‖V (‖eisEmbedding z‖^2/X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hV
    intro z
    dsimp only [f]
    by_cases hz : z=0
    · simp only [hz,ite_true,mul_zero,norm_zero]
      exact norm_nonneg _
    · rw [ite_eq_right hz,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (QuadraticUnitInvariance.rowCoprimeMask_norm_le_one P Finset.univ z)
  have h0 : f 0=0 := by simp only [f,ite_true,mul_zero]
  have hu (u : Oˣ) (z : O) : f (u.val*z)=f z := by
    dsimp only [f]
    rw [QuadraticUnitInvariance.rowCoprimeMask_unit_mul,norm_eisEmbedding_unit_mul]
    simp only [mul_eq_zero,u.ne_zero,false_or]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  have hm (z : O) : rowCoprimeMask P Finset.univ z=idealZeroMask I z*idealZeroMask J z := by
    rw [singleton_rowCoprimeMask_eq_idealZeroMask,idealZeroMask_mul I J hI.1 hJ.1]
  have hd : (∑' A : NonzeroIdeal, f (idealGenerator A.val))=dualPrincipalIdeal I J V X := by
    unfold dualPrincipalIdeal
    apply tsum_congr
    intro A
    simp only [f,hm,ite_eq_right (idealGenerator_ne_zero A.val A.property),idealGenerator_norm_sq]
  rw [hd] at he
  have hs : principalTruncation P Finset.univ V X Z + middleTruncation P Finset.univ V X Y Z lengthScale +
      truncationError P Finset.univ V X Y Z lengthScale = ∑' z : O, f z := by
    unfold truncationError
    dsimp only [f]
    ring
  change dualPrincipalIdeal I J V X=(6:ℂ)⁻¹ *
    (principalTruncation P Finset.univ V X Z + middleTruncation P Finset.univ V X Y Z lengthScale +
      truncationError P Finset.univ V X Y Z lengthScale)
  rw [hs,he]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem unrestrictedDualPrincipal_error_uniform (l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n],
      ∀ (ε : ℝ) (hε : 0 < ε) (B N M F T : ℝ),
        1 ≤ B → 1 ≤ N → 0 < M → 0 < F → 4 ≤ T →
        ∀ (rows : m → Ideal O) (cols : n → Ideal O),
          Function.Injective rows → Function.Injective cols →
          (∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B) →
          (∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
          ∀ (a : n → ℂ) (W : 𝓢(ℝ, ℂ)),
          ‖unrestrictedDualPrincipalErrorSum rows cols a W M F N T‖ ≤
            16384 * B * N *
              ((2 * M / (F * N)) * ((supportConstant ε hε * (N * N) ^ ε) *
                (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l)) *
              ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := primePool_symmetric_error_bound l
  refine ⟨s, C, hC, ?_⟩
  intro m n _ _ _ _ ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols a W
  let E₀ := (supportConstant ε hε * (N * N) ^ ε) *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l
  let error : m → n → n → ℂ := fun i j k =>
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))
  have hsc := (supportConstant_pos ε hε).le
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖ ≤ (2 * M / (F * N)) * E₀ := by
    have hi : 0 < (Ideal.absNorm (rows i) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    obtain ⟨hX₀, hlo, hhi⟩ := dual_truncation_reference_bounds M F (Ideal.absNorm (rows i)) N
      (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k)) hM hF hi (by linarith) (hcols j).2 (hcols k).2
    have hh := hb ε hε (cols j * cols k) (mul_ne_zero (hcols j).1.1 (hcols k).1.1) W
      _ _ T hX₀ hlo hhi hT
    simp only [map_mul, Nat.cast_mul] at hh
    have he : ‖truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4)‖ ≤ E₀ := by
      apply hh.trans
      dsimp only [E₀]
      gcongr
      · exact (hcols j).2.2
      · exact (hcols k).2.2
    dsimp only [error]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul
      (dual_truncation_prefactor_bound M F N (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k))
        hM hF (by linarith) (hcols j).2 (hcols k).2) he (norm_nonneg _) (by positivity)
  exact unrestricted_pair_error_ideal_bound rows cols hr hc B N hB hN hrows
    (fun j => ⟨(hcols j).1.1, (hcols j).2.2⟩) a _ (by positivity) error herr

section
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def retainedDualPrincipalSum (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M F : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k *
    (((M/(Real.sqrt ((Ideal.absNorm (cols j):ℝ)*(Ideal.absNorm (cols k):ℝ))*F):ℝ):ℂ) *
      dualPrincipalIdeal (cols j) (cols k) W
        (Real.sqrt (F*(Ideal.absNorm (cols j):ℝ)*(Ideal.absNorm (cols k):ℝ)/
          (M*(Ideal.absNorm (rows i):ℝ)))))

omit [DecidableEq m] [DecidableEq n] in
theorem retainedDualPrincipalSum_symmetric_truncation
    (W : 𝓢(ℝ,ℂ)) (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (M F N T : ℝ) (hM : 0<M) (hF : 0<F)
    (hrows : ∀ i, rows i ≠ 0) (hcols : ∀ j, Admissible (cols j)) :
    (6:ℂ)*retainedDualPrincipalSum W rows cols a M F =
      unrestrictedDualPrincipalTruncation W rows cols cols a a M F
        (fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) +
      unrestrictedDualTruncatedMiddle W rows cols cols a a M F
        (fun i => (N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))/T)
        (fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) (T^4) +
      unrestrictedDualPrincipalErrorSum rows cols a W M F N T := by
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  unfold retainedDualPrincipalSum unrestrictedDualPrincipalTruncation
    unrestrictedDualTruncatedMiddle unrestrictedDualPrincipalErrorSum
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [dualPrincipalIdeal_truncated_all_conductors (cols j) (cols k) (hcols j) (hcols k)]
  · ring
  · have hi := hpos _ (hrows i)
    have hj := hpos _ (hcols j).1
    have hk := hpos _ (hcols k).1
    exact Real.sqrt_pos.mpr (by positivity : 0 <
      F*(Ideal.absNorm (cols j):ℝ)*(Ideal.absNorm (cols k):ℝ)/(M*(Ideal.absNorm (rows i):ℝ)))

end

lemma norm_four_correction_terms (A B C D : ℂ) :
    ‖-A-B+C+D‖ ≤ ‖A‖+‖B‖+‖C‖+‖D‖ := by
  have hab := norm_sub_le (-A) B
  have habc := norm_add_le (-A-B) C
  have habcd := norm_add_le (-A-B+C) D
  simp only [norm_neg] at hab
  linarith

theorem retained_dual_principal_difference (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        {α : ℝ} (hexp : HasSieveExponent α), 1/2 ≤ α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ),
        1≤B → 1≤N → 0<M → 0<F → 4≤T →
      ∀ (rows : m → Ideal O) (cols : n → Ideal O),
        Function.Injective rows → Function.Injective cols →
        (∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B) →
        (∀ j, Admissible (cols j) ∧ N/2 ≤ (Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ) ≤ N) →
        (∀ j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖(6:ℂ)*retainedDualPrincipalSum W rows cols a M F -
          paperRadialFourier W 0*unrestrictedPrincipalDensity rows cols cols a a (M/F)‖ ≤
        ‖paperRadialFourier W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a a) +
        ‖W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F T a a) +
        4*dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F T a a W +
        16384*B*N*((2*M/(F*N))*((supportConstant ε hε*(N*N)^ε)*
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l))*∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,herr⟩ := unrestrictedDualPrincipal_error_uniform l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ α hexp hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols hray a W
  let Z := fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))
  let Y := fun i => (N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))/T
  have hT0 : 0≤T := by linarith
  have hmain := unrestrictedDualPrincipalTruncation_eq W rows cols cols a a M F Z hM hF
    (fun i => (hrows i).1.ne_zero) (fun j => (hcols j).1) (fun k => (hcols k).1)
  have hsplit := retainedDualPrincipalSum_symmetric_truncation W rows cols a M F N T hM hF
    (fun i => (hrows i).1.ne_zero) (fun j => (hcols j).1)
  change (6:ℂ)*retainedDualPrincipalSum W rows cols a M F =
    unrestrictedDualPrincipalTruncation W rows cols cols a a M F Z +
    unrestrictedDualTruncatedMiddle W rows cols cols a a M F Y Z (T^4) +
    unrestrictedDualPrincipalErrorSum rows cols a W M F N T at hsplit
  have heq : (6:ℂ)*retainedDualPrincipalSum W rows cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity rows cols cols a a (M/F) =
      -(paperRadialFourier W 0*unrestrictedLargePrincipalSum rows cols cols a a M F Z) -
      (W 0*unrestrictedSmallPrincipalSum rows cols cols a a M F (fun d i => (Ideal.absNorm d:ℝ)≤Z i)) +
      unrestrictedDualTruncatedMiddle W rows cols cols a a M F Y Z (T^4) +
      unrestrictedDualPrincipalErrorSum rows cols a W M F N T := by
    rw [hsplit,hmain]
    ring
  have hl := hexp.unrestricted_large_principal_sum hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
    rows cols cols hr hc hc hrows (fun j => ⟨(hcols j).1,(hcols j).2.2⟩)
    (fun k => ⟨(hcols k).1,(hcols k).2.2⟩) hray a a Z (fun _ => le_rfl)
  have hs := hexp.unrestricted_small_principal_sum hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT0
    rows cols cols hr hc hc hrows hcols hcols hray a a (fun d i => (Ideal.absNorm d:ℝ)≤Z i)
    (fun _ _ h => h)
  have hm := hexp.unrestricted_dual_truncated_middle hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT0
    rows cols cols hr hc hc hrows a a W Y Z (T^4) hcols hcols hray (fun _ => le_rfl)
  have he := herr ε hε B N M F T hB hN hM hF hT rows cols hr hc
    (fun i => ⟨(hrows i).1.ne_zero,(hrows i).2.2⟩) hcols a W
  rw [heq]
  apply (norm_four_correction_terms _ _ _ _).trans
  rw [norm_mul,norm_mul]
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hl (norm_nonneg _))
    (mul_le_mul_of_nonneg_left hs (norm_nonneg _))) hm) he

lemma sum_ideal_subtype_dyadic {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (K : ℝ) (f : Ideal O → A) :
    (∑ I : S, f I.val) = ∑ j : Fin (columnDyadicLength K+1),
      ∑ I : divisorDyadicBin S K j, f I.val := by
  classical
  rw [Finset.sum_coe_sort S f,sum_divisorDyadicBins S K f]
  exact Finset.sum_congr rfl (fun j _ => (Finset.sum_coe_sort (divisorDyadicBin S K j) f).symm)

def retainedDualMajorant {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ‖paperRadialFourier W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a a) +
  ‖W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F T a a) +
  4*dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F T a a W +
  16384*B*N*((2*M/(F*N))*((supportConstant ε hε*(N*N)^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l))*∑ j, ‖a j‖^2

lemma retainedDualMajorant_nonneg {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0≤N) (hM : 0≤M) (hF : 0≤F) (hT : 0≤T) :
    0≤retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a W := by
  have hs0 := smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F (1/2) a a hB hN hM hF (by norm_num)
  have hs1 := smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F T a a hB hN hM hF hT
  have hm := dualMiddleMajorant_nonneg hexp deltaLoss hδ ε hε B N M F T a a W hB hN hM hF hT
  have hc := (supportConstant_pos ε hε).le
  unfold retainedDualMajorant
  positivity

lemma retainedDualMajorant_mono {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B' B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB' : 0≤B') (hB : B'≤B) (hN : 0≤N) (hM : 0≤M) (hF : 0≤F) (hT : 0≤T) :
    retainedDualMajorant s C l hexp deltaLoss hδ ε hε B' N M F T a W ≤
      retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a W := by
  have hB0 := hB'.trans hB
  have hα0 : 0≤α-1/2 := by linarith
  have he := divisorEnergyFactor_nonneg ε hε N a a
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hs := (supportConstant_pos ε hε).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  unfold retainedDualMajorant smallPrincipalMajorant dualMiddleMajorant
  gcongr

lemma retainedDualPrincipalDifference_dyadic {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (S : Finset (Ideal O)) (K : ℝ) (cols : n → Ideal O) (a : n → ℂ) (M F : ℝ) :
    (6:ℂ)*retainedDualPrincipalSum W (fun I : S => I.val) cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity (fun I : S => I.val) cols cols a a (M/F) =
    ∑ j : Fin (columnDyadicLength K+1),
      ((6:ℂ)*retainedDualPrincipalSum W (fun I : divisorDyadicBin S K j => I.val) cols a M F -
        paperRadialFourier W 0*unrestrictedPrincipalDensity
          (fun I : divisorDyadicBin S K j => I.val) cols cols a a (M/F)) := by
  classical
  have h := sum_ideal_subtype_dyadic (A := ℂ) S K (fun I =>
    (6:ℂ)*retainedDualPrincipalSum W (fun _ : Unit => I) cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity (fun _ : Unit => I) cols cols a a (M/F))
  simpa only [retainedDualPrincipalSum,unrestrictedPrincipalDensity,unrestrictedPairTerm,
    Finset.mul_sum,←Finset.sum_sub_distrib,Fintype.sum_unique] using h

theorem retained_dual_principal_global (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (K N M F T : ℝ),
        1≤K → 1≤N → 0<M → 0<F → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀ j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀ j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖(6:ℂ)*retainedDualPrincipalSum W (fun I : squarefreeIdealRange K => I.val) cols a M F -
          paperRadialFourier W 0*unrestrictedPrincipalDensity
            (fun I : squarefreeIdealRange K => I.val) cols cols a a (M/F)‖ ≤
        (columnDyadicLength K+1:ℕ)*retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M F T a W := by
  obtain ⟨s,C,hC,hbound⟩ := retained_dual_principal_difference l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε K N M F T hK hN hM hF hT cols hc hcols hray a W
  classical
  let S := squarefreeIdealRange K
  let R := retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M F T a W
  have hS (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K := by
    have hi := mem_squarefreeIdealRange.mp hI
    refine ⟨?_,hi.2⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hi.1.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))
  have hR : 0≤R := retainedDualMajorant_nonneg s C hC.le l hexp deltaLoss hδ ε hε (2*K) N M F T a W
    (by linarith) (by linarith) hM.le hF.le (by linarith)
  have hb (j : Fin (columnDyadicLength K+1)) :
      ‖(6:ℂ)*retainedDualPrincipalSum W (fun I : divisorDyadicBin S K j => I.val) cols a M F -
        paperRadialFourier W 0*unrestrictedPrincipalDensity
          (fun I : divisorDyadicBin S K j => I.val) cols cols a a (M/F)‖ ≤ R := by
    by_cases hj : (divisorDyadicBin S K j).Nonempty
    · let B := 2*divisorDyadicScale j.val
      have hB : 1≤B := by dsimp only [B]; linarith [divisorDyadicScale_ge_one j.val]
      have hBK : B≤2*K := by
        dsimp only [B]
        exact mul_le_mul_of_nonneg_left (divisorDyadicBin_scale_le S K hS j hj) (by norm_num)
      have hrows (I : divisorDyadicBin S K j) : Squarefree I.val ∧
          B/2≤(Ideal.absNorm I.val:ℝ) ∧ (Ideal.absNorm I.val:ℝ)≤B := by
        have hi := divisorDyadicBin_bounds S K hS j I.val I.property
        refine ⟨(mem_squarefreeIdealRange.mp (Finset.mem_filter.mp I.property).1).1,?_,hi.2⟩
        dsimp only [B]
        linarith
      have hh := hbound hexp hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
        (fun I : divisorDyadicBin S K j => I.val) cols Subtype.val_injective hc hrows hcols hray a W
      apply hh.trans
      exact retainedDualMajorant_mono s C hC.le l hexp hα deltaLoss hδ ε hε B (2*K) N M F T a W
        (by linarith) hBK (by linarith) hM.le hF.le (by linarith)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hj
      have : IsEmpty (divisorDyadicBin S K j) := by
        refine ⟨fun I => ?_⟩
        have hi := I.property
        simp only [he,Finset.notMem_empty] at hi
      simpa only [retainedDualPrincipalSum,unrestrictedPrincipalDensity,Finset.univ_eq_empty,
        Finset.sum_empty,mul_zero,sub_zero,norm_zero] using hR
  rw [retainedDualPrincipalDifference_dyadic W (squarefreeIdealRange K) K cols a M F]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength K+1), R := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,R]

end

open scoped BigOperators Classical
open ActualEisensteinCubic QuadraticSquarefreeKernel CompletedGauss

def highSquareParts (M K : ℝ) : Finset (Ideal O) := (highKernelRange M K).image squarePart

theorem highSquareParts_bounds (M K : ℝ) (hK : 0 < K) (A : Ideal O)
    (hA : A ∈ highSquareParts M K) :
    Supported A ∧ 1 ≤ (Ideal.absNorm A : ℝ) ∧
    (Ideal.absNorm A : ℝ) ≤ Real.sqrt (M/K) ∧
    1 ≤ M/(Ideal.absNorm A : ℝ)^2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨hs,hN,hlarge⟩ := mem_highKernelRange.mp hI
  have hparts := (supported_square_parts I).mp hs
  have hna : 1 ≤ (Ideal.absNorm (squarePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hparts.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hnb : 1 ≤ (Ideal.absNorm (squarefreePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hparts.2.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hprod : (Ideal.absNorm (squarePart I) : ℝ)^2*(Ideal.absNorm (squarefreePart I) : ℝ) ≤ M := by
    have he : (Ideal.absNorm (squarePart I) : ℝ)^2*(Ideal.absNorm (squarefreePart I) : ℝ) =
        (Ideal.absNorm I : ℝ) := by exact_mod_cast norm_decomposition I
    rwa [he]
  have hsquare : (Ideal.absNorm (squarePart I) : ℝ)^2 ≤ M/K := by
    apply (le_div_iff₀ hK).mpr
    exact (mul_le_mul_of_nonneg_left hlarge.le (sq_nonneg _)).trans hprod
  have hM : 0 ≤ M/K := (sq_nonneg _).trans hsquare
  have hroot : (Ideal.absNorm (squarePart I) : ℝ) ≤ Real.sqrt (M/K) := by
    nlinarith [Real.sq_sqrt hM,Real.sqrt_nonneg (M/K)]
  refine ⟨hparts.1,hna,hroot,?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (Ideal.absNorm (squarePart I) : ℝ)^2)).mpr
  nlinarith

theorem highSquarePart_fiber_row_bounds (M K : ℝ) (A I : Ideal O)
    (hI : I ∈ highKernelRange M K) (hA : squarePart I = A) :
    Admissible (squarefreePart I) ∧
      (Ideal.absNorm (squarefreePart I) : ℝ) ≤ M/(Ideal.absNorm A : ℝ)^2 := by
  have hs := (mem_highKernelRange.mp hI).1
  have hparts := (supported_square_parts I).mp hs
  have hna : 0 < (Ideal.absNorm A : ℝ) := by
    rw [←hA]
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hparts.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  refine ⟨hparts.2,(le_div_iff₀ (sq_pos_of_pos hna)).mpr ?_⟩
  have he : (Ideal.absNorm A : ℝ)^2*(Ideal.absNorm (squarefreePart I) : ℝ) = (Ideal.absNorm I : ℝ) := by
    rw [←hA]
    exact_mod_cast norm_decomposition I
  simpa only [mul_comm,he] using (mem_highKernelRange.mp hI).2.1

def highSquarePartFiber (M K : ℝ) (A : Ideal O) : Finset (Ideal O) :=
  (highKernelRange M K).filter (fun I => squarePart I = A)

theorem highSquarePartFiber_energy (M N K : ℝ) (A : Ideal O)
    (a : idealRange N → ℂ) :
    (∑ I ∈ highSquarePartFiber M K A,
      ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖^2) ≤
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N * ∑ J, ‖a J‖^2 := by
  let S := highSquarePartFiber M K A
  let b : idealRange N → ℂ := fun J => idealZeroMask J.val (primaryGenerator A) * a J
  let B : Matrix S (idealRange N) ℂ := fun I J =>
    quadraticRow J.val (primaryGenerator (squarefreePart I.val))
  have hinj : Function.Injective (fun I : S => squarefreePart I.val) := by
    intro I I' heq
    dsimp only at heq
    apply Subtype.ext
    have hI := (Finset.mem_filter.mp I.property).2
    have hI' := (Finset.mem_filter.mp I'.property).2
    calc
      I.val = A^2 * squarefreePart I.val := by
        simpa only [hI] using (squarePart_sq_mul_squarefreePart I.val).symm
      _ = A^2 * squarefreePart I'.val := by rw [heq]
      _ = I'.val := by simpa only [hI'] using squarePart_sq_mul_squarefreePart I'.val
  have hnorm : ‖FiniteSieveOperator.operator B‖^2 ≤
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N := by
    apply family_squared_norm_le (fun I : S => squarefreePart I.val)
      (fun J : idealRange N => J.val) hinj Subtype.val_injective
    · intro I
      exact highSquarePart_fiber_row_bounds M K A I.val
        (Finset.mem_filter.mp I.property).1 (Finset.mem_filter.mp I.property).2
    · intro J
      exact mem_idealRange.mp J.property
  have hrow (I : S) :
      (∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J) =
      ∑ J : idealRange N, B I J * b J := by
    apply Finset.sum_congr rfl
    intro J _
    have hI := (Finset.mem_filter.mp I.property).2
    have he : I.val = A^2 * squarefreePart I.val := by
      simpa only [hI] using (squarePart_sq_mul_squarefreePart I.val).symm
    rw [he, canonical_quadraticRow_primary_squarefree J.val
      (mem_idealRange.mp J.property).1]
    change _ = quadraticRow J.val (primaryGenerator (squarefreePart I.val)) *
      (idealZeroMask J.val (primaryGenerator A) * a J)
    ring
  have hb (J : idealRange N) : ‖b J‖^2 ≤ ‖a J‖^2 := by
    dsimp only [b]
    unfold idealZeroMask
    split_ifs <;> simp
  rw [← Finset.sum_coe_sort S]
  simp_rw [hrow]
  exact (FiniteSieveOperator.energy_bound B b).trans
    ((mul_le_mul_of_nonneg_right hnorm (by positivity)).trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun J _ => hb J)
        (sieveNorm_nonneg _ _)))

theorem highKernelNorm_le_squarePart_sum (M N K : ℝ) :
    highKernelNorm M N K ≤
      ∑ A ∈ highSquareParts M K, sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N := by
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _
    (Finset.sum_nonneg fun A _ => sieveNorm_nonneg _ _)
  intro a
  simp only [highKernelMatrix]
  rw [Finset.sum_coe_sort (highKernelRange M K)
    (fun I : Ideal O => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖^2)]
  have hmaps : ∀ I ∈ highKernelRange M K, squarePart I ∈ highSquareParts M K :=
    fun I hI => Finset.mem_image_of_mem squarePart hI
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ A ∈ highSquareParts M K,
        sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N * ∑ J, ‖a J‖^2 := by
      apply Finset.sum_le_sum
      intro A hA
      exact highSquarePartFiber_energy M N K A a
    _ = _ := (Finset.sum_mul _ _ _).symm

end CanonicalQuadraticSieve

end

end OAI
