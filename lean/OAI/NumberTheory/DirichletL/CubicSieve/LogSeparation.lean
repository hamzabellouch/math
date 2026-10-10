import OAI.NumberTheory.DirichletL.RowCompletion.SupportBounds
import OAI.NumberTheory.DirichletL.CubicSieve.ReopeningSeparation

namespace OAI

noncomputable section

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CanonicalCubeSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open FourierBridge JointLogSeparation

lemma cube_log_bin (B n : ℝ) (hB : 0 < B) (hn : B ≤ n)
    (hn' : n ≤ Real.exp 1 * B) : Real.log (n/B) ∈ Set.Icc (0:ℝ) 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  constructor
  · exact Real.log_nonneg ((le_div_iff₀ hB).mpr (by simpa using hn))
  · have hh : n/B ≤ Real.exp 1 := (div_le_iff₀ hB).mpr hn'
    have := Real.log_le_log (div_pos hn0 hB) hh
    simpa only [Real.log_exp] using this

lemma cube_log_argument (B ell n q : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) (hq : 0 < q) :
    Real.exp (Real.log (q/ell) + 3*Real.log (n/B)) = q*n^3/(B^3*ell) := by
  rw [Real.exp_add, Real.exp_log (div_pos hq hell)]
  have he : Real.exp (3*Real.log (n/B)) = (n/B)^3 := by
    rw [show (3:ℝ)*Real.log (n/B) =
      Real.log (n/B)+Real.log (n/B)+Real.log (n/B) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hn hB)]
    ring
  rw [he]
  field_simp

lemma cube_half_normalization (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell))⁻¹ * Real.sqrt n =
      (B*Real.sqrt ell)⁻¹ * Real.exp (Real.log (n/B)/2) := by
  have hb0 := (Real.sqrt_pos.mpr hB).ne'
  have he0 := (Real.sqrt_pos.mpr hell).ne'
  have hs : Real.sqrt (B^3*ell) = B*Real.sqrt B*Real.sqrt ell := by
    rw [show B^3*ell=B^2*(B*ell) by ring,
      Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB.le, Real.sqrt_mul hB.le]
    ring
  have hnexp : Real.exp (Real.log (n/B)/2) = Real.sqrt n/Real.sqrt B := by
    rw [← sqrt_exp_half, Real.exp_log (div_pos hn hB), Real.sqrt_div hn.le]
  rw [hs, hnexp]
  field_simp

lemma cube_half_normalization_complex (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell) : ℂ)⁻¹ * (Real.sqrt n : ℂ) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * (Real.exp (Real.log (n/B)/2) : ℂ) := by
  exact_mod_cast cube_half_normalization B ell n hB hell hn

theorem reopening_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) * W (q*n^3/X) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  have hsep := reopening_separation_with_window W a b ha hs hW V hV
    (Real.log (n/B)) (Real.log (q/ell)) (cube_log_bin B n hB hn hn')
  rw [cube_log_argument B ell n q hB hell hn0 hq] at hsep
  rw [hX, cube_half_normalization_complex B ell n hB hell hn0, mul_assoc, hsep]

lemma completed_cube_half_weight (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    n⁻¹ * (Real.sqrt (X/n^3))⁻¹ = (Real.sqrt X)⁻¹ * Real.sqrt n := by
  have hs : Real.sqrt (n^3) = n*Real.sqrt n := by
    rw [show n^3=n^2*n by ring, Real.sqrt_mul (sq_nonneg n), Real.sqrt_sq hn.le]
  rw [Real.sqrt_div hX.le, hs, inv_div]
  field_simp

lemma completed_cube_half_weight_complex (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ =
      (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) := by
  exact_mod_cast completed_cube_half_weight X n hX hn

theorem completed_cube_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ * W (q/(X/n^3)) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hXp : 0 < X := hX ▸ mul_pos (pow_pos hB _) hell
  rw [completed_cube_half_weight_complex X n hXp (lt_of_lt_of_le hB hn), div_div_eq_mul_div]
  exact reopening_norm_separation W a b ha hs hW V hV B ell X n q hB hell hX hn hn' hq

def separatedCubeCoefficient {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ : ℝ) (v : κ) : ℂ := β v * cubeFrequencyFactor (Real.log (n v/B)) ξ

lemma separatedCubeCoefficient_bound {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ Γ : ℝ) (hB : 0 < B) (hΓ : 0 ≤ Γ) (v : κ)
    (hn : B ≤ n v) (hn' : n v ≤ Real.exp 1*B) (hβ : ‖β v‖ ≤ Γ) :
    ‖separatedCubeCoefficient β n B ξ v‖ ≤ Γ*Real.exp (1/2) := by
  unfold separatedCubeCoefficient
  rw [norm_mul]
  exact mul_le_mul hβ (cubeFrequencyFactor_bound _ ξ (cube_log_bin B _ hB hn hn').2)
    (norm_nonneg _) hΓ

theorem reopening_finite_sum_integrable {κ τ : Type*}
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell : ℝ) (b V : 𝓢(ℝ,ℂ)) :
    Integrable (fun ξ : ℝ => b ξ * ∑v∈Q,∑j∈S,
      separatedCubeCoefficient β n B ξ v * A v j * frequencyTwist V ξ (Real.log (q j/ell))) := by
  have hi : Integrable (fun ξ : ℝ => ∑v∈Q,∑j∈S,
      (β v*A v j)*(b ξ*cubeFrequencyFactor (Real.log (n v/B)) ξ*
        frequencyTwist V ξ (Real.log (q j/ell)))) := by
    apply integrable_finsetSum
    intro v hv
    apply integrable_finsetSum
    intro j hj
    exact (reopening_integrable b V _ _).const_mul _
  convert hi using 1
  funext ξ
  simp only [Finset.mul_sum, separatedCubeCoefficient]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem reopening_finite_sum {κ τ : Type*}
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀v∈Q,B ≤ n v) (hn' : ∀v∈Q,n v ≤ Real.exp 1*B)
    (hq : ∀j∈S,0 < q j) :
    (∑v∈Q,∑j∈S, (β v*A v j)*
      ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3)))) =
    ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ * ∑v∈Q,∑j∈S,
        separatedCubeCoefficient β n B ξ v * A v j *
          frequencyTwist V ξ (Real.log (q j/ell)) := by
  let G : ℝ → κ → τ → ℂ := fun ξ v j => (β v*A v j)*
    (reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
      frequencyTwist V ξ (Real.log (q j/ell)))
  have hi (v : κ) (j : τ) : Integrable (fun ξ => G ξ v j) :=
    (reopening_integrable _ V _ _).const_mul _
  have hterm (v : κ) (hv : v∈Q) (j : τ) (hj : j∈S) :
      (β v*A v j)*((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3))) =
        ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,G ξ v j := by
    rw [completed_cube_norm_separation W a b ha hs hW V hV B ell X (n v) (q j)
      hB hell hX (hn v hv) (hn' v hv) (hq j hj)]
    rw [show (∫ ξ : ℝ,G ξ v j) = (β v*A v j)*∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
          frequencyTwist V ξ (Real.log (q j/ell)) from integral_const_mul _ _]
    ring
  calc
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∑v∈Q,∑j∈S,∫ ξ : ℝ,G ξ v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hterm v hv j hj)
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,∑v∈Q,∑j∈S,G ξ v j := by
      congr 1
      rw [integral_finsetSum _ (fun v hv => integrable_finsetSum _ (fun j hj => hi v j))]
      apply Finset.sum_congr rfl
      intro v hv
      exact (integral_finsetSum _ (fun j hj => hi v j)).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [Finset.mul_sum, separatedCubeCoefficient]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [G]
      ring

end CanonicalCubeSeparation

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight

theorem rowTwist_primary_zero_of_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    rowTwist Ψ m f z (primaryGenerator B) = 0 := by
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryGenerator B=0
  · rw [hg]
    change Ψ 0 * idealRowHom _ (Ideal.span {(0:ActualEisensteinCubic.O)}) = 0
    rw [Ideal.span_singleton_zero]
    change Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O) = 0
    rw [map_zero (idealRowHom _),mul_zero]
  · change Ψ (primaryGenerator B) * idealRowHom _ (Ideal.span {primaryGenerator B}) = 0
    rw [(primaryGenerator_spec B hg).1,idealRowHom_zero_of_dvd _ hP hPB hx,mul_zero]

theorem cubeWeight_zero_of_prime_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    cubeWeight (rowTwist Ψ m f z) B = 0 :=
  cubeWeight_zero_of_mask _ B (rowTwist_primary_zero_of_mask Ψ m f z hP hPB hm)

theorem summand_cube_support (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D)
    (I B : Ideal ActualEisensteinCubic.O) (hn : summand (rowTwist Ψ m f z) W X I B≠0) :
    B∈outsideIdealsUpTo S D := by
  have hI : I≠0 := fun h=>hn (by rw [h,summand_zero_left])
  have hB : B≠0 := fun h=>hn (by rw [h,summand_zero_right])
  have hw : W ((Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X)≠0 :=
    fun h=>hn (summand_zero_window _ W X I B h)
  have hsize := (div_le_iff₀ hX).mp (hW _ hw)
  have hb := (triple_scale_bounds (Ideal.absNorm I:ℝ) (Ideal.absNorm B:ℝ) 1
    (norm_at_least_one I hI) (norm_at_least_one B hB) (by norm_num)).2.1
  simp only [one_pow,mul_one] at hb
  apply mem_outsideIdealsUpTo.mpr
  refine ⟨?_,?_,?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hB (Ideal.absNorm_eq_zero_iff.mp h))
  · exact_mod_cast (hb.trans hsize).trans hD
  · intro P hP hPB
    have hz := cubeWeight_zero_of_prime_mask Ψ m f z (hSp P hP) hPB (hm P hP)
    exact hn (by simp only [summand,hz,mul_zero,zero_mul])

theorem large_cube_sum_comm (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0<X) :
    (∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B) =
      ∑'B:Ideal ActualEisensteinCubic.O,∑'I:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let a : Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O → ℂ := fun p=>largeCubeCoefficient H₀ p.2*summand Ψ W X p.1 p.2
  have hf : (Function.support a).Finite :=
    (completedT_finite_support Ψ W hW X hX).subset (by
      intro p hp
      exact fun h=>hp (by simp only [a,h,mul_zero]))
  have hs : Summable a := summable_of_hasFiniteSupport hf
  let e := Equiv.prodComm (Ideal ActualEisensteinCubic.O) (Ideal ActualEisensteinCubic.O)
  have ht : Summable (fun p=>a (e p)) := e.summable_iff.mpr hs
  calc
    _ = ∑'p:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O,a p := hs.tsum_prod.symm
    _ = ∑'p:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O,a (e p) := (e.tsum_eq a).symm
    _ = _ := ht.tsum_prod

theorem large_cube_sum_finite (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand (rowTwist Ψ m f z) W X I B) =
      ∑B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑'I:Ideal ActualEisensteinCubic.O,summand (rowTwist Ψ m f z) W X I B := by
  rw [large_cube_sum_comm _ W hWc X H₀ hX]
  simp only [tsum_mul_left]
  apply tsum_eq_sum
  intro B hB
  have hz : ∀I:Ideal ActualEisensteinCubic.O,summand (rowTwist Ψ m f z) W X I B=0 := by
    intro I
    by_contra hn
    exact hB (summand_cube_support S D hSp Ψ m f z hm W b X hX hW hD I B hn)
  simp only [hz,tsum_zero,mul_zero]

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O

theorem inner_completed_sum (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (hX : 0<X)
    (B : Ideal ActualEisensteinCubic.O) (hB : B≠0) :
    (∑'I:Ideal ActualEisensteinCubic.O,summand Ψ W X I B) =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        ∑'I:Ideal ActualEisensteinCubic.O,columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3)) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := div_pos hX (pow_pos hN _)
  have ht (I:Ideal ActualEisensteinCubic.O) : summand Ψ W X I B =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        (columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
    have harg : (Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X =
        (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3) := by
      rw [div_div_eq_mul_div]
    have hn := vstar_source_normalization Ψ W (X/(Ideal.absNorm B:ℝ)^3) hY I
    calc
      _ = cubeWeight Ψ B * (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ) *
          Vstar W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
        rw [summand,harg]
        ring
      _ = _ := by rw [hn]; ring
  simp_rw [ht]
  exact tsum_mul_left

theorem outsideCanonicalRow_reopened (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hb : 0 ≤ b) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑B∈outsideIdealsUpTo S D,
        (largeCubeCoefficient H₀ B * cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) B *
          (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) * idealRowHom z B^3 *
          outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm B:ℝ)^3) := by
  rw [outsideCanonicalRow_cube_split S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  rw [large_cube_sum_finite S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W hWc b X H₀ hX hW hD]
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  have hB0 : B≠0 := outsideIdealsUpTo_ne_bot S D B hB
  have hN := norm_at_least_one B hB0
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := by positivity
  have hYX : X/(Ideal.absNorm B:ℝ)^3 ≤ X :=
    div_le_self hX.le (one_le_pow₀ hN)
  have hDY : b*(X/(Ideal.absNorm B:ℝ)^3) ≤ D :=
    (mul_le_mul_of_nonneg_left hYX hb).trans hD
  rw [inner_completed_sum _ W X hX B hB0]
  rw [←outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b
    (X/(Ideal.absNorm B:ℝ)^3) hY hW hDY]
  rw [cubeWeight_row_factor]
  ring

theorem outsideCanonicalRow_reopened_exponents (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hb : 0 ≤ b) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑v∈(outsideIdealsUpTo S D).image (cubeIndex F),
        (largeCubeCoefficient H₀ (cubeIdeal F v) *
          cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) *
          (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹) *
          idealRowHom z (cubeIdeal F v)^3 *
          outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3) := by
  dsimp only
  rw [outsideCanonicalRow_reopened S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD]
  rw [sum_outside_cubeIndex S D]

end

open ActualEisensteinCubic
open CompletedGauss hiding O

theorem cubeWeight_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubeWeight Ψ B‖ ≤ 1/(Ideal.absNorm B:ℝ) := by
  have hang : ‖FiniteGaussPhase.angularFactor (primaryGenerator B)‖ ≤ 1 := by
    by_cases hz : primaryGenerator B=0
    · simp [hz,FiniteGaussPhase.angularFactor]
    · exact (FiniteGaussPhase.norm_angularFactor _ hz).le
  change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator B))^3*
    Ψ (primaryGenerator B)^3/(Ideal.absNorm B:ℂ)‖ ≤ _
  rw [norm_div,norm_mul,norm_pow,norm_pow,norm_star,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) hang)).trans (pow_le_one₀ (norm_nonneg _) (hΨ _))

def cubePhase (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) : ℂ :=
  (Ideal.absNorm B:ℂ)*cubeWeight Ψ B

theorem cubePhase_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubePhase Ψ B‖ ≤ 1 := by
  by_cases hB : B=0
  · simp [hB,cubePhase]
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  rw [cubePhase,norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm B:ℝ)*(1/(Ideal.absNorm B:ℝ)) :=
      mul_le_mul_of_nonneg_left (cubeWeight_norm_le Ψ hΨ B) hN.le
    _ = 1 := by field_simp

theorem cube_weight_scale (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) (hB : B≠0)
    (X : ℝ) (hX : 0<X) :
    cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹ =
      cubePhase Ψ B * (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)/(Real.sqrt X:ℂ) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hs3 : Real.sqrt ((Ideal.absNorm B:ℝ)^3) =
      (Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ) := by
    rw [show (Ideal.absNorm B:ℝ)^3=(Ideal.absNorm B:ℝ)^2*(Ideal.absNorm B:ℝ) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hN]
  have hs : Real.sqrt (X/(Ideal.absNorm B:ℝ)^3) =
      Real.sqrt X/((Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ)) := by
    rw [Real.sqrt_div hX.le,hs3]
  rw [hs,Complex.ofReal_div,Complex.ofReal_mul,cubePhase]
  push_cast
  have hNc : (Ideal.absNorm B:ℂ)≠0 := by exact_mod_cast hN.ne'
  have hsN : (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  have hsX : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  field_simp

def reopenedCubeCoefficient (H₀ : ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) : ℂ :=
  largeCubeCoefficient H₀ B * cubePhase Ψ B

theorem reopenedCubeCoefficient_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀(H₀:ℝ) (Ψ:ActualEisensteinCubic.O →* ℂ), (∀z,‖Ψ z‖≤1) →
      ∀B:Ideal ActualEisensteinCubic.O,B≠0 → ‖reopenedCubeCoefficient H₀ Ψ B‖ ≤ C*(Ideal.absNorm B:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := largeCubeCoefficient_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro H₀ Ψ hΨ B hB
  rw [reopenedCubeCoefficient,norm_mul]
  calc
    _ ≤ ‖largeCubeCoefficient H₀ B‖*1 :=
      mul_le_mul_of_nonneg_left (cubePhase_norm_le Ψ hΨ B) (norm_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using hbound H₀ B hB

theorem reopenedCubeCoefficient_support (H₀:ℝ) (Ψ:ActualEisensteinCubic.O →* ℂ) (B:Ideal ActualEisensteinCubic.O)
    (h:reopenedCubeCoefficient H₀ Ψ B≠0) : B≠0 ∧ H₀ ≤ (Ideal.absNorm B:ℝ) := by
  exact largeCubeCoefficient_support H₀ B (fun hz=>h (by simp only [reopenedCubeCoefficient,hz,zero_mul]))

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels

def childLabelRotation (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O :=
  (z.1,(u : ActualEisensteinCubic.O)^4*(if negative then -z.2 else z.2))

theorem childLabelRotation_injective (u : ActualEisensteinCubic.Oˣ) (negative : Bool) :
    Function.Injective (childLabelRotation u negative) := by
  intro z w he
  have hf := congrArg Prod.fst he
  change z.1=w.1 at hf
  have hs := congrArg Prod.snd he
  change (u : ActualEisensteinCubic.O)^4*(if negative then -z.2 else z.2)=
    (u : ActualEisensteinCubic.O)^4*(if negative then -w.2 else w.2) at hs
  have hz := mul_left_cancel₀ (pow_ne_zero 4 u.ne_zero) hs
  apply Prod.ext hf
  cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,neg_inj] using hz

theorem childLabelRotation_norm (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) :
    ‖eisEmbedding (childLabelRotation u negative z).2‖^2=‖eisEmbedding z.2‖^2 := by
  cases negative <;> simp only [childLabelRotation,Bool.false_eq_true,ite_false,ite_true,
    map_mul,norm_mul,map_pow,norm_pow,GaussGeneratorTransport.norm_eisEmbedding_unit,
    one_pow,one_mul,map_neg,norm_neg]

theorem childLabelRotation_ne_zero (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)
    (hz : z.2≠0) : (childLabelRotation u negative z).2≠0 := by
  apply mul_ne_zero (pow_ne_zero 4 u.ne_zero)
  cases negative <;> simpa using hz

section
variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem fixedChildRow_label_mul (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (u f z : ActualEisensteinCubic.O) :
    fixedChildRow p hp hcop hg pool Ψ m H (u*f) z=
      fixedChildRow p hp hcop hg pool Ψ m H f (u^4*z) := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,finiteSquarefreeRow_mul,row_pow,mul_pow]
  ring

theorem idealChildRow_eq_rotated (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (negative : Bool) (u : ActualEisensteinCubic.Oˣ) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) :
    idealChildRow p hp hcop hg pool Ψ m H negative u z=
      fixedChildRow p hp hcop hg pool Ψ m H
        (ConcretePrimeRowBridge.idealGenerator (childLabelRotation u negative z).1)
        (childLabelRotation u negative z).2 := by
  exact fixedChildRow_label_mul p hp hcop hg pool Ψ m H (u : ActualEisensteinCubic.O) _ _

def canonicalSmoothedEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) : ℝ :=
  (∑I∈labels,nonzeroRowMajorantSum
    (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) K).re

theorem canonicalSmoothedEnergy_nonneg (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    0≤canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K := by
  unfold canonicalSmoothedEnergy
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro I hI
  have he := finite_nonzero_row_energy_le_majorant
    (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) ∅ K hK
    (by simp) (by simp)
  simpa using he

theorem canonicalSmoothedEnergy_zero_correction (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K=
      (∑I∈labels,∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*
        (‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I) z‖^2:ℝ)).re-
      ∑I∈labels,‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I) 0‖^2 := by
  unfold canonicalSmoothedEnergy
  simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re,
    Complex.re_sum,Complex.ofReal_re]

theorem idealChildRow_energy_le_canonical (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (negative : Bool) (u : ActualEisensteinCubic.Oˣ)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (K : ℝ) (hK : 0<K)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    (∑z∈T,‖idealChildRow p hp hcop hg pool Ψ m H negative u z‖^2)≤
      canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K := by
  let f : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O → ℝ := fun z=>
    ‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator z.1) z.2‖^2
  let R := (firstFrequencyDisk K).erase 0
  have hsub : T.image (childLabelRotation u negative)⊆labels.product R := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_product.mpr
    refine ⟨hlabels z hz,Finset.mem_erase.mpr ⟨childLabelRotation_ne_zero u negative z (hzero z hz),?_⟩⟩
    apply (mem_firstFrequencyDisk K _).mpr
    rw [childLabelRotation_norm]
    exact hrows z hz
  calc
    _ = ∑w∈T.image (childLabelRotation u negative),f w := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro z hz
        rw [idealChildRow_eq_rotated]
      · exact fun _ _ _ _ he=>childLabelRotation_injective u negative he
    _ ≤ ∑w∈labels.product R,f w :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>sq_nonneg _)
    _ = ∑I∈labels,∑z∈R,f (I,z) := by rw [Finset.product_eq_sprod,Finset.sum_product]
    _ ≤ ∑I∈labels,(nonzeroRowMajorantSum
        (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) K).re := by
      apply Finset.sum_le_sum
      intro I hI
      apply finite_nonzero_row_energy_le_majorant _ R K hK
      · intro z hz
        rw [←eisEmbedding_norm_sq_eq_absNorm_span]
        exact (mem_firstFrequencyDisk K z).mp (Finset.mem_erase.mp hz).2
      · exact fun z hz=>(Finset.mem_erase.mp hz).1
    _ = _ := by unfold canonicalSmoothedEnergy; rw [Complex.re_sum]

def canonicalLogEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X K : ℝ) : ℝ :=
  canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels (fun S=>V (columnLog p X S)) K

end

def orientedLogProfile (negative : Bool) (V : ℝ → ℂ) : ℝ → ℂ :=
  if negative then fun s=>star (V s) else V

theorem fixedSecondTest_zero_profile {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)
    (V : ℝ → ℂ) (X : ℝ) (negative : Bool) :
    fixedSecondTest p V X 0 0 negative=(fun S=>orientedLogProfile negative V (columnLog p X S)) := by
  funext S
  cases negative <;> simp [fixedSecondTest,orientedLogProfile,JointLogSeparation.fixedColumnTest,FourierBridge.logPhase]

end SecondPassArithmetic

end

end OAI
