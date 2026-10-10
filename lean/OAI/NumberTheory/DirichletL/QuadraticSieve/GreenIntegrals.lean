import OAI.NumberTheory.DirichletL.QuadraticSieve.MiddleWindows

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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_double_sum_real_factor_fun {n p : Type*} [Fintype n] [Fintype p]
    (u z : n → p → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ j, ∑ k, u j k * ((c : ℂ) * z j k)‖ = c * ‖∑ j, ∑ k, u j k * z j k‖ := by
  have he : (∑ j, ∑ k, u j k * ((c : ℂ) * z j k)) =
      (c : ℂ) * ∑ j, ∑ k, u j k * z j k := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualPrincipalKernel (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O)
    (left : n → Ideal O) (right : p → Ideal O) (M F : ℝ) (h : O)
    (d : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  ((Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
    paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ))

def dualProductDivisorMiddleAt (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j * right k then
      originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualProductDivisorMiddleAt W K rows left right a b M F P h := by
  classical
  unfold dualProductDivisorMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_le_window
    (W : 𝓢(ℝ, ℂ)) (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    dualProductDivisorMiddleAt W K rows left right a b M F P h ≤
      dualMiddleWindowAt W S T rows left right a b M F (fun d i => d ∈ K ∧ P d i) h := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P (fun d i j k => dualPrincipalKernel W rows left right M F h d i j k)
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  rw [dualMiddleWindowAt_eq_finset]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : D * E ∈ K
  · by_cases hpi : P (D * E) i
    · simp only [hd, hpi, and_self, ite_true]
      unfold dualPrincipalKernel
      simp only [map_mul, Nat.cast_mul]
      exact norm_double_sum_real_factor_fun _ _ _ (by positivity)
    · simp only [hd, hpi, and_false, ite_false, ite_true]
  · simp only [hd, false_and, ite_false]

theorem HasSieveExponent.dual_product_divisor_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (K : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ d ∈ K, ∀ i, P d i →
      (Ideal.absNorm d : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hs := hexp.dual_middle_pool deltaLoss hδ ε hε S T B N M F U hB hN hM hF hU
    (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2.2))
    (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2.2))
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W (fun d i => d ∈ K ∧ P d i) hleft hright
    (fun D E i hp => hP _ hp.1 i hp.2)
  have hdom (h : {h : O // h ≠ 0}) := dualProductDivisorMiddleAt_le_window W K S T
    rows left right (a h.val) (b h.val) M F P h.val hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
  have ht := Summable.of_nonneg_of_le
    (fun h : {h : O // h ≠ 0} => dualProductDivisorMiddleAt_nonneg W K rows left right
      (a h.val) (b h.val) M F P h.val) hdom hs.1
  exact ⟨ht, (ht.tsum_le_tsum hdom hs.1).trans hs.2⟩

end CanonicalQuadraticSieve

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc in
theorem secondChildColumn_norm_le_test (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m f y : O) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondChildColumn p hp hcop hg Ψ m f y H S‖ ≤ ‖H S‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) S m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondChildColumn,norm_mul,norm_pow,columnCoefficient_norm_one p hp hcop hg hc]
  calc
    _ ≤ 1 * 1 * 1 * 1^4 * 1 * ‖H S‖ := by
      gcongr <;> first
        | exact hΨ _
        | exact hm
        | exact finiteSquarefreeRow_norm_le_one _ hg S f
        | exact finiteSquarefreeRow_norm_le_one _ hg S y
    _ = _ := by ring

include hc in

theorem fixedChildRow_elementary
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m f y : O) (H : Finset ι → ℂ) (X M : ℝ) (hX : 1 ≤ X) (hM : 0 ≤ M)
    (hH : ∀ S, ‖H S‖ ≤ M) (hSupp : ∀ S, H S ≠ 0 → primeProductNorm p S ≤ X) :
    ‖fixedChildRow p hp hcop hg F Ψ m H f y‖ ≤ 128 * X * M := by
  have heq : fixedChildRow p hp hcop hg F Ψ m H f y =
      ∑ S ∈ boundedPrimeSupports p F X, secondChildColumn p hp hcop hg Ψ m f y H S := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hn
    have hHS : H S = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hS,hSupp S h⟩)
    simp only [secondChildColumn,hHS,mul_zero]
  rw [heq]
  calc
    _ ≤ ∑ S ∈ boundedPrimeSupports p F X, ‖secondChildColumn p hp hcop hg Ψ m f y H S‖ := norm_sum_le _ _
    _ ≤ ∑ S ∈ boundedPrimeSupports p F X, M :=
      Finset.sum_le_sum (fun S hS => (secondChildColumn_norm_le_test p hp hcop hg hc Ψ hΨ m f y H S).trans (hH S))
    _ = ((boundedPrimeSupports p F X).card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F X hX) hM

end SecondPassArithmetic

namespace DescentFiberCost
open ActualEisensteinCubic ConcreteTraceCRT
open ShortDraftLatticeCount ActualEisensteinCoordinates

theorem finite_element_count_real (S : Finset O) (K : ℝ) (hK : 1 ≤ K)
    (hS : ∀ z ∈ S, ‖eisEmbedding z‖^2 ≤ K) : (S.card : ℝ) ≤ 128*K := by
  have hbound : ∀ z ∈ S, q (coords z) ≤ (⌊K⌋₊ : ℕ) := by
    intro z hz
    have hq : (qNat z : ℝ) ≤ K := by
      rw [qNat_eq_absNorm_span, ← eisEmbedding_norm_sq_eq_absNorm_span]
      exact hS z hz
    have hn := Nat.le_floor hq
    have he : (qNat z : ℤ) = q (coords z) := Int.toNat_of_nonneg (qO_nonneg z)
    rw [← he]
    exact_mod_cast hn
  have hcard := actual_eisenstein_count S ⌊K⌋₊ hbound
  have hr : (S.card : ℝ) ≤ 64*((⌊K⌋₊ : ℝ)+1) := by exact_mod_cast hcard
  have hf : (⌊K⌋₊ : ℝ) ≤ K := Nat.floor_le (by linarith)
  linarith

theorem finite_label_row_count (T : Finset (Ideal O × O)) (F K : ℝ)
    (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hT : ∀ z ∈ T, z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖eisEmbedding z.2‖^2 ≤ K) :
    (T.card : ℝ) ≤ 128^2 * F * K := by
  let I := T.image Prod.fst
  let R := T.image Prod.snd
  have hI : (I.card : ℝ) ≤ 128*F := by
    apply finite_ideal_count_real I F hF
    · intro J hJ
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hJ
      exact (hT z hz).1
    · intro J hJ
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hJ
      exact (hT z hz).2.1
  have hR : (R.card : ℝ) ≤ 128*K := by
    apply finite_element_count_real R K hK
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    exact (hT z hz).2.2
  have hsub : T ⊆ I ×ˢ R := by
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  have hn := Finset.card_le_card hsub
  rw [Finset.card_product] at hn
  calc
    _ ≤ (I.card : ℝ) * R.card := by exact_mod_cast hn
    _ ≤ (128*F)*(128*K) := mul_le_mul hI hR (Nat.cast_nonneg _) (by linarith)
    _ = _ := by ring

end DescentFiberCost

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open FirstPassCubeLabels (primeProductNorm columnLog)

theorem childEnergy_elementary_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X F K A M a b : ℝ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (_hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV : ∀ s, ‖V s‖ ≤ M) (hVsupp : ∀ s, V s ≠ 0 → |s| ≤ A)
    (hT : ∀ z ∈ T, z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b / (X*F) ≤
      6 * 128^4 * K * (max 1 (X*Real.exp A))^2 * M^2 / X := by
  let H := fixedSecondTest p V X a b testNegative
  let Y := max 1 (X*Real.exp A)
  have hX0 : 0 < X := hX
  have hF0 : 0 < F := by linarith
  have hY : 1 ≤ Y := le_max_left _ _
  have hH : ∀ S, ‖H S‖ ≤ M := by
    intro S
    cases testNegative <;>
      simpa only [H,fixedSecondTest,Bool.false_eq_true,ite_false,ite_true,
        fixedColumnTest,norm_mul,norm_star,FourierBridge.logPhase_norm,mul_one] using hV (columnLog p X S)
  have hSupp : ∀ S, H S ≠ 0 → primeProductNorm p S ≤ Y := by
    intro S hS
    have hv : V (columnLog p X S) ≠ 0 := by
      intro hz
      apply hS
      cases testNegative <;> simp [H,fixedSecondTest,fixedColumnTest,hz]
    exact (columnLog_norm_upper p hp X A hX0 S ((le_abs_self _).trans (hVsupp _ hv))).trans
      (le_max_right _ _)
  have hrow (f y : O) : ‖fixedChildRow p hp hcop hg pool Ψ m H f y‖ ≤ 128*Y*M :=
    fixedChildRow_elementary p hp hcop hg hc hinj pool Ψ hΨ m f y H Y M hY hM hH hSupp
  have hu (u : Oˣ) : (∑ z ∈ T, ‖idealChildRow p hp hcop hg pool Ψ m H rowNegative u z‖^2) ≤
      (T.card : ℝ) * (128*Y*M)^2 := by
    calc
      _ ≤ ∑ z ∈ T, (128*Y*M)^2 := by
        apply Finset.sum_le_sum
        intro z hz
        exact pow_le_pow_left₀ (norm_nonneg _) (hrow _ _) 2
      _ = _ := by simp
  have he := idealChildRow_unit_energy_le p hp hcop hg pool Ψ m H rowNegative T
    ((T.card : ℝ)*(128*Y*M)^2) hu
  change childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b ≤ _ at he
  have ht := DescentFiberCost.finite_label_row_count T F K hF hK hT
  apply (div_le_iff₀ (mul_pos hX0 hF0)).mpr
  calc
    _ ≤ 6*((T.card : ℝ)*(128*Y*M)^2) := he
    _ ≤ 6*((128^2*F*K)*(128*Y*M)^2) := by gcongr
    _ = (6*128^4*K*(max 1 (X*Real.exp A))^2*M^2/X)*(X*F) := by
      dsimp [Y]
      field_simp

end SecondPassIntegration

namespace ShortDraftLatticeCount
open ActualEisensteinCubic ActualEisensteinCoordinates ConcreteTraceCRT

theorem rowNormBall_norm_sq_le (H : ℕ) (k : ActualEisensteinCubic.O) (hk : k ∈ rowNormBall H) :
    ‖eisEmbedding k‖^2 ≤ 3*((H : ℝ)+1)^2 := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hv
  obtain ⟨haL,haU⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hbL,hbU⟩ := Finset.mem_Icc.mp hb
  have ha2 : v.1^2 ≤ ((H : ℤ)+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haU) (show 0 ≤ (H : ℤ)+1+v.1 by linarith)]
  have hb2 : v.2^2 ≤ ((H : ℤ)+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbU) (show 0 ≤ (H : ℤ)+1+v.2 by linarith)]
  have hq : v.1*v.1-v.1*v.2+v.2*v.2 ≤ 3*((H : ℤ)+1)^2 := by
    nlinarith [sq_nonneg (v.1+v.2)]
  rw [eisEmbedding_eval_norm_sq]
  exact_mod_cast hq

end ShortDraftLatticeCount
namespace SecondPassArithmetic
open ActualEisensteinCubic ConcreteTraceCRT

theorem secondFrequencyCutoff_norm_sq_le (scale H : ℝ) (k : ActualEisensteinCubic.O)
    (hk : k ∈ secondFrequencyCutoff scale H) :
    ‖eisEmbedding k‖^2 ≤ 3*((⌈H/scale⌉₊ : ℝ)+1)^2 :=
  ShortDraftLatticeCount.rowNormBall_norm_sq_le _ k hk

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma green_identity_interval (f g : ℝ → ℂ) (a b : ℝ)
    (hf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ f x)
    (hg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ g x)
    (hdf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv f) x)
    (hdg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv g) x)
    (hif : IntervalIntegrable (deriv (deriv f)) volume a b)
    (hig : IntervalIntegrable (deriv (deriv g)) volume a b) :
    (∫x in a..b,deriv (deriv f) x*star (g x)-f x*star (deriv (deriv g) x)) =
      (deriv f b*star (g b)-f b*star (deriv g b)) -
      (deriv f a*star (g a)-f a*star (deriv g a)) := by
  have hfc : ContinuousOn f (Set.uIcc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    convert (((hdf x hx).hasDerivAt.mul (hg x hx).hasDerivAt.star).sub
      ((hf x hx).hasDerivAt.mul (hdg x hx).hasDerivAt.star)) using 1 ; ring
  · have hstar : IntervalIntegrable (fun x => star (deriv (deriv g) x)) volume a b := by
      apply hig.mono_fun
        ((aestronglyMeasurable_deriv (deriv g) _).star)
      exact Filter.Eventually.of_forall (fun x => by simp only [Pi.star_apply,norm_star,le_refl])
    exact (hif.mul_continuousOn hgc.star).sub (hstar.continuousOn_mul hfc)

lemma axisSlice_update (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) :
    axisSlice f (Function.update p j t) j = axisSlice f p j := by
  funext z
  simp only [axisSlice,Function.update_idem]

theorem actual_axis_local_regular (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε C : ℝ, 0<ε ∧ ∀t∈Metric.ball (p j) ε,
      0<(Function.update p j t) 2 ∧
      DifferentiableAt ℝ (axisSlice (upperEisensteinField s) p j) t ∧
      DifferentiableAt ℝ (deriv (axisSlice (upperEisensteinField s) p j)) t ∧
      ‖deriv (deriv (axisSlice (upperEisensteinField s) p j)) t‖≤C := by
  obtain ⟨ε,hε,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := axis_summable_derivative_bounds s hs p hv j
  refine ⟨ε,∑'r,M₂ r,hε,?_⟩
  intro t ht
  have hpos := (hbound t ht).1
  have hterms := eisenstein_axis_termwise s hs (Function.update p j t) hpos j
  simp only [axisSlice_update,Function.update_self] at hterms
  have heq := axisSlice_eventuallyEq_of_positive (upperEisensteinField s) (smoothEisenstein s)
    (fun q hq => upperEisensteinField_eq_smooth s q hq) (Function.update p j t) hpos j
  simp only [axisSlice_update,Function.update_self] at heq
  refine ⟨hpos,(hterms.2.2.1.congr_of_eventuallyEq heq).differentiableAt,
    (hterms.2.2.2.congr_of_eventuallyEq heq.deriv).differentiableAt,?_⟩
  rw [heq.deriv.deriv_eq,hterms.2.2.2.deriv]
  exact tsum_of_norm_bounded hM₂.hasSum (fun r => ((hbound t ht).2 r).2.2)

lemma intervalIntegrable_second_of_bound (f : ℝ → ℂ) (C a b : ℝ)
    (hbound : ∀x∈Set.uIcc a b, ‖deriv (deriv f) x‖≤C) :
    IntervalIntegrable (deriv (deriv f)) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume a b).mono_fun
    (aestronglyMeasurable_deriv _ _)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  exact (hbound x (Set.uIoc_subset_uIcc hx)).trans (le_abs_self C)

theorem actual_eisenstein_local_green (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε : ℝ, 0<ε ∧ ∀a b : ℝ, Set.uIcc a b ⊆ Metric.ball (p j) ε →
      (∫x in a..b,
        deriv (deriv (axisSlice (upperEisensteinField s) p j)) x *
          star (axisSlice (upperEisensteinField t) p j x) -
        axisSlice (upperEisensteinField s) p j x *
          star (deriv (deriv (axisSlice (upperEisensteinField t) p j)) x)) =
      (deriv (axisSlice (upperEisensteinField s) p j) b *
          star (axisSlice (upperEisensteinField t) p j b) -
        axisSlice (upperEisensteinField s) p j b *
          star (deriv (axisSlice (upperEisensteinField t) p j) b)) -
      (deriv (axisSlice (upperEisensteinField s) p j) a *
          star (axisSlice (upperEisensteinField t) p j a) -
        axisSlice (upperEisensteinField s) p j a *
          star (deriv (axisSlice (upperEisensteinField t) p j) a)) := by
  obtain ⟨εs,Cs,hεs,hregs⟩ := actual_axis_local_regular s hs p hv j
  obtain ⟨εt,Ct,hεt,hregt⟩ := actual_axis_local_regular t ht p hv j
  refine ⟨min εs εt,lt_min hεs hεt,?_⟩
  intro a b hab
  have hsa (x : ℝ) (hx : x∈Set.uIcc a b) := hregs x
    (Metric.ball_subset_ball (min_le_left _ _) (hab hx))
  have hta (x : ℝ) (hx : x∈Set.uIcc a b) := hregt x
    (Metric.ball_subset_ball (min_le_right _ _) (hab hx))
  apply green_identity_interval
  · exact fun x hx => (hsa x hx).2.1
  · exact fun x hx => (hta x hx).2.1
  · exact fun x hx => (hsa x hx).2.2.1
  · exact fun x hx => (hta x hx).2.2.1
  · exact intervalIntegrable_second_of_bound _ Cs a b (fun x hx => (hsa x hx).2.2.2)
  · exact intervalIntegrable_second_of_bound _ Ct a b (fun x hx => (hta x hx).2.2.2)

lemma actual_axis_differentiable_at (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (ht : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (axisSlice (upperEisensteinField s) p j) t ∧
      DifferentiableAt ℝ (deriv (axisSlice (upperEisensteinField s) p j)) t := by
  obtain ⟨ε,C,hε,hreg⟩ := actual_axis_local_regular s hs (Function.update p j t) ht j
  have h := hreg t (by simpa only [Function.update_self] using Metric.mem_ball_self hε)
  simp only [axisSlice_update] at h
  exact ⟨h.2.1,h.2.2.1⟩

lemma actual_axis_second_locallyIntegrable (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (j : Fin 3) :
    LocallyIntegrableOn (deriv (deriv (axisSlice (upperEisensteinField s) p j)))
      {t : ℝ | 0<(Function.update p j t) 2} volume := by
  intro t ht
  obtain ⟨ε,C,hε,hreg⟩ := actual_axis_local_regular s hs (Function.update p j t) ht j
  simp only [axisSlice_update,Function.update_self,Function.update_idem] at hreg
  refine ⟨Metric.ball t ε,mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hε),?_⟩
  have hconst : IntegrableOn (fun _ : ℝ => C) (Metric.ball t ε) volume := integrableOn_const
  apply hconst.mono' (aestronglyMeasurable_deriv _ _)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact (hreg x hx).2.2.2

theorem actual_eisenstein_green_interval (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (j : Fin 3) (a b : ℝ)
    (hheight : ∀x∈Set.uIcc a b,0<(Function.update p j x) 2) :
      (∫x in a..b,
        deriv (deriv (axisSlice (upperEisensteinField s) p j)) x *
          star (axisSlice (upperEisensteinField t) p j x) -
        axisSlice (upperEisensteinField s) p j x *
          star (deriv (deriv (axisSlice (upperEisensteinField t) p j)) x)) =
      (deriv (axisSlice (upperEisensteinField s) p j) b *
          star (axisSlice (upperEisensteinField t) p j b) -
        axisSlice (upperEisensteinField s) p j b *
          star (deriv (axisSlice (upperEisensteinField t) p j) b)) -
      (deriv (axisSlice (upperEisensteinField s) p j) a *
          star (axisSlice (upperEisensteinField t) p j a) -
        axisSlice (upperEisensteinField s) p j a *
          star (deriv (axisSlice (upperEisensteinField t) p j) a)) := by
  apply green_identity_interval
  · exact fun x hx => (actual_axis_differentiable_at s hs p j x (hheight x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at t ht p j x (hheight x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at s hs p j x (hheight x hx)).2
  · exact fun x hx => (actual_axis_differentiable_at t ht p j x (hheight x hx)).2
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable s hs p j).integrableOn_compact_subset hheight isCompact_uIcc
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable t ht p j).integrableOn_compact_subset hheight isCompact_uIcc

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT

lemma periodic_deriv {f : ℝ → ℂ} {T : ℝ} (hf : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  rw [← deriv_comp_add_const]
  congr 1
  exact funext hf

lemma embedding_rectangular_period :
    3*eisEmbedding (ActualEisensteinCoordinates.eval 1 2) = (3*Real.sqrt 3:ℝ)*Complex.I := by
  rw [eisEmbedding_eval]
  norm_num only [Int.cast_one,Int.cast_ofNat]
  unfold EisensteinEmbedding.omega3
  push_cast
  ring

lemma actual_axis_periodic_zero (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hv : 0<p 2) :
    Function.Periodic (axisSlice (upperEisensteinField s) p 0) 3 := by
  intro x
  have h := upperEisenstein_periodic (1:O) ((x:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv s hs
  have hz : ((x+3:ℝ):ℂ)+(p 1:ℂ)*Complex.I =
      ((x:ℂ)+(p 1:ℂ)*Complex.I)+3*eisEmbedding (1:O) := by simp; ring
  unfold axisSlice upperEisensteinField
  simp only [Function.update,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,
    dite_false,dite_true]
  simp only [dite_eq_left hv]
  rw [hz]
  exact h

lemma actual_axis_periodic_one (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hv : 0<p 2) :
    Function.Periodic (axisSlice (upperEisensteinField s) p 1) (3*Real.sqrt 3) := by
  intro y
  have h := upperEisenstein_periodic (ActualEisensteinCoordinates.eval 1 2)
    ((p 0:ℂ)+(y:ℂ)*Complex.I) (p 2) hv s hs
  have hz : (p 0:ℂ)+((y+3*Real.sqrt 3:ℝ):ℂ)*Complex.I =
      ((p 0:ℂ)+(y:ℂ)*Complex.I)+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 2) := by
    rw [embedding_rectangular_period]
    push_cast
    ring
  unfold axisSlice upperEisensteinField
  simp only [Function.update,show (0:Fin 3)≠1 by decide,show (2:Fin 3)≠1 by decide,
    dite_false,dite_true]
  simp only [dite_eq_left hv]
  rw [hz]
  exact h

lemma green_periodic_zero {f g : ℝ → ℂ} {T : ℝ}
    (hf : Function.Periodic f T) (hg : Function.Periodic g T) :
    (deriv f T*star (g T)-f T*star (deriv g T)) -
      (deriv f 0*star (g 0)-f 0*star (deriv g 0)) = 0 := by
  have hf0 : f T=f 0 := by simpa only [zero_add] using hf 0
  have hg0 : g T=g 0 := by simpa only [zero_add] using hg 0
  have hdf : deriv f T=deriv f 0 := by simpa only [zero_add] using periodic_deriv hf 0
  have hdg : deriv g T=deriv g 0 := by simpa only [zero_add] using periodic_deriv hg 0
  rw [hf0,hg0,hdf,hdg,sub_self]

theorem actual_green_real_period_zero (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∫x in (0:ℝ)..3,
      deriv (deriv (axisSlice (upperEisensteinField s) p 0)) x *
        star (axisSlice (upperEisensteinField t) p 0 x) -
      axisSlice (upperEisensteinField s) p 0 x *
        star (deriv (deriv (axisSlice (upperEisensteinField t) p 0)) x)) = 0 := by
  rw [actual_eisenstein_green_interval s t hs ht p 0 0 3]
  · exact green_periodic_zero (actual_axis_periodic_zero s hs p hv) (actual_axis_periodic_zero t ht p hv)
  · intro x hx
    simpa only [Function.update_of_ne (show (2:Fin 3)≠0 by decide)] using hv

theorem actual_green_imag_period_zero (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∫x in (0:ℝ)..(3*Real.sqrt 3),
      deriv (deriv (axisSlice (upperEisensteinField s) p 1)) x *
        star (axisSlice (upperEisensteinField t) p 1 x) -
      axisSlice (upperEisensteinField s) p 1 x *
        star (deriv (deriv (axisSlice (upperEisensteinField t) p 1)) x)) = 0 := by
  rw [actual_eisenstein_green_interval s t hs ht p 1 0 (3*Real.sqrt 3)]
  · exact green_periodic_zero (actual_axis_periodic_one s hs p hv) (actual_axis_periodic_one t ht p hv)
  · intro x hx
    simpa only [Function.update_of_ne (show (2:Fin 3)≠1 by decide)] using hv

def cuspRectangle : Set (ℝ × ℝ) := Set.Icc 0 3 ×ˢ Set.Icc 0 (3*Real.sqrt 3)

lemma cuspRectangle_volume : volume cuspRectangle = ENNReal.ofReal (9*Real.sqrt 3) := by
  rw [cuspRectangle,MeasureTheory.Measure.volume_eq_prod,MeasureTheory.Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
  norm_num only [sub_zero]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)]
  congr 1
  ring

lemma cuspRectangle_volume_twice_period : volume cuspRectangle = 2*volume periodDomain := by
  rw [cuspRectangle_volume,periodDomain_volume]
  have h2 : (2:ENNReal)=ENNReal.ofReal (2:ℝ) := by norm_num
  rw [h2,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring

lemma rectangular_period_change_of_basis :
    (3:ℂ)=periodBasis 0 ∧
    (3*Real.sqrt 3:ℝ)*Complex.I=periodBasis 0+2*periodBasis 1 := by
  constructor
  · exact periodBasis_zero.symm
  · rw [periodBasis_zero,periodBasis_one]
    unfold EisensteinEmbedding.omega3
    push_cast
    ring

lemma rectangular_period_matrix_det :
    Matrix.det (!![(1:ℤ),1;0,2]) = 2 := by norm_num [Matrix.det_fin_two]

end CubicEisenstein

end

end OAI
