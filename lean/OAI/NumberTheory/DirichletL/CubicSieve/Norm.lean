import OAI.NumberTheory.DirichletL.CubicSieve.Ideal
import OAI.NumberTheory.DirichletL.CubicSieve.Initial

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem primaryGenerator_inj_on_cubic_admissible {I J : Ideal O}
    (hI : Admissible I) (hJ : Admissible J)
    (heq : primaryGenerator I = primaryGenerator J) : I = J := by
  calc
    I = Ideal.span {primaryGenerator I} := (primaryGenerator_spec I hI.2).1.symm
    _ = Ideal.span {primaryGenerator J} := by rw [heq]
    _ = J := (primaryGenerator_spec J hJ.2).1

theorem idealSymbol_eq_idealSexticRow_sq
    (F : Finset (Ideal O)) (hFp : ∀ I ∈ F, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (hI : I ∈ F) (hsq : Squarefree I) (z : O) :
    eisEmbedding (CubicJacobiGlobal.idealSymbol I z) =
      (idealSexticRow F hFp hFg I z) ^ 2 := by
  rw [← CanonicalRowCompletion.idealRowHom_square]
  congr 1
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFp
  conv_lhs => rw [← idealSupport_product_eq F hI hsq, map_prod]
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_congr rfl
  intro i hi
  exact CanonicalRowCompletion.idealRowHom_prime z i.val (primePool_good F hFg i)

theorem sieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    sieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  let F := idealRange N
  let R := (idealRange M).image primaryGenerator
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => primaryGenerator_ne_zero_ideal I (hF I hI).2
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (primaryPrime_spec P
      (primaryPrime_factor_ne_zero I P (hF I hI).2 hP)).2.1
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    intro z hz
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hz
    rw [primaryGenerator_norm_sq I ((mem_idealRange.mp hI).1.2)]
    exact (mem_idealRange.mp hI).2
  have hgen : Set.InjOn primaryGenerator (idealRange M) := by
    intro I hI J hJ heq
    exact primaryGenerator_inj_on_cubic_admissible (mem_idealRange.mp hI).1 (mem_idealRange.mp hJ).1 heq
  apply FiniteSieveOperator.squared_norm_le_of_energy (idealMatrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2) =
        ∑ J : F, eisEmbedding (CubicJacobiGlobal.idealSymbol J.val z) * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    rw [idealSymbol_eq_idealSexticRow_sq F hFp hFg J.val J.property (hF J.val J.property).1 z]
    simp only [aext, dite_eq_left J.property]
    change a J * (idealSexticRow F hFp hFg J.val z) ^ 2 =
      (idealSexticRow F hFp hFg J.val z) ^ 2 * a J
    exact mul_comm _ _
  have he := ideal_initial_cubic_sieve F hFp hFg
    (fun I hI => (hF I hI).1) ⌈N⌉₊ hnat hnorm aext M hM R hR
  have heR : (∑ z ∈ R, ‖∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2‖ ^ 2) =
      ∑ I : idealRange M, ‖∑ J : F, eisEmbedding (CubicJacobiGlobal.idealSymbol J.val (primaryGenerator I.val)) * a J‖ ^ 2 := by
    dsimp only [R]
    rw [Finset.sum_image (fun I hI J hJ heq => hgen hI hJ heq)]
    simp_rw [hinner]
    exact (Finset.sum_coe_sort _ _).symm
  have hea : (∑ I ∈ F, ‖aext I‖ ^ 2) = ∑ J : F, ‖a J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    simp only [aext, dite_eq_left J.property]
    rfl
  rw [heR, hea] at he
  exact he

end
end SevenEighths.CubicSieve

end OAI
