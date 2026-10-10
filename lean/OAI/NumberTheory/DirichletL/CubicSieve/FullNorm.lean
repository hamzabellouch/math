import OAI.NumberTheory.DirichletL.CubicSieve.Gcd

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def elementRange (M : ℝ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌊M⌋₊).filter
    (fun z => z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)

lemma mem_elementRange (M : ℝ) (z : O) :
    z ∈ elementRange M ↔ z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_qNat_le
    rw [ActualEisensteinCubic.qNat_eq_absNorm_span]
    exact Nat.le_floor h.2

def elementMatrix (M N : ℝ) : Matrix (elementRange M) (idealRange N) ℂ :=
  fun z J => cubicRow J.val z.val

def elementSieveNorm (M N : ℝ) : ℝ := squaredNorm (elementMatrix M N)

lemma elementSieveNorm_nonneg (M N : ℝ) : 0 ≤ elementSieveNorm M N := squaredNorm_nonneg _

theorem element_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => cubicRow (cols j) (rows i)) ≤ elementSieveNorm M N := by
  let r : m → elementRange M := fun i => ⟨rows i, (mem_elementRange M (rows i)).mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (elementMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma sieveNorm_le_elementSieveNorm (M N : ℝ) : sieveNorm M N ≤ elementSieveNorm M N := by
  apply element_family_squared_norm_le
    (fun I : idealRange M => primaryGenerator I.val) (fun J : idealRange N => J.val)
  · intro I J he
    exact Subtype.ext (primaryGenerator_inj_on_cubic_admissible
      (mem_idealRange.mp I.property).1 (mem_idealRange.mp J.property).1 he)
  · exact Subtype.val_injective
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1.2, by
      rw [(primaryGenerator_spec I.val (mem_idealRange.mp I.property).1.2).1]
      exact (mem_idealRange.mp I.property).2⟩
  · intro J
    exact mem_idealRange.mp J.property

lemma elementSieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    elementSieveNorm M N ≤ elementSieveNorm M' N' := by
  apply element_family_squared_norm_le (fun z : elementRange M => z.val)
    (fun I : idealRange N => I.val) Subtype.val_injective Subtype.val_injective
  · intro z
    exact ⟨((mem_elementRange M z.val).mp z.property).1,
      ((mem_elementRange M z.val).mp z.property).2.trans hM⟩
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1, (mem_idealRange.mp I.property).2.trans hN⟩

theorem element_coprime_bilinear_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (hN : 0 ≤ N)
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a b : n → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
      star (cubicRow (cols j) (rows i) * a j) * (cubicRow (cols k) (rows i) * b k) else 0‖) ^ 2 ≤
      (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) *
      (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * ∑ j, ‖b j‖ ^ 2) := by
  have hb := IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound ε hε cols cols
    (fun j => primaryGenerator_ne_zero_ideal _ (hcols j).1.2)
    (fun j => primaryGenerator_ne_zero_ideal _ (hcols j).1.2)
    N N hN hN (fun j => (hcols j).2) (fun j => (hcols j).2)
    (fun i j => cubicRow (cols j) (rows i)) (fun i j => cubicRow (cols j) (rows i)) a b
  have hn := element_family_squared_norm_le rows cols hr hc M N hrows hcols
  have hfac : 0 ≤ IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε :=
    mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN _)
  apply hb.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · positivity
  · exact mul_nonneg (mul_nonneg (elementSieveNorm_nonneg _ _) hfac) (by positivity)

theorem elementSieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    elementSieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  let F := idealRange N
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => primaryGenerator_ne_zero_ideal I (hF I hI).2
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (primaryPrime_spec P
      (primaryPrime_factor_ne_zero I P (hF I hI).2 hP)).2.1
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ elementRange M, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    intro z hz
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact ((mem_elementRange M z).mp hz).2
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2) =
        ∑ J : F, cubicRow J.val z * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J hJ
    change aext J.val * (idealSexticRow F hFp hFg J.val z) ^ 2 =
      eisEmbedding (CubicJacobiGlobal.idealSymbol J.val z) * a J
    rw [idealSymbol_eq_idealSexticRow_sq F hFp hFg J.val J.property (hF J.val J.property).1 z]
    simp only [aext, dite_eq_left J.property]
    exact mul_comm _ _
  have he := ideal_initial_cubic_sieve F hFp hFg
    (fun I hI => (hF I hI).1) ⌈N⌉₊ hnat hnorm aext M hM (elementRange M) hR
  have hea : (∑ I ∈ F, ‖aext I‖ ^ 2) = ∑ J : F, ‖a J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J hJ
    simp only [aext, dite_eq_left J.property]
    rfl
  simp_rw [hinner] at he
  rw [hea, ← Finset.sum_coe_sort] at he
  exact he

end
end SevenEighths.CubicSieve

end OAI
