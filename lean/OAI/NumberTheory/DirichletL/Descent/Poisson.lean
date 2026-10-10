import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Descent.Marks
import OAI.NumberTheory.DirichletL.Descent.LocalReflection

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open FirstPassCubeLabels
open SecondPassArithmetic

noncomputable local instance markedQuotientField (P : Ideal ActualEisensteinCubic.O)
    [P.IsMaximal] : Field (ActualEisensteinCubic.O ⧸ P) := Ideal.Quotient.field P

noncomputable local instance markedQuotientFintype (P : Ideal ActualEisensteinCubic.O)
    [P.IsMaximal] : Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _

theorem ideal_divisibility_local_zeroMark
    (P A : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hA : CompletedGauss.primaryGenerator A ≠ 0) :
    zeroMark (Ideal.Quotient.mk P (CompletedGauss.primaryGenerator A)) =
      if P ∣ A then 1 else 0 := by
  have hd : P ∣ A ↔ CompletedGauss.primaryGenerator A ∈ P := by
    calc
      P ∣ A ↔ A ≤ P := Ideal.dvd_iff_le
      _ ↔ Ideal.span {CompletedGauss.primaryGenerator A} ≤ P := by
        rw [(CompletedGauss.primaryGenerator_spec A hA).1]
      _ ↔ _ := Ideal.span_singleton_le_iff_mem P
  simp only [zeroMark, Ideal.Quotient.eq_zero_iff_mem, hd]

theorem actual_marked_active_eq
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x =
      -LocalReflectionBrackets.activeRow (CompletedGauss.actualSextic P hg) ψ 0 σ ε x := by
  simpa only [localReflectionActive, localFourier,
    LocalReflectionBrackets.activeRow, pow_zero] using
    marked_active_eq_neg_trivial (CompletedGauss.actualSextic P hg) ψ hψ σ ε x

theorem actual_marked_active_norm
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hchar : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    ‖localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x‖ =
      (LocalReflectionBrackets.rootCard (ActualEisensteinCubic.O ⧸ P))⁻¹ *
        if x = 0 then 0 else 1 := by
  rw [actual_marked_active_eq P hg ψ hψ σ ε x, norm_neg,
    LocalReflectionBrackets.canonical_A5_norm_eq_bracket P hg hchar ψ hψ 0
      (by norm_num) σ ε x, LocalReflectionBrackets.norm_bracket_zero]

theorem actual_marked_active_formula
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hchar : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x =
      (LocalReflectionBrackets.rootCard (ActualEisensteinCubic.O ⧸ P) : ℂ)⁻¹ *
        LocalReflectionBrackets.tau (CompletedGauss.actualSextic P hg) ψ 2 *
        (((CompletedGauss.actualSextic P hg) ^ 2)⁻¹)
          ((σ : ActualEisensteinCubic.O ⧸ P) * (ε : ActualEisensteinCubic.O ⧸ P) * x) := by
  rw [actual_marked_active_eq P hg ψ hψ σ ε x,
    LocalReflectionBrackets.canonical_A5_normalized P hg hchar ψ hψ 0 (by norm_num)]
  simp only [LocalReflectionBrackets.phase, LocalReflectionBrackets.bracket,
    show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, inv_pow, map_mul]
  ring

theorem actual_marked_gauss_phase_norm
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hchar : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    ‖LocalReflectionBrackets.tau (CompletedGauss.actualSextic P hg) ψ 2‖ = 1 := by
  have h := LocalReflectionBrackets.canonical_phase_norm P hg hchar ψ hψ 0 (by norm_num) 1
  simpa only [LocalReflectionBrackets.phase, show (0 : ℕ) ≠ 4 by decide,
    ↓reduceIte, Units.val_one, map_one, mul_one, norm_neg] using h

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hcop

omit [DecidableEq ι] in
theorem row_slot_cross_phase
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k) :
    MixedCrossSeparation.crossSymbol p hg i k ^ 4 *
      MixedCrossSeparation.crossSymbol p hg k i ^ 2 = 1 := by
  have hs : MixedCrossSeparation.crossSymbol p hg i k ^ 2 =
      MixedCrossSeparation.crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  have h6 : MixedCrossSeparation.crossSymbol p hg i k ^ 6 = 1 := by
    simpa only [MixedCrossSeparation.crossSymbol, map_pow, ite_eq_right hnot] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
  calc
    _ = MixedCrossSeparation.crossSymbol p hg i k ^ 6 := by rw [← hs]; ring
    _ = 1 := h6

omit [DecidableEq ι] in
theorem row_slot_product_phase
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1) (R P : Finset ι) (hRP : Disjoint R P) :
    (∏ i ∈ R, ∏ k ∈ P,
      MixedCrossSeparation.crossSymbol p hg i k ^ 4 *
        MixedCrossSeparation.crossSymbol p hg k i ^ 2) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  apply Finset.prod_eq_one
  intro k hk
  exact row_slot_cross_phase p hcop hg hpr i k (fun h =>
    (Finset.disjoint_left.mp hRP) hi (h.symm ▸ hk))

theorem canonicalSourceCoefficient_mark_priority
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A S : Finset ι) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f
      (fun U => H U * primeMark I L a (A ∪ U)) S =
    ∑ J ∈ I.powerset, primeMark J L a A *
      canonicalSourceCoefficient p hp hcop hg Ψ m f
        (fun U => H U * primeMark (I \ J) L a (U \ A)) S := by
  simp only [canonicalSourceCoefficient, primeMark_priority, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem marked_disjoint_source_poisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (F M B A₁ A₂ : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (C₁ C₂ : Finset ι → ℂ) (I₁ I₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ K : ℝ) (hK : 0 < K) :
    disjointCanonicalSource p hp hcop hg F M B v ε₁ ε₂
      (fun U => C₁ U * primeMark I₁ L₁ a₁ (A₁ ∪ U))
      (fun U => C₂ U * primeMark I₂ L₂ a₂ (A₂ ∪ U)) W V₁ V₂ X₁ X₂ K =
    ∑ D ∈ M.powerset,
      (UniqueFactorizationMonoid.moebius (∏ i ∈ D, Ideal.span {p i}) : ℂ) /
        (primeProductNorm p D : ℂ) *
      ∑' h : ActualEisensteinCubic.O,
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂
          (fun U => C₁ U * primeMark I₁ L₁ a₁ (A₁ ∪ U))
          (fun U => C₂ U * primeMark I₂ L₂ a₂ (A₂ ∪ U)) W V₁ V₂ X₁ X₂ K
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) h := by
  exact disjointCanonicalSource_poisson p hp hcop hg hinj hc F M B v ε₁ ε₂
    (fun U => C₁ U * primeMark I₁ L₁ a₁ (A₁ ∪ U))
    (fun U => C₂ U * primeMark I₂ L₂ a₂ (A₂ ∪ U)) W V₁ V₂ X₁ X₂ K hK

end

end SevenEighths.InverseMoment

end OAI
