import OAI.NumberTheory.DirichletL.Descent.IdealMasks
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

structure HybridColumnData where
  common : Ideal Eis
  residualN : Ideal Eis
  residualB : Ideal Eis
  square : Ideal Eis
  n_squarefree : Squarefree (common * residualN)
  g_squarefree : Squarefree (common * residualB)
  residual_coprime : IsCoprime residualN residualB
  square_ne_zero : square ≠ 0

def HybridColumnData.reconstruct (d : HybridColumnData) : Ideal Eis × Ideal Eis :=
  (d.common * d.residualN, (d.common * d.residualB) * d.square ^ 2)

theorem HybridColumnData.common_ne_zero (d : HybridColumnData) : d.common ≠ 0 :=
  ne_zero_of_dvd_ne_zero d.n_squarefree.ne_zero (dvd_mul_right _ _)

theorem HybridColumnData.common_eq_gcd (d : HybridColumnData) :
    d.common = gcd (d.common * d.residualN) (d.common * d.residualB) := by
  rw [gcd_mul_left, normalize_eq, Ideal.isCoprime_iff_gcd.mp d.residual_coprime, mul_one]

theorem HybridColumnData.residual_product_squarefree (d : HybridColumnData) :
    Squarefree (d.residualN * d.residualB) := by
  have hm := (squarefree_mul_iff.mp d.n_squarefree).2.2
  have hh := (squarefree_mul_iff.mp d.g_squarefree).2.2
  exact squarefree_mul_iff.mpr ⟨d.residual_coprime.isRelPrime, hm, hh⟩

theorem HybridColumnData.primary_factors (d : HybridColumnData)
    (hn : CompletedGauss.primaryGenerator (d.common * d.residualN) ≠ 0)
    (hb : CompletedGauss.primaryGenerator ((d.common * d.residualB) * d.square ^ 2) ≠ 0) :
    CompletedGauss.primaryGenerator d.common ≠ 0 ∧
    CompletedGauss.primaryGenerator d.residualN ≠ 0 ∧
    CompletedGauss.primaryGenerator d.residualB ≠ 0 ∧
    CompletedGauss.primaryGenerator d.square ≠ 0 ∧
    CompletedGauss.primaryGenerator (d.common * d.square) ≠ 0 := by
  rw [CompletedGauss.primaryGenerator_mul] at hn
  have hpow : CompletedGauss.primaryGenerator (d.square ^ 2) =
      CompletedGauss.primaryGenerator d.square ^ 2 :=
    map_pow CompletedGauss.primaryGeneratorHom d.square 2
  rw [CompletedGauss.primaryGenerator_mul, CompletedGauss.primaryGenerator_mul, hpow] at hb
  have hc := (mul_ne_zero_iff.mp hn).1
  have hm := (mul_ne_zero_iff.mp hn).2
  have hch := (mul_ne_zero_iff.mp hb).1
  have hh := (mul_ne_zero_iff.mp hch).2
  have ht : CompletedGauss.primaryGenerator d.square ≠ 0 := by
    intro hz
    apply (mul_ne_zero_iff.mp hb).2
    simp [hz]
  refine ⟨hc, hm, hh, ht, ?_⟩
  rw [CompletedGauss.primaryGenerator_mul]
  exact mul_ne_zero hc ht

theorem HybridColumnData.residual_norm_identity (d : HybridColumnData) :
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) =
      ((Ideal.absNorm (d.common * d.residualN) : ℝ) *
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ)) /
      ((Ideal.absNorm d.common : ℝ) ^ 2 * (Ideal.absNorm d.square : ℝ) ^ 2) := by
  have hc : (Ideal.absNorm d.common : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => d.common_ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  have ht : (Ideal.absNorm d.square : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => d.square_ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  field_simp

theorem HybridColumnData.residual_norm_bounds (d : HybridColumnData)
    (N B C T : ℝ) (hN : 0 ≤ N) (_hB : 0 ≤ B) (hC : 0 < C) (hT : 0 < T)
    (hn : (Ideal.absNorm (d.common * d.residualN) : ℝ) ≤ N)
    (hb : (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B)
    (hc : C ≤ (Ideal.absNorm d.common : ℝ))
    (ht : T ≤ (Ideal.absNorm d.square : ℝ)) :
    (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
    (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) ∧
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ N * B / (C ^ 2 * T ^ 2) := by
  have hn' := hn
  have hb' := hb
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hn' hb'
  have hm : (Ideal.absNorm d.residualN : ℝ) ≤ N / C := by
    apply (le_div_iff₀ hC).mpr
    calc
      _ ≤ (Ideal.absNorm d.common : ℝ) * (Ideal.absNorm d.residualN : ℝ) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hc
          (Nat.cast_nonneg (Ideal.absNorm d.residualN))
      _ ≤ N := hn'
  have hh : (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) := by
    apply (le_div_iff₀ (mul_pos hC (sq_pos_of_pos hT))).mpr
    calc
      _ ≤ (Ideal.absNorm d.common : ℝ) * (Ideal.absNorm d.residualB : ℝ) *
          (Ideal.absNorm d.square : ℝ) ^ 2 := by
        calc
          _ = C * (Ideal.absNorm d.residualB : ℝ) * T ^ 2 := by ring
          _ ≤ _ := by gcongr
      _ ≤ B := hb'
  refine ⟨hm, hh, ?_⟩
  calc
    _ = (Ideal.absNorm d.residualN : ℝ) * (Ideal.absNorm d.residualB : ℝ) := by
      rw [map_mul, Nat.cast_mul]
    _ ≤ (N / C) * (B / (C * T ^ 2)) :=
      mul_le_mul hm hh (Nat.cast_nonneg _) (div_nonneg hN hC.le)
    _ = N * B / (C ^ 2 * T ^ 2) := by ring

theorem HybridColumnData.reconstruct_injective :
    Function.Injective HybridColumnData.reconstruct := by
  intro d e he
  have hn : d.common * d.residualN = e.common * e.residualN := congrArg Prod.fst he
  have hb : d.square ^ 2 * (d.common * d.residualB) =
      e.square ^ 2 * (e.common * e.residualB) := by
    simpa only [HybridColumnData.reconstruct, mul_comm] using congrArg Prod.snd he
  obtain ⟨ht, hg⟩ := QuadraticSquarefreeKernel.squarefree_decomposition_unique
    d.square_ne_zero e.square_ne_zero d.g_squarefree e.g_squarefree hb
  have hc : d.common = e.common := by
    calc
      _ = gcd (d.common * d.residualN) (d.common * d.residualB) := d.common_eq_gcd
      _ = gcd (e.common * e.residualN) (e.common * e.residualB) := by rw [hn, hg]
      _ = e.common := e.common_eq_gcd.symm
  rw [hc] at hn hg
  have hm := mul_left_cancel₀ e.common_ne_zero hn
  have hh := mul_left_cancel₀ e.common_ne_zero hg
  cases d
  cases e
  cases hc
  cases hm
  cases hh
  cases ht
  rfl

def HybridColumnData.toOriginal (d : HybridColumnData) :
    {p : Ideal Eis × Ideal Eis // Squarefree p.1 ∧ p.2 ≠ 0} :=
  ⟨d.reconstruct, d.n_squarefree,
    mul_ne_zero d.g_squarefree.ne_zero (pow_ne_zero 2 d.square_ne_zero)⟩

theorem HybridColumnData.toOriginal_bijective : Function.Bijective HybridColumnData.toOriginal := by
  constructor
  · intro d e he
    exact reconstruct_injective (congrArg Subtype.val he)
  · intro p
    obtain ⟨c, m, h, t, hn, hb, hcs, hms, hhs, hcm, hch, hmh, ht⟩ :=
      hybrid_column_decomposition p.val.1 p.val.2 p.property.1 p.property.2
    refine ⟨⟨c, m, h, t, ?_, ?_, hmh, ht⟩, ?_⟩
    · exact hn ▸ p.property.1
    · exact squarefree_mul_iff.mpr ⟨hch, hcs, hhs⟩
    · apply Subtype.ext
      exact Prod.ext hn.symm hb.symm

def hybridColumnEquiv : HybridColumnData ≃
    {p : Ideal Eis × Ideal Eis // Squarefree p.1 ∧ p.2 ≠ 0} :=
  Equiv.ofBijective HybridColumnData.toOriginal HybridColumnData.toOriginal_bijective

theorem hybrid_column_reindex (f : Ideal Eis → Ideal Eis → ℂ) :
    (∑' p : {p : Ideal Eis × Ideal Eis // Squarefree p.1 ∧ p.2 ≠ 0}, f p.val.1 p.val.2) =
      ∑' d : HybridColumnData,
        f (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) := by
  exact (hybridColumnEquiv.tsum_eq (fun p => f p.val.1 p.val.2)).symm

def hybridColumnSupport (S : Finset (Ideal Eis × Ideal Eis)) : Finset HybridColumnData :=
  S.preimage HybridColumnData.reconstruct HybridColumnData.reconstruct_injective.injOn

@[simp] theorem mem_hybridColumnSupport (S : Finset (Ideal Eis × Ideal Eis))
    (d : HybridColumnData) :
    d ∈ hybridColumnSupport S ↔ d.reconstruct ∈ S := Finset.mem_preimage

theorem hybrid_finite_column_reindex {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal Eis × Ideal Eis))
    (hS : ∀ p ∈ S, Squarefree p.1 ∧ p.2 ≠ 0)
    (f : Ideal Eis × Ideal Eis → A) :
    (∑ p ∈ S, f p) = ∑ d ∈ hybridColumnSupport S, f d.reconstruct := by
  symm
  apply Finset.sum_preimage
  intro p hp hn
  obtain ⟨d, hd⟩ := HybridColumnData.toOriginal_bijective.surjective ⟨p, hS p hp⟩
  exact (hn ⟨d, congrArg Subtype.val hd⟩).elim

end
end SevenEighths.InverseMoment

end OAI
