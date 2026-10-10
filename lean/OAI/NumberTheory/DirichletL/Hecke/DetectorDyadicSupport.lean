import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge
import OAI.NumberTheory.DirichletL.Hecke.DetectorFinite

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily HeckeDetectorFinite HeckeDetectorPartition
open CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def fourierSet (U : ℝ) : Finset (Ideal O) := idealsUpTo ⌈16*U⌉₊

lemma fourierSet_nonzero (U : ℝ) (J : Ideal O) (hJ : J∈fourierSet U) : J≠0 := by
  have hn := (mem_idealsUpTo.mp hJ).1
  exact Ideal.absNorm_eq_zero_iff.not.mp (by omega)

lemma pairSet_subset_fourier (U : ℝ) (hU : 0≤U) :
    pairSet U ⊆ fourierSet U ×ˢ fourierSet U := by
  intro p hp
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
  have hb : ⌈2*U⌉₊ ≤ ⌈16*U⌉₊ := Nat.ceil_mono (by linarith)
  exact Finset.mem_product.mpr
    ⟨mem_idealsUpTo.mpr ⟨(mem_idealsUpTo.mp h1).1,(mem_idealsUpTo.mp h1).2.trans hb⟩,
     mem_idealsUpTo.mpr ⟨(mem_idealsUpTo.mp h2).1,(mem_idealsUpTo.mp h2).2.trans hb⟩⟩

lemma annular_covered (U D : ℝ) (hD : 0<D) (hDU : D≤8*U)
    (W : ℝ→ℂ) (hW : ∀ x : ℝ, 2≤x → W x=0)
    (J : Ideal O) (hJ : J≠0) (hw : W ((J.absNorm : ℝ)/D)≠0) :
    J∈fourierSet U := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hr : (J.absNorm : ℝ)/D<2 := lt_of_not_ge (fun hn => hw (hW _ hn))
  have hn : (J.absNorm : ℝ)≤16*U := by
    have hh := (div_lt_iff₀ hD).mp hr
    linarith
  exact_mod_cast hn.trans (Nat.le_ceil (16*U))

lemma inverse_annular_covered (U D Dstar : ℝ) (hD : 0<D) (hDU : D≤8*U)
    (V W : ℝ→ℂ) (hW : ∀ x : ℝ, 2≤x → W x=0)
    (J : Ideal O) (hJ : J≠0) (hw : inverseProfile V W Dstar D ((J.absNorm : ℝ)/D)≠0) :
    J∈fourierSet U := by
  apply annular_covered U D hD hDU W hW J hJ
  exact (mul_ne_zero_iff.mp hw).2

lemma scales_le_eight_terminal (U : ℝ) (j k : ℕ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U) :
    (2 : ℝ)^j≤8*U ∧ (2 : ℝ)^k≤8*U := by
  have hj : 1≤(2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hk : 1≤(2 : ℝ)^k := one_le_pow₀ (by norm_num)
  constructor
  · exact (le_mul_of_one_le_right (by positivity) hk).trans hprod.le
  · exact (le_mul_of_one_le_left (by positivity) hj).trans hprod.le

theorem dyadicBlock_eq_fourier_rectangle (χ : Character) (V T : ℝ→ℂ)
    (D Y U : ℝ) (hU : 0<U) (hT : ∀ x : ℝ, 2≤x → T x=0)
    (s : ℂ) (j k : ℕ) :
    dyadicBlock χ V T D Y U s j k =
      ∑ J∈fourierSet U, ∑ K∈fourierSet U,
        pairCoefficient χ V T D Y U s (J,K)*
          DyadicTransfer.annularCutoff V ((J.absNorm : ℝ)/(2 : ℝ)^j)*
          DyadicTransfer.annularCutoff V ((K.absNorm : ℝ)/(2 : ℝ)^k) := by
  unfold dyadicBlock
  calc
    _ = ∑ p∈fourierSet U ×ˢ fourierSet U,
        pairCoefficient χ V T D Y U s p *
          DyadicTransfer.annularCutoff V ((p.1.absNorm : ℝ)/(2 : ℝ)^j) *
          DyadicTransfer.annularCutoff V ((p.2.absNorm : ℝ)/(2 : ℝ)^k) := by
      apply Finset.sum_subset (pairSet_subset_fourier U hU.le)
      intro p hp hn
      rw [pairCoefficient_support χ V T D Y U hU hT s p hn, zero_mul, zero_mul]
    _ = _ := Finset.sum_product _ _ _

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI
