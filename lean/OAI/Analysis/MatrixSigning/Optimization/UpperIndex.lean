import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.RationalAtoms
import OAI.Analysis.MatrixSigning.Potential.RealTraceVarianceRank

namespace OAI

open Matrix

namespace CurrentKS.RationalGrid

def upperIndex (den : ℕ) (test : ℚ → Bool) : ℕ → ℕ
  | 0 => 0
  | k+1 => if test ((k:ℚ)/den) then upperIndex den test k else k+1

def upper (den : ℕ) (test : ℚ → Bool) : ℚ := (upperIndex den test den:ℚ)/den

lemma upperIndex_le (den : ℕ) (test : ℚ → Bool) (k : ℕ) : upperIndex den test k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [upperIndex]
    split
    · exact ih.trans (Nat.le_succ k)
    · rfl

lemma upperIndex_spec (den : ℕ) (test : ℚ → Bool) (r : ℝ)
    (htest : ∀ k : ℕ,test ((k:ℚ)/den)=true ↔ r ≤ (k:ℝ)/den) (k : ℕ)
    (hk : r ≤ (k:ℝ)/den) :
    r ≤ (upperIndex den test k:ℝ)/den ∧
      (upperIndex den test k:ℝ)/den ≤ r+1/(den:ℝ) ∨ r ≤ 0 ∧ upperIndex den test k=0 := by
  induction k with
  | zero => exact Or.inr ⟨by simpa using hk,rfl⟩
  | succ k ih =>
    by_cases h : test ((k:ℚ)/den)=true
    · simp only [upperIndex,h,↓reduceIte]
      exact ih ((htest k).mp h)
    · have hlt : (k:ℝ)/den < r := lt_of_not_ge (fun he => h ((htest k).mpr he))
      simp only [upperIndex,h,Bool.false_eq_true,↓reduceIte]
      apply Or.inl
      refine ⟨hk,?_⟩
      rw [Nat.cast_add,Nat.cast_one,add_div]
      linarith

theorem upper_spec (den : ℕ) (hden : 0 < den) (test : ℚ → Bool) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (htest : ∀ k : ℕ,test ((k:ℚ)/den)=true ↔ r ≤ (k:ℝ)/den) :
    r ≤ (upper den test:ℝ) ∧ (upper den test:ℝ) ≤ r+1/(den:ℝ) ∧ upper den test ≤ 1 := by
  have hd : (0:ℝ)<den := by exact_mod_cast hden
  have hdq : (0:ℚ)<den := by exact_mod_cast hden
  have hspec := upperIndex_spec den test r htest den (by simpa only [div_self hd.ne'] using hr1)
  have hle : upper den test ≤ 1 := by
    unfold upper
    apply (div_le_one hdq).mpr
    exact_mod_cast upperIndex_le den test den
  have he : (upper den test:ℝ)=(upperIndex den test den:ℝ)/den := by simp [upper]
  refine ⟨?_,?_,hle⟩
  · rcases hspec with hs|hs
    · simpa only [he] using hs.1
    · rw [he,hs.2,Nat.cast_zero,zero_div]
      exact hs.1
  · rcases hspec with hs|hs
    · simpa only [he] using hs.2
    · rw [he,hs.2,Nat.cast_zero,zero_div]
      positivity

end CurrentKS.RationalGrid

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators

variable {d N : ℕ}

def rationalVariance (coords : Fin N → Fin d × Fin d → ℚ) :
    Matrix (Fin (d+d)) (Fin (d+d)) ℚ :=
  ∑ i,realFinDecode d (coords i)*realFinDecode d (coords i)

def varianceTest (coords : Fin N → Fin d × Fin d → ℚ) (q : ℚ) : Bool :=
  (KS.W17.rationalNegativeWitness (d+d) (q • 1-rationalVariance coords)).isNone

def varianceQuery (coords : Fin N → Fin d × Fin d → ℚ) : ℚ :=
  CurrentKS.RationalGrid.upper (1000*N*d^2) (varianceTest coords)

noncomputable section
open CurrentKS.Hermitian CurrentKS.Variational CurrentKS.State
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

lemma rationalVariance_symm (coords : Fin N → Fin d × Fin d → ℚ) :
    (rationalVariance coords).IsSymm := by
  change (∑ i,realFinDecode d (coords i)*realFinDecode d (coords i)).transpose=_
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.transpose_mul,(realFinDecode_symm _).eq]

lemma rationalVariance_cast (coords : Fin N → Fin d × Fin d → ℚ) :
    (rationalVariance coords).map (fun q => (q:ℝ)) =
      finRealify ((varianceH (rationalAtoms coords) : H d) : Mat d) := by
  simp only [rationalVariance,cast_matrix_sum,cast_matrix_mul,realFinDecode_cast,
    varianceH,Submodule.coe_sum,finRealify_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sandwich_val]
  change _=finRealify ((_ : Mat d)*1*(_ : Mat d))
  rw [mul_one,finRealify_mul]
  congr 1

lemma varianceTest_spec (coords : Fin N → Fin d × Fin d → ℚ) (q : ℚ) (hq : 0 ≤ q) :
    varianceTest coords q=true ↔ operatorNorm (varianceH (rationalAtoms coords)) ≤ (q:ℝ) := by
  have hsym : (q • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ)-rationalVariance coords).IsSymm :=
    (Matrix.isSymm_one.smul q).sub (rationalVariance_symm coords)
  rw [varianceTest,Option.isNone_iff_eq_none,KS.W17.rationalNegativeWitness_none_iff_psd _ _ hsym,
    cast_matrix_sub,cast_matrix_smul,cast_matrix_one,rationalVariance_cast]
  rw [← finRealify_one,← finRealify_smul,← finRealify_sub,finRealify_psd]
  change (q:ℝ) • (Hermitian.one : H d)-varianceH (rationalAtoms coords) ∈ psdCone d ↔ _
  rw [mem_psd_iff_nonneg,sub_nonneg]
  constructor
  · exact operatorNorm_le_of_psd_le (varianceH_psd _) (by exact_mod_cast hq)
  · intro h
    exact (le_operatorNorm_smul_one _).trans (scalar_one_mono h)

theorem varianceQuery_spec [NeZero d] [NeZero N] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) :
    let ν := varianceQuery coords
    let ν₀ := operatorNorm (varianceH (rationalAtoms coords))
    0 < ν ∧ ν ≤ 1 ∧ ν₀ ≤ (ν:ℝ) ∧ (ν:ℝ) ≤ (1001/1000:ℝ)*ν₀ := by
  have hd : 0 < d := NeZero.pos d
  have hN : 0 < N := NeZero.pos N
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  let A := rationalAtoms coords
  have hpos := varianceH_pos A hA htr
  have hle := operatorNorm_le_of_psd_le (varianceH_psd A) zero_le_one (by simpa using varianceH_le_one A hA hrank htr)
  have h := CurrentKS.RationalGrid.upper_spec (1000*N*d^2) (by positivity) (varianceTest coords)
    (operatorNorm (varianceH A)) hpos.le hle (fun k => by
      rw [varianceTest_spec coords _ (by positivity)]
      simp only [Rat.cast_div,Rat.cast_natCast]
      rfl)
  have hlow := variance_lower_paper A hA hrank htr
  refine ⟨by exact_mod_cast hpos.trans_le h.1,h.2.2,h.1,?_⟩
  apply h.2.1.trans
  have he : (1:ℝ)/(1000*N*d^2)=(1/1000)*(1/((N:ℝ)*d^2)) := by ring
  push_cast
  rw [he]
  linarith

end
end CurrentKS.RationalSDP

end OAI
