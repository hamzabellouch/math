import Mathlib
import OAI.Geometry.PrescribedRicci.HermitianPair

namespace OAI

/-! Hermitian Tensor Energy. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Kronecker
namespace MongeAmpere
variable {n m : Type*} [Fintype n] [Fintype m]

lemma hermPair_sum_left {ι : Type*} (s : Finset ι) (K : Matrix n n ℂ) (V : ι → n → ℂ) (w : n → ℂ) :
    hermPair K (∑ i ∈ s, V i) w = ∑ i ∈ s, hermPair K (V i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermPair]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,hermPair_add_left,ih]

lemma hermPair_sum_right {ι : Type*} (s : Finset ι) (K : Matrix n n ℂ) (v : n → ℂ) (W : ι → n → ℂ) :
    hermPair K v (∑ i ∈ s, W i) = ∑ i ∈ s, hermPair K v (W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermPair]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,hermPair_add_right,ih]

def tensorEnergy (B : Matrix m m ℂ) (K : Matrix n n ℂ) (V : m → n → ℂ) : ℂ :=
  ∑ a, ∑ b, B a b*hermPair K (V a) (V b)

lemma tensorEnergy_eq (B : Matrix m m ℂ) (K : Matrix n n ℂ) (V : m → n → ℂ) :
    tensorEnergy B K V = hermPair (B ⊗ₖ K) (fun i => V i.1 i.2) (fun i => V i.1 i.2) := by
  simp only [tensorEnergy,hermPair_expand,Fintype.sum_prod_type,Matrix.kronecker_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma tensorEnergy_nonneg {B : Matrix m m ℂ} {K : Matrix n n ℂ}
    (hB : B.PosSemidef) (hK : K.PosSemidef) (V : m → n → ℂ) :
    0 ≤ (tensorEnergy B K V).re := by
  classical
  rw [tensorEnergy_eq]
  exact hermPair_nonneg (hB.kronecker hK) _

lemma hermPair_weighted_rough_left (B : Matrix m m ℂ) (hB : B.IsHermitian)
    (K : Matrix n n ℂ) (P : m → m → n → ℂ) (f : n → ℂ) :
    ∑ a, ∑ b, B a b*hermPair K (P b a) f =
      hermPair K (∑ a, ∑ b, B a b • P a b) f := by
  classical
  simp only [hermPair_sum_left,hermPair_smul_left]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [show star (B a b) = B b a from Matrix.IsHermitian.ext_iff.mp hB b a]

lemma hermPair_weighted_rough_right (B : Matrix m m ℂ) (K : Matrix n n ℂ)
    (P : m → m → n → ℂ) (f : n → ℂ) :
    ∑ a, ∑ b, B a b*hermPair K f (P a b) =
      hermPair K f (∑ a, ∑ b, B a b • P a b) := by
  classical
  simp only [hermPair_sum_right,hermPair_smul_right]

lemma hermPair_weighted_curvature (B : Matrix m m ℂ) (K : Matrix n n ℂ)
    (R : m → m → Matrix n n ℂ) (f : n → ℂ) :
    ∑ a, ∑ b, B a b*hermPair K f (R a b*ᵥ f) =
      hermPair K f ((∑ a, ∑ b, B a b • R a b)*ᵥ f) := by
  classical
  simp only [Matrix.sum_mulVec,Matrix.smul_mulVec,hermPair_sum_right,hermPair_smul_right]

lemma tensorEnergy_flip (B : Matrix m m ℂ) (K : Matrix n n ℂ) (V : m → n → ℂ) :
    ∑ a, ∑ b, B a b*hermPair K (V b) (V a) = tensorEnergy B.transpose K V := by
  rw [Finset.sum_comm]
  rfl

lemma hermPair_two_re (K : Matrix n n ℂ) (hK : K.IsHermitian) (v w : n → ℂ) :
    (hermPair K v w+hermPair K w v).re = 2*(hermPair K w v).re := by
  rw [← hermPair_conj K hK w v]
  simp only [Complex.add_re,Complex.star_def,Complex.conj_re]
  ring

end MongeAmpere

end

end OAI
