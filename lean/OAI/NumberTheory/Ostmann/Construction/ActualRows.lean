import OAI.NumberTheory.Ostmann.Construction.ActualTests
import OAI.NumberTheory.Ostmann.Construction.CRTInterpolation
import OAI.NumberTheory.Ostmann.Construction.CRTRow
import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem residueTransform_sq_sum (d : Decomposition) (p : ℕ) (hp : Nat.Prime p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (∑ v : ZMod p,‖residueTransform d p v‖^2)=(p:ℝ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  simp only [residueTransform_eq]
  apply Supply.additiveTransform_parseval
  · simpa only [Supply.density,Decomposition.residueDensity,ZMod.card] using d.residueDensity_pos p hp
  · simpa only [Supply.density,Decomposition.residueDensity,ZMod.card] using d.residueDensity_lt_one p hp

theorem giantResidueTransform_sq_sum_le (d : Decomposition) (p : ℕ) [NeZero p] :
    (∑ v : ZMod p,‖giantResidueTransform d p v‖^2)≤(p:ℝ) := by
  calc
    _ ≤ ∑ _ : ZMod p,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (giantResidueTransform_norm_le d p v) 2
    _ = _ := by simp [ZMod.card]

def extractedUnits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (D : ℕ) (hD : ∀i,D.Coprime (p i)) (i : ι) : (ZMod (p i))ˣ :=
  (ZMod.unitOfCoprime (D*otherProduct p i)
    ((hD i).mul_left (otherProduct_coprime p hcop i)))⁻¹

def actualExtractedRow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : Decomposition) (p : ι → ℕ) (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (D : ℕ) (hD : ∀i,D.Coprime (p i)) (giant : ι → Bool)
    (t : ZMod (∏ i,p i)) : ℂ :=
  crtRow p hcop (extractedUnits p hcop D hD)
    (fun i => if giant i then giantResidueTransform d (p i) else residueTransform d (p i)) t

theorem actualExtractedRow_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : Decomposition) (p : ι → ℕ) (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (D : ℕ) (hD : ∀i,D.Coprime (p i)) (giant : ι → Bool) (t : ZMod (∏ i,p i)) :
    actualExtractedRow d p hcop D hD giant t =
      ∏ i,(if giant i then giantResidueTransform d (p i) else residueTransform d (p i))
        (ZMod.prodEquivPi p hcop t i*(D*otherProduct p i:ZMod (p i))⁻¹) := by
  change (∏ i,(if giant i then giantResidueTransform d (p i) else residueTransform d (p i))
    (ZMod.prodEquivPi p hcop t i*((D*otherProduct p i:ℕ):ZMod (p i))⁻¹)) = _
  simp only [Nat.cast_mul]

theorem actualExtractedRow_sq_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : Decomposition) (p : ι → ℕ) [∀i,NeZero (p i)] [NeZero (∏ i,p i)]
    (hp : ∀i,Nat.Prime (p i)) (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (D : ℕ) (hD : ∀i,D.Coprime (p i)) (giant : ι → Bool) :
    (∑ t : ZMod (∏ i,p i),‖actualExtractedRow d p hcop D hD giant t‖^2)≤(∏ i,p i : ℕ) := by
  apply crtRow_sq_norm_le
  intro i
  cases hgiant : giant i with
  | false => simpa only [hgiant,Bool.false_eq_true,ite_false] using (residueTransform_sq_sum d (p i) (hp i)).le
  | true => simpa only [hgiant,ite_true] using giantResidueTransform_sq_sum_le d (p i)

theorem actual_extracted_row_transfer {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (d : Decomposition) (μ : FinitePrior α) (p : α → ι → ℕ)
    [∀x i,NeZero (p x i)] [∀x,NeZero (∏ i,p x i)]
    (hp : ∀x i,Nat.Prime (p x i))
    (hcop : ∀x,Pairwise (fun i j => (p x i).Coprime (p x j)))
    (D : α → ℕ) (hD : ∀x i,(D x).Coprime (p x i)) (giant : ι → Bool)
    (B : (x : α) → ZMod (∏ i,p x i) → ℂ) :
    ‖μ.cmean (fun x => ∑t,actualExtractedRow d (p x) (hcop x) (D x) (hD x) giant t*B x t)‖^2 ≤
      μ.mean (fun x => (∏ i,p x i : ℕ)*∑t,‖B x t‖^2) := by
  refine (μ.norm_cmean_sq_le _).trans (μ.mean_mono fun x => ?_)
  exact (row_cauchy _ _).trans (mul_le_mul_of_nonneg_right
    (actualExtractedRow_sq_norm_le d (p x) (hp x) (hcop x) (D x) (hD x) giant)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end Ostmann.Construction

end

end OAI
