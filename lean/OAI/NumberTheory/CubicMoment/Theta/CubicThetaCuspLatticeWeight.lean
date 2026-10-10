import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRemainderBound

namespace OAI

/-! The summable lattice weight controlling both values and first
spatial derivatives of the arithmetic remainder in each cusp. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaCuspLatticeWeight (δ : SL(2,Eisenstein)) (s : ℂ) (r : CubicThetaBottomRow) : ℝ :=
  norm (cubicThetaCuspRow δ r).c^(-(s.re-2))*(1+norm (cubicThetaCuspRow δ r).d)^(-2:ℝ)

def cubicThetaCuspLatticeMass (s : ℂ) : ℝ :=
  (∑' c : Eisenstein, norm c^(-(s.re-2)))*(∑' d : Eisenstein, (1+norm d)^(-2:ℝ))

lemma cubicThetaCuspLatticeWeight_nonneg (δ : SL(2,Eisenstein)) (s : ℂ) (r : CubicThetaBottomRow) :
    0≤cubicThetaCuspLatticeWeight δ s r :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (by linarith [norm_nonneg (cubicThetaCuspRow δ r).d]) _)

private def pairWeight (s : ℂ) (cd : Eisenstein × Eisenstein) : ℝ :=
  norm cd.1^(-(s.re-2))*(1+norm cd.2)^(-2:ℝ)

private def rowIndex (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow) : Eisenstein × Eisenstein :=
  ((cubicThetaCuspRow δ r).c,(cubicThetaCuspRow δ r).d)

private lemma rowIndex_injective (δ : SL(2,Eisenstein)) : Function.Injective (rowIndex δ) := by
  intro r t he
  exact cubicThetaCuspRow_injective δ
    (CubicThetaPrimitiveRow.ext (congrArg Prod.fst he) (congrArg Prod.snd he))

private lemma pairWeight_summable {s : ℂ} (hs : 3<s.re) : Summable (pairWeight s) := by
  have hc := summable_eisenstein_norm_rpow (show 1<s.re-2 by linarith)
  have hd := summable_eisenstein_one_add_norm (by norm_num : (1:ℝ)<2)
  exact summable_mul_of_summable_norm hc.norm hd.norm

lemma cubicThetaCuspLatticeWeight_summable (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3<s.re) :
    Summable (cubicThetaCuspLatticeWeight δ s) := by
  change Summable (fun r => pairWeight s (rowIndex δ r))
  exact (pairWeight_summable hs).comp_injective (rowIndex_injective δ)

lemma cubicThetaCuspLatticeWeight_tsum_le (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3<s.re) :
    (∑' r, cubicThetaCuspLatticeWeight δ s r)≤cubicThetaCuspLatticeMass s := by
  have hc := summable_eisenstein_norm_rpow (show 1<s.re-2 by linarith)
  have hd := summable_eisenstein_one_add_norm (by norm_num : (1:ℝ)<2)
  have h := pairWeight_summable hs
  have hn (cd : Eisenstein × Eisenstein) : 0≤pairWeight s cd :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg cd.1) _)
      (Real.rpow_nonneg (by linarith [norm_nonneg cd.2]) _)
  have hb := tsum_comp_le_tsum_of_inj h hn (rowIndex_injective δ)
  have hm : (∑' cd, pairWeight s cd)=cubicThetaCuspLatticeMass s :=
    (hc.tsum_mul_tsum hd h).symm
  exact hb.trans_eq hm

end CubicFirstMoment

end

end OAI
