import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationPowers

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def RawMoment (data : RowData) (W : ℝ→ℂ) (c κ C : ℝ) : Prop :=
  ∀ H D : ℝ, 1≤H → 0<D → D^(1+c)≤H →
    ∀ rows : Finset NonzeroElement,
      (∀ v∈rows, ((Ideal.span {v.val}).absNorm : ℝ)≤H) →
      ∑ v∈rows, ‖polynomial (data.character v) true W D 0 0‖^2≤
        C*H*(H*max 1 D)^κ

theorem RawMoment.scaleEnergy {data : RowData} {W : ℝ→ℂ} {c κ C : ℝ}
    (hraw : RawMoment data W c κ C) (hc : 0≤c) (hκ : 0≤κ) (hC : 0≤C)
    (U D V : ℝ) (hD : 1≤D) (hH : 1≤U*V^6) (hHD : D^(1+c)≤U*V^6) :
    RawScaleEnergy data W U D V (C*(U*V^6)*((U*V^6)*D)^κ) := by
  intro rows hrows l hl
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hHp : 0<U*V^6 := zero_lt_one.trans_le hH
  have hexp : Real.exp l≤D := by
    rw [←Real.exp_log hDp]
    exact Real.exp_le_exp.mpr hl.2
  have hp : (Real.exp l)^(1+c)≤U*V^6 :=
    (Real.rpow_le_rpow (Real.exp_pos l).le hexp (by linarith)).trans hHD
  have hh := hraw (U*V^6) (Real.exp l) hH (Real.exp_pos l) hp rows hrows
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hHp.le)
  apply Real.rpow_le_rpow (by positivity) _ hκ
  exact mul_le_mul_of_nonneg_left (max_le hD hexp) hHp.le

end SevenEighths.HeckeInverseAmplification

end

end OAI
