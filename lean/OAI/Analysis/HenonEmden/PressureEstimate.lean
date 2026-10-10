import OAI.Analysis.HenonEmden.IntegratedPressure

namespace OAI

section PressureEstimate

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents LayerTonelli Angular

def pressureGeomCoefficient (n : ℕ) : ℝ := 12*(N n:ℝ)*((n:ℝ)-2)
def pressureSmallCoefficient (n : ℕ) (p q A B κ : ℝ) : ℝ :=
  3*sphereMass n*oscillationConstant (volume : Measure (Space n)) κ+
    6*(N n:ℝ)*(endpointConstant q B+endpointConstant p A)
def pressureHighCoefficient (n : ℕ) (p q A B κ δ : ℝ) : ℝ :=
  2*(boundConstant (volume : Measure (Space n)) κ*rayConstant n*sourceBallConstant n p q A B)/δ^n
def pressureConstant (n : ℕ) (p q A B κ δ P : ℝ) : ℝ :=
  sphereMass n*boundConstant (volume : Measure (Space n)) κ*
    (farConstant n p q A B δ+farConstant n q p B A δ)+
  2*lowLevelConstant n*P*(max (uniformMassConstant n p q A B) 0+max (uniformMassConstant n q p B A) 0)

lemma pressureGeomCoefficient_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ pressureGeomCoefficient n := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  unfold pressureGeomCoefficient
  positivity
lemma pressureSmallCoefficient_nonneg (n : ℕ) (p q A B : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    0 ≤ pressureSmallCoefficient n p q A B κ := by
  have ho := oscillationConstant_nonneg (volume : Measure (Space n)) hκ
  have hs := sphereMass_nonneg n
  have heq := endpointConstant_nonneg q B
  have hep := endpointConstant_nonneg p A
  unfold pressureSmallCoefficient
  positivity
lemma pressureHighCoefficient_nonneg (n : ℕ) (p q A B : ℝ) {κ δ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) :
    0 ≤ pressureHighCoefficient n p q A B κ δ := by
  have hb := boundConstant_nonneg (volume : Measure (Space n)) hκ
  have hm := sourceBallConstant_nonneg n p q A B
  have hr : 0 ≤ rayConstant n := by unfold rayConstant; positivity
  unfold pressureHighCoefficient
  positivity
lemma pressureConstant_nonneg (n : ℕ) (p q A B : ℝ) {κ δ P : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hP : 0 ≤ P) :
    0 ≤ pressureConstant n p q A B κ δ P := by
  have hb := boundConstant_nonneg (volume : Measure (Space n)) hκ
  have hs := sphereMass_nonneg n
  have hf := farConstant_nonneg (n:=n) p q A B hδ
  have hg := farConstant_nonneg (n:=n) q p B A hδ
  have hl := lowLevelConstant_nonneg n
  unfold pressureConstant
  positivity

lemma IsSolution.pressure_estimate {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ P : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) (hP : 0 < P) :
    (q+1)⁻¹*weightedEnergy (w n) u q B+(p+1)⁻¹*weightedEnergy (w n) v p A-
      radialPressure (source u q B) (source v p A) ≤
      (pressureGeomCoefficient n*κ+pressureSmallCoefficient n p q A B κ*δ+
        pressureHighCoefficient n p q A B κ δ/P)*
        (weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A)+
      pressureConstant n p q A B κ δ P := by
  have hn2 : 2 ≤ n := by omega
  let Ef := weightedEnergy (eta n) u q B
  let Eg := weightedEnergy (eta n) v p A
  let R := radialPressure (source u q B) (source v p A)
  let L := lossCoefficient (volume : Measure (Space n)) κ δ (sourceBallConstant n p q A B) P
  let Uf := lowLevelConstant n*P*max (uniformMassConstant n p q A B) 0
  let Ug := lowLevelConstant n*P*max (uniformMassConstant n q p B A) 0
  let T := sphereMass n*(oscillationConstant (volume : Measure (Space n)) κ*δ*(Ef+Eg)+
    boundConstant (volume : Measure (Space n)) κ*(farConstant n p q A B δ+farConstant n q p B A δ))
  have hEf : 0 ≤ Ef := weightedEnergyN_nonneg (eta_nonneg n) (fun x => (h.positive_u x).le)
  have hEg : 0 ≤ Eg := weightedEnergyN_nonneg (eta_nonneg n) (fun x => (h.positive_v x).le)
  have hR : 0 ≤ R := radialPressure_nonneg hn2 _ _
  have hL : 0 ≤ L := lossCoefficient_nonneg volume hκ.le hδ.le (sourceBallConstant_nonneg n p q A B) hP.le
  have hUf : 0 ≤ Uf := by dsimp [Uf]; positivity [lowLevelConstant_nonneg n]
  have hUg : 0 ≤ Ug := by dsimp [Ug]; positivity [lowLevelConstant_nonneg n]
  have hG := pressureGeomCoefficient_nonneg hn2
  have ho := oscillationConstant_nonneg (volume : Measure (Space n)) hκ.le
  have hb := boundConstant_nonneg (volume : Measure (Space n)) hκ.le
  have hs := sphereMass_nonneg n
  have hfC : 0 ≤ farConstant n p q A B δ := farConstant_nonneg p q A B hδ.le
  have hgC : 0 ≤ farConstant n q p B A δ := farConstant_nonneg q p B A hδ.le
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have heq := endpointConstant_nonneg q B
  have hep := endpointConstant_nonneg p A
  have hNEf := h.weightedEnergyN_eq hn2 (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hNEg := h.swap.weightedEnergyN_eq hn2 (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hDq := weightedEnergyN_d_w_le h.continuous_u (fun x => (h.positive_u x).le) q B
  have hDp := weightedEnergyN_d_w_le h.continuous_v (fun x => (h.positive_v x).le) p A
  rw [hNEf,← ENNReal.ofReal_mul (by positivity : 0 ≤ 6*(N n:ℝ))] at hDq
  rw [hNEg,← ENNReal.ofReal_mul (by positivity : 0 ≤ 6*(N n:ℝ))] at hDp
  have hLf := h.angular_loss_bound hn2 hp hq hκ hκ1 hδ (by linarith) hP
  have hLg := h.swap.angular_loss_bound hn2 hq hp hκ hκ1 hδ (by linarith) hP
  rw [sourceBallConstant_swap] at hLg
  have hh := h.integrated_directional_pressure hn hp hq hκ hκ1 hδ.le
  have hnq : 0 ≤ 1/(q+1) := by positivity
  have hnp : 0 ≤ 1/(p+1) := by positivity
  have hWf := weightedEnergyN_nonneg (w_nonneg n) (fun x => (h.positive_u x).le) (q:=q) (B:=B)
  have hWg := weightedEnergyN_nonneg (w_nonneg n) (fun x => (h.positive_v x).le) (q:=p) (B:=A)
  rw [h.weightedEnergyN_eq hn2 (continuous_w n) (compactSupport_w n) (w_nonneg n),
    h.swap.weightedEnergyN_eq hn2 (continuous_w n) (compactSupport_w n) (w_nonneg n),
    ← ENNReal.ofReal_mul hnq,← ENNReal.ofReal_mul hnp,
    ← ENNReal.ofReal_add (mul_nonneg hnq hWf) (mul_nonneg hnp hWg)] at hh
  have htot : ENNReal.ofReal (1/(q+1)*weightedEnergy (w n) u q B+1/(p+1)*weightedEnergy (w n) v p A) ≤ ENNReal.ofReal (R+pressureGeomCoefficient n*κ*Ef)+ENNReal.ofReal T+
      2*(ENNReal.ofReal (L*Ef+Uf)+ENNReal.ofReal (L*Eg+Ug))+
      (ENNReal.ofReal (endpointConstant q B*δ)*ENNReal.ofReal (6*(N n:ℝ)*Ef)+
      ENNReal.ofReal (endpointConstant p A*δ)*ENNReal.ofReal (6*(N n:ℝ)*Eg)) := by
    apply hh.trans
    exact add_le_add (add_le_add (add_le_add (h.angular_pressure_bound hn2 hp hq hκ hκ1)
      (h.angular_mismatch_bound hn2 hp hq hκ hκ1 hδ hδ1))
      (mul_le_mul le_rfl (add_le_add hLf hLg) bot_le bot_le))
      (add_le_add (mul_le_mul le_rfl hDq bot_le bot_le) (mul_le_mul le_rfl hDp bot_le bot_le))
  have hLF0 : 0 ≤ L*Ef+Uf := by positivity
  have hLG0 : 0 ≤ L*Eg+Ug := by positivity
  have htwo (x : ℝ) : (2:ℝ≥0∞)*ENNReal.ofReal x=ENNReal.ofReal (2*x) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [← ENNReal.ofReal_add (add_nonneg hR (by positivity)) hT,
    ← ENNReal.ofReal_add hLF0 hLG0,
    ← ENNReal.ofReal_mul (mul_nonneg heq hδ.le),← ENNReal.ofReal_mul (mul_nonneg hep hδ.le),
    ← ENNReal.ofReal_add (by positivity : 0 ≤ (endpointConstant q B*δ)*(6*(N n:ℝ)*Ef))
      (by positivity : 0 ≤ (endpointConstant p A*δ)*(6*(N n:ℝ)*Eg)),
    htwo,
    ← ENNReal.ofReal_add (by positivity : 0 ≤ R+pressureGeomCoefficient n*κ*Ef+T) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at htot
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htot
  dsimp only [R,Ef,Eg] at hreal
  simp only [one_div] at hreal
  have hraw : (q+1)⁻¹*weightedEnergy (w n) u q B+(p+1)⁻¹*weightedEnergy (w n) v p A-R ≤
      pressureGeomCoefficient n*κ*Ef+T+2*(L*Ef+Uf+(L*Eg+Ug))+
        (endpointConstant q B*δ*(6*(N n:ℝ)*Ef)+endpointConstant p A*δ*(6*(N n:ℝ)*Eg)) := by
    dsimp only [R,Ef,Eg]
    linarith [hreal]
  apply hraw.trans
  have hGE : pressureGeomCoefficient n*κ*Ef ≤ pressureGeomCoefficient n*κ*(Ef+Eg) := by
    nlinarith [mul_nonneg (mul_nonneg hG hκ.le) hEg]
  have hEE : endpointConstant q B*δ*(6*(N n:ℝ)*Ef)+endpointConstant p A*δ*(6*(N n:ℝ)*Eg) ≤
      6*(N n:ℝ)*(endpointConstant q B+endpointConstant p A)*δ*(Ef+Eg) := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg heq hδ.le) (by positivity : 0 ≤ 6*(N n:ℝ))) hEg,
      mul_nonneg (mul_nonneg (mul_nonneg hep hδ.le) (by positivity : 0 ≤ 6*(N n:ℝ))) hEf]
  have halg :
      (pressureGeomCoefficient n*κ+pressureSmallCoefficient n p q A B κ*δ+
        pressureHighCoefficient n p q A B κ δ/P)*(Ef+Eg)+pressureConstant n p q A B κ δ P =
      pressureGeomCoefficient n*κ*(Ef+Eg)+T+2*(L*Ef+Uf+(L*Eg+Ug))+
        6*(N n:ℝ)*(endpointConstant q B+endpointConstant p A)*δ*(Ef+Eg) := by
    dsimp only [L,T,Uf,Ug,lossCoefficient,pressureSmallCoefficient,pressureHighCoefficient,pressureConstant,sphereMass]
    simp only [finrank_euclideanSpace_fin]
    ring
  change pressureGeomCoefficient n*κ*Ef+T+2*(L*Ef+Uf+(L*Eg+Ug))+
      (endpointConstant q B*δ*(6*(N n:ℝ)*Ef)+endpointConstant p A*δ*(6*(N n:ℝ)*Eg)) ≤
      (pressureGeomCoefficient n*κ+pressureSmallCoefficient n p q A B κ*δ+
        pressureHighCoefficient n p q A B κ δ/P)*(Ef+Eg)+pressureConstant n p q A B κ δ P
  rw [halg]
  linarith [hGE,hEE]

end HenonLaneEmden
end
end PressureEstimate

end OAI
