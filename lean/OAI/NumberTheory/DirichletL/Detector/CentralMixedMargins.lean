import OAI.NumberTheory.DirichletL.Detector.CentralDyadicWeight

namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeDetectorRowCount ProbeCentralExponent

lemma balanced_count_range (δ x Δ loss : ℝ) (hδ : 0≤δ) (hd : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8)
    (hl : 0≤loss) (hl' : loss≤1/32) :
    let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
    1-δ≤R ∧ R≤3/2 := by
  have ht := balanced_cutoff_bounds hδ hd hx hx'
  have hp0 := mul_nonneg (show 0≤5/6-δ by linarith) (show 0≤Endpoint.balancedCutoff δ (1/2-x)-1 by linarith)
  have hp1 := mul_le_mul_of_nonneg_left ht.2 (show 0≤5/6-δ by linarith)
  dsimp only
  unfold Endpoint.balancedRowCount
  constructor <;> nlinarith

lemma balanced_mixed_margin (δ x Δ loss ζ μ v d : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
    mixedSourceExponent ((1+δ)/2) v d R (δ*x)-(3/16+Δ)≤
      -49/440640-(51/64)*Δ+(13/16)*loss+2*ζ+(3/2)*μ := by
  dsimp only
  let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
  have hr := balanced_count_range δ x Δ loss hδ hd hx hx' hΔ hΔ' hl hl'
  have hlo : 0≤R+δ/2-17/50 := by dsimp [R]; linarith [hr.1]
  have hhi : R+δ/2-17/50≤2 := by dsimp [R]; linarith [hr.2]
  have hm := balanced_source_margin δ x R Δ loss ζ v hδ hd hx hx' le_rfl hζ hv hlo hhi
  have hs := mixed_source_slack ((1+δ)/2) v d R (δ*x) μ (3/2)
    (by dsimp [R];linarith [hr.1]) hr.2 hμ hdv
  linarith

lemma high_mixed_margin (δ q Δ loss ζ μ v d : ℝ)
    (hδ : 5/6≤δ) (hd : δ≤1) (hq : q≤δ/2)
    (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    mixedSourceExponent ((1+δ)/2) v d (1-δ+loss) q-(3/16+Δ)≤
      -1/48-δ/16-Δ+(13/16)*loss+2*ζ+μ := by
  have hlo : 0≤(1-δ+loss)+δ/2-17/50 := by linarith
  have hhi : (1-δ+loss)+δ/2-17/50≤2 := by linarith
  have hm := high_source_margin δ (1-δ+loss) q Δ loss ζ v hq le_rfl hζ hv hlo hhi
  have hs := mixed_source_slack ((1+δ)/2) v d (1-δ+loss) q μ 1
    (by linarith) (by linarith) hμ hdv
  linarith

lemma balanced_mixed_saving (δ x Δ loss ζ μ v d other saving : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ)
    (hbudget : (13/16)*loss+2*ζ+(3/2)*μ+other+saving≤49/440640) :
    mixedSourceExponent ((1+δ)/2) v d
      (Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss) (δ*x)+other≤3/16+Δ-saving := by
  have hm := balanced_mixed_margin δ x Δ loss ζ μ v d hδ hd hx hx' hΔ hΔ' hl hl' hζ hv hμ hdv
  linarith
end SevenEighths.ProbeHighRowFamily

end

end OAI
