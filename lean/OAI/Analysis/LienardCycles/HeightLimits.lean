import OAI.Analysis.LienardCycles.CharacteristicSigns

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus
noncomputable def HN (q : (ℝ × ℝ) × ℝ) : ℝ := H ((q.1.1*q.2,q.1.2*q.2^3),1)
noncomputable def DN (q : (ℝ × ℝ) × ℝ) : ℝ :=
  HN q+q.1.1*q.2*PN q+3*q.1.2*q.2^3*QN q
lemma HN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω HN q := by
  apply (H_analytic (by norm_num : (0:ℝ)<1)).comp q
  fun_prop
lemma DN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω DN q := by
  unfold DN
  have h1 := HN_analytic q
  have h2 := PN_analytic q
  have h3 := QN_analytic q
  fun_prop
lemma HN_zero (d k : ℝ) : HN ((d,k),0)=0 := by
  simpa [HN] using (zero_data (by norm_num : (0:ℝ)<1)).2
lemma DN_zero (d k : ℝ) : DN ((d,k),0)=0 := by simp [DN,HN_zero]
lemma Hr_DN {d k r : ℝ} (hr : 0 < r) : Hr ((d,k),r)=DN ((d,k),r) := by
  have he := euler_identity (d := d) (k := k) hr
  rw [scaling d k hr,P_scaling d k hr,Q_scaling d k hr] at he
  dsimp [DN,HN,PN,QN]
  apply (mul_left_cancel₀ (ne_of_gt hr))
  nlinarith only [he]
lemma HN_deriv_zero (d k : ℝ) : HasDerivAt (fun r => HN ((d,k),r)) (d/3) 0 := by
  have hm : HasDerivAt (fun s : ℝ => ((d*s,k*s^3),(1:ℝ))) ((d,0),0) 0 := by
    convert! (((hasDerivAt_id (0:ℝ)).const_mul d).prodMk
      (((hasDerivAt_id (0:ℝ)).pow 3).const_mul k)).prodMk (hasDerivAt_const (0:ℝ) (1:ℝ)) using 1
    norm_num [id_eq]
  have hH : HasFDerivAt H (fderiv ℝ H ((0,0),1)) ((d*0,k*0^3),1) := by
    simpa using ((H_analytic (d := 0) (k := 0) (by norm_num : (0:ℝ)<1)).differentiableAt (by simp)).hasFDerivAt
  have hd := hH.comp_hasDerivAt (f := fun s : ℝ => ((d*s,k*s^3),(1:ℝ))) 0 hm
  rw [fderiv_model] at hd
  change HasDerivAt (fun r => HN ((d,k),r))
    (d*P ((0,0),1)+0*Q ((0,0),1)+0*Hr ((0,0),1)) 0 at hd
  simpa [QuadraticVariation.P_zero (by norm_num : (0:ℝ)<1),div_eq_mul_inv] using hd
lemma DN_deriv_zero (d k : ℝ) : HasDerivAt (fun r => DN ((d,k),r)) (2*d/3) 0 := by
  have hd := ((HN_deriv_zero d k).add
    (((hasDerivAt_id (0:ℝ)).const_mul d).mul (PNr_hasDerivAt d k 0))).add
      ((((hasDerivAt_id (0:ℝ)).pow 3).const_mul (3*k)).mul (QNr_hasDerivAt d k 0))
  convert! hd using 1
  dsimp [DN,Pi.pow_apply,id_eq]
  norm_num [PN,QuadraticVariation.P_zero (by norm_num : (0:ℝ)<1)]
  ring
lemma Hr_negative_near_zero {d k : ℝ} (hd : d < 0) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), Hr ((d,k),r) < 0 := by
  have ht := (DN_deriv_zero d k).hasDerivWithinAt (s := Ioi 0)
  have hlim := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp ht
  have hn : (2:ℝ)*d/3 < 0 := by linarith
  filter_upwards [hlim.eventually (eventually_lt_nhds hn),self_mem_nhdsWithin] with r hh hr
  rw [Hr_DN hr]
  have hh' : DN ((d,k),r)/r < 0 := by
    simpa [slope,DN_zero,vsub_eq_sub,div_eq_mul_inv,mul_comm] using hh
  have h := (div_lt_iff₀ hr).mp hh'
  simpa using h
end QuinticLienard.QuadraticCoordinates

end OAI
