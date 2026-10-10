import OAI.Probability.PosteriorReplicas.Information.GenericInformationBound

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma priorLog_le_dimension_add_log {d : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1+(d:ℝ)+u) ≤ (d:ℝ)+Real.log (1+u) := by
  have hd : 0 ≤ (d:ℝ) := by positivity
  have hh := Real.log_le_log (by positivity : 0<1+(d:ℝ)+u)
    (show 1+(d:ℝ)+u ≤ (1+(d:ℝ))*(1+u) by nlinarith)
  rw [Real.log_mul (by positivity) (by positivity)] at hh
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0<1+(d:ℝ))
  linarith

lemma priorLog_le_dimension_add_div {d : ℕ} (hd : 1 ≤ d) {b : ℝ} (hb : 0 ≤ b) :
    Real.log (1+(d:ℝ)+b) ≤ 2*(d:ℝ)+b/(d:ℝ) := by
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0:ℝ)<d := by linarith
  have hh := log_le_tangent (by positivity : 0<1+(d:ℝ)+b) hdp
  have he : (1+(d:ℝ)+b)/(d:ℝ)-1 = 1/(d:ℝ)+b/(d:ℝ) := by
    field_simp
    ring
  have hi : (1:ℝ)/(d:ℝ) ≤ d := (div_le_iff₀ hdp).mpr (by nlinarith)
  have hl := Real.log_le_self hdp.le
  linarith

theorem gaussianReplicaBlock : GaussianReplicaBlock := by
  refine ⟨200+Real.pi,by positivity,64,?_⟩
  intro d hd
  dsimp only
  intro p hp f L hf hfL hpf N hN κ hκ
  have hL : 1 ≤ L := by
    have : IsProbabilityMeasure ((sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x))) := hpf ▸ hp
    exact spherical_density_bound_one_le (by omega) (fun x => (hfL x).2)
  have hi := gaussian_replica_information_real (m := 2*(d/16))
    (by omega : 4*(2*(d/16))+2*(d/16)+2≤d) (by omega) (by omega)
    (by omega : 2*(d/16)+2*(d/16)≤4*(2*(d/16))) (by omega) (by omega)
    p hf hL hfL hpf κ
  apply hi.trans
  apply ENNReal.ofReal_le_ofReal
  have hlog := priorLog_le_dimension_add_log (d:=d) (Real.log_nonneg hL)
  have hmono := Real.log_le_log (by linarith [Real.log_nonneg hL] : 0<1+Real.log L)
    (show 1+Real.log L ≤ 2+Real.log L by linarith)
  have hpos := Real.log_nonneg (show 1≤2+Real.log L by linarith [Real.log_nonneg hL])
  have hdp : 0 ≤ (d:ℝ) := by positivity
  nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le hpos]

theorem distanceReplicaBlock : DistanceReplicaBlock := by
  refine ⟨200+Real.pi,by positivity,64,?_⟩
  intro d hd p hp f b hb hf hfL hpf N hN κ hκ
  have hL : 1 ≤ Real.exp b := Real.one_le_exp_iff.mpr hb
  have hi := gaussian_replica_information_real (m := d/8-1) (ℓ := d/2)
    (by omega : 4*(d/16)+(d/8-1)+2≤d) (by omega) (by omega)
    (by omega : d/16+(d/8-1)≤d/2) (by omega) (by omega)
    p hf hL hfL hpf κ
  rw [Nat.sub_add_cancel (by omega : 1≤d/8),Real.log_exp] at hi
  apply hi.trans
  apply ENNReal.ofReal_le_ofReal
  have hlog := priorLog_le_dimension_add_div (by omega : 1≤d) hb
  have hdp : 0 ≤ (d:ℝ) := by positivity
  have hbdiv : 0 ≤ b/(d:ℝ) := div_nonneg hb hdp
  nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le hbdiv]

theorem syntheticReplicaBlock : SyntheticReplicaBlock := by
  refine ⟨200+Real.pi,by positivity,?_⟩
  intro d hd p hp f L hL hf hfL hpf N hN z hz
  have hi := gaussian_replica_information_real (m := d/8-1) (ℓ := d/2)
    (by omega : 4*(d/8)+(d/8-1)+2≤d) (by omega) (by omega)
    (by omega : d/8+(d/8-1)≤d/2) (by omega) (by omega)
    p hf hL hfL hpf (Kernel.deterministic z hz)
  rw [Nat.sub_add_cancel (by omega : 1≤d/8)] at hi
  apply hi.trans
  apply ENNReal.ofReal_le_ofReal
  have hH : messageEntropy (signalMessageLaw p (Kernel.deterministic z hz)) ≤ Real.log (N:ℝ) := by
    simpa only [messageEntropy_eq_finiteEntropy,Fintype.card_fin] using
      finiteEntropy_le_log_card (signalMessageLaw p (Kernel.deterministic z hz)).snd
  have hH' := div_le_div_of_nonneg_right hH (show 0 ≤ ((d/8:ℕ):ℝ) by positivity)
  have hlog := priorLog_le_dimension_add_log (d:=d) (Real.log_nonneg hL)
  have hpos := Real.log_nonneg (show 1≤1+Real.log L by linarith [Real.log_nonneg hL])
  have hdp : 0 ≤ (d:ℝ) := by positivity
  nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le hpos]

theorem incidenceReplicaBlock : IncidenceReplicaBlock := by
  refine ⟨200+Real.pi,by positivity,64,?_⟩
  intro d hd p hp f F hF hf hfF hpf N hN κ hκ
  have hi := gaussian_replica_information_real (m := d/16-1) (ℓ := d/4)
    (by omega : 4*(d/16)+(d/16-1)+2≤d) (by omega) (by omega)
    (by omega : d/16+(d/16-1)≤d/4) (by omega) (by omega)
    p hf hF hfF hpf κ
  rw [Nat.sub_add_cancel (by omega : 1≤d/16)] at hi
  apply hi.trans
  apply ENNReal.ofReal_le_ofReal
  have hH : messageEntropy (signalMessageLaw p κ) ≤ Real.log (N:ℝ) := by
    simpa only [messageEntropy_eq_finiteEntropy,Fintype.card_fin] using
      finiteEntropy_le_log_card (signalMessageLaw p κ).snd
  have hH' := div_le_div_of_nonneg_right hH (show 0 ≤ ((d/16:ℕ):ℝ) by positivity)
  have hlog := priorLog_le_dimension_add_log (d:=d) (Real.log_nonneg hF)
  have hpos := Real.log_nonneg (show 1≤1+Real.log F by linarith [Real.log_nonneg hF])
  have hdp : 0 ≤ (d:ℝ) := by positivity
  nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le hpos]

end PosteriorReplicas
end

end OAI
