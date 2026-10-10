import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedFullFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedConstantCoefficient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveHeightSeparation

namespace OAI

/-! Vanishing of the actual constant coefficient at every positive height
for the two nontrivial translated cusps. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedPositiveZero_observation_germ (m n : ℤ)
    (hn : ¬(3:Eisenstein) ∣ -lambdaE*(n:Eisenstein))
    (W : C_c(ℝ,ℂ)) {a : ℝ} (ha : 0<a) (d : ℝ)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (hSK : cubicThetaShiftedWindow a d⊆K)
    {s : ℂ} (hs : 1<s.re) :
    cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) 0 W a d hK
      =ᶠ[𝓝[≠] s] (fun _ => 0) := by
  have hL : MeromorphicOn
      (cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) 0 W a d hK)
      {z : ℂ | 1<z.re} := fun z hz =>
    cubicThetaShiftedFullObservation_meromorphic _ 0 W ha d hK hz
  have hR : MeromorphicOn (fun _ : ℂ => (0:ℂ)) {z : ℂ | 1<z.re} :=
    fun z _ => MeromorphicAt.const 0 z
  apply cubicThetaMeromorphic_identity hL hR (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hnear : ∀ᶠ z in 𝓝 (4:ℂ),3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hnear] with z hz
  have hD : cubicThetaShiftedFrequencyDirichlet ((m:Eisenstein)+n*omegaE) 0 z=0 := by
    rw [cubicThetaShiftedFrequencyDirichlet_eq,zero_sub,←neg_mul,ite_eq_right hn]
  rw [cubicThetaShiftedFullObservation_normalized _ 0 W ha d hK hSK hz,hD,
    mul_zero,zero_mul]

lemma cubicThetaShiftedPositiveZero_window_pairing (m n : ℤ)
    (hn : ¬(3:Eisenstein) ∣ -lambdaE*(n:Eisenstein))
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) :
    (∫ v in Icc a d,star (W v)*
      cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 v/(v:ℂ)^3)=0 := by
  obtain ⟨K,hK,hSK,_⟩ := cubicThetaShiftedWindow_compact_container (by linarith : 0<a) d
  have hg := cubicThetaShiftedPositiveZero_observation_germ m n hn W (by linarith : 0<a) d hK hSK
    (s:=(4/3:ℂ)) (by norm_num)
  have ht : Tendsto (fun z : ℂ => (z-4/3)*
      cubicThetaShiftedFullObservation ((m:Eisenstein)+n*omegaE) 0 W a d hK z)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (0:ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hg] with z hz
    simp only [hz,mul_zero]
  rw [←cubicThetaShiftedModel_window_pairing _ 0 W (by linarith) d]
  exact tendsto_nhds_unique (cubicThetaShiftedFullObservation_residue _ 0 W ha d hK hSK) ht


theorem cubicThetaShiftedPositiveConstantCoefficient_zero (m n : ℤ)
    (hn : ¬(3:Eisenstein) ∣ -lambdaE*(n:Eisenstein)) {v : ℝ} (hv : 0<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 v=0 := by
  let F : ℝ → ℂ := fun t =>
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 t/(t:ℂ)^3
  have hF : ContinuousOn F (Ioi (0:ℝ)) := by
    have hnum := cubicThetaShiftedModelHorizontal_continuous ((m:Eisenstein)+n*omegaE) 0
    have hden : ContinuousOn (fun t : ℝ => (t:ℂ)^3) (Ioi (0:ℝ)) :=
      (Complex.continuous_ofReal.pow 3).continuousOn
    exact hnum.div hden (fun t ht => pow_ne_zero 3
      (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)))
  have hz := cubicThetaPositiveHeightWindow_separates hF (fun W a d ha _ => by
    have he := cubicThetaShiftedPositiveZero_window_pairing m n hn W (d:=d) ha
    convert he using 1
    congr 1
    ext t
    dsimp [F]
    ring) hv
  have hv0 : (v:ℂ)^3≠0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt hv))
  exact (div_eq_iff hv0).mp hz |>.trans (zero_mul _)

theorem cubicThetaShiftedPositiveConstantCoefficient_nontrivial (m n : ℤ)
    (hn : ¬(3:ℤ) ∣ n) {v : ℝ} (hv : 0<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 v=0 :=
  cubicThetaShiftedPositiveConstantCoefficient_zero m n
    (cubicThetaShifted_nontrivial_constant n hn) hv

end CubicFirstMoment

end

end OAI
