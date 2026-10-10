import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedResiduePairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeightWindowSeparation

namespace OAI

/-! Nontrivial translated cusps have zero constant coefficient. This is
deduced from the exact finite Gauss support, not assumed as a cusp condition. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedZero_observation_germ (m n : ℤ)
    (hn : ¬(3:Eisenstein) ∣ -lambdaE*(n:Eisenstein))
    (W : C_c(ℝ,ℂ)) {a : ℝ} (ha : 0<a) (d : ℝ)
    {K : Set CubicThetaPoint} (hK : IsCompact K) (hSK : cubicThetaShiftedWindow a d⊆K)
    (hhigh : ∀ p∈K,1<p.val.2) {s : ℂ} (hs : 1<s.re) :
    cubicThetaShiftedWindowObservation ((m:Eisenstein)+n*omegaE) 0 W a d hK
      =ᶠ[𝓝[≠] s] (fun _ => 0) := by
  have hL : MeromorphicOn
      (cubicThetaShiftedWindowObservation ((m:Eisenstein)+n*omegaE) 0 W a d hK)
      {z : ℂ | 1<z.re} := fun z hz =>
    cubicThetaShiftedWindowObservation_meromorphic _ 0 W a d hK hz
  have hR : MeromorphicOn (fun _ : ℂ => (0:ℂ)) {z : ℂ | 1<z.re} :=
    fun z _ => MeromorphicAt.const 0 z
  apply cubicThetaMeromorphic_identity hL hR (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hnear : ∀ᶠ z in 𝓝 (4:ℂ),3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hnear] with z hz
  have hD : cubicThetaShiftedFrequencyDirichlet ((m:Eisenstein)+n*omegaE) 0 z=0 := by
    rw [cubicThetaShiftedFrequencyDirichlet_eq,zero_sub,←neg_mul,ite_eq_right hn]
  rw [cubicThetaShiftedWindowObservation_normalized _ 0 W ha d hK hSK hhigh hz,hD,
    mul_zero,zero_mul]

lemma cubicThetaShiftedZero_window_pairing (m n : ℤ)
    (hn : ¬(3:Eisenstein) ∣ -lambdaE*(n:Eisenstein))
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 1<a) :
    (∫ v in Icc a d,star (W v)*
      cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 v/(v:ℂ)^3)=0 := by
  obtain ⟨K,hK,hSK,hbound⟩ := cubicThetaShiftedWindow_compact_container (by linarith : 0<a) d
  have hg := cubicThetaShiftedZero_observation_germ m n hn W (by linarith : 0<a) d hK hSK
    (fun p hp => ha.trans_le (hbound p hp)) (s:=(4/3:ℂ)) (by norm_num)
  have ht : Tendsto (fun z : ℂ => (z-4/3)*
      cubicThetaShiftedWindowObservation ((m:Eisenstein)+n*omegaE) 0 W a d hK z)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (0:ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hg] with z hz
    simp only [hz,mul_zero]
  rw [←cubicThetaShiftedModel_window_pairing _ 0 W (by linarith) d]
  exact tendsto_nhds_unique (cubicThetaShiftedWindowObservation_residue _ 0 W a d hK hSK) ht

theorem cubicThetaShiftedConstantCoefficient_zero (m n : ℤ)
    (hn : ¬(3:Eisenstein) ∣ -lambdaE*(n:Eisenstein)) {v : ℝ} (hv : 1<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 v=0 := by
  let F : ℝ → ℂ := fun t =>
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 t/(t:ℂ)^3
  have hF : ContinuousOn F (Ioi (1:ℝ)) := by
    dsimp only [F]
    have hsub : Ioi (1:ℝ)⊆Ioi (0:ℝ) := by
      intro t ht
      exact lt_trans (show (0:ℝ)<1 by norm_num) ht
    have hnum : ContinuousOn (cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0)
        (Ioi (1:ℝ)) :=
      (cubicThetaShiftedModelHorizontal_continuous _ 0).mono hsub
    have hden : ContinuousOn (fun t : ℝ => (t:ℂ)^3) (Ioi (1:ℝ)) :=
      (Complex.continuous_ofReal.pow 3).continuousOn
    exact hnum.div hden (fun t ht => pow_ne_zero 3
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans (show (0:ℝ)<1 by norm_num) ht))))
  have hz := cubicThetaHeightWindow_separates hF (fun W a d ha _ => by
    have he := cubicThetaShiftedZero_window_pairing m n hn W (d:=d) ha
    convert he using 1
    congr 1
    ext t
    dsimp [F]
    ring) hv
  have hv0 : (v:ℂ)^3≠0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by linarith : v≠0))
  exact (div_eq_iff hv0).mp hz |>.trans (zero_mul _)

lemma cubicThetaShifted_nontrivial_constant (n : ℤ) (hn : ¬(3:ℤ) ∣ n) :
    ¬(3:Eisenstein) ∣ -lambdaE*(n:Eisenstein) := by
  rintro ⟨c,hc⟩
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective c
  have hl : -lambdaE*(n:Eisenstein)=ofCoords (-n) (-2*n) := by
    unfold lambdaE ofCoords
    push_cast
    ring
  have hr : (3:Eisenstein)*ofCoords a b=ofCoords (3*a) (3*b) := by
    unfold ofCoords
    push_cast
    ring
  rw [hl,hr] at hc
  have hcoords := coordinates_unique (congrArg (fun z : Eisenstein => (z:ℂ)) hc)
  exact hn ⟨-a,by linarith [hcoords.1]⟩

theorem cubicThetaShiftedConstantCoefficient_nontrivial (m n : ℤ) (hn : ¬(3:ℤ) ∣ n)
    {v : ℝ} (hv : 1<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) 0 v=0 :=
  cubicThetaShiftedConstantCoefficient_zero m n (cubicThetaShifted_nontrivial_constant n hn) hv

end CubicFirstMoment

end

end OAI
