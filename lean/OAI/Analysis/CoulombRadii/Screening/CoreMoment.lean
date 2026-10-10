import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalDeficitMoment

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

def fixedCoreMomentBound (t : ℝ) : ℝ :=
  1+(observedDeficitCoefficient (fun _ : Fin 1 => t/16) 0 (t/4))^2+
    ∑' k : ℕ, (observedDeficitCoefficient (fun _ : Fin 1 => t/16) 0 (t/4)*
      (1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ))

lemma fixedCoreMomentBound_pos (t : ℝ) : 0<fixedCoreMomentBound t := by
  unfold fixedCoreMomentBound
  have hs : 0≤∑' k : ℕ, (observedDeficitCoefficient (fun _ : Fin 1 => t/16) 0 (t/4)*
      (1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ)) :=
    tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  positivity

lemma zero_offset_raw_deficit_moment {n : ℕ} (Z : ℕ) (hZ : 1≤Z)
    (u : Coulomb.H1Vector n) (ha : Coulomb.Antisymmetric u) (hm : Coulomb.mass u=1)
    {E : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (he : Coulomb.form (Coulomb.atom Z hZ) u≤E) {t : ℝ} (ht : 0<t) :
    Coulomb.potentialForm (fun x => (Coulomb.positiveInnerDeficit (Z:ℝ) (Metric.ball 0 t) x)^2) u≤
      fixedCoreMomentBound t := by
  let ψ := fromH1Wave u
  let g := fromH1Gradient u
  have hd : FormDomain ψ g := fromH1_domain u ha
  have hn : normSquared ψ=1 := (fromH1_mass u).trans hm
  have hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g≤energy Z χ h := by
    intro χ h hχ hχm
    have hv := Coulomb.unrestrictedFormBottom_le_trial (Coulomb.atom Z hZ)
      (asH1 χ h hχ.2.1 hχ.2.2.1 hχ.2.2.2.1) (asH1_antisymmetric hχ) ((asH1_mass ..).trans hχm)
    rw [asH1_energy Z hZ] at hv
    rw [fromH1_energy Z hZ]
    exact he.trans (EReal.coe_le_coe_iff.mp (hE.trans hv))
  have hbase : energy Z ψ g≤E+0 := by
    change energy Z (fromH1Wave u) (fromH1Gradient u)≤E+0
    simpa only [fromH1_energy Z hZ,add_zero] using he
  have hsqrt : Real.sqrt 3≤2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  have hw : Real.sqrt 3*(t/16)≤t/8 := by nlinarith
  have H := physical_raw_positive_deficit_second_moment Z hZ hd hn hmin hE hbase le_rfl
    (fun _ : Fin 1 => t/16) (fun _ => by positivity) (0:Fin 1)
    (show 0<t/4 by positivity) (show t/4+Real.sqrt 3*(t/16)≤t/2 by linarith)
    (show t/2+Real.sqrt 3*(t/16)≤t by linarith)
  have H' : Coulomb.potentialForm (fun x => (Coulomb.positiveInnerDeficit (Z:ℝ) (Metric.ball 0 t) x)^2) u≤
      (observedDeficitCoefficient (fun _ : Fin 1 => t/16) 0 (t/4))^2+
        ∑' k : ℕ, (observedDeficitCoefficient (fun _ : Fin 1 => t/16) 0 (t/4)*
          (1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ)) := by
    simpa only [Coulomb.potentialForm,ψ,g,asH1,fromH1Wave,ContinuousLinearEquiv.apply_symm_apply] using H
  unfold fixedCoreMomentBound
  linarith

end NeutralAtom
namespace Coulomb.RecordedEnsemble

lemma zero_offset_core_deficit_moment {n : ℕ} (Z : ℕ) (hZ : 1≤Z)
    (u : H1Vector n) (ha : Antisymmetric u) (hm : mass u=1)
    {E : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom (atom Z hZ))
    (he : form (atom Z hZ) u≤E) {t : ℝ} (ht : 0<t) (T : RecordedEnsemble n)
    (hT : T.Conserves u) (hO : T.OutSupported {y | t≤‖y‖}) :
    T.coreDeficitMoment Z≤NeutralAtom.fixedCoreMomentBound t := by
  have hd : Disjoint (Metric.ball (0:Space) t) {y | t≤‖y‖} := by
    refine Set.disjoint_left.mpr ?_
    intro y hy hz
    have : ‖y‖<t := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact not_lt_of_ge hz this
  exact (coreDeficitMoment_le_raw hT (Nat.cast_nonneg Z) measurableSet_ball hd hO).trans
    (NeutralAtom.zero_offset_raw_deficit_moment Z hZ u ha hm hE he ht)

end Coulomb.RecordedEnsemble
end

end

end OAI
