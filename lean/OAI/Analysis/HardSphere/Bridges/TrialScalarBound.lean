import Mathlib
import OAI.Analysis.HardSphere.Allocation.TargetSupply
import OAI.Analysis.HardSphere.Bridges.SupplyIntegral
import OAI.Analysis.HardSphere.Cutoffs.Mesh
import OAI.Analysis.HardSphere.Thermodynamics.TrialScale

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma trial_scalar_bound {D Cn M c a b t : ℝ} {n : ℕ}
    (hD : 1 ≤ D) (hM : 0 ≤ M) (hc : 0 ≤ c) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hnlo : a*D^2 ≤ (n:ℝ)) (hnhi : (n:ℝ) ≤ Cn*D^2)
    (w : Time) (hw : t*(w:ℝ)=D⁻¹) :
    (n:ℝ)*(3*M*Real.exp (-c*((D^(1/12:ℝ)/6)/36)^2))+
      Real.exp (-(n:ℝ)/((1+D^(1/12:ℝ)/6)^3))+
      3*(M*Real.exp (-c*(D^(1/12:ℝ))^2))+
      scaleMoment 2 t (b*D^(-(1/3):ℝ)/8) 0 w/(1/12:ℝ)^2+
      scaleMoment 2 t 1 0 1/(1/3:ℝ)^2 ≤
      scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2 := by
  obtain ⟨rate, rfl⟩ : ∃ rate : ℝ, rate^2 = c := ⟨Real.sqrt c, Real.sq_sqrt hc⟩
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hRD : 0 ≤ D^(1/12:ℝ) := Real.rpow_nonneg hDp.le _
  have hp : (D^(1/12:ℝ))^2=D^(1/6:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hDp.le]
    norm_num
  have hs : ((D^(1/12:ℝ)/6)/36)^2=D^(1/6:ℝ)/46656 := by
    rw [div_pow,div_pow,hp]
    ring
  have hden : 0 < (1+D^(1/12:ℝ)/6)^3 := by positivity
  have hdenb : (1+D^(1/12:ℝ)/6)^3 ≤ 8*D := by
    exact (pow_le_pow_left₀ (by positivity) (by linarith :
      1+D^(1/12:ℝ)/6 ≤ 1+D^(1/12:ℝ)) 3).trans (regularScale_denominator hD)
  have hexp : Real.exp (-(n:ℝ)/((1+D^(1/12:ℝ)/6)^3)) ≤ Real.exp (-(a/8)*D) := by
    have hh : a/8*D ≤ (n:ℝ)/((1+D^(1/12:ℝ)/6)^3) := by
      apply (le_div_iff₀ hden).mpr
      calc
        _ ≤ (a/8*D)*(8*D) := mul_le_mul_of_nonneg_left hdenb (by positivity)
        _ = a*D^2 := by ring
        _ ≤ _ := hnlo
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  rw [hs,hp,source_window_moment hDp ht w hw,scaleMoment_two ht]
  simp only [show ((1:Time):ℝ)=1 from rfl,mul_one,one_pow,div_one]
  have hfirst : (n:ℝ)*(3*M*Real.exp (-rate^2*(D^(1/6:ℝ)/46656))) ≤
      Cn*D^2*(3*M)*Real.exp (-(rate^2/46656)*D^(1/6:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hnhi (by positivity : 0 ≤ 3*M*Real.exp (-rate^2*(D^(1/6:ℝ)/46656)))
    simpa only [show -rate^2*(D^(1/6:ℝ)/46656)=-(rate^2/46656)*D^(1/6:ℝ) by ring,mul_assoc] using hh
  unfold scalarTrialRemainder
  norm_num only [div_pow,one_pow] at *
  linarith

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma trial_remainder_small {ε : ℝ} (hε : 0 < ε) :
    ∃t₀ : ℝ,0 < t₀ ∧ ∀t : ℝ,0 < t → t ≤ t₀ →
    ∀Cn M c a b : ℝ,0 < c → 0 < a → ∃D₀ : ℝ,1 ≤ D₀ ∧ ∀D : ℝ,D₀ ≤ D →
      2*(scalarTrialRemainder Cn M c a b D+3888*t*normPowerMean 2) ≤ ε := by
  have hn := normPowerMean_nonneg 2
  let Q := 3888*(normPowerMean 2+1)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨ε/(4*Q),by positivity,?_⟩
  intro t ht htt Cn M c a b hc ha
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.1 ((scalarTrialRemainder_decay Cn M b hc ha).eventually
    (gt_mem_nhds (by positivity : (0:ℝ) < ε/4)))
  refine ⟨max 1 D₀,le_max_left _ _,?_⟩
  intro D hD
  have hd := hD₀ D ((le_max_right _ _).trans hD)
  have hsmall : t*Q ≤ ε/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*Q)).mp htt
    nlinarith
  dsimp [Q] at hsmall
  nlinarith

lemma sourceHalf_bounds {t r D A B : ℝ} (ht : 0 < t) (hr : 0 < r)
    (hD : 1 ≤ D) (hA : 0 < A) (hl : A ≤ D*r) (hu : D*r ≤ B) :
    (t/B^2)*D^2 ≤ (⌈t/r^2⌉₊:ℝ) ∧
      (⌈t/r^2⌉₊:ℝ) ≤ (t/A^2+1)*D^2 := by
  have hh := sourceMesh_bounds ht hr hD hA hl hu
  simp only [sourceMesh,Nat.cast_mul,Nat.cast_ofNat] at hh
  ring_nf at hh ⊢
  constructor <;> linarith [hh.1,hh.2]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison
attribute [local instance] Classical.propDecidable

def StrongExcept {L : Length} {N : ℕ} (n : ℕ) (t r R C S : ℝ) (w : Time)
    (y z v : Point) (ω : Fin N → ConfigurationPath 1 L) (label : Fin N)
    (B : Fin 7 → Set Point) : Prop :=
  ∀j, ENNReal.ofReal (99/100:ℝ)≤(volume.restrict (B j))
    {u | ENNReal.ofReal (9/10:ℝ)≤trialKernel t y z u (SuccessExcept n r R C S w v ω label)}

lemma full_success_count {L : Length} {N m : ℕ} (n : ℕ) (t r R C S : ℝ) (w : Time)
    (y z : Fin m → Point) (v : Point) (ω : Fin N → ConfigurationPath 1 L)
    (label : Fin m → Fin N) (B : Fin 7 → Set Point)
    (hB : ∀j,MeasurableSet (B j)) (hvol : ∀j,volume (B j)=1)
    (herror : ∀j, (∑i,∫⁻u in B j,trialKernel t (y i) (z i) u
      (SuccessExcept n r R C S w v ω (label i))ᶜ)≤ENNReal.ofReal ((m:ℝ)/70000)) :
    ((Finset.univ.filter (fun i ↦ ¬StrongExcept n t r R C S w (y i) (z i) v ω (label i) B)).card:ℝ)≤(m:ℝ)/10 := by
  classical
  let f : Fin m → Fin 7 → ℝ≥0∞ := fun i j ↦ ∫⁻u in B j,
    trialKernel t (y i) (z i) u (SuccessExcept n r R C S w v ω (label i))ᶜ
  have hf_le (i : Fin m) (j : Fin 7) : f i j≤1 := by
    calc
      _ ≤ ∫⁻_ in B j,(1:ℝ≥0∞) := lintegral_mono (fun _ ↦ prob_le_one)
      _ = _ := by simp [hvol]
  have hf_fin (i : Fin m) (j : Fin 7) : f i j≠⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hf_le i j)
  have hsum (j : Fin 7) : (∑i,(f i j).toReal)≤(m:ℝ)/70000 := by
    rw [←ENNReal.toReal_sum (fun i _ ↦ hf_fin i j)]
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (herror j)
    simpa only [f,ENNReal.toReal_ofReal (by positivity : 0≤(m:ℝ)/70000)] using hh
  have hc := seven_target_count (fun i j ↦ (f i j).toReal) (fun _ _ ↦ ENNReal.toReal_nonneg) hsum
  have hsub : Finset.univ.filter (fun i ↦ ¬StrongExcept n t r R C S w (y i) (z i) v ω (label i) B)⊆
      Finset.univ.filter (fun i ↦ ∃j,(1/1000:ℝ)<(f i j).toReal) := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i,?_⟩
    by_contra! hn
    have hg : StrongExcept n t r R C S w (y i) (z i) v ω (label i) B := by
      intro j
      let _ : IsProbabilityMeasure (volume.restrict (B j)) :=
        ⟨by rw [Measure.restrict_apply' (hB j), Set.univ_inter, hvol]⟩
      apply good_target_mass_of_failure _ _ _ (successExcept_measurable n r R C S w v ω (label i))
      change f i j≤ENNReal.ofReal (1/1000:ℝ)
      apply (ENNReal.toReal_le_toReal (hf_fin i j) ENNReal.ofReal_ne_top).mp
      simpa using hn j
    exact (Finset.mem_filter.mp hi).2 hg
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hc

lemma successExcept_mono_obstacles {L : Length} {N : ℕ} (n : ℕ) (r R C S : ℝ)
    (w : Time) (v : Point) (ω : Fin N → ConfigurationPath 1 L) (i : Fin N) (J : Finset (Fin N))
    (hi : i∉J) :
    SuccessExcept n r R C S w v ω i⊆
      {f | TrialCutoff L n r R C w S v f ∧ ∀j∈J,¬TrialCollision r (ω j) f} := by
  intro f hf
  exact ⟨hf.1,fun j hj ↦ hf.2 j (fun he ↦ hi (he ▸ hj))⟩

end HardSphere.Bridge

end
end

end

end OAI
