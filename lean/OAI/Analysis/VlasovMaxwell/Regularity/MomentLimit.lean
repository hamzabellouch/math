import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.PicardBounds

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma uniform_compact_moment {X W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℕ → X → Vec → ℝ} {f : X → Vec → ℝ} {S : Set X} {P : ℝ}
    (hF : ∀ n, ∀ p∈S, Continuous (F n p)) (hf : ∀ p∈S, Continuous (f p))
    (hSF : ∀ n, ∀ p∈S, ∀ v : Vec, P<‖v‖ → F n p v=0)
    (hSf : ∀ p∈S, ∀ v : Vec, P<‖v‖ → f p v=0)
    (hlim : TendstoUniformlyOn (fun n (p : X × Vec) => F n p.1 p.2)
      (fun p => f p.1 p.2) atTop {p | p.1∈S})
    {ψ : Vec → W} (hψ : Continuous ψ) (hbψ : ∀ v, ‖ψ v‖≤1) :
    TendstoUniformlyOn (fun n p => ∫ v, F n p v • ψ v) (fun p => ∫ v, f p v • ψ v) atTop S := by
  let K := closedBall (0:Vec) P
  have hK : IsCompact K := isCompact_closedBall _ _
  have hkiF (n : ℕ) (p : X) (hp : p∈S) : HasCompactSupport (F n p) :=
    compactSupport_of_zero_off hK (fun v hv => hSF n p hp v (by simpa only [K,mem_closedBall_zero_iff,not_le] using hv))
  have hkif (p : X) (hp : p∈S) : HasCompactSupport (f p) :=
    compactSupport_of_zero_off hK (fun v hv => hSf p hp v (by simpa only [K,mem_closedBall_zero_iff,not_le] using hv))
  have hiF (n : ℕ) (p : X) (hp : p∈S) : Integrable (fun v => F n p v • ψ v) :=
    ((hF n p hp).smul hψ).integrable_of_hasCompactSupport (hkiF n p hp).smul_right
  have hif (p : X) (hp : p∈S) : Integrable (fun v => f p v • ψ v) :=
    ((hf p hp).smul hψ).integrable_of_hasCompactSupport (hkif p hp).smul_right
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε/(volume.real K+1)
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with n hn p hp
  rw [dist_eq_norm,← integral_sub (hif p hp) (hiF n p hp)]
  have he : (∫ v in K, f p v • ψ v-F n p v • ψ v)=∫ v, f p v • ψ v-F n p v • ψ v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hv' : P<‖v‖ := by simpa only [K,mem_closedBall_zero_iff,not_le] using hv
    simp [hSf p hp v hv',hSF n p hp v hv']
  rw [← he]
  have hb : ∀ v∈K, ‖f p v • ψ v-F n p v • ψ v‖≤δ := by
    intro v hv
    have hh := hn (p,v) hp
    rw [dist_eq_norm,Real.norm_eq_abs] at hh
    rw [← sub_smul,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hh.le (hbψ v) (norm_nonneg _) hδ.le).trans_eq (mul_one δ)
  apply (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hb).trans_lt
  have hd : δ*(volume.real K+1)=ε := by dsimp [δ]; exact div_mul_cancel₀ _ (by positivity)
  nlinarith

lemma continuous_velocity_slice {f : Particle} {T t : ℝ}
    (hf : ContinuousOn f {p | p.1∈Icc 0 T}) (ht : t∈Icc 0 T) (x : Vec) :
    Continuous (fun v => f (t,x,v)) := by
  apply continuousOn_univ.mp
  apply hf.comp ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn)
  exact fun _ _ => ht

lemma uniform_source_moments {f : ℕ → Particle} {g : Particle} {T A R P : ℝ}
    (hf : ∀ n, ContinuousOn (f n) {p | p.1∈Icc 0 T})
    (hg : ContinuousOn g {p | p.1∈Icc 0 T})
    (hbF : ∀ n, LocalParticleBound T A R P (f n)) (hbG : LocalParticleBound T A R P g)
    (hl : TendstoUniformlyOn f g atTop {p | p.1∈Icc 0 T}) :
    TendstoUniformlyOn (fun n (p : ℝ × Vec) => rho (fun z => f n (p.1,z)) p.2)
      (fun p => rho (fun z => g (p.1,z)) p.2) atTop {p | p.1∈Icc 0 T} ∧
    TendstoUniformlyOn (fun n (p : ℝ × Vec) => current (fun z => f n (p.1,z)) p.2)
      (fun p => current (fun z => g (p.1,z)) p.2) atTop {p | p.1∈Icc 0 T} := by
  have hcF (n : ℕ) (p : ℝ × Vec) (hp : p.1∈Icc 0 T) : Continuous (fun v => f n (p.1,p.2,v)) :=
    continuous_velocity_slice (hf n) hp p.2
  have hcG (p : ℝ × Vec) (hp : p.1∈Icc 0 T) : Continuous (fun v => g (p.1,p.2,v)) :=
    continuous_velocity_slice hg hp p.2
  have hsF (n : ℕ) (p : ℝ × Vec) (hp : p.1∈Icc 0 T) (v : Vec) (hv : P<‖v‖) : f n (p.1,p.2,v)=0 := by
    by_contra hn
    exact (not_le_of_gt hv) ((hbF n p.1 hp p.2 v).2 hn).2
  have hsG (p : ℝ × Vec) (hp : p.1∈Icc 0 T) (v : Vec) (hv : P<‖v‖) : g (p.1,p.2,v)=0 := by
    by_contra hn
    exact (not_le_of_gt hv) ((hbG p.1 hp p.2 v).2 hn).2
  have hl' := hl.comp (fun p : (ℝ × Vec) × Vec => (p.1.1,p.1.2,p.2))
  have hr := uniform_compact_moment hcF hcG hsF hsG hl' (continuous_const (y:=(1:ℝ))) (fun v => by norm_num)
  have hj := uniform_compact_moment hcF hcG hsF hsG hl' (contDiff_velocity (k:=1)).continuous
    (fun v => (norm_velocity_lt_one v).le)
  constructor
  · convert hr using 1; simp only [smul_eq_mul,mul_one,rho]; rfl
  · exact hj

end RVM
end

end OAI
