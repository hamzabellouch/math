import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RotationIntegralBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.NonlinearLocalLimitBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakExteriorDecayBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma exterior_tail_tendsto_of_le {ι : Type*} {l : Filter ι}
    {ρ : ι → Space → ℝ} {R S : ℝ}
    (hi : ∀ i, Integrable (ρ i)) (hn : ∀ i x, 0 ≤ ρ i x) (hRS : R ≤ S)
    (ht : Tendsto (fun i => ∫ x in {x : Space | R < ‖x‖}, ρ i x) l (𝓝 0)) :
    Tendsto (fun i => ∫ x in {x : Space | S < ‖x‖}, ρ i x) l (𝓝 0) := by
  apply squeeze_zero (fun i => integral_nonneg (hn i)) _ ht
  intro i
  exact setIntegral_mono_set (hi i).integrableOn (ae_of_all _ (hn i))
    (ae_of_all _ (fun x hx => hRS.trans_lt hx))

theorem screened_limit_dynamics {ι : Type*} {l : Filter ι} [NeBot l]
    {ρ : ι → Space → ℝ} {Z : ι → ℝ} {u : Space → ℝ} {q R k C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hm : ∀ i, Measurable (ρ i)) (hi : ∀ i, Integrable (ρ i))
    (hn : ∀ i x, 0 ≤ ρ i x) (hb : ∀ i, ∃ M ≥ 0, ∀ x, ρ i x ≤ M)
    (hu : ContinuousOn u {0}ᶜ)
    (hc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      TendstoUniformlyOn (fun i x => Z i/‖x‖-tfPotential (ρ i) x) u l K)
    (hTF : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      ∃ e : ι → ℝ, Tendsto e l (𝓝 0) ∧ ∀ᶠ i in l, ∀ x ∈ K,
        |ρ i x-k*(max (Z i/‖x‖-tfPotential (ρ i) x-1) 0)^(3/2:ℝ)| ≤ e i)
    (hq : Tendsto (fun i => Z i-∫ x, ρ i x) l (𝓝 q))
    (ht : Tendsto (fun i => ∫ x in {x : Space | R < ‖x‖}, ρ i x) l (𝓝 0))
    (hcap : ∀ x, x ≠ 0 → u x ≤ 1+C/‖x‖^4) :
    PuncturedPoisson u (fun x => CoulombPDE.reaction (4*Real.pi*k) (u x)) ∧
    (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | R < ‖x‖} → (∫ x, u x*Δ g x) = 0) ∧
    (∀ p : Space, R < ‖p‖ → sphereMean u p = q/‖p‖) ∧
    (∀ ε > 0, ∃ S > 0, ∀ x : Space, S ≤ ‖x‖ → |u x| < ε) := by
  let f : ι → Space → ℝ := fun i x => Z i/‖x‖-tfPotential (ρ i) x
  have hf : ∀ i, ContinuousOn (f i) {0}ᶜ := by
    intro i
    obtain ⟨M,hM,hMb⟩ := hb i
    exact screened_field_continuousOn (hm i) (hi i) hM (hn i) hMb
  have he : ∀ i, PuncturedPoisson (f i) (fun x => 4*Real.pi*ρ i x) := by
    intro i
    obtain ⟨M,hM,hMb⟩ := hb i
    exact screened_field_punctured_poisson (hm i) (hi i) hM (hn i) hMb
  have hρc (K : Set Space) (hK : IsCompact K) (hK0 : K ⊆ {0}ᶜ) :
      TendstoUniformlyOn ρ (fun x => k*(max (u x-1) 0)^(3/2:ℝ)) l K := by
    obtain ⟨e,he0,hebound⟩ := hTF K hK hK0
    exact local_tf_density_limit hK (hu.mono hK0) (hc K hK hK0) he0 hebound
  have hρc' (K : Set Space) (hK : IsCompact K) (hK0 : K ⊆ {0}ᶜ) :
      TendstoUniformlyOn (fun i x => 4*Real.pi*ρ i x)
        (fun x => CoulombPDE.reaction (4*Real.pi*k) (u x)) l K := by
    have hh := compact_uniformly_comp_continuous_real (f := ρ)
      (u := fun x => k*(max (u x-1) 0)^(3/2:ℝ)) (G := fun t : ℝ => 4*Real.pi*t)
      hK ((reaction_continuous k).continuousOn.comp (hu.mono hK0)
        (fun _ _ => mem_univ _)) (continuous_const.mul continuous_id) (hρc K hK hK0)
    simpa only [CoulombPDE.reaction,mul_assoc] using hh
  have hpart := punctured_poisson_integrable_density_limit hf hu
    (fun i => (hi i).const_mul (4*Real.pi))
    ((reaction_continuous (4*Real.pi*k)).continuousOn.comp hu
      (fun _ _ => mem_univ _)) he hc hρc'
  have hhar : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | R < ‖x‖} → (∫ x, u x*Δ g x) = 0 := by
    intro g hg hcg hs
    exact weak_field_tail_harmonic hR hf hu hi hn he hc ht hg hcg hs
  have hmean (p : Space) (hp : R < ‖p‖) : sphereMean u p = q/‖p‖ := by
    have hp0 : p ≠ 0 := norm_pos_iff.mp (hR.trans hp)
    apply sphericalMean_limit_charge hp0 hm hi hn hb
      (fun x hx => hu.continuousAt (isOpen_compl_singleton.mem_nhds hx))
      (hc _ (isCompact_sphere _ _) (by
        intro x hx hx0
        rw [mem_sphere_zero_iff_norm,hx0,norm_zero] at hx
        exact (norm_ne_zero_iff.mpr hp0) hx.symm)) hq
    exact exterior_tail_tendsto_of_le hi hn hp.le ht
  refine ⟨hpart,hhar,hmean,?_⟩
  apply weak_exterior_mean_uniform_decay (K := 1+C/R^4) hR hu hhar _ hmean
  intro x hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hR.trans_le hx)
  apply (hcap x hx0).trans
  exact add_le_add_right (div_le_div_of_nonneg_left hC (pow_pos hR 4)
    (pow_le_pow_left₀ hR.le hx 4)) 1

end CoulombAnalysis

end

end OAI
