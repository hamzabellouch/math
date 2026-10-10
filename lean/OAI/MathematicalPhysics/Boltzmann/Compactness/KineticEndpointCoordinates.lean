import OAI.MathematicalPhysics.Boltzmann.Approximation.CapCoveredDamping
import OAI.MathematicalPhysics.Boltzmann.Branching.EndpointHistoryMass

namespace OAI

section

/-! # The four compactness alternatives for kinetic endpoints -/

noncomputable section

open Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem kinetic_endpoint_subsequence {a T : ℝ} (z : ℕ → Published.KineticPhase)
    (ht : ∀ n, (z n).1.1 ∈ Icc a T) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (Tendsto (fun n => ‖(z (φ n)).2‖) atTop atTop ∨
      ((∃ V : ℝ, 0 ≤ V ∧ ∀ n, ‖(z (φ n)).2‖ ≤ V) ∧
      (Tendsto (fun n => ‖transverse (z (φ n)).1.2‖) atTop atTop ∨
       Tendsto (fun n => |axial (z (φ n)).1.2|) atTop atTop ∨
       ∃ z₀ : Published.KineticPhase, Tendsto (z ∘ φ) atTop (𝓝 z₀)))) := by
  rcases endpoint_subsequence_or_escape (fun n => (z n).2) with hvel | hvel
  · obtain ⟨v,φ,hφ,hv⟩ := hvel
    obtain ⟨V,hVpos,hV⟩ := (Metric.isBounded_range_of_tendsto _ hv).exists_pos_norm_le
    rcases endpoint_subsequence_or_escape (fun n => transverse (z (φ n)).1.2) with htrans | htrans
    · obtain ⟨y,ψ,hψ,hy⟩ := htrans
      rcases endpoint_subsequence_or_escape (fun n => axial (z (φ (ψ n))).1.2) with hax | hax
      · obtain ⟨b,χ,hχ,hb⟩ := hax
        obtain ⟨t,_,τ,hτ,htt⟩ := isCompact_Icc.tendsto_subseq
          (fun n => ht (φ (ψ (χ n))))
        let ρ : ℕ → ℕ := φ ∘ ψ ∘ χ ∘ τ
        have hx : Tendsto (fun n => (z (ρ n)).1.2) atTop (𝓝 (PlaneChart.join y b)) := by
          have h := PlaneChart.join_tendsto
            ((hy.comp hχ.tendsto_atTop).comp hτ.tendsto_atTop) (hb.comp hτ.tendsto_atTop)
          simpa only [ρ,Function.comp_apply,PlaneChart.join_transverse_axial] using h
        refine ⟨ρ,hφ.comp (hψ.comp (hχ.comp hτ)),Or.inr ⟨?_,Or.inr (Or.inr ?_)⟩⟩
        · exact ⟨V,hVpos.le,fun n => hV _ (mem_range_self (ψ (χ (τ n))))⟩
        · refine ⟨((t,PlaneChart.join y b),v),?_⟩
          exact (htt.prodMk_nhds hx).prodMk_nhds
            (((hv.comp hψ.tendsto_atTop).comp hχ.tendsto_atTop).comp hτ.tendsto_atTop)
      · refine ⟨φ ∘ ψ,hφ.comp hψ,Or.inr ⟨?_,Or.inr (Or.inl ?_)⟩⟩
        · exact ⟨V,hVpos.le,fun n => hV _ (mem_range_self (ψ n))⟩
        · simpa only [Function.comp_apply,Real.norm_eq_abs] using hax
    · exact ⟨φ,hφ,Or.inr ⟨⟨V,hVpos.le,fun n => hV _ (mem_range_self n)⟩,Or.inl htrans⟩⟩
  · exact ⟨id,strictMono_id,Or.inl hvel⟩

end BoltzmannNonuniqueness

end

end

section

/-! # Continuous endpoint coordinates and a fixed nonaxial velocity window -/

noncomputable section

open Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.FiveGainMap

theorem fromKinetic_continuous : Continuous toKinetic.symm := by
  change Continuous (fun z : Published.KineticPhase =>
    (z.1.1,WithLp.ofLp z.1.2,WithLp.ofLp z.2))
  exact continuous_fst.fst.prodMk
    (((PiLp.continuous_ofLp 2 _).comp continuous_fst.snd).prodMk
      ((PiLp.continuous_ofLp 2 _).comp continuous_snd))

theorem nonaxial_of_transverse_ne_zero {v : Velocity} (hv : transverse v ≠ 0) :
    0 < (WithLp.ofLp v) 0^2+(WithLp.ofLp v) 1^2 := by
  have hnorm : 0 < ‖transverse v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  rw [EuclideanSpace.real_norm_sq_eq] at hnorm
  simpa [transverse,Fin.sum_univ_two] using hnorm

theorem eventually_velocityWindow {v : ℕ → Velocity} {v₀ : Velocity}
    (hv : Tendsto v atTop (𝓝 v₀)) (hv₀ : transverse v₀ ≠ 0) :
    ∃ R b : ℝ, 0 < R ∧ 0 < b ∧ ∀ᶠ n in atTop, v n ∈ JetCopyDatum.velocityWindow R b := by
  have htrans : Tendsto (fun n => ‖transverse (v n)‖) atTop (𝓝 ‖transverse v₀‖) := by
    exact (show Continuous (fun w : Velocity => ‖transverse w‖) by unfold transverse; fun_prop).continuousAt.tendsto.comp hv
  refine ⟨‖v₀‖+1,‖transverse v₀‖/2,by positivity,half_pos (norm_pos_iff.mpr hv₀),?_⟩
  filter_upwards [hv.norm.eventually_lt_const (lt_add_one _),
    htrans.eventually_const_lt (half_lt_self (norm_pos_iff.mpr hv₀))] with n hn ht
  exact ⟨hn.le,ht.le⟩

end BoltzmannNonuniqueness.FiveGainMap

end

end

end OAI
