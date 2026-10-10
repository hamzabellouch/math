import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.PhysicalRescaleDomain
import OAI.Analysis.HardSphere.Thermodynamics.ThermodynamicCalibration
import OAI.Analysis.HardSphere.Thermodynamics.PhysicalPhaseWindow

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere

lemma occupation_le_norm_sq {N : ℕ} (hN : 0<N) {L : Length} (ψ : ScalarL2 N L) :
    occupation hN ψ≤‖ψ‖^2 := by
  have hLp := L.property
  let f := fun p : Configuration (N-1) L×Torus L ↦ ψ (insertFirst hN p.2 p.1)
  have hf : MemLp f 2 (volume.prod volume) := ground_slice_memLp hN ψ
  have ha := Phase.memLp_integral_norm hf
  have hc : MemLp (fun Y ↦ ‖∫x,f (Y,x)‖) 2 volume := by
    refine ha.mono' hf.aestronglyMeasurable.integral_prod_right'.norm ?_
    exact Eventually.of_forall fun Y ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
      exact norm_integral_le_integral_norm _
  have hi := (hf.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).integral_prod_left
  have hbound : (∫Y,‖∫x,f (Y,x)‖^2)≤(volume : Measure (Torus L)).real univ * ∫p,‖f p‖^2 ∂volume.prod volume := by
    calc
      _ ≤ ∫Y,(volume : Measure (Torus L)).real univ * ∫x,‖f (Y,x)‖^2 := by
        apply integral_mono_ae hc.integrable_sq (hi.const_mul _)
        filter_upwards [Phase.memLp_slices hf] with Y hY
        exact (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2).trans
          (Phase.integral_norm_sq_le hY)
      _ = _ := by rw [integral_const_mul,←integral_prod _ (hf.integrable_norm_pow (by norm_num : (2:ℕ)≠0))]
  have hm : (∫p,‖f p‖^2 ∂volume.prod volume)=‖ψ‖^2 := by
    rw [scalar_norm_sq_integral]
    exact (bathFirst_preserving hN L).integral_comp
      (by
        cases N with
        | zero => omega
        | succ n =>
          convert (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm.measurableEmbedding.comp
            (MeasurableEquiv.prodComm (α:=Configuration n L) (β:=Torus L)).measurableEmbedding using 1 <;> try rfl
          funext p i
          simp [insertFirst,MeasurableEquiv.piFinSuccAbove,MeasurableEquiv.prodComm])
      (fun X ↦ ‖ψ X‖^2)
  rw [hm,Measure.real,BathSlice.volume_torus,ENNReal.toReal_ofReal (by positivity : 0≤L.val^3)] at hbound
  unfold occupation
  change (L.val^3)⁻¹*(∫Y,‖∫x,f (Y,x)‖^2)≤‖ψ‖^2
  calc
    _ ≤ (L.val^3)⁻¹*(L.val^3*‖ψ‖^2) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ L.property.ne'),one_mul]

end HardSphere
end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere
attribute [local instance] Classical.propDecidable

theorem eventually_all_ground_occupation :
    ∃ε₀ c₀ : ℝ,0<ε₀ ∧ 0<c₀ ∧
    ∀a ρ : ℝ,0<a → 0<ρ → ρ*a^3<ε₀ →
    ∀(N : ℕ→ℕ) (L : ℕ→Length) (hN : ∀k,0<N k),
      Tendsto N atTop atTop → Tendsto (fun k ↦ (L k).val) atTop atTop →
      Tendsto (fun k ↦ (N k:ℝ)/(L k).val^3) atTop (𝓝 ρ) →
      ∀ᶠ k in atTop,∀ψ : Jet (N k) (L k),IsGroundVector (N k) (L k) a ψ →
        c₀≤occupation (hN k) ψ.1 := by
  obtain ⟨A,c,D₀,hA,hc,hD₀,K₀,hK₀,hscaled⟩ := physical_scaled_occupation
  have hAp : 0<A := by linarith
  have hDp : 0<D₀ := by linarith
  refine ⟨A^3/(4*D₀^2),c,by positivity,hc,?_⟩
  intro a ρ ha hρ hd N L hN hNtop hLtop hdensity
  let K := fun k ↦ Calibration.scaleK a A (N k) (L k).val
  have hKtop : Tendsto K atTop atTop :=
    (Calibration.scale_limits ha hAp hρ N (fun k ↦ (L k).val) hN
      (fun k ↦ (L k).property) hLtop hdensity).1
  have hw := Calibration.eventually_scaled_window ha hAp hρ hDp hd N
    (fun k ↦ (L k).val) hN (fun k ↦ (L k).property) hLtop hdensity
  have hlim := Calibration.densityLimit_above_threshold ha hAp hρ hDp hd
  filter_upwards [hw,hKtop.eventually (eventually_ge_atTop K₀),hNtop.eventually (eventually_ge_atTop 2)] with k hk hK hNk
  have hKpos : 0<K k := by omega
  let : NeZero (K k) := ⟨hKpos.ne'⟩
  let J : Length := ⟨(K k:ℝ),by exact_mod_cast hKpos⟩
  let D : ℝ := (N k:ℝ)/J.val^3
  let α : ℝ := D*(a*J.val/(L k).val)
  have hD : D₀≤D := by
    have hh : (D₀+Calibration.densityLimit a A ρ)/2<D := hk.2.2.1
    linarith
  have hαlo : A/2≤α := hk.1.le
  have hαhi : α≤2*A := hk.2.1.le
  have hDpos : 0<D := hDp.trans_le hD
  have hradius : J.val/(L k).val*a=α/D := by
    dsimp only [α]
    field_simp
  intro ψ hψ
  have hg := Rescaling.jet_ground (L:=J) hψ
  rw [hradius] at hg
  have hh := hscaled hNk (show J.val=(K k:ℝ) from rfl) hK D α rfl hD hαlo hαhi
    (Rescaling.jet (N k) J (L k) ψ) hg
  rw [Rescaling.jet_fst,Rescaling.pull_occupation] at hh
  exact hh

theorem condensation : Condensation := by
  obtain ⟨ε,c,hε,hc,hevent⟩ := eventually_all_ground_occupation
  refine ⟨ε,c,hε,hc,?_⟩
  intro a ρ ha hρ hd N L hN hNtop hLtop hdensity Ψ hΨ
  apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (x:=1) (fun k ↦ ?_))
  · filter_upwards [hevent a ρ ha hρ hd N L hN hNtop hLtop hdensity] with k hk
    exact hk (Ψ k) (hΨ k)
  · simpa only [(hΨ k).2.2.1,one_pow] using occupation_le_norm_sq (hN k) (Ψ k).1

end HardSphere
end
end

end OAI
