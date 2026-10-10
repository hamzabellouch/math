import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.OccupationBound

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere

namespace Orbital
variable {N : ℕ} (hN : 0<N) {L : Length}

lemma sliceIntegral_memLp (ψ : ScalarL2 N L) : MemLp (sliceIntegral hN ψ) 2 volume := by
  have hf := ground_slice_memLp hN ψ
  have ha := Phase.memLp_integral_norm hf
  have hh : MemLp (fun Y ↦ ∫x : Torus L,ψ (insertFirst hN x Y)) 2 volume := by
    refine ha.mono' hf.aestronglyMeasurable.integral_prod_right' ?_
    exact Eventually.of_forall fun Y ↦ norm_integral_le_integral_norm _
  exact hh.const_smul ((Real.sqrt (L.val^3))⁻¹ : ℝ)

lemma map_ae (ψ : ScalarL2 N L) : (map hN ψ : Configuration (N-1) L→ℂ)=ᵐ[volume] sliceIntegral hN ψ :=
  by
  unfold map
  exact MemLp.coeFn_toLp _

lemma map_add (f g : ScalarL2 N L) : map hN (f+g)=map hN f+map hN g := by
  apply Lp.ext
  have hp := (bathFirst_preserving hN L).quasiMeasurePreserving.tendsto_ae.eventually (Lp.coeFn_add f g)
  have hs := Measure.ae_ae_of_ae_prod hp
  filter_upwards [map_ae hN (f+g),map_ae hN f,map_ae hN g,Lp.coeFn_add (map hN f) (map hN g),hs,
    Phase.memLp_slices (ground_slice_memLp hN f),Phase.memLp_slices (ground_slice_memLp hN g)] with Y hh hf hg hsum hY hfi hgi
  rw [hh,hsum]
  change sliceIntegral hN (f+g) Y=(map hN f) Y+(map hN g) Y
  rw [hf,hg]
  unfold sliceIntegral
  rw [←smul_add,←integral_add (hfi.integrable (by norm_num)) (hgi.integrable (by norm_num))]
  congr 1
  apply integral_congr_ae
  exact hY

lemma map_smul (c : ℂ) (f : ScalarL2 N L) : map hN (c • f)=c • map hN f := by
  apply Lp.ext
  have hp := (bathFirst_preserving hN L).quasiMeasurePreserving.tendsto_ae.eventually (Lp.coeFn_smul c f)
  have hs := Measure.ae_ae_of_ae_prod hp
  filter_upwards [map_ae hN (c•f),map_ae hN f,Lp.coeFn_smul c (map hN f),hs] with Y hh hf hc hY
  rw [hh,hc]
  change sliceIntegral hN (c•f) Y=c • (map hN f) Y
  rw [hf]
  change (Real.sqrt (L.val^3))⁻¹ • (∫x : Torus L,(c•f) (insertFirst hN x Y))=
    c • ((Real.sqrt (L.val^3))⁻¹ • ∫x : Torus L,f (insertFirst hN x Y))
  rw [integral_congr_ae hY]
  simp only [Pi.smul_apply]
  rw [integral_smul]
  exact smul_comm _ _ _

section
attribute [local instance] scalarL2_addCommMonoid scalarL2_module

def linear : ScalarL2 N L →ₗ[ℂ] ScalarL2 (N-1) L where
  toFun := map hN
  map_add' := map_add hN
  map_smul' := map_smul hN

lemma map_norm_sq (ψ : ScalarL2 N L) : ‖map hN ψ‖^2=occupation hN ψ := by
  have hLp := L.property
  rw [scalar_norm_sq_integral]
  have hsi := integral_congr_ae ((map_ae hN ψ).fun_comp fun x ↦ ‖x‖^2)
  simp only [Function.comp_def] at hsi
  rw [hsi]
  unfold sliceIntegral occupation
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,
    integral_const_mul,Real.sq_sqrt (by positivity : 0≤L.val^3)]

lemma map_norm_le (ψ : ScalarL2 N L) : ‖map hN ψ‖≤‖ψ‖ := by
  have hh := (map_norm_sq hN ψ).trans_le (occupation_le_norm_sq hN ψ)
  nlinarith [norm_nonneg (map hN ψ),norm_nonneg ψ]


end

lemma norm_sq (ψ : ScalarL2 N L) : ‖continuous hN ψ‖^2=occupation hN ψ := map_norm_sq hN ψ

end Orbital

lemma occupation_smul {N : ℕ} (hN : 0<N) {L : Length} (c : ℝ) (ψ : ScalarL2 N L) :
    occupation hN (c • ψ)=c^2*occupation hN ψ := by
  rw [←Orbital.norm_sq,←Orbital.norm_sq]
  have hh := (Orbital.continuous hN (L:=L)).map_smul_of_tower c ψ
  rw [hh,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

end HardSphere
end
end

end OAI
