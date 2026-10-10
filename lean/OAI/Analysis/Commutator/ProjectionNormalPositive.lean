import Mathlib
import OAI.Analysis.Commutator.SpectralCompression
import OAI.Analysis.Commutator.SpectralExhaustion
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def ProjectionContinuousAtOne (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) : Prop :=
  ∀ P : ℕ → M,(∀ n,IsStarProjection (P n : H →L[ℂ] H)) →
    Monotone (fun n => (P n : H →L[ℂ] H)) →
    (∀ x,Tendsto (fun n => (P n : H →L[ℂ] H) x) atTop (𝓝 x)) →
    Tendsto (fun n => f (P n)) atTop (𝓝 (f 1))

lemma functional_compression_bound (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ)
    (A E : M) (hA : 0≤A) (h1 : A≤1) (hE : IsStarProjection (E : H →L[ℂ] H)) :
    ‖f A‖≤2*‖f (E*A*E)‖+2*‖f (1-E)‖ := by
  have hl : A≤(E*A*E+E*A*E)+((1-E)+(1-E)) := by
    have hh := positive_compression_bound (show 0≤(A:H →L[ℂ] H) from hA)
      (show (A:H →L[ℂ] H)≤1 from h1) hE
    change (A:H →L[ℂ] H)≤(E:H →L[ℂ] H)*(A:H →L[ℂ] H)*(E:H →L[ℂ] H)+
      (E:H →L[ℂ] H)*(A:H →L[ℂ] H)*(E:H →L[ℂ] H)+
      ((1:H →L[ℂ] H)-(E:H →L[ℂ] H)+((1:H →L[ℂ] H)-(E:H →L[ℂ] H)))
    simpa only [two_smul ℝ] using hh
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg (f.monotone hl) (f.map_nonneg hA)
  change ‖f A‖≤‖f ((E*A*E+E*A*E)+((1-E)+(1-E)))‖ at hn
  simp only [map_add] at hn
  have ht := norm_add_le (f (E*A*E)+f (E*A*E)) (f (1-E)+f (1-E))
  have ht1 := norm_add_le (f (E*A*E)) (f (E*A*E))
  have ht2 := norm_add_le (f (1-E)) (f (1-E))
  linarith

theorem positive_subsequence_null [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f)
    (A : ℕ → M) (hA : ∀ n,0≤A n) (h1 : ∀ n,A n≤1)
    (ht : ∀ x,Tendsto (fun n => (A n : H →L[ℂ] H) x) atTop (𝓝 0)) :
    ∃ u : ℕ → ℕ,StrictMono u ∧ Tendsto (fun n => f (A (u n))) atTop (𝓝 0) := by
  obtain ⟨u,hu,B,hBM,hB,hB1,hi,hdecay⟩ := exists_smoothing_subsequence M
    (fun n => (A n : H →L[ℂ] H)) (fun n => (A n).property) hA ht
  let P (n : ℕ) : M := ⟨threshold B (1/((n:ℝ)+1)),threshold_mem M hBM _⟩
  have hp (n : ℕ) : IsStarProjection (P n : H →L[ℂ] H) := threshold_projection B _
  obtain ⟨hmono,hstrong⟩ := threshold_exhaustion M hBM hB hi
  have hfp : Tendsto (fun n => f (P n)) atTop (𝓝 (f 1)) := hf P hp hmono hstrong
  have hfq : Tendsto (fun n => ‖f (1-P n)‖) atTop (𝓝 0) := by
    simp only [map_sub]
    simpa only [sub_self,norm_zero] using ((tendsto_const_nhds (x:=f 1)).sub hfp).norm
  have hbab : Tendsto (fun k => B*(A (u k) : H →L[ℂ] H)*B) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun _ => norm_nonneg _) hdecay tendsto_one_div_add_atTop_nhds_zero_nat)
  have hcompress (n : ℕ) : Tendsto (fun k => ‖f (P n*A (u k)*P n)‖) atTop (𝓝 0) := by
    have hh := threshold_compression_tendsto hB (by positivity : (0:ℝ)<1/((n:ℝ)+1))
      (fun k => (A (u k) : H →L[ℂ] H)) hbab
    have hs : Tendsto (fun k => P n*A (u k)*P n) atTop (𝓝 (0:M)) := tendsto_subtype_rng.mpr hh
    have hfc : Continuous f := map_continuous f
    simpa only [Function.comp_def,map_zero,norm_zero] using (hfc.tendsto 0 |>.comp hs).norm
  refine ⟨u,hu,tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨n,hn⟩ := (hfq.eventually_lt_const (show (0:ℝ)<ε/8 by positivity)).exists
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((hcompress n).eventually_lt_const (show (0:ℝ)<ε/8 by positivity))
  refine ⟨K,?_⟩
  intro k hk
  have hb := functional_compression_bound M f (A (u k)) (P n) (hA _) (h1 _) (hp n)
  have hsmall := hK k hk
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_norm] using (show ‖f (A (u k))‖<ε by linarith)

theorem positive_strong_null [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f)
    (A : ℕ → M) (hA : ∀ n,0≤A n) (h1 : ∀ n,A n≤1)
    (ht : ∀ x,Tendsto (fun n => (A n : H →L[ℂ] H) x) atTop (𝓝 0)) :
    Tendsto (fun n => f (A n)) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro v hv
  obtain ⟨u,hu,hlim⟩ := positive_subsequence_null M f hf (fun n => A (v n))
    (fun n => hA (v n)) (fun n => h1 (v n)) (fun x => (ht x).comp hv)
  exact ⟨u,hlim⟩

end Kadison.PositiveWOT

end

end
end

end OAI
