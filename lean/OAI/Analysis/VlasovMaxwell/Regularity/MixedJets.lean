import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ConeRegularity
import OAI.Analysis.VlasovMaxwell.Retarded.MagneticBoundaryJets

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma retarded_density_spatial_smooth {s : Solution} (hf : ContDiff ℝ ∞ s.f)
    (hE : ContDiff ℝ ∞ s.E) (hB : ContDiff ℝ ∞ s.B) (hc : CompactOnFiniteHorizons s)
    {t P : ℝ} (ht : 0≤t)
    (hsupport : ∀ u∈Icc (0:ℝ) t, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0) :
    ContDiff ℝ ∞ (fun x => ∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z)) ∧
    ContDiff ℝ ∞ (fun x => ∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z)) := by
  obtain ⟨δ,hδ,hden⟩ := uniform_cone_denominator P
  have hG := normalisedRetardedExtension_smooth hδ hf hE hB t
  rw [retardedElectricDensity_polar_compact hf hE hB hc ht hδ hden hsupport,
    retardedMagneticDensity_polar_compact hf hE hB hc ht hδ hden hsupport]
  exact ⟨compactPolarIntegral_smooth t P _ hG,compactPolarIntegral_smooth t P _
    (contDiff_cross.comp (contDiff_fst.snd.fst.prodMk hG))⟩

lemma norm_iteratedFDeriv_const_smul {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → W}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (c : ℝ) (x : U) :
    ‖iteratedFDeriv ℝ n (fun y => c • f y) x‖=‖c‖*‖iteratedFDeriv ℝ n f x‖ := by
  rw [iteratedFDeriv_const_smul_apply' ((hf.of_le (by exact_mod_cast le_top)).contDiffAt),norm_smul]

lemma mixed_fields_derivative_tame {d : Datum} (hd : Admissible d)
    (k : ℕ) (hk : 1≤k) (P A : ℝ) (hA : 1≤A) :
    ∃ D C : ℝ, 0≤D ∧ 0≤C ∧
      (∀ x, ‖iteratedFDeriv ℝ (k+1) d.E₀ x‖≤D ∧ ‖iteratedFDeriv ℝ (k+1) d.B₀ x‖≤D) ∧
      ∀ (s : Solution) (E B : Field), PicardRegular d s →
      ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → TransportFor s E B →
      ∀ T : ℝ, T≤1 →
      (∀ u∈Icc (0:ℝ) T, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0) →
      ParticleJetBound k T A s.f → SpatialJetBound k T A E B →
      ∀ H : ℝ → ℝ, Continuous H → (∀ u∈Icc (0:ℝ) T, 0≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ z, ‖iteratedFDeriv ℝ (k+1) (fun w => s.f (u,w)) z‖≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ x, ‖iteratedFDeriv ℝ (k+1) (fun y => E (u,y)) x‖≤H u ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => B (u,y)) x‖≤H u) →
      ∀ t∈Icc (0:ℝ) T, ∀ x,
        ‖iteratedFDeriv ℝ (k+1) (fun y => s.E (t,y)) x‖≤D+C*(∫ u in Icc (0:ℝ) t, 1+H u) ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => s.B (t,y)) x‖≤D+C*(∫ u in Icc (0:ℝ) t, 1+H u) := by
  obtain ⟨D,hD,hinit,hbd⟩ := datum_boundary_global_jets hd (k+1)
  obtain ⟨K,hK,hcone⟩ := physical_cone_derivative_tame k hk P A hA
  refine ⟨D,(4*Real.pi)⁻¹*K,hD,by positivity,hinit,?_⟩
  intro s E B hs hE hB hV T hT hsupport hfj hEBj H hH hHpos hft hEBt t ht x
  by_cases ht0 : t=0
  · subst t
    have hEs : (fun y => s.E (0,y))=d.E₀ := funext hs.initial_E
    have hBs : (fun y => s.B (0,y))=d.B₀ := funext hs.initial_B
    simpa [hEs,hBs] using hinit x
  have htpos : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  let q : Solution := {s with E:=E,B:=B}
  have hbound := hcone q hs.smooth_f hE hB hs.compact T hT hsupport hfj hEBj H hH hHpos hft hEBt t ht x
  have hsmooth := retarded_density_spatial_smooth (s:=q) hs.smooth_f hE hB hs.compact ht.1
    (fun u hu => hsupport u ⟨hu.1,hu.2.trans ht.2⟩)
  have hboundary := hbd t ⟨htpos,ht.2.trans hT⟩
  have he (y : Vec) := mixed_physical_vector hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
    hs.smooth_rho hs.smooth_current hs.maxwell htpos y
  have heq : (fun y => s.E (t,y))=(fun y => electricBoundaryField (datumBoundarySolution d) t y+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity q t y (y+z)) := by
    funext y; rw [(he y).1,(hs.boundary_eq htpos y).1]
  have hbq : (fun y => s.B (t,y))=(fun y => magneticBoundaryField (datumBoundarySolution d) t y+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity q t y (y+z)) := by
    funext y; rw [(he y).2,(hs.boundary_eq htpos y).2]
  rw [heq,hbq]
  constructor
  · apply (norm_iteratedFDeriv_add_le hboundary.1.1 (hsmooth.1.const_smul _) (k+1) x).trans
    rw [norm_iteratedFDeriv_const_smul hsmooth.1,Real.norm_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
    exact (add_le_add (hboundary.2 x).1 (mul_le_mul_of_nonneg_left hbound.1 (by positivity))).trans_eq (by ring)
  · apply (norm_iteratedFDeriv_add_le hboundary.1.2 (hsmooth.2.const_smul _) (k+1) x).trans
    rw [norm_iteratedFDeriv_const_smul hsmooth.2,Real.norm_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
    exact (add_le_add (hboundary.2 x).2 (mul_le_mul_of_nonneg_left hbound.2 (by positivity))).trans_eq (by ring)

end RVM
end

end OAI
