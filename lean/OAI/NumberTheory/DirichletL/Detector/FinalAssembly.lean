import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyFixedHigh

namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

theorem common_probe_of_raw_moments (hmom : RawMomentInput) : HeckeCommonProbe.UniformCommonProbe := by
  intro hβ
  have hgap : 0<HeckeZeroSupremum.beta-7/8 := by linarith
  obtain ⟨D⟩ := exists_high_data (HeckeZeroSupremum.beta-7/8) hgap
  obtain ⟨F⟩ := exists_source_data D
  obtain ⟨counts⟩ := source_count_parameters F
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := raw_input_chosen_height hmom hβ D F counts
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-7/8)/2
  have hloss : 0<loss := by dsimp [loss];linarith
  have hlossgap : loss<HeckeZeroSupremum.beta-7/8 := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    hmask,hH,hHbound,F.probe_low loss hloss η,?_⟩
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource] with Z hh hs
  exact hh Cm hCm.le hs

theorem dirichlet_of_raw_moments (hmom : RawMomentInput) (q : ℕ) (hq : q≠0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8:ℝ)<s.re)
    (hexc : ¬(χ=1 ∧ s=1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s≠0 :=
  HeckeCommonProbe.dirichlet_of_common_probe (common_probe_of_raw_moments hmom) q hq χ s hs hexc

theorem zeta_of_raw_moments (hmom : RawMomentInput) (s : ℂ) (hs : (7/8:ℝ)<s.re) :
    riemannZeta s≠0 :=
  HeckeCommonProbe.zeta_of_common_probe (common_probe_of_raw_moments hmom) s hs

theorem hecke_of_raw_moments (hmom : RawMomentInput) (χ : Character) (s : ℂ)
    (hs : (7/8:ℝ)<s.re) (hpole : s≠1 ∨ χ.residue≠1) : LFunction χ s≠0 :=
  HeckeCommonProbe.hecke_ne_zero_of_common_probe (common_probe_of_raw_moments hmom) χ s hs hpole

end SevenEighths.ProbeFinalAssembly

end

end OAI
