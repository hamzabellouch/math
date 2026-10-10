import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCoreSlices
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateMarginalScales
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationPrimePriorsGrid
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourceHeights
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingModulusBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinSourceSelectedNormEventual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSourceScales
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSourceSyntax

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval TemplateOneSidedBudget
open HistoryFrequencyLabels HistoryFrequencyBudget Arithmetic Preliminaries Construction
open HigherBiasSource HigherBiasSource.SourceTemplate HigherBiasSourceRoleBounds HigherBiasSourceWord
open InitialCharacterScale DiagonalEstimate
open Template.OneSidedPhase TemplateOneSidedSourceScales TemplateOneSidedSourceSyntax
open TemplateOneSidedNumericInputs TemplateOneSidedPrior Filter
attribute [local instance] Classical.propDecidable

theorem eventually_sourceCorePairMean_small (k j : ℕ) (hj : j<k)
    (BD α β ρ γ c₀ c : ℝ) (hBD : 0≤BD) (hα : 0<α) (hαβ : α<β)
    (hρ : 0<ρ) (hγ : 0<γ) (hc₀ : 0<c₀) (hc : 0<c) :
    ∃rate : ℝ,0<rate ∧ ∀ᶠ L : ℝ in atTop,
    ∀(d : Decomposition)(E : Finset ℕ)(δ : ℝ),
    (∀p∈E,p.Prime) →
    (∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L) →
    ∀(s : SelectedWordSource d E δ L k α β ρ γ c₀)(w : FixedConfigurationWitness s c BD),
    ∀(B : ℕ→ℤ)(P : ℕ+),P∈DiagonalEstimate.sourcePivotRanges w j →
    ∀e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j),
    (∀i,IsCopiedBulk w.configuration (wordSize k L) j (e i) ↔
      IsCopiedBulk w.configuration (wordSize k L) j i) →
    e∉codePreservingMatchings w.configuration (wordSize k L) j →
    ∀h h':SourceHistory (k:=k) (L:=L) (BD:=BD) j,h.val.1=h'.val.1 →
      ‖sourceCorePairMean w j hj B
        (fun l=>(bound (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) l:ℤ)) P e h h'‖ ≤
          Real.exp (-rate*Real.exp (lowerExponent α γ*L)) := by
  let a := BD+20*Real.log (depthScale k)
  have ha : 0≤a := add_nonneg hBD
    (mul_nonneg (by norm_num) (Real.log_nonneg (one_le_depthScale k)))
  let Cmod := survivingPairModulusConstant a k j
  have hCmod : 0<Cmod := survivingPairModulusConstant_pos ha k j
  have hβ : 0<β := hα.trans hαβ
  obtain ⟨C,hC,happly⟩ := exists_surviving_core_prime_bound k j
    (sourceWidthConstant k) (sourceCopiedConstant k)
    (sourceAtomWidth k c) (configurationProductWidth k c) (sourceCopiedWidth k c)
    (depthScale_pos k) ha hCmod.le (show 0≤β+1 by linarith)
    (sourceCopiedWidth_nonneg k hc)
  obtain ⟨rate,hrate,hgrid⟩ := eventually_original_prime_priors_scale_grid
    (τ:=Unit⊕(Fin (2^j)⊕Fin (2^j))) C (depthScale k) (β+1) 4 α β γ β
    hC.le (depthScale_pos k) (by linarith) hα hγ hβ.le
  refine ⟨rate,hrate,?_⟩
  filter_upwards [hgrid,source_compiler_heights_eventually k j BD c β hBD (by linarith),
    eventually_sourceSurvivor_marginal_bounds k hα hαβ hρ hγ hc₀ hc,
    eventually_sourceSelectedFactors_norms k BD c α hBD hα,
    (wordSize_tendsto k).eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)]
    with L hgridL hheight hmass hfactor hm hL
  intro d E δ hE hband s w B P hP e hbulk hbad h h' hroot
  have hbulkinv (i) : IsCopiedBulk w.configuration (wordSize k L) j (e.symm i) ↔
      IsCopiedBulk w.configuration (wordSize k L) j i := by
    simpa only [Equiv.apply_symm_apply] using (hbulk (e.symm i)).symm
  have hcode : ¬∀i,actualCopiedCode w.configuration (wordSize k L) j ((Equiv.refl _) i)=
      actualCopiedCode w.configuration (wordSize k L) j (e.symm i) := by
    intro he
    apply hbad
    rw [mem_codePreservingMatchings]
    intro i
    simpa only [Equiv.refl_apply,Equiv.symm_apply_apply] using he (e i)
  obtain ⟨long,short,positive,n,hne,hforward,hreverse,hn,hαpair,hαn,hngap,hshort,hlong,hsep⟩ :=
    changed_actualCode_sourceEdge_scales w hα hγ hL hband j hj
      (Equiv.refl _) e.symm (fun _=>Iff.rfl) hbulkinv hcode
  let m := wordSize k L
  let width := sourceWidth w.configuration m
  let V := fun l=>(bound a (m:ℝ) l:ℤ)
  let T := sourcePivotTarget w.configuration s.J (gapSchedule BD k L)
  let Tc := T j+gapSchedule BD k L (j+1)
  let EL := sourceSurvivorShells w j long
  let ES := sourceSurvivorShells w j short
  let hEL := sourceSurvivorShells_pos w j long
  let hES := sourceSurvivorShells_pos w j short
  have hmR : (1:ℝ) ≤ m := hm
  have hmN : 1 ≤ ⌊depthScale k*L⌋₊ := by exact_mod_cast hm
  have ht : RangeSupported (ranges a (m:ℝ) j) j [] h.val.1 h.val.2 := h.property
  have hu : RangeSupported (ranges a (m:ℝ) j) j [] h'.val.1 h'.val.2 := h'.property
  have hQ := surviving_historyPairResidueModulus_le_quartic_cost ha k j (depthScale k) L hmN
    width P P (Equiv.refl _) e h.val.1 h'.val.1 h.val.2 h'.val.2 ht hu
  have hheightL := hheight Cmod hCmod.le
  apply norm_sourceCorePairMean_le_of_slices w j hj B V P e h h' long short hroot _
  intro p hp
  have hUV := hfactor d E δ β ρ γ c₀ hband s w j hj (Equiv.refl _) e.symm
    (sourceSurvivorPhaseMasks w j P e) (sourceSurvivorPhaseMasks_norm w j P e)
    h h' hroot p hp long short hne P
  let U := fun q : PrimeUpTo s.locations.Q=>
    sourceLongFactor w.configuration m j hj (Equiv.refl _) e.symm (familyCharacter s.family)
      (sourceScheduledUnits w j) (sourceSurvivorPhaseMasks w j P e) p long short P
      h.val.1 h.val.2 h'.val.2 q.val
  let VV := fun q : ↥ES=>
    sourceShortFactor w.configuration m j hj (Equiv.refl _) e.symm (familyCharacter s.family)
      (sourceScheduledUnits w j) (sourceSurvivorPhaseMasks w j P e) p long short P
      h.val.1 h.val.2 h'.val.2 q.val.val
  let χ := fun q : ↥ES=>exposedCharacter
    (sourceSliceCharacters w.configuration m j hj s.locations.Q (familyCharacter s.family)
      short q.val.val) positive
  have hbound := happly L (β+1) (lowerExponent α γ) (shortExponent γ n.val)
    (longExponent γ n.val+scaleStep γ) β rate (hgridL n hn)
    EL ES hEL hES width (sourceWidthConstant k*(m+1)) B T s.J P h.val.1 h'.val.1
    (Equiv.refl _) e h.val.2 h'.val.2 long
    (fun q : ↥ES=>heldPrimeCoordinates p long short q.val)
    (sourcePairPolynomialGate w j P e h h') s.locations.X Tc χ U VV
    hmR (source_X_ge_one w) (actual_sourceWidth_le w m) le_rfl
    (actual_sourceCopied_card_le w m j hj.le) ht hu hheightL.1
    (by simpa only [Int.cast_natCast] using hheightL.2 d E δ α ρ γ c₀ s w hj P hP) hQ
    (fun q hq r=>sourceHeldCoordinates_height w j hL.le hCmod.le hband p hp long short
      q r.val hq r.property)
    (fun q=>sourceSelected_exposedCharacter_ne_one w j hj short q.val q.property positive)
    hUV.1 (fun q=>hUV.2 q.val q.property)
    (hmass d E δ BD hE hband s w j long).1
    (hmass d E δ BD hE hband s w j short).1
    (fun q hq=>(hshort q hq).1) (fun q hq=>(hshort q hq).2)
    (fun q hq=>(hlong q hq).1) (fun q hq=>(hlong q hq).2)
  have hamp (q r : PrimeUpTo s.locations.Q) :
      survivingCorePairAmplitude k j width B V T s.J P h.val.1 h'.val.1
        (Equiv.refl _) e h.val.2 h'.val.2 (sourcePairPolynomialGate w j P e h h')
        s.locations.X (a*(m:ℝ)) (sourceAtomWidth k c) (configurationProductWidth k c)
        Tc (sourceCopiedWidth k c) (insertCoordinate long (heldPrimeCoordinates p long short r) (q.val:ℤ)) =
      sourcePairCoreAmplitude w j B V P e h h' (primeIntegerAssignment (twoPrimeSample p long short q r)) := by
    rw [insert_heldPrimeCoordinates p long short hne q r]
    rfl
  rw [sourceSurvivorCoordinatePrior_eq,sourceSurvivorCoordinatePrior_eq]
  change ‖(primeShellPrior EL hEL).cmean (fun q=>(primeShellPrior ES hES).cmean
    (fun r=>sourceMaskedRetainedPairAt w.configuration m j hj (Equiv.refl _) e.symm
      (familyCharacter s.family) (familyCenter s.family) (sourceScheduledUnits w j)
      (sourceSurvivorPhaseMasks w j P e) p long short q r P h.val.1 h.val.2 h'.val.2 *
      sourcePairCoreAmplitude w j B V P e h h' (primeIntegerAssignment (twoPrimeSample p long short q r))))‖ ≤ _
  rw [sourceRetainedPair_cmean_eq_oneSidedMean w.configuration m j hj (Equiv.refl _) e.symm
    (familyCharacter s.family) (familyCenter s.family) (sourceScheduledUnits w j)
    (sourceSurvivorPhaseMasks w j P e) p long short hne EL ES hEL hES hsep P h.val.1
    h.val.2 h'.val.2 positive hforward hreverse]
  simp_rw [←hamp]
  simpa only [oneSidedMean,FinitePrior.cmean,sourceShortMass,mul_assoc,U,VV,χ,V,T,Tc,m,width,
    a,wordSize] using hbound

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
