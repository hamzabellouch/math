import OAI.NumberTheory.DirichletL.Moments.FirstReferenceBlock
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalActiveDictionary
import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalLocalWeightSum

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceSource
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstRetainedNorm
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstPhysicalActiveDictionary CenteredMomentFirstSourceReduction
open CenteredMomentFirstInactiveRadicalMass CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentExceptionalAmplitudePair CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev SourceBlocks (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):=
  Blocks (effectiveScale p.val.1 p.val.2 E K) (localRadius s R seed K Z ξ p E)
    (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)

def originalBlock (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):ℂ:=
  block s.η (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    p.val.1 p.val.2
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).1
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).2 E
    (retainedRows (localRadius s R seed K Z ξ p E) 1) W (fun _=>logAnnulus)
    K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))

def radicalWeight (s:Input ι)(R seed:Ideal O)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
    ((commonRadical p.val.1 p.val.2).absNorm:ℝ)

omit [DecidableEq ι] in
lemma radicalWeight_nonneg (s:Input ι)(R seed:Ideal O)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):0≤radicalWeight s R seed p E:=
  div_nonneg (inactiveWeight_nonneg _ _ _ _) (Nat.cast_nonneg _)

lemma physicalMass_eq_sum (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ):
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ=
      ∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑n:SourceBlocks s R seed K Z ξ p E,‖originalBlock s R seed W K Z ξ p E n‖:=by
  rw [physicalMass_full_source]
  rfl

theorem original_block_sum (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,∀s:Input ι,∀R seed:Ideal O,
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→
      (∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
    ∀W:𝓢(ℝ,ℂ),∀K A:ℝ,0<K→0≤A→volume s.toData≤Z^B→K⁻¹≤Z^B→
    (∀p:Labels s R seed,∀E∈inactiveSubsets p.val.1 p.val.2,
      ∀n:SourceBlocks s R seed K Z ξ p E,
      ‖originalBlock s R seed W K Z ξ p E n‖/volume s.toData≤A*radicalWeight s R seed p E)→
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ/
      volume s.toData≤A*(C₀*Z^ε/(seed.absNorm:ℝ)) := by
  obtain ⟨Cd,hCd,hd⟩:=original_input_local_blocks_subpower hi b₁ b₂ B ξ (ε/2) hB hξ (by linarith)
  obtain ⟨Cm,hCm,hm⟩:=actual_inactive_radical_mass (B+1) (ε/2) (by linarith) (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ),eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hd hZ hfixed
  intro s R seed hs hs0 hz₁ hz₂ hhi hb₁ hb₂ hH W K A hK hA hV hKi hblock
  have hZ1:1≤Z:=by linarith
  have hcap:=input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ1 hfixed hV
  have hmass:=hm Z hZ seed hs hs0
    (finiteColumns (Fintype.piFinset s.pools)) (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (fun I _ hI=>original_column_mask s R seed I hI)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2.trans hcap) 0 (le_refl _)
  have hf:∀p E,0≤radicalWeight s R seed p E:=radicalWeight_nonneg s R seed
  have hsector (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
      (hE:E∈inactiveSubsets p.val.1 p.val.2):
      (∑n:SourceBlocks s R seed K Z ξ p E,‖originalBlock s R seed W K Z ξ p E n‖/volume s.toData)≤
        (Cd*Z^(ε/2)*A)*radicalWeight s R seed p E := by
    have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
    have hcard:=hd s hhi hb₁ hb₂ hH p.val.1 p.val.2 hp.1.1 hp.2.1 E K hK hV hKi
    change (Fintype.card (SourceBlocks s R seed K Z ξ p E):ℝ)≤Cd*Z^(ε/2) at hcard
    calc
      _≤∑_n:SourceBlocks s R seed K Z ξ p E,A*radicalWeight s R seed p E:=
        Finset.sum_le_sum (fun n _=>hblock p E hE n)
      _ = (Fintype.card (SourceBlocks s R seed K Z ξ p E):ℝ)*(A*radicalWeight s R seed p E) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ ≤ (Cd*Z^(ε/2))*(A*radicalWeight s R seed p E) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hA (hf p E))
      _ = _ := (mul_assoc _ _ _).symm
  rw [physicalMass_eq_sum]
  simp only [Finset.sum_div]
  calc
    _≤∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        (Cd*Z^(ε/2)*A)*radicalWeight s R seed p E:=by
      apply Finset.sum_le_sum;intro p _
      exact Finset.sum_le_sum (fun E hE=>hsector p E hE)
    _=(Cd*Z^(ε/2)*A)*(∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        radicalWeight s R seed p E):=by simp_rw [←Finset.mul_sum]
    _≤(Cd*Z^(ε/2)*A)*(Cm*Z^(ε/2)/(seed.absNorm:ℝ)):=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _=_ := by
      rw [show Z^ε=Z^(ε/2)*Z^(ε/2) by rw [←Real.rpow_add (by linarith : 0<Z)];congr 1;ring]
      ring

end SevenEighths.CenteredMomentFirstReferenceSource

end

end OAI
