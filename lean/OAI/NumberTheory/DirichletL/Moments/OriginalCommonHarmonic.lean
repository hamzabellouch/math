import OAI.NumberTheory.DirichletL.Moments.CommonRadialData
import OAI.NumberTheory.DirichletL.Moments.SourceZeroEnergy
import OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass
import OAI.NumberTheory.DirichletL.Moments.SecondActiveCount

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentOriginalCommonHarmonic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceZeroEnergy CenteredMomentAddedZeroUniform
open CenteredMomentSecondActiveCount CenteredMomentActiveSource CenteredMomentCommonHarmonicMass
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def coefficient (s:Input ι) (R seed:Ideal O) : Ideal O→ℂ:=
  finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)

def sourceRadius (s:Input ι):ℝ:=(∏i,s.hi i)*s.b₁*s.b₂*(s.X₁*s.X₂)*(∏i,s.P i)

omit [DecidableEq ι] in
 theorem original_column_mask (s:Input ι) (R seed I:Ideal O) (h:coefficient s R seed I≠0):
    seed∣I:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I h
  rw [←he]
  by_contra hn
  apply hv0
  simp only [profileCoefficient,hn,ite_false,mul_zero]

omit [DecidableEq ι] in
 theorem original_column_norm (s:Input ι) (R seed I:Ideal O)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (h:coefficient s R seed I≠0):
    I≠0 ∧ (Ideal.absNorm I:ℝ)≤sourceRadius s:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I h
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    have hh:=(s.support i hn).1
    linarith [s.lo_pos i]
  have hh:=profileCoefficient_product_bound R s.ν s.W s.P s.hi s.W₁ s.W₂ s.b₁ s.b₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product hz hz₁ hz₂
    (fun i x hx=>(s.support i hx).2) (fun x hx=>s.support₁ hx) (fun x hx=>s.support₂ hx) v hv0
  rw [he] at hh
  simpa only [sourceRadius,map_one,Nat.cast_one,mul_one,div_one] using hh

omit [DecidableEq ι] in
 theorem actual_common_gates (s:Input ι) (R seed:Ideal O) (hs:Squarefree seed)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (C D:Ideal O)
    (hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
      (CenteredMomentSourceRow.supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))):
    C≠0 ∧ D≠0 ∧ CompletedGauss.primeSupport C=CompletedGauss.primeSupport D ∧
      seed∣C ∧ seed∣D ∧ (Ideal.absNorm C:ℝ)≤sourceRadius s ∧ (Ideal.absNorm D:ℝ)≤sourceRadius s:=by
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s R seed
  have hm (I:Ideal O) (_:I∈S) (hI:β I≠0):seed∣I:=original_column_mask s R seed I hI
  have hp:(C,D)∈commonShell S β (Ideal.absNorm (CenteredMomentRankinRadical.commonRadical C D):ℝ):=
    Finset.mem_filter.mpr ⟨hlabel,le_rfl⟩
  have hh:=active_common_data S β seed hs hm _ (C,D) hp
  have hn:=commonLabel_norm_bounds S β (sourceRadius s)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2) C D hlabel
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hn⟩

omit [DecidableEq ι] in
 theorem actual_original_common_mass (B δ:ℝ) (hB:0≤B) (hδ:0<δ):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z → ∀(s:Input ι),s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      ∀R seed:Ideal O,Squarefree seed → seed≠0 → ∀Y:ℝ,
      (∑v∈partitionLabels (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Y,
        1/Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm))≤C*Z^δ/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hbound⟩:=common_harmonic_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ s hz₁ hz₂ hcap R seed hs hs0 Y
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s R seed
  have hm (I:Ideal O) (_:I∈S) (hI:β I≠0):seed∣I:=original_column_mask s R seed I hI
  have hN (I:Ideal O) (_:I∈S) (hI:β I≠0):(Ideal.absNorm I:ℝ)≤Z^B:=
    (original_column_norm s R seed I hz₁ hz₂ hI).2.trans hcap
  apply hbound Z hZ seed hs hs0 (partitionLabels S β Y)
  · intro v hv
    obtain ⟨hp,hU⟩:=(mem_partitionLabels S β Y v).mp hv
    have hh:=active_common_data S β seed hs hm Y v.1 hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hU⟩
  · intro v hv
    have hp:=(mem_partitionLabels S β Y v).mp hv
    exact commonLabel_norm_bounds S β (Z^B) hN v.1.1 v.1.2 (Finset.mem_filter.mp hp.1).1

end SevenEighths.CenteredMomentOriginalCommonHarmonic

end

end OAI
