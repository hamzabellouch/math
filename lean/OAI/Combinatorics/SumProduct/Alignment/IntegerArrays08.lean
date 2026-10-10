import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays07
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
end

noncomputable section
namespace SourceIntegerArrays
open GlobalJoint
open RoughArrayFace
open RationalLattice MalcevCharacters RoughFaceShift RoughTopologicalFace RoughArrayCoordinates SourceResidueAlignment
open RoughScales RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw ProductExposureCutoff MeasureTheory Filter
open scoped BigOperators Topology ENNReal BoundedContinuousFunction NNReal
attribute [local instance] Classical.propDecidable
open ConstructedWordPlan.GlobalWordPlan
open ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
variable {a₀ : ℕ} (D : Pivot a₀) {ι : Fin D.targets→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : Fin D.targets→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j) (Γ : ∀ t i,Subgroup (G t i))
variable (coord : ∀ e,Fin (q (D.owner e)))

 

theorem source_intrinsic_decay
    (hΓ : ∀ t i g,g∈Γ t i ↔ ∀ j,∃ z : ℤ,(c t i).coord g j=z)
    (hmono : ∀ t i,Monotone (w t i)) (s : ℕ)
    (h0 : ∀ t i,(A t i).level 0=⊤) (h1 : ∀ t i,(A t i).level 1=⊤)
    (hs : ∀ t i,(A t i).level (s+1)=⊥)
    (a : ℕ) (m h : Fin D.targets→ℕ) (perm : ∀ t,Fin (m t+h t)≃Fin a)
    (w0 M Xp : ℕ→ℕ) (X : ℕ→Fin a→ℕ) (R Q : ℕ→ℝ) (L : ℕ→ℤ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j,4*primorial (w0 N)≤X N j) (hXp : ∀ N,4*primorial (w0 N)≤Xp N)
    (hXt : ∀ j,Tendsto (fun N=>X N j) atTop atTop) (hXpt : Tendsto Xp atTop atTop)
    (hR : ∀ N,0<R N) (hRX : Tendsto (fun N=>R N/(Xp N:ℝ)) atTop (𝓝 0))
    (hZ : ∀ t (u : ℝ),0<u →Tendsto (fun N=>(R N/(M N:ℝ))/
      (1+∑ j : Fin (m t),(X N (perm t (j.castAdd (h t))):ℝ)^2)^u) atTop atTop)
    (hQ0 : ∀ N,0≤Q N)
    (hSize : ∀ t,Tendsto (fun N=>(Q N+(∏ l : Fin (m t),(X N (perm t (l.castAdd (h t))):ℝ)^2)*(L N:ℝ))/R N) atTop (𝓝 0))
    (hWM : ∀ N,(primorial (w0 N):ℤ)∣(M N:ℤ))
    (hM : ∀ N,0<M N) (hMs : ∀ N,Smooth (w0 N) (M N:ℤ))
    (hL : ∀ N,0<L N) (hsm : ∀ N,Smooth (w0 N) (L N))
    (hWL : ∀ N,(primorial (w0 N):ℤ)∣L N) (hML : ∀ N,(M N:ℤ)∣L N)
    (hLexact : ∀ N,L N=(M N:ℤ)*(primorial (w0 N):ℤ)^(w0 N))
    (hXL : ∀ t (j : Fin (m t)),Tendsto (fun N=>(X N (perm t (j.castAdd (h t))):ℝ)/(L N:ℝ)) atTop atTop)
    (g x : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→∀ i,G t i)
    (slot : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→ι t→ℤ)
    (qval : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→Fin (q t)→ℤ)
    (hQ : ∀ t N y,y∈outsideDomain (fun l : Fin (h t)=>X N (perm t (l.natAdd (m t)))) (primorial (w0 N)) →
      ∀ b,b∈(fullDomain (fun l : Fin (m t)=>X N (perm t (l.castAdd (h t)))) (Xp N) (primorial (w0 N))).image
      (expose (L N) (M N:ℤ) (R N)) →∀ k,|(qval t N y b k:ℝ)|≤Q N)
    (metric : ∀ t i,MetricSpace ((G t i)⧸Γ t i))
    (hmetric : ∀ t i,QuotientGroup.instTopologicalSpace (Γ t i)=(metric t i).toUniformSpace.toTopologicalSpace) :
    letI : ∀ t i,MetricSpace ((G t i)⧸Γ t i):=fun t i=>(metric t i).replaceTopology (hmetric t i)
    ∀ (Obs : ℕ→((Fin a→ℕ)×ℕ)→∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ) (Kobs : ℝ≥0) (Bobs : ℝ)
    (_hLip : ∀ N z t i,LipschitzWith Kobs (Obs N z t i))
    (_hBound : ∀ N z t i y,|Obs N z t i y|≤Bobs)
    (J : ℕ→ℕ) (_hJ : ∀ N,0<J N) (_hRJ : ∀ N,R N=(M N:ℝ)*(J N:ℝ))
    (r : ℕ) (hs1 : 1 ≤ s) (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (Fs Bs : Finset (Scale a₀)) (q₀ : ℕ) (_hq₀ : pivotModulus s r hs1 D Fs Bs∣q₀)
    (b : Scale a₀) (_hb : b∈Bs) (τ : ℝ) (_hτ : 0<τ),
    Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)) {z |
        (ProbabilityMixtures.empirical (J N) (fun k : ℕ=>k) : Measure ℕ)
          {k | QuotientGroup.mk (rawLocalOrbit D G n q c hsk A w hA hw m h perm
            (M N) (J N) (L N) (R N) (fun t=>g t N) (fun t=>x t N)
            (fun t=>slot t N) (fun t=>qval t N) z (k:ℤ)) ∈
            intrinsicSuccess D G n q c hsk A w hA Γ coord s r hs1 formula (Obs N z) Fs q₀ b τ}
          ≤ (((((pivotOptions s r hs1 D Fs).card : ℝ≥0)⁻¹/2) : ℝ≥0) : ℝ≥0∞)}) atTop (𝓝 0)
 := by
  classical
  let : ∀ t i,MetricSpace ((G t i)⧸Γ t i):=fun t i=>(metric t i).replaceTopology (hmetric t i)
  intro Obs Kobs Bobs hLip hBound J hJ hRJ r hs1 formula Fs Bs q₀ hq₀ b hb τ hτ
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact (not_lt_of_ge bot_le hε).elim
  · intro ε hε
    by_contra hnot
    have hfreq : ∃ᶠ N in atTop, ε≤(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)) {z |
        (ProbabilityMixtures.empirical (J N) (fun k : ℕ=>k) : Measure ℕ)
          {k | QuotientGroup.mk (rawLocalOrbit D G n q c hsk A w hA hw m h perm
            (M N) (J N) (L N) (R N) (fun t=>g t N) (fun t=>x t N)
            (fun t=>slot t N) (fun t=>qval t N) z (k:ℤ)) ∈
            intrinsicSuccess D G n q c hsk A w hA Γ coord s r hs1 formula (Obs N z) Fs q₀ b τ}
          ≤ (((((pivotOptions s r hs1 D Fs).card : ℝ≥0)⁻¹/2) : ℝ≥0) : ℝ≥0∞)} := by
      simpa only [Filter.Frequently,not_le] using hnot
    obtain ⟨ρ,hρ,hρE⟩:=Filter.extraction_of_frequently_atTop hfreq
    obtain ⟨N,z,hzE,hz,hgood⟩:=source_intrinsic_selection D G n q c hsk A w hA hw Γ coord
      hΓ hmono s h0 h1 hs a m h perm (w0∘ρ) (M∘ρ) (Xp∘ρ) (X∘ρ) (R∘ρ) (Q∘ρ) (L∘ρ)
      (hw0.comp hρ.tendsto_atTop) (fun N=>hX (ρ N)) (fun N=>hXp (ρ N))
      (fun j=>(hXt j).comp hρ.tendsto_atTop) (hXpt.comp hρ.tendsto_atTop)
      (fun N=>hR (ρ N)) (hRX.comp hρ.tendsto_atTop)
      (fun t u hu=>(hZ t u hu).comp hρ.tendsto_atTop) (fun N=>hQ0 (ρ N))
      (fun t=>(hSize t).comp hρ.tendsto_atTop)
      (fun N=>hWM (ρ N)) (fun N=>hM (ρ N)) (fun N=>hMs (ρ N))
      (fun N=>hL (ρ N)) (fun N=>hsm (ρ N)) (fun N=>hWL (ρ N)) (fun N=>hML (ρ N))
      (fun N=>hLexact (ρ N)) (fun t j=>(hXL t j).comp hρ.tendsto_atTop)
      (fun t N=>g t (ρ N)) (fun t N=>x t (ρ N)) (fun t N=>slot t (ρ N))
      (fun t N=>qval t (ρ N)) (fun t N=>hQ t (ρ N)) metric hmetric
      (Obs∘ρ) Kobs Bobs (fun N=>hLip (ρ N)) (fun N=>hBound (ρ N))
      (J∘ρ) (fun N=>hJ (ρ N)) (fun N=>hRJ (ρ N)) r hs1 formula Fs Bs q₀ hq₀ b hb τ hτ
      _ ε hε hρE
    exact (not_lt_of_ge hzE) hgood

end SourceIntegerArrays
end

noncomputable section
namespace SourceIntegerArrays
open GlobalJoint
open RoughArrayFace
open RationalLattice MalcevCharacters RoughFaceShift RoughTopologicalFace RoughArrayCoordinates SourceResidueAlignment
open RoughScales RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw ProductExposureCutoff MeasureTheory Filter
open scoped BigOperators Topology ENNReal BoundedContinuousFunction NNReal
attribute [local instance] Classical.propDecidable
open ConstructedWordPlan.GlobalWordPlan
open ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
variable {a₀ : ℕ} (D : Pivot a₀) {ι : Fin D.targets→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : Fin D.targets→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j) (Γ : ∀ t i,Subgroup (G t i))
variable (coord : ∀ e,Fin (q (D.owner e)))

 
def sourceCell (M J p : ℕ) : Finset ℕ :=
  MicrocellFibers.fiber M J (J*(p/(M*J))) (p%M)

def fullCell (X M J p : ℕ) : Prop :=
  X≤M*(J*(p/(M*J))) ∧ M*(J*(p/(M*J))+J)≤X^2

 

def cellRatio (X W M J p : ℕ) (hW : 0<W) (hX : 4*W≤X) (S : Set ℕ) : ℝ :=
  (RawHarmonicProbability.law X W hW hX : Measure ℕ).real
    ((MicrocellFibers.point M (J*(p/(M*J))) (p%M) '' S)∩(sourceCell M J p : Set ℕ)) /
  (RawHarmonicProbability.law X W hW hX : Measure ℕ).real (sourceCell M J p : Set ℕ)

private lemma scalar_to_harmonic (X W M J p : ℕ) (hW : 0<W) (hX : 4*W≤X)
    (hM : 0<M) (hJ : 0<J) (hWM : W∣M) (hp : W.Coprime p) (hcell : fullCell X M J p)
    (c : ℝ≥0) (hsmall : ((M*J:ℕ):ℝ)/X≤(c:ℝ)/6) (S : Set ℕ)
    (hS : (((c/2:ℝ≥0):ℝ≥0∞))<(ProbabilityMixtures.empirical J (fun k : ℕ=>k) : Measure ℕ) S) :
    (c:ℝ)/3<cellRatio X W M J p hW hX S := by
  classical
  let f:=MicrocellFibers.point M (J*(p/(M*J))) (p%M)
  let : Nonempty (Fin J):=Fin.pos_iff_nonempty.mp hJ
  have hf : Function.Injective f:=MicrocellFibers.point_injective M _ _ hM
  have hpre : f ⁻¹' (f '' S)=S:=Set.preimage_image_eq S hf
  have he:=ProbabilityMixtures.empirical_preimage J (fun k : ℕ=>k) f (f '' S)
  rw [hpre] at he
  have huni : (ProbabilityMixtures.empirical J f : Measure ℕ)=
      (MicrocellProbability.uniformLaw (fun k : Fin J=>f k.val) : Measure ℕ) := by
    simp only [ProbabilityMixtures.empirical,hJ,↓reduceDIte]
    rfl
  rw [huni] at he
  have hsreal : (c:ℝ)/2<
      (MicrocellProbability.uniformLaw (fun k : Fin J=>f k.val) : Measure ℕ).real (f '' S) := by
    rw [he] at hS
    have hl:= (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr hS
    simpa only [measureReal_def,ENNReal.coe_toReal,NNReal.coe_div,NNReal.coe_ofNat] using hl
  have hr : W.Coprime (p%M) := by
    apply (UnitIntervalCounts.coprime_mod W (p%M)).mp
    rw [Nat.mod_mod_of_dvd p hWM]
    exact (UnitIntervalCounts.coprime_mod W p).mpr hp
  exact MicrocellFibers.raw_fiber_success X W M J (J*(p/(M*J))) (p%M) hW hX hM hJ
    (Nat.mod_lt p hM) hr hWM hcell.1 hcell.2 (c:ℝ) (f '' S) hsmall hsreal
 

theorem source_harmonic_decay
    (hΓ : ∀ t i g,g∈Γ t i ↔ ∀ j,∃ z : ℤ,(c t i).coord g j=z)
    (hmono : ∀ t i,Monotone (w t i)) (s : ℕ)
    (h0 : ∀ t i,(A t i).level 0=⊤) (h1 : ∀ t i,(A t i).level 1=⊤)
    (hs : ∀ t i,(A t i).level (s+1)=⊥)
    (a : ℕ) (m h : Fin D.targets→ℕ) (perm : ∀ t,Fin (m t+h t)≃Fin a)
    (w0 M Xp : ℕ→ℕ) (X : ℕ→Fin a→ℕ) (R Q : ℕ→ℝ) (L : ℕ→ℤ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j,4*primorial (w0 N)≤X N j) (hXp : ∀ N,4*primorial (w0 N)≤Xp N)
    (hXt : ∀ j,Tendsto (fun N=>X N j) atTop atTop) (hXpt : Tendsto Xp atTop atTop)
    (hR : ∀ N,0<R N) (hRX : Tendsto (fun N=>R N/(Xp N:ℝ)) atTop (𝓝 0))
    (hZ : ∀ t (u : ℝ),0<u →Tendsto (fun N=>(R N/(M N:ℝ))/
      (1+∑ j : Fin (m t),(X N (perm t (j.castAdd (h t))):ℝ)^2)^u) atTop atTop)
    (hQ0 : ∀ N,0≤Q N)
    (hSize : ∀ t,Tendsto (fun N=>(Q N+(∏ l : Fin (m t),(X N (perm t (l.castAdd (h t))):ℝ)^2)*(L N:ℝ))/R N) atTop (𝓝 0))
    (hWM : ∀ N,(primorial (w0 N):ℤ)∣(M N:ℤ))
    (hM : ∀ N,0<M N) (hMs : ∀ N,Smooth (w0 N) (M N:ℤ))
    (hL : ∀ N,0<L N) (hsm : ∀ N,Smooth (w0 N) (L N))
    (hWL : ∀ N,(primorial (w0 N):ℤ)∣L N) (hML : ∀ N,(M N:ℤ)∣L N)
    (hLexact : ∀ N,L N=(M N:ℤ)*(primorial (w0 N):ℤ)^(w0 N))
    (hXL : ∀ t (j : Fin (m t)),Tendsto (fun N=>(X N (perm t (j.castAdd (h t))):ℝ)/(L N:ℝ)) atTop atTop)
    (g x : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→∀ i,G t i)
    (slot : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→ι t→ℤ)
    (qval : ∀ t,ℕ→(Fin (h t)→ℕ)→Label (m t)→Fin (q t)→ℤ)
    (hQ : ∀ t N y,y∈outsideDomain (fun l : Fin (h t)=>X N (perm t (l.natAdd (m t)))) (primorial (w0 N)) →
      ∀ b,b∈(fullDomain (fun l : Fin (m t)=>X N (perm t (l.castAdd (h t)))) (Xp N) (primorial (w0 N))).image
      (expose (L N) (M N:ℤ) (R N)) →∀ k,|(qval t N y b k:ℝ)|≤Q N)
    (metric : ∀ t i,MetricSpace ((G t i)⧸Γ t i))
    (hmetric : ∀ t i,QuotientGroup.instTopologicalSpace (Γ t i)=(metric t i).toUniformSpace.toTopologicalSpace) :
    letI : ∀ t i,MetricSpace ((G t i)⧸Γ t i):=fun t i=>(metric t i).replaceTopology (hmetric t i)
    ∀ (Obs : ℕ→((Fin a→ℕ)×ℕ)→∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ) (Kobs : ℝ≥0) (Bobs : ℝ)
    (_hLip : ∀ N z t i,LipschitzWith Kobs (Obs N z t i))
    (_hBound : ∀ N z t i y,|Obs N z t i y|≤Bobs)
    (J : ℕ→ℕ) (_hJ : ∀ N,0<J N) (_hRJ : ∀ N,R N=(M N:ℝ)*(J N:ℝ))
    (r : ℕ) (hs1 : 1 ≤ s) (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (Fs Bs : Finset (Scale a₀)) (q₀ : ℕ) (_hq₀ : pivotModulus s r hs1 D Fs Bs∣q₀)
    (b : Scale a₀) (_hb : b∈Bs) (τ : ℝ) (_hτ : 0<τ),
    Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)) {z | fullCell (Xp N) (M N) (J N) z.2 ∧
        cellRatio (Xp N) (primorial (w0 N)) (M N) (J N) z.2 (primorial_pos _) (hXp N)
          {k | QuotientGroup.mk (rawLocalOrbit D G n q c hsk A w hA hw m h perm
            (M N) (J N) (L N) (R N) (fun t=>g t N) (fun t=>x t N)
            (fun t=>slot t N) (fun t=>qval t N) z (k:ℤ)) ∈
            intrinsicSuccess D G n q c hsk A w hA Γ coord s r hs1 formula (Obs N z) Fs q₀ b τ}
          ≤ ((pivotOptions s r hs1 D Fs).card : ℝ)⁻¹/3}) atTop (𝓝 0)
 := by
  classical
  let : ∀ t i,MetricSpace ((G t i)⧸Γ t i):=fun t i=>(metric t i).replaceTopology (hmetric t i)
  intro Obs Kobs Bobs hLip hBound J hJ hRJ r hs1 formula Fs Bs q₀ hq₀ b hb τ hτ
  have hd:=source_intrinsic_decay D G n q c hsk A w hA hw Γ coord
    hΓ hmono s h0 h1 hs a m h perm w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX hZ hQ0
    hSize hWM hM hMs hL hsm hWL hML hLexact hXL g x slot qval hQ metric hmetric
    Obs Kobs Bobs hLip hBound J hJ hRJ r hs1 formula Fs Bs q₀ hq₀ b hb τ hτ
  let c₀ : ℝ≥0:=((pivotOptions s r hs1 D Fs).card : ℝ≥0)⁻¹
  have hc₀ : (0:ℝ)<(c₀:ℝ) := by
    dsimp [c₀]
    simp only [NNReal.coe_natCast]
    exact inv_pos.mpr (by exact_mod_cast Finset.card_pos.mpr (pivotOptions_nonempty s r hs1 D Fs))
  have hsmall : ∀ᶠ N in atTop,R N/(Xp N:ℝ)≤(c₀:ℝ)/6:=
    hRX.eventually_le_const (by positivity)
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact (not_lt_of_ge bot_le hε).elim
  · intro ε hε
    filter_upwards [hsmall,(tendsto_order.mp hd).2 ε hε] with N hN hεN
    apply lt_of_le_of_lt ?_ hεN
    apply measure_mono_ae
    filter_upwards [joint_ae_fullDomain (X N) (Xp N) (primorial (w0 N))
      (primorial_pos _) (hX N) (hXp N)] with z hz
    intro hbad
    by_contra hgood
    have hgood := lt_of_not_ge hgood
    have hdvd : primorial (w0 N)∣M N := by exact_mod_cast hWM N
    have hp : (primorial (w0 N)).Coprime z.2:=(Finset.mem_filter.mp hz).2
    have hsize' : ((M N*J N:ℕ):ℝ)/(Xp N:ℝ)≤(c₀:ℝ)/6 := by
      simpa only [Nat.cast_mul,hRJ] using hN
    have ht:=scalar_to_harmonic (Xp N) (primorial (w0 N)) (M N) (J N) z.2
      (primorial_pos _) (hXp N) (hM N) (hJ N) hdvd hp hbad.1 c₀ hsize' _ hgood
    dsimp [c₀] at ht
    simp only [NNReal.coe_natCast] at ht
    exact (not_lt_of_ge hbad.2) ht

end SourceIntegerArrays

end
end

end OAI
