import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays06
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates
open ConstructedWordPlan.GlobalWordPlan
open AllLevelFactorization AllLevelFactorization.Factorization MeasureTheory
open ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
open Filter
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a) {ι : Fin D.targets→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : Fin D.targets→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j)
variable (Γ : ∀ t i,Subgroup (G t i)) (coord : ∀ e,Fin (q (D.owner e)))

 

def intrinsicTerminal {r : ℕ} (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (obs : ∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ) (Fs : Finset (Scale a))
    (q₀ : ℕ) (b : Scale a) (p : Path D) (i : Comparison D Fs r)
    (x : (Full G n q c hsk A w hA)⧸FullLattice G n q c hsk A w hA Γ) : ℝ :=
  let t:=i.2.1.1
  let a₀:=blockProduct (scaleRun D 0 p b*i.1.val) (block D.index D.tail t)
  let h:=terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val
  let v:=h.toAdd+jumpSlot D q₀ p b
  obs t (formula t a₀ v i.2.2)
    (modelEval D G n q c hsk A w hA Γ t (formula t a₀ v i.2.2) (ownInput D q coord t h.toAdd)
      (targetCoset G n q c hsk A w hA Γ (FullLattice G n q c hsk A w hA Γ) le_rfl t x))

 

def intrinsicSuccess (s r : ℕ) (hs : 1 ≤ s) (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (obs : ∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ) (Fs : Finset (Scale a))
    (q₀ : ℕ) (b : Scale a) (τ : ℝ) : Set ((Full G n q c hsk A w hA)⧸FullLattice G n q c hsk A w hA Γ) :=
  let π:=fun t x=>targetCoset G n q c hsk A w hA Γ (FullLattice G n q c hsk A w hA Γ) le_rfl t x
  ⋃ p∈pivotOptions s r hs D Fs,AlignmentMass.Success τ
    (centerReading D (Target D G n q c hsk A w hA Γ) π (modelRead D G n q c hsk A w hA Γ formula obs) Fs q₀ b p)
    (intrinsicTerminal D G n q c hsk A w hA Γ coord formula obs Fs q₀ b p)

omit [∀ t,Fintype (ι t)] in
private lemma intrinsicTerminal_eq
    [act : ∀ t,MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t)]
    (hunit : ∀ e x,
      unitShift D e • x = faceAction (G (D.owner e)) (n (D.owner e)) (q (D.owner e))
        (c (D.owner e)) (hsk (D.owner e)) (A (D.owner e)) (w (D.owner e)) (hA (D.owner e)) (Γ (D.owner e))
        (fun _ (_ : Fin 1)=>1) (coord e) 0 x)
    {r : ℕ} (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (obs : ∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ) (Fs : Finset (Scale a))
    (q₀ : ℕ) (b : Scale a) (p : Path D) (i : Comparison D Fs r)
    (x : (Full G n q c hsk A w hA)⧸FullLattice G n q c hsk A w hA Γ) :
    translatedReading D (Target D G n q c hsk A w hA Γ)
      (fun t x=>targetCoset G n q c hsk A w hA Γ (FullLattice G n q c hsk A w hA Γ) le_rfl t x)
      (modelRead D G n q c hsk A w hA Γ formula obs) Fs q₀ b p i x=
    intrinsicTerminal D G n q c hsk A w hA Γ coord formula obs Fs q₀ b p i x := by
  exact own_terminal_model_reading D G n q c hsk A w hA Γ coord hunit formula obs
    i.2.1.1 _ i.2.2 q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val i.2.1.2.property _ _
 

theorem array_empirical_subsequence
    (s : ℕ) (P : ℕ→ℤ→Full G n q c hsk A w hA) (Z : ℕ→ℝ)
    (Obs : ℕ→∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ)
    (hh : FactorizedEmpirical D G n q c hsk A w hA Γ coord s P Z Obs) :
    ∃ ψ : ℕ→ℕ,StrictMono ψ ∧
      ∀ (r : ℕ) (hs : 1 ≤ s) (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
        (Fs Bs : Finset (Scale a)) (q₀ : ℕ) (_hq₀ : pivotModulus s r hs D Fs Bs∣q₀)
        (b : Scale a) (_hb : b∈Bs) (τ : ℝ) (_hτ : 0<τ),
        ∀ᶠ N in atTop, (((((pivotOptions s r hs D Fs).card : ℝ≥0)⁻¹/2) : ℝ≥0) : ℝ≥0∞) <
          (ProbabilityMixtures.empirical ⌊Z (ψ N)⌋₊ (fun k : ℕ=>k) : Measure ℕ)
            {k | (QuotientGroup.mk (P (ψ N) (k:ℤ)))∈
              intrinsicSuccess D G n q c hsk A w hA Γ coord s r hs formula (Obs (ψ N)) Fs q₀ b τ}
 := by
  classical
  obtain ⟨d,B,hd,hfil,hrational,F,act,hcont,hunit,hgood⟩:=hh
  refine ⟨F.state.subseq,F.state.strictmono,?_⟩
  let : ∀ t,MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t):=act
  let J:=Full G n q c hsk A w hA
  let Λ:=FullLattice G n q c hsk A w hA Γ
  let : T2Space J:=d.coord.symm.t2Space
  let : SecondCountableTopology J:=d.coord.secondCountableTopology
  let : DiscreteTopology Λ:=B.discrete
  let : IsClosed (Λ : Set J):=Λ.isClosed_of_discreteTopology
  let : T2Space (J⧸Λ):=inferInstance
  let : MeasurableSpace (J⧸Λ):=borel _
  let : BorelSpace (J⧸Λ):=⟨rfl⟩
  let : MeasurableSingletonClass (J⧸Λ):=⟨fun _=>isClosed_singleton.measurableSet⟩
  intro r hs formula Fs Bs q₀ hq₀ b hb τ hτ
  have H:=hgood r hs formula Fs Bs q₀ hq₀ b hb τ hτ
  filter_upwards [H] with N hN
  let π:=fun t x=>targetCoset G n q c hsk A w hA Γ Λ le_rfl t x
  let RN:=modelRead D G n q c hsk A w hA Γ formula (Obs (F.state.subseq N))
  have ht : (translatedReading D (Target D G n q c hsk A w hA Γ) π RN Fs q₀ b)=
      intrinsicTerminal D G n q c hsk A w hA Γ coord formula (Obs (F.state.subseq N)) Fs q₀ b := by
    funext p i x
    exact intrinsicTerminal_eq D G n q c hsk A w hA Γ coord hunit formula _ Fs q₀ b p i x
  change _ < (F.coveredEmpiricalPointLaw Λ N : Measure (J⧸Λ))
    (⋃ p∈pivotOptions s r hs D Fs,AlignmentMass.Success τ
      (centerReading D (Target D G n q c hsk A w hA Γ) π RN Fs q₀ b p)
      (translatedReading D (Target D G n q c hsk A w hA Γ) π RN Fs q₀ b p)) at hN
  rw [ht] at hN
  have he:=ProbabilityMixtures.empirical_preimage ⌊Z (F.state.subseq N)⌋₊ (fun k : ℕ=>k)
    (fun k : ℕ=>(QuotientGroup.mk (P (F.state.subseq N) (k:ℤ)) : J⧸Λ))
    (intrinsicSuccess D G n q c hsk A w hA Γ coord s r hs formula (Obs (F.state.subseq N)) Fs q₀ b τ)
  exact hN.trans_eq he.symm

end SourceIntegerArrays.GlobalJoint
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
variable {a₀ : ℕ} (D : Pivot a₀) {ι : Fin D.targets→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : Fin D.targets→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j) (Γ : ∀ t i,Subgroup (G t i))
variable (coord : ∀ e,Fin (q (D.owner e)))
theorem source_compact_empirical
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
    (E : ℕ→Set ((Fin a→ℕ)×ℕ)) (ε : ℝ≥0∞) (_hε : 0<ε)
    (_hE : ∀ N,ε≤(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)) (E N)),
    ∃ φ : ℕ→ℕ,StrictMono φ ∧ ∃ z : ℕ→(Fin a→ℕ)×ℕ,
      (∀ k,z k∈E (φ k) ∧ z k∈fullDomain (X (φ k)) (Xp (φ k)) (primorial (w0 (φ k)))) ∧
      ∃ f : ∀ t i,((G t i)⧸Γ t i) →ᵇ ℝ,
      (∀ t i,TendstoUniformly (fun k=>Obs (φ k) (z k) t i) (f t i) atTop) ∧
      (∀ η : ℝ,0<η →∀ᶠ k in atTop,∀ t i y,|Obs (φ k) (z k) t i y-f t i y|<η) ∧
      ∀ pstar : Fin D.targets→ℕ→ℤ,
      (∀ t k,(M (φ k):ℤ)∣pstar t k-((z k).2:ℤ)) →
      (∀ t k,|(pstar t k:ℝ)-((z k).2:ℝ)|≤R (φ k)) →
      let zout := fun t k l=>(z k).1 (perm t (l.natAdd (m t)))
      let zin := fun t k=>((fun l=>(z k).1 (perm t (l.castAdd (h t)))),(z k).2)
      let label := fun t k=>expose (L (φ k)) (M (φ k):ℤ) (R (φ k)) (zin t k)
      FactorizedEmpirical D G n q c hsk A w hA Γ coord s
        (fun k=>rawJoint G n q m c hsk A w hA hw (M (φ k)) (L (φ k))
          (fun t=>label t k) (fun t l=>((zin t k).1 l:ℤ)) (fun t=>pstar t k)
          (fun t=>slot t (φ k) (zout t k) (label t k))
          (fun t=>qval t (φ k) (zout t k) (label t k))
          (fun t=>g t (φ k) (zout t k) (label t k))
          (fun t=>x t (φ k) (zout t k) (label t k)))
        (fun k=>R (φ k)/(M (φ k):ℝ)) (fun k=>Obs (φ k) (z k)) := by
  classical
  let : ∀ t i,MetricSpace ((G t i)⧸Γ t i):=fun t i=>(metric t i).replaceTopology (hmetric t i)
  intro Obs Kobs Bobs hLip hBound E ε hε hE
  let Yobs (u : Sigma ι):=(G u.1 u.2)⧸Γ u.1 u.2
  let : ∀ u,MetricSpace (Yobs u):=fun u=>inferInstanceAs (MetricSpace ((G u.1 u.2)⧸Γ u.1 u.2))
  let : ∀ u,CompactSpace (Yobs u):=fun u=>AbelianMalcevTorus.quotient_compact (c u.1 u.2) (Γ u.1 u.2) (hΓ u.1 u.2)
  obtain ⟨φ,hφ,z,hz,f,hu,he,hgood⟩:=source_compact_physical D G n q c hsk A w hA hw Γ coord
    hΓ hmono s h0 h1 hs a m h perm w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX hZ hQ0
    hSize hWM hM hMs hL hsm hWL hML hLexact hXL g x slot qval hQ Yobs
    (fun N z u=>Obs N z u.1 u.2) Kobs Bobs (fun N z u=>hLip N z u.1 u.2)
    (fun N z u=>hBound N z u.1 u.2) E ε hε hE
  refine ⟨φ,hφ,z,hz,(fun t i=>f ⟨t,i⟩),(fun t i=>hu ⟨t,i⟩),?_,?_⟩
  · intro η hη
    filter_upwards [he η hη] with k hk
    exact fun t i y=>hk ⟨t,i⟩ y
  · intro pstar hpstar hpclose
    refine factorized_empirical D G n q c hsk A w hA Γ coord s _ _ (hgood pstar hpstar hpclose)
      (fun k=>div_pos (hR _) (by exact_mod_cast hM _)) ?_ (fun k=>Obs (φ k) (z k)) (fun t i=>f ⟨t,i⟩) ?_
    · rintro ⟨t⟩
      have ht : Tendsto (fun N=>(R N/(M N:ℝ))/
          (1+∑ j : Fin (m t),(X N (perm t (j.castAdd (h t))):ℝ)^2)) atTop atTop := by
        simpa only [Real.rpow_one] using hZ t 1 zero_lt_one
      have hT : Tendsto (fun N=>R N/(M N:ℝ)) atTop atTop := by
        apply tendsto_atTop.mpr
        intro B
        filter_upwards [ht.eventually (eventually_ge_atTop B)] with N hN
        apply hN.trans
        apply div_le_self (le_of_lt (div_pos (hR N) (by exact_mod_cast hM N)))
        have hn : 0≤∑ j : Fin (m t),(X N (perm t (j.castAdd (h t))):ℝ)^2:=
          Finset.sum_nonneg (fun _ _=>sq_nonneg _)
        linarith
      exact hT.comp hφ.tendsto_atTop
    · intro η hη
      filter_upwards [he η hη] with k hk
      exact fun t i y=>hk ⟨t,i⟩ y

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

 

def firstPivot (M N p : ℕ) : ℤ := (p:ℤ)-(M:ℤ)*((p/M)%N:ℕ)

 

def rawLocalOrbit {a : ℕ} (m h : Fin D.targets→ℕ) (perm : ∀ t,Fin (m t+h t)≃Fin a)
    (M J : ℕ) (L : ℤ) (R : ℝ)
    (g x : ∀ t,(Fin (h t)→ℕ)→Label (m t)→∀ i,G t i)
    (slot : ∀ t,(Fin (h t)→ℕ)→Label (m t)→ι t→ℤ)
    (qval : ∀ t,(Fin (h t)→ℕ)→Label (m t)→Fin (q t)→ℤ)
    (z : (Fin a→ℕ)×ℕ) (k : ℤ) : Full G n q c hsk A w hA :=
  let zout:=fun t l=>z.1 (perm t (l.natAdd (m t)))
  let zin:=fun t=>((fun l=>z.1 (perm t (l.castAdd (h t)))),z.2)
  let label:=fun t=>expose L (M:ℤ) R (zin t)
  rawJoint G n q m c hsk A w hA hw M L label (fun t l=>((zin t).1 l:ℤ))
    (fun _=>firstPivot M J z.2) (fun t=>slot t (zout t) (label t))
    (fun t=>qval t (zout t) (label t)) (fun t=>g t (zout t) (label t))
    (fun t=>x t (zout t) (label t)) k

lemma firstPivot_congruent (M N p : ℕ) : (M:ℤ)∣firstPivot M N p-(p:ℤ) := by
  refine ⟨-(((p/M)%N:ℕ):ℤ),?_⟩
  unfold firstPivot
  ring

lemma firstPivot_close (M N p : ℕ) (hN : 0<N) :
    |(firstPivot M N p:ℝ)-(p:ℝ)|≤(M:ℝ)*(N:ℝ) := by
  have hr : (((p/M)%N:ℕ):ℝ)≤(N:ℝ) := by exact_mod_cast (Nat.mod_lt (p/M) hN).le
  have hn : (0:ℝ)≤(M:ℝ)*(((p/M)%N:ℕ):ℝ) := by positivity
  have he : (firstPivot M N p:ℝ)-(p:ℝ)= -((M:ℝ)*(((p/M)%N:ℕ):ℝ)) := by
    simp only [firstPivot,Int.cast_sub,Int.cast_natCast,Int.cast_mul]
    ring
  rw [he,abs_neg,abs_of_nonneg hn]
  exact mul_le_mul_of_nonneg_left hr (by positivity)

 
lemma firstPivot_eq_point (M N p : ℕ) :
    firstPivot M N p=(MicrocellFibers.point M (N*(p/(M*N))) (p%M) 0:ℤ) := by
  have h₁ : ((p%M:ℕ):ℤ)+(M:ℤ)*(p/M:ℕ)=(p:ℤ) := by exact_mod_cast Nat.mod_add_div p M
  have h₂ : (((p/M)%N:ℕ):ℤ)+(N:ℤ)*(p/(M*N):ℕ)=(p/M:ℕ) := by
    have hh := Nat.mod_add_div (p/M) N
    rw [Nat.div_div_eq_div_mul] at hh
    exact_mod_cast hh
  change (p:ℤ)-(M:ℤ)*(((p/M)%N:ℕ):ℤ)=((M*(N*(p/(M*N)))+p%M+M*0:ℕ):ℤ)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.cast_add,Nat.cast_mul]
  linear_combination -h₁ - (M:ℤ)*h₂
 

theorem source_intrinsic_selection
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
    (b : Scale a₀) (_hb : b∈Bs) (τ : ℝ) (_hτ : 0<τ)
    (E : ℕ→Set ((Fin a→ℕ)×ℕ)) (ε : ℝ≥0∞) (_hε : 0<ε)
    (_hE : ∀ N,ε≤(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)) (E N)),
    ∃ N z,z∈E N ∧ z∈fullDomain (X N) (Xp N) (primorial (w0 N)) ∧
      (((((pivotOptions s r hs1 D Fs).card : ℝ≥0)⁻¹/2) : ℝ≥0) : ℝ≥0∞)<
        (ProbabilityMixtures.empirical (J N) (fun k : ℕ=>k) : Measure ℕ)
          {k | QuotientGroup.mk (rawLocalOrbit D G n q c hsk A w hA hw m h perm
            (M N) (J N) (L N) (R N) (fun t=>g t N) (fun t=>x t N)
            (fun t=>slot t N) (fun t=>qval t N) z (k:ℤ)) ∈
            intrinsicSuccess D G n q c hsk A w hA Γ coord s r hs1 formula (Obs N z) Fs q₀ b τ}
 := by
  classical
  let : ∀ t i,MetricSpace ((G t i)⧸Γ t i):=fun t i=>(metric t i).replaceTopology (hmetric t i)
  intro Obs Kobs Bobs hLip hBound J hJ hRJ r hs1 formula Fs Bs q₀ hq₀ b hb τ hτ E ε hε hE
  obtain ⟨φ,hφ,z,hz,f,hu,he,hgood⟩:=source_compact_empirical D G n q c hsk A w hA hw Γ coord
    hΓ hmono s h0 h1 hs a m h perm w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX hZ hQ0
    hSize hWM hM hMs hL hsm hWL hML hLexact hXL g x slot qval hQ metric hmetric
    Obs Kobs Bobs hLip hBound E ε hε hE
  let pstar : Fin D.targets→ℕ→ℤ:=fun _ k=>firstPivot (M (φ k)) (J (φ k)) (z k).2
  have hpstar : ∀ t k,(M (φ k):ℤ)∣pstar t k-((z k).2:ℤ):=fun t k=>firstPivot_congruent _ _ _
  have hpclose : ∀ t k,|(pstar t k:ℝ)-((z k).2:ℝ)|≤R (φ k) := by
    intro t k
    rw [hRJ]
    exact firstPivot_close _ _ _ (hJ _)
  have hh:=hgood pstar hpstar hpclose
  obtain ⟨ψ,hψ,hψgood⟩:=array_empirical_subsequence D G n q c hsk A w hA Γ coord s _ _ _ hh
  obtain ⟨N,hN⟩:=(hψgood r hs1 formula Fs Bs q₀ hq₀ b hb τ hτ).exists
  refine ⟨φ (ψ N),z (ψ N),(hz _).1,(hz _).2,?_⟩
  have hlen : ⌊R (φ (ψ N))/(M (φ (ψ N)):ℝ)⌋₊=J (φ (ψ N)) := by
    rw [hRJ,mul_div_cancel_left₀ _ (by exact_mod_cast (hM _).ne')]
    exact Nat.floor_natCast _
  simpa only [hlen,pstar,rawLocalOrbit] using hN

end SourceIntegerArrays

end
end

end OAI
