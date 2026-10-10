import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
noncomputable section
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates SourceResidueAlignment
open ProductExposureLabels AllLevelFactorization AllLevelFactorization.Factorization
open PhysicalCubeMaps CubeLocalHaar MeasureTheory
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable
variable {τ : Type} [Fintype τ] {ι : τ→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q m : τ→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j) (Γ : ∀ t i,Subgroup (G t i))
def FactorizedAllHaar (s : ℕ) (P : ℕ→ℤ→Full G n q c hsk A w hA) (Z : ℕ→ℝ) : Prop :=
  ∃ d : RealCoordinates (Full G n q c hsk A w hA) (FullDim n q w),
  ∃ B : CoveredLattice d (FullLattice G n q c hsk A w hA Γ),
    SecondKind d ∧
    (∀ k f,f∈(FullFiltration G n q c hsk A w hA).level k ↔
      ∀ j,JointArrays.jointWeight (FlatN n) (FlatQ q) (FlatW w) j<k → d.coord f j=0) ∧
    (∀ f,IsRational d f → ∀ t (i : ι t) (u : Fin (q t)→ℤ),
      IsRational (c t i) ((f ⟨t,i⟩).val (fun j=>(u j:ℝ)))) ∧
    ∃ F : Factorization d B.small s (FullFiltration G n q c hsk A w hA) P Z,
    letI : SecondCountableTopology (Full G n q c hsk A w hA):=coordinates_secondCountable d
    letI : CompactSpace ((Full G n q c hsk A w hA)⧸B.small):=AbelianMalcevTorus.quotient_compact d B.small B.integer
    letI : MeasurableSpace ((Full G n q c hsk A w hA)⧸B.small):=borel _
    letI : BorelSpace ((Full G n q c hsk A w hA)⧸B.small):=⟨rfl⟩
    ∀ t (r : Fin F.period) (C : F.ResidueCover r) (ν : Fin (s+1)),
    letI : MeasurableSpace (C.CubeSpace (ι:=Fin (ν.val+1))):=borel _
    letI : BorelSpace (C.CubeSpace (ι:=Fin (ν.val+1))):=⟨rfl⟩
    let Y := (Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
        lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
    letI : MeasurableSpace (Finset (Fin (ν.val+1))→Y):=borel _
    letI : BorelSpace (Finset (Fin (ν.val+1))→Y):=⟨rfl⟩
    ∀ (e : Fin (q t)) (j : Fin (ν.val+1)) (β : ℝ),
      Measure.map (upperFace j (faceAction (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
        (fun _ (_ : Fin 1)=>1) e 0))
        (C.marginalCubeHaar (ι:=Fin (ν.val+1)) β (vertices (targetCoset G n q c hsk A w hA Γ B.small B.le t)) : Measure (Finset (Fin (ν.val+1))→Y))=
        (C.marginalCubeHaar (ι:=Fin (ν.val+1)) β (vertices (targetCoset G n q c hsk A w hA Γ B.small B.le t)) : Measure (Finset (Fin (ν.val+1))→Y))
end SourceIntegerArrays.GlobalJoint
end

noncomputable section
namespace SourceIntegerArrays
open GlobalJoint
open RoughArrayFace
open RationalLattice MalcevCharacters RoughFaceShift RoughTopologicalFace RoughArrayCoordinates SourceResidueAlignment
open RoughScales RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw ProductExposureCutoff MeasureTheory Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
variable {τ : Type} [Fintype τ] {ι : τ→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : τ→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j) (Γ : ∀ t i,Subgroup (G t i))
theorem source_all_order_factorized_haar
    (hΓ : ∀ t i g,g∈Γ t i ↔ ∀ j,∃ z : ℤ,(c t i).coord g j=z)
    (hmono : ∀ t i,Monotone (w t i)) (s : ℕ)
    (h0 : ∀ t i,(A t i).level 0=⊤) (h1 : ∀ t i,(A t i).level 1=⊤)
    (hs : ∀ t i,(A t i).level (s+1)=⊥)
    (a : ℕ) (m h : τ→ℕ) (perm : ∀ t,Fin (m t+h t)≃Fin a)
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
    (E : ℕ→Set ((Fin a→ℕ)×ℕ)) (ε : ℝ≥0∞) (hε : 0<ε)
    (hE : ∀ N,ε≤(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)) (E N)) :
    ∃ φ : ℕ→ℕ,StrictMono φ ∧ ∃ z : ℕ→(Fin a→ℕ)×ℕ,
      (∀ k,z k∈E (φ k) ∧ z k∈fullDomain (X (φ k)) (Xp (φ k)) (primorial (w0 (φ k)))) ∧
      ∀ pstar : τ→ℕ→ℤ,
      (∀ t k,(M (φ k):ℤ)∣pstar t k-((z k).2:ℤ)) →
      (∀ t k,|(pstar t k:ℝ)-((z k).2:ℝ)|≤R (φ k)) →
      let zout := fun t k l=>(z k).1 (perm t (l.natAdd (m t)))
      let zin := fun t k=>((fun l=>(z k).1 (perm t (l.castAdd (h t)))),(z k).2)
      let label := fun t k=>expose (L (φ k)) (M (φ k):ℤ) (R (φ k)) (zin t k)
      FactorizedAllHaar G n q c hsk A w hA Γ s
        (fun k=>rawJoint G n q m c hsk A w hA hw (M (φ k)) (L (φ k))
          (fun t=>label t k) (fun t l=>((zin t k).1 l:ℤ)) (fun t=>pstar t k)
          (fun t=>slot t (φ k) (zout t k) (label t k))
          (fun t=>qval t (φ k) (zout t k) (label t k))
          (fun t=>g t (φ k) (zout t k) (label t k))
          (fun t=>x t (φ k) (zout t k) (label t k)))
        (fun k=>R (φ k)/(M (φ k):ℝ))
 := by
  classical
  obtain ⟨φ,hφ,z,hz,hgood⟩:=source_global_all_order_haar G n q c hsk A w hA hw Γ hΓ
    a s m h perm w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX hZ hQ0 hSize hWM hM hMs
    hL hsm hWL hML hLexact hXL g x slot qval hQ E ε hε hE
  refine ⟨φ,hφ,z,hz,?_⟩
  intro pstar hpstar hpclose
  let zout := fun t k (l : Fin (h t))=>(z k).1 (perm t (l.natAdd (m t)))
  let zin := fun t k=>((fun l : Fin (m t)=>(z k).1 (perm t (l.castAdd (h t)))),(z k).2)
  let label := fun t k=>expose (L (φ k)) (M (φ k):ℤ) (R (φ k)) (zin t k)
  let Z := fun k=>R (φ k)/(M (φ k):ℝ)
  have hZp (k : ℕ) : 0<Z k:=div_pos (hR _) (by exact_mod_cast hM _)
  let P := fun k=>rawJoint G n q m c hsk A w hA hw (M (φ k)) (L (φ k))
    (fun t=>label t k) (fun t l=>((zin t k).1 l:ℤ)) (fun t=>pstar t k)
    (fun t=>slot t (φ k) (zout t k) (label t k))
    (fun t=>qval t (φ k) (zout t k) (label t k))
    (fun t=>g t (φ k) (zout t k) (label t k))
    (fun t=>x t (φ k) (zout t k) (label t k))
  change FactorizedAllHaar G n q c hsk A w hA Γ s P Z
  obtain ⟨d,B,hskd,hf,hr,⟨F⟩⟩:=literal_joint_factorization
    (FlatG G) (FlatN n) (FlatQ q) (FlatM m) (FlatC c) (FlatSk hsk) (FlatA A) (FlatW w) (FlatHA hA) (FlatHw hw)
    (fun a=>hmono a.1 a.2) (FlatΓ Γ) (fun a=>hΓ a.1 a.2) s
    (fun a=>h0 a.1 a.2) (fun a=>h1 a.1 a.2) (fun a=>hs a.1 a.2)
    (fun k=>M (φ k)) (fun k=>hM (φ k)) (fun k=>L (φ k))
    (fun k b=>label b.1 k) (fun k b l=>((zin b.1 k).1 l:ℤ))
    (fun k b=>pstar b.1 k) (fun k b=>slot b.1 (φ k) (zout b.1 k) (label b.1 k) b.2)
    (fun k b=>qval b.1 (φ k) (zout b.1 k) (label b.1 k))
    (fun k b=>g b.1 (φ k) (zout b.1 k) (label b.1 k) b.2)
    (fun k b=>x b.1 (φ k) (zout b.1 k) (label b.1 k) b.2) Z hZp
  refine ⟨d,B,hskd,hf,?_,F,?_⟩
  · intro f hf t i u
    exact hr f hf ⟨t,i⟩ u
  · let : SecondCountableTopology (Full G n q c hsk A w hA):=coordinates_secondCountable d
    let : CompactSpace ((Full G n q c hsk A w hA)⧸B.small):=AbelianMalcevTorus.quotient_compact d B.small B.integer
    let : MeasurableSpace ((Full G n q c hsk A w hA)⧸B.small):=borel _
    let : BorelSpace ((Full G n q c hsk A w hA)⧸B.small):=⟨rfl⟩
    intro t r C ν
    let : MeasurableSpace (C.CubeSpace (ι:=Fin (ν.val+1))):=borel _
    let : BorelSpace (C.CubeSpace (ι:=Fin (ν.val+1))):=⟨rfl⟩
    let Y := (Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
        lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
    let : MeasurableSpace (Finset (Fin (ν.val+1))→Y):=borel _
    let : BorelSpace (Finset (Fin (ν.val+1))→Y):=⟨rfl⟩
    dsimp only
    intro e j β
    have hh:=hgood t ν e j (pstar t) (hpstar t) (hpclose t)
    exact hh (Full G n q c hsk A w hA) (FullDim n q w) s d B.small
      (FullFiltration G n q c hsk A w hA) P F
      (targetCoset G n q c hsk A w hA Γ B.small B.le t) (fun _ _=>rfl) r C β

end SourceIntegerArrays
end

section
 

 

noncomputable section
open Filter Topology
open scoped BoundedContinuousFunction NNReal
namespace FiniteObservableCompactness
variable {I : Type} [Fintype I]
variable (X : I → Type) [∀ i,MetricSpace (X i)] [∀ i,CompactSpace (X i)]
variable (F : ℕ → (i : I) → X i →ᵇ ℝ) (K : ℝ≥0) (B : ℝ)
variable (hLip : ∀ N i,LipschitzWith K (F N i))
variable (hbound : ∀ N i x,|F N i x|≤B)

include hLip hbound in
 

theorem exists_common_uniform_subsequence :
    ∃ f : (i : I) → X i →ᵇ ℝ,∃ φ : ℕ → ℕ,StrictMono φ ∧
      (∀ i,TendstoUniformly (fun N=>F (φ N) i) (f i) atTop) ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ N in atTop,∀ i x,|F (φ N) i x-f i x|<ε := by
  let A (i : I):=Set.range (fun N=>F N i)
  have hc (i : I) : IsCompact (closure (A i)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Set.Icc (-B) B) isCompact_Icc (A i)
    · intro f x hf
      obtain ⟨N,rfl⟩:=hf
      exact abs_le.mp (hbound N i x)
    · apply (LipschitzWith.uniformEquicontinuous (fun f : A i=> (f.val : X i → ℝ)) K ?_).equicontinuous
      intro f
      obtain ⟨N,hN⟩:=f.property
      simpa only [←hN] using hLip N i
  obtain ⟨f,hf,φ,hφ,hconv⟩:=(isCompact_pi_infinite hc).tendsto_subseq
    (fun N i=>subset_closure (Set.mem_range_self N))
  have huni (i : I) : TendstoUniformly (fun N=>F (φ N) i) (f i) atTop := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    exact (tendsto_pi_nhds.mp hconv) i
  refine ⟨f,φ,hφ,huni,?_⟩
  intro ε hε
  have hi (i : I) : ∀ᶠ N in atTop,∀ x,|F (φ N) i x-f i x|<ε := by
    simpa only [Real.dist_eq,abs_sub_comm] using (Metric.tendstoUniformly_iff.mp (huni i)) ε hε
  exact Filter.eventually_all.mpr hi

end FiniteObservableCompactness
end
 
end

noncomputable section
namespace SourceIntegerArrays
open RoughArrayFace
open RationalLattice MalcevCharacters RoughFaceShift RoughTopologicalFace RoughArrayCoordinates SourceResidueAlignment
open RoughScales RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw ProductExposureCutoff MeasureTheory Filter
open scoped BigOperators Topology ENNReal BoundedContinuousFunction NNReal
attribute [local instance] Classical.propDecidable
variable {τ : Type} [Fintype τ] {ι : τ→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : τ→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j) (Γ : ∀ t i,Subgroup (G t i))
 

theorem source_global_compact_haar
    (hΓ : ∀ t i g,g∈Γ t i ↔ ∀ j,∃ z : ℤ,(c t i).coord g j=z)
    (a s : ℕ) (m h : τ→ℕ) (perm : ∀ t,Fin (m t+h t)≃Fin a)
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
    {κ : Type} [Fintype κ] (Yobs : κ→Type) [∀ i,MetricSpace (Yobs i)] [∀ i,CompactSpace (Yobs i)]
    (Obs : ℕ→((Fin a→ℕ)×ℕ)→(i : κ)→Yobs i →ᵇ ℝ) (Kobs : ℝ≥0) (Bobs : ℝ)
    (hLip : ∀ N z i,LipschitzWith Kobs (Obs N z i))
    (hBound : ∀ N z i y,|Obs N z i y|≤Bobs)
    (E : ℕ→Set ((Fin a→ℕ)×ℕ)) (ε : ℝ≥0∞) (hε : 0<ε)
    (hE : ∀ N,ε≤(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)) (E N)) :
    ∃ φ : ℕ→ℕ,StrictMono φ ∧ ∃ z : ℕ→(Fin a→ℕ)×ℕ,
      (∀ k,z k∈E (φ k) ∧ z k∈fullDomain (X (φ k)) (Xp (φ k)) (primorial (w0 (φ k)))) ∧
      ∃ f : (i : κ)→Yobs i →ᵇ ℝ,
      (∀ i,TendstoUniformly (fun k=>Obs (φ k) (z k) i) (f i) atTop) ∧
      (∀ η : ℝ,0<η →∀ᶠ k in atTop,∀ i y,|Obs (φ k) (z k) i y-f i y|<η) ∧
      ∀ t (k : Fin (s+1)),
      let zout := fun k l=>(z k).1 (perm t (l.natAdd (m t)))
      let zin := fun k=>((fun l=>(z k).1 (perm t (l.castAdd (h t)))),(z k).2)
      let label := fun k=>expose (L (φ k)) (M (φ k):ℤ) (R (φ k)) (zin k)
      let Z := fun k=>R (φ k)/(M (φ k):ℝ)
      ∀ (e : Fin (q t)) (j : Fin (k.val+1)) (pstar : ℕ→ℤ),
      (∀ k,(M (φ k):ℤ)∣pstar k-((z k).2:ℤ)) →
      (∀ k,|(pstar k:ℝ)-((z k).2:ℝ)|≤R (φ k)) →
      let state := fun k b=>QuotientGroup.mk
        (literalState (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t)
          (M (φ k)) (L (φ k)) (label k) (fun l=>((zin k).1 l:ℤ)) (pstar k)
          (fun _ (_ : Fin 1)=>1)
          (g t (φ k) (zout k) (label k)) (x t (φ k) (zout k) (label k))
          (slot t (φ k) (zout k) (label k)) (qval t (φ k) (zout k) (label k)) (fun _=>b))
      SourcePhysicalDecay.AllCenteredHaar Z state (k.val+1) j
        (faceAction (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
          (fun _ (_ : Fin 1)=>1) e 0)
 := by
  classical
  obtain ⟨φ,hφ,z,hz,hgood⟩:=source_global_literal_cube_faces
    (τ:=τ×Fin (s+1)) (ι:=fun t=>ι t.1)
    (fun t=>G t.1) (fun t=>n t.1) (fun t=>q t.1) (fun t=>c t.1)
    (fun t=>hsk t.1) (fun t=>A t.1) (fun t=>w t.1) (fun t=>hA t.1) (fun t=>hw t.1) (fun t=>Γ t.1)
    (fun t=>hΓ t.1) a (fun t=>m t.1) (fun t=>h t.1) (fun t=>t.2.val+1)
    (fun t=>perm t.1) w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX
    (fun t=>hZ t.1) hQ0 (fun t=>hSize t.1) hWM hM hMs hL hsm hWL hML hLexact
    (fun t=>hXL t.1) (fun t=>g t.1) (fun t=>x t.1) (fun t=>slot t.1) (fun t=>qval t.1)
    (fun t=>hQ t.1) E ε hε hE
  obtain ⟨f,ψ,hψ,huniform,herror⟩:=FiniteObservableCompactness.exists_common_uniform_subsequence
    Yobs (fun k=>Obs (φ k) (z k)) Kobs Bobs (fun k=>hLip (φ k) (z k)) (fun k=>hBound (φ k) (z k))
  refine ⟨φ∘ψ,hφ.comp hψ,z∘ψ,fun k=>hz (ψ k),f,huniform,herror,?_⟩
  intro t ν
  dsimp only
  intro e j pstar hpstar hpclose
  let pstar' : ℕ→ℤ:=Function.extend ψ pstar (fun k=>(z k).2)
  have hext (k : ℕ) : pstar' (ψ k)=pstar k:=hψ.injective.extend_apply _ _ _
  have hcong (k : ℕ) : (M (φ k):ℤ)∣pstar' k-((z k).2:ℤ) := by
    by_cases hn : ∃ l,ψ l=k
    · obtain ⟨l,rfl⟩:=hn
      rw [hext]
      exact hpstar l
    · have he : pstar' k=((z k).2:ℤ):=Function.extend_apply' _ _ _ hn
      rw [he,sub_self]
      exact dvd_zero _
  have hnear (k : ℕ) : |(pstar' k:ℝ)-((z k).2:ℝ)|≤R (φ k) := by
    by_cases hn : ∃ l,ψ l=k
    · obtain ⟨l,rfl⟩:=hn
      rw [hext]
      exact hpclose l
    · have he : pstar' k=((z k).2:ℤ):=Function.extend_apply' _ _ _ hn
      rw [he,Int.cast_natCast,sub_self,abs_zero]
      exact (hR _).le
  let zout := fun k (l : Fin (h t))=>(z k).1 (perm t (l.natAdd (m t)))
  let zin := fun k=>((fun l : Fin (m t)=>(z k).1 (perm t (l.castAdd (h t)))),(z k).2)
  let lab := fun k=>expose (L (φ k)) (M (φ k):ℤ) (R (φ k)) (zin k)
  let Y := (Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
    lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
  let state : ℕ→ℤ→Y := fun k b=>QuotientGroup.mk
    (literalState (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t)
      (M (φ k)) (L (φ k)) (lab k) (fun l=>((zin k).1 l:ℤ)) (pstar' k)
      (fun _ (_ : Fin 1)=>1) (g t (φ k) (zout k) (lab k)) (x t (φ k) (zout k) (lab k))
      (slot t (φ k) (zout k) (lab k)) (qval t (φ k) (zout k) (lab k)) (fun _=>b))
  let S:=faceAction (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
    (fun _ (_ : Fin 1)=>1) e 0
  let Z := fun k=>R (φ k)/(M (φ k):ℝ)
  have hZp (k : ℕ) : 0<Z k:=div_pos (hR _) (by exact_mod_cast hM _)
  have hZT : Tendsto Z atTop atTop := by
    have ht : Tendsto (fun N=>(R N/(M N:ℝ))/
        (1+∑ j : Fin (m t),(X N (perm t (j.castAdd (h t))):ℝ)^2)) atTop atTop := by
      simpa only [Real.rpow_one] using hZ t 1 zero_lt_one
    have ht' := ht.comp hφ.tendsto_atTop
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [ht'.eventually (eventually_ge_atTop B)] with N hN
    apply hN.trans
    apply div_le_self (hZp N).le
    have hn : 0≤∑ j : Fin (m t),(X (φ N) (perm t (j.castAdd (h t))):ℝ)^2:=
      Finset.sum_nonneg (fun _ _=>sq_nonneg _)
    linarith
  have hboxes : SourcePhysicalDecay.AllBoxes Z
      (fun N b w=>state N (cubeVertex (ν.val+1) b w)) (PhysicalCubeMaps.upperFace j S) := by
    intro d hd c₀ C₀ hc₀ hC₀ lo hi res hbox F
    exact hgood (t,ν) e j d hd pstar' hcong hnear c₀ C₀ hc₀ hC₀ lo hi res hbox F
  have hsub:=SourcePhysicalDecay.allBoxes_subsequence Z (fun k=>(hZp k).le) _ _ hboxes ψ hψ
  have htop:=joint_array_topology (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t) (Γ t) (hΓ t)
  let : CompactSpace Y:=htop.2.2.1
  let : TopologicalSpace.MetrizableSpace Y:=htop.2.2.2
  have hhaar:=SourcePhysicalDecay.compatible_haar_of_allBoxes (Z∘ψ) (fun k=>hZp (ψ k))
    (hZT.comp hψ.tendsto_atTop) (state∘ψ) (ν.val+1) j S hsub
  have hcent:=SourcePhysicalDecay.compatible_haar_allCenters (Z∘ψ) (fun k=>hZp (ψ k))
    (state∘ψ) (ν.val+1) j S hhaar
  simpa only [Function.comp_def,state,zout,zin,lab,Z,S,hext] using hcent

end SourceIntegerArrays

end

end OAI
