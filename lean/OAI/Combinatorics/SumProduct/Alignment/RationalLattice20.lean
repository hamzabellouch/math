import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
noncomputable section
end

noncomputable section
namespace SourceIntegerArrays
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates SourceResidueAlignment
open ProductExposureLabels
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j) (Γ : ∀ i,Subgroup (G i))

include hw in
 

theorem joint_array_topology
    (hΓ : ∀ i g,g∈Γ i ↔ ∀ j,∃ z : ℤ,(c i).coord g j=z) :
    SecondCountableTopology ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ) ∧
    T2Space ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ) ∧
    CompactSpace ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ) ∧
    TopologicalSpace.MetrizableSpace ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ)
 := by
  classical
  let V:=Carrier G n q c hsk A w hA
  let Λ:=lattice G n q c hsk A w hA Γ
  let : T2Space V:=(coefficientsHomeomorph G n q c hsk A w hA).symm.t2Space
  let : SecondCountableTopology V := (coefficientsHomeomorph G n q c hsk A w hA).secondCountableTopology
  let : ∀ i,DiscreteTopology (Γ i) := fun i=>integerCoordinates_discrete (c i) (Γ i) (hΓ i)
  let : ∀ i,DiscreteTopology (PolynomialArrays.lattice (q:=q) (c i) (hsk i) (A i) (w i) (hA i) (Γ i)) :=
    fun i=>PolynomialArrays.lattice_discrete (c i) (hsk i) (A i) (w i) (hA i) (Γ i)
  let emb (f : Λ) : ∀ i,PolynomialArrays.lattice (q:=q) (c i) (hsk i) (A i) (w i) (hA i) (Γ i) :=
    fun i=>⟨f.val i,f.property i⟩
  have he : Continuous emb := continuous_pi (fun i=>Continuous.subtype_mk
    ((continuous_apply i).comp continuous_subtype_val) _)
  have hinj : Function.Injective emb := by
    intro f g hfg
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hfg i)
  let : DiscreteTopology Λ := DiscreteTopology.of_continuous_injective he hinj
  let : IsClosed (Λ : Set V) := Λ.isClosed_of_discreteTopology
  let : T2Space (V⧸Λ) := inferInstance
  let : SecondCountableTopology (V⧸Λ) := inferInstance
  obtain ⟨chart,grid,hgridpos,hgrid,J,hJ,hdegree⟩ := source_joint_geometry G n q c hsk A w hA hw Γ hΓ
  obtain ⟨Λ₀,ec,hec,hΛ,hle,D,hD,hdeg⟩ := RoughCoveredFace.grid_second_degree_cover chart Λ grid hgridpos hgrid
  have hcompact : CompactSpace (V⧸Λ) := by
    obtain ⟨S,hS,hrep⟩ := compact_reps_of_integerCoordinates ec Λ₀ hΛ
    apply CompactGroupProducts.HasCompactReps.quotient_compactSpace
    refine ⟨S,hS,fun _ _=>Subgroup.mem_top _,?_⟩
    intro u _
    obtain ⟨s,hs,hsa⟩ := hrep u
    exact ⟨s,hs,hle hsa⟩
  let := hcompact
  let : WeaklyLocallyCompactSpace (V⧸Λ) := ⟨fun _=>⟨Set.univ,isCompact_univ,Filter.univ_mem⟩⟩
  let : R1Space (V⧸Λ) := T2Space.r1Space
  let : RegularSpace (V⧸Λ) := .of_hasBasis isCompact_isClosed_basis_nhds (fun _ _ ⟨_,_,h⟩=>h)
  have : T3Space (V⧸Λ) := instT3Space
  exact ⟨inferInstance,inferInstance,hcompact,TopologicalSpace.metrizableSpace_of_t3_secondCountable (V⧸Λ)⟩

end SourceIntegerArrays
end

noncomputable section
namespace SourceIntegerArrays
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
 

theorem source_global_literal_cube_faces
    (hΓ : ∀ t i g,g∈Γ t i ↔ ∀ j,∃ z : ℤ,(c t i).coord g j=z)
    (a : ℕ) (m h v : τ→ℕ) (perm : ∀ t,Fin (m t+h t)≃Fin a)
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
      ∀ t,
      let zout := fun k l=>(z k).1 (perm t (l.natAdd (m t)))
      let zin := fun k=>((fun l=>(z k).1 (perm t (l.castAdd (h t)))),(z k).2)
      let label := fun k=>expose (L (φ k)) (M (φ k):ℤ) (R (φ k)) (zin k)
      let Z := fun k=>R (φ k)/(M (φ k):ℝ)
      ∀ (e : Fin (q t)) (j : Fin (v t)) (d : ℕ),0<d → ∀ (pstar : ℕ→ℤ),
      (∀ k,(M (φ k):ℤ)∣pstar k-((z k).2:ℤ)) →
      (∀ k,|(pstar k:ℝ)-((z k).2:ℝ)|≤R (φ k)) →
      let state := fun k b=>QuotientGroup.mk
        (literalState (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t)
          (M (φ k)) (L (φ k)) (label k) (fun l=>((zin k).1 l:ℤ)) (pstar k)
          (fun _ (_ : Fin 1)=>1)
          (g t (φ k) (zout k) (label k)) (x t (φ k) (zout k) (label k))
          (slot t (φ k) (zout k) (label k)) (qval t (φ k) (zout k) (label k)) (fun _=>b))
      ∀ (c₀ C₀ : ℝ),0<c₀ →0<C₀ →
      ∀ (lo hi : ℕ→Fin (v t+1)→ℝ) (res : ℕ→Fin (v t+1)→ℤ),
      (∀ᶠ k in atTop,(∀ i,c₀*Z k≤hi k i-lo k i) ∧
        (∀ i,-C₀*Z k≤lo k i ∧ hi k i≤C₀*Z k)) →
      ∀ F : C((Finset (Fin (v t))→((Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
        lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t))),ℂ),
      Tendsto (fun k=>mean (physicalResidueBox (lo k) (hi k) (res k) d)
        (fun β=>F (fun S=>if j∈S then
          faceAction (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
            (fun _ (_ : Fin 1)=>1) e 0 (state k (cubeVertex (v t) β S))
          else state k (cubeVertex (v t) β S)))-
      mean (physicalResidueBox (lo k) (hi k) (res k) d)
        (fun β=>F (fun S=>state k (cubeVertex (v t) β S)))) atTop (𝓝 0)
 := by
  classical
  let Gd := fun t=>DG (G t) (v t)
  let nd := fun t=>Dn (n t) (v t)
  let cd := fun t=>Dc (c t) (v t)
  let skd := fun t=>Dhsk (hsk t) (v t)
  let Ad := fun t=>DA (A t) (v t)
  let wd := fun t=>Dw (w t) (v t)
  let hAd := fun t=>DhA (hA t) (v t)
  let hwd := fun t=>Dhw (hw t) (v t)
  let Γd := fun t=>DΓ (Γ t) (v t)
  have hΓd : ∀ t i f,f∈Γd t i ↔ ∀ j,∃ z : ℤ,(cd t i).coord f j=z := fun t i=>hΓ t i.1
  let Qd := fun t=>(Carrier (Gd t) (nd t) (q t) (cd t) (skd t) (Ad t) (wd t) (hAd t))⧸
    lattice (Gd t) (nd t) (q t) (cd t) (skd t) (Ad t) (wd t) (hAd t) (Γd t)
  let : ∀ t,TopologicalSpace.MetrizableSpace (Qd t) := fun t=>
    (joint_array_topology (Gd t) (nd t) (q t) (cd t) (skd t) (Ad t) (wd t) (hAd t) (hwd t) (Γd t) (hΓd t)).2.2.2
  let : ∀ t,MetricSpace (Qd t) := fun t=>TopologicalSpace.metrizableSpaceMetric (Qd t)
  have htop : ∀ t,(inferInstance : MetricSpace (Qd t)).toUniformSpace.toTopologicalSpace=
    QuotientGroup.instTopologicalSpace (lattice (Gd t) (nd t) (q t) (cd t) (skd t) (Ad t) (wd t) (hAd t) (Γd t)) :=
    fun _=>rfl
  obtain ⟨φ,hφ,z,hz,hgood⟩ := source_global_literal_array_faces Gd nd q cd skd Ad wd hAd hwd Γd hΓd htop
    a m h v perm w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX hZ hQ0 hSize hWM hM hMs
    hL hsm hWL hML hLexact hXL (fun t b=>cubePattern (v t) b.2) (fun _ _=>rfl)
    (fun t N y b i=>g t N y b i.1) (fun t N y b i=>x t N y b i.1)
    (fun t N y b i=>slot t N y b i.1) qval hQ E ε hε hE
  refine ⟨φ,hφ,z,hz,?_⟩
  intro t
  dsimp only
  intro e j d hd pstar hpstar hpclose c₀ C₀ hc₀ hC₀ lo hi res hbox F
  let π:=cubeProjection (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t) (v t)
  have hh:=hgood t e j.succ d hd pstar hpstar hpclose c₀ C₀ hc₀ hC₀ lo hi res hbox (F.comp π)
  apply hh.congr'
  apply Filter.Eventually.of_forall
  intro k
  apply congrArg₂ (fun a b : ℂ=>a-b)
  · apply congrArg (mean (physicalResidueBox (lo k) (hi k) (res k) d))
    funext β
    apply congrArg F
    funext S
    dsimp only [π,Gd,nd,cd,skd,Ad,wd,hAd,hwd,Γd]
    rw [cubeProjection_face,cubeProjection_literal]
  · apply congrArg (mean (physicalResidueBox (lo k) (hi k) (res k) d))
    funext β
    apply congrArg F
    funext S
    exact cubeProjection_literal (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t) (Γ t) (v t)
      _ _ _ _ _ _ _ _ _ β S

end SourceIntegerArrays
end

 

section
 

 

noncomputable section
open scoped Topology
namespace RationalLattice
open MalcevCharacters
variable {G H : Type*} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable {m n : ℕ} (c : RealCoordinates G m) (d : RealCoordinates H n)

 

theorem exists_joint_integer_sublattice (F : H →* G)
    (hpoly : IsPolynomialMap c (fun x : Fin n → ℝ=>F (d.coord.symm x)))
    (hc : Continuous F) (hinj : Function.Injective F)
    (Γ : Subgroup G) (Ξ : Subgroup H)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (hΞ : ∀ g : H,g∈Ξ ↔ ∀ i,∃ z : ℤ,d.coord g i=z) :
    ∃ Δ : Subgroup H,∃ e : RealCoordinates H n,
      SecondKind e ∧ (∀ g : H,g∈Δ ↔ ∀ i,∃ z : ℤ,e.coord g i=z) ∧
      Δ≤Ξ ∧ Δ≤Γ.comap F ∧ (Δ.subgroupOf Ξ).FiniteIndex ∧
      (Δ.subgroupOf (Γ.comap F)).FiniteIndex ∧
      (∀ (B : Subgroup H) (k : ℕ),
        (∀ g,g∈B ↔ ∀ i : Fin n,i.val<k → d.coord g i=0) →
        ∀ g,g∈B ↔ ∀ i : Fin n,i.val<k → e.coord g i=0) ∧
      (∀ g : H,IsRational e g ↔ IsRational d g) := by
  classical
  obtain ⟨E,hE,hgrid⟩:=rationalHom_origin_grid c d F hpoly
  obtain ⟨w,hpos,hEw,hw⟩:=exists_lattice_weights d E hE
  let Δ:=weightedLattice d w hw
  let e:=scaledCoordinates d w hpos
  have hΔ : ∀ g : H,g∈Δ ↔ ∀ i,∃ z : ℤ,e.coord g i=z :=
    weightedLattice_iff d w hw hpos
  have hle : Δ≤Γ.comap F := by
    intro g hg
    apply (hΓ (F g)).mpr
    have hx : ∀ j,∃ z : ℤ,d.coord g j=(E:ℝ)*(z:ℝ) := by
      intro j
      obtain ⟨a,ha⟩:=hg j
      obtain ⟨b,hb⟩:=hEw j
      refine ⟨(b:ℤ)*a,?_⟩
      rw [ha,hb]
      push_cast
      ring
    simpa using hgrid (d.coord g) hx
  have hsource : Δ≤Ξ := by
    intro g hg
    apply (hΞ g).mpr
    intro i
    obtain ⟨z,hz⟩:=hg i
    exact ⟨(w i:ℤ)*z,by push_cast; exact hz⟩
  let : T2Space H:=d.coord.symm.t2Space
  let : DiscreteTopology Γ:=integerCoordinates_discrete c Γ hΓ
  let : DiscreteTopology Ξ:=integerCoordinates_discrete d Ξ hΞ
  let : DiscreteTopology (Γ.comap F):=
    DiscreteTopology.preimage_of_continuous_injective (Γ:Set G) hc hinj
  obtain ⟨C,hC,hrep⟩:=compact_reps_of_integerCoordinates e Δ hΔ
  have hidx:=TriangularDenominators.finiteIndex_of_compact_reps Δ (Γ.comap F) hle C hC hrep
  have hidx':=TriangularDenominators.finiteIndex_of_compact_reps Δ Ξ hsource C hC hrep
  refine ⟨Δ,secondCoordinates e,secondCoordinates_secondKind e,
    expCoordinates_lattice e Δ hΔ,hsource,hle,hidx',hidx,?_,?_⟩
  · intro B k hB
    apply secondCoordinates_adapted e B k
    intro g
    rw [hB]
    apply forall_congr'
    intro i
    apply imp_congr_right
    intro _
    change d.coord g i=0 ↔ d.coord g i/(w i:ℝ)=0
    have hn : (w i:ℝ)≠0:=by exact_mod_cast (hpos i).ne'
    simp [hn]
  · intro g
    exact (secondCoordinates_rational e g).trans (scaledCoordinates_rational d w hpos g)

 

def conjugateEmbedding (F : H →* G) (σ : G) : H →* G :=
  (MulAut.conj σ⁻¹).toMonoidHom.comp F

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp] lemma conjugateEmbedding_apply (F : H →* G) (σ : G) (x : H) :
    conjugateEmbedding F σ x=σ⁻¹*F x*σ := by simp [conjugateEmbedding]

theorem rational_conjugate_cover (hsk : SecondKind d) (F : H →* G)
    (hc : Continuous F) (hinj : Function.Injective F)
    (hrat : ∀ x,IsRational d x → IsRational c (F x))
    (Γ : Subgroup G) (Ξ : Subgroup H)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (hΞ : ∀ g : H,g∈Ξ ↔ ∀ i,∃ z : ℤ,d.coord g i=z)
    (σ : G) (hσ : IsRational c σ) :
    ∃ Δ : Subgroup H,∃ e : RealCoordinates H n,
      SecondKind e ∧ (∀ g : H,g∈Δ ↔ ∀ i,∃ z : ℤ,e.coord g i=z) ∧
      Δ≤Ξ ∧ Δ≤Γ.comap (conjugateEmbedding F σ) ∧
      (Δ.subgroupOf Ξ).FiniteIndex ∧
      (Δ.subgroupOf (Γ.comap (conjugateEmbedding F σ))).FiniteIndex ∧
      (∀ (B : Subgroup H) (k : ℕ),
        (∀ g,g∈B ↔ ∀ i : Fin n,i.val<k → d.coord g i=0) →
        ∀ g,g∈B ↔ ∀ i : Fin n,i.val<k → e.coord g i=0) ∧
      (∀ g : H,IsRational e g ↔ IsRational d g) := by
  have hcont : Continuous (conjugateEmbedding F σ):=by
    have he : (conjugateEmbedding F σ : H → G) = (fun x=>σ⁻¹*F x*σ) :=
      funext (conjugateEmbedding_apply F σ)
    rw [he]
    exact (continuous_const.mul hc).mul continuous_const
  have hinj' : Function.Injective (conjugateEmbedding F σ):=
    (MulAut.conj σ⁻¹).injective.comp hinj
  have hrat' (x : H) (hx : IsRational d x) :
      IsRational c (conjugateEmbedding F σ x) := by
    rw [conjugateEmbedding_apply]
    exact rational_mul c (rational_mul c (rational_inv c hσ) (hrat x hx)) hσ
  exact exists_joint_integer_sublattice c d (conjugateEmbedding F σ)
    (rationalHom_polynomial c d hsk _ hcont hrat') hcont hinj' Γ Ξ hΓ hΞ

end RationalLattice

end
end

end OAI
