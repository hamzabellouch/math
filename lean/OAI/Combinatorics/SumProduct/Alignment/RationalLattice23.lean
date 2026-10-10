import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays04
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
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
variable {τ : Type} [Fintype τ] {ι : τ→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : τ→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j) (Γ : ∀ t i,Subgroup (G t i))
theorem source_compact_factorized_haar
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
  obtain ⟨φ,hφ,z,hz,f,huniform,herror,hgood⟩:=source_global_compact_haar G n q c hsk A w hA hw Γ hΓ
    a s m h perm w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX hZ hQ0 hSize hWM hM hMs
    hL hsm hWL hML hLexact hXL g x slot qval hQ Yobs Obs Kobs Bobs hLip hBound E ε hε hE
  refine ⟨φ,hφ,z,hz,f,huniform,herror,?_⟩
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
namespace RationalLattice
open MalcevCharacters RationalLevelFlow
variable {G H : Type*} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable {m n : ℕ} (c : RealCoordinates G m) (d : RealCoordinates H n)

omit [IsTopologicalGroup H] in
lemma rationalHom_of_basis (hsk : SecondKind d) (F : H →* G)
    (hF : Continuous F) (hb : ∀ i,IsRational c (F (axis d i 1)))
    (g : H) (hg : IsRational d g) : IsRational c (F g) := by
  let A (i : Fin n) : Multiplicative ℝ →* H :=
    { toFun := fun t=>axis d i t.toAdd
      map_one' := axis_zero d i
      map_mul' := fun t u=>hsk.axis_add i t.toAdd u.toAdd }
  have he (i : Fin n) (t : ℝ) : F (axis d i t)=realPower c (F (axis d i 1)) t :=
    continuous_flow_eq_realPower c (F.comp (A i))
      (hF.comp ((axis_continuous d i).comp continuous_toAdd)) t
  have hp (i : Fin n) : F (axis d i (d.coord g i))∈rationalSubgroup c := by
    obtain ⟨q,hq⟩:=hg i
    rw [he,←hq]
    exact realPower_rational c (hb i) q
  have hprod : (List.ofFn (fun i : Fin n=>F (axis d i (d.coord g i)))).prod∈rationalSubgroup c := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
    exact hp i
  change F g∈rationalSubgroup c
  have hmap : F g=(List.ofFn (fun i : Fin n=>F (axis d i (d.coord g i)))).prod := by
    conv_lhs => rw [hsk.ordered g]
    rw [map_list_prod,List.map_ofFn]
    rfl
  rw [hmap]
  exact hprod

omit [IsTopologicalGroup H] in
lemma rationalHom_of_lattice (hsk : SecondKind d) (F : H →* G)
    (hF : Continuous F) (Δ : Subgroup H)
    (hΔ : ∀ g,g∈Δ ↔ ∀ i,∃ z : ℤ,d.coord g i=z)
    (himage : ∀ g∈Δ,IsRational c (F g)) :
    ∀ g,IsRational d g → IsRational c (F g) :=
  rationalHom_of_basis c d hsk F hF
    (fun i=>himage _ (axis_one_mem d Δ hΔ i))

end RationalLattice
end
 
end

noncomputable section
namespace RationalLattice
open MalcevCharacters RationalLevelFlow
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {k : ℕ} (d : RealCoordinates H k)
omit [IsTopologicalGroup H] in
lemma rational_of_pos_pow (g : H) (n : ℕ) (hn : 0<n) (hg : IsRational d (g^n)) :
    IsRational d g := by
  have he : realPower d (g^n) ((1/(n:ℚ):ℚ):ℝ)=g := by
    apply (logHomeomorph d).injective
    simp only [logHomeomorph_apply,canonicalLog_realPower]
    rw [←realPower_nat d g n,canonicalLog_realPower]
    have hn' : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
    simp [smul_smul,hn']
  rw [←he]
  exact realPower_rational d hg _
 

lemma CoveredLattice.mem_rational (Γ : Subgroup H) (B : CoveredLattice d Γ)
    (g : H) (hg : g∈Γ) : IsRational d g := by
  let : T2Space H:=d.coord.symm.t2Space
  let : DiscreteTopology Γ:=B.discrete
  obtain ⟨C,hC,hrep⟩:=compact_reps_of_integerCoordinates d B.small B.integer
  let : (B.small.subgroupOf Γ).FiniteIndex:=
    TriangularDenominators.finiteIndex_of_compact_reps B.small Γ B.le C hC hrep
  obtain ⟨n,hn,_,hpow⟩:=(B.small.subgroupOf Γ).exists_pow_mem_of_index_ne_zero
    Subgroup.FiniteIndex.index_ne_zero ⟨g,hg⟩
  apply rational_of_pos_pow d g n hn
  have hi:= (B.integer (g^n)).mp hpow
  intro i
  obtain ⟨z,hz⟩:=hi i
  exact ⟨(z:ℚ),by simpa only [Rat.cast_intCast] using hz.symm⟩

omit [IsTopologicalGroup H] in
lemma rationalHom_covered {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {n : ℕ} (c : RealCoordinates G n) (Γ : Subgroup G) (C : CoveredLattice c Γ)
    (hd : SecondKind d) (Δ : Subgroup H) (hΔ : ∀ g,g∈Δ ↔ ∀ i,∃ z : ℤ,d.coord g i=z)
    (p : H→*G) (hp : Continuous p) (himage : ∀ g∈Δ,p g∈Γ) :
    ∀ g,IsRational d g →IsRational c (p g) :=
  rationalHom_of_lattice c d hd p hp Δ hΔ
    (fun g hg=>C.mem_rational c Γ (p g) (himage g hg))
end RationalLattice
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
include hw in
 

theorem target_geometry (hmono : ∀ t i,Monotone (w t i))
    (hΓ : ∀ t i g,g∈Γ t i ↔ ∀ j,∃ z : ℤ,(c t i).coord g j=z)
    (d : RealCoordinates (Full G n q c hsk A w hA) (FullDim n q w))
    (B : CoveredLattice d (FullLattice G n q c hsk A w hA Γ)) (hd : SecondKind d) :
    ∃ dc : ∀ t,RealCoordinates (Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))
      (Fintype.card (FiniteProducts.Index (JointArrays.dimension (n t) (fun _=>q t) (w t)))),
    ∃ _ : ∀ t,CoveredLattice (dc t) (lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)),
      (∀ t,SecondKind (dc t)) ∧
      ∀ t f,IsRational d f → IsRational (dc t) (targetHom G n q c hsk A w hA t f)
 := by
  classical
  have hc (t : τ):=JointArrays.covered_geometry (G t) (n t) (fun _=>q t) (c t) (hsk t)
    (A t) (w t) (hA t) (hw t) (hmono t) (Γ t) (hΓ t)
  choose dc hdc hC ha hr using hc
  let C t:=Classical.choice (hC t)
  refine ⟨dc,C,hdc,?_⟩
  intro t
  exact RationalLattice.rationalHom_covered d (dc t) _ (C t) hd B.small B.integer
    (targetHom G n q c hsk A w hA t) (targetHom_continuous G n q c hsk A w hA t)
    (fun g hg=>targetHom_lattice G n q c hsk A w hA Γ t g (B.le hg))

end SourceIntegerArrays.GlobalJoint

end

end OAI
