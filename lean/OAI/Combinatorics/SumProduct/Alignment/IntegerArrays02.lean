import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays01
import OAI.Combinatorics.SumProduct.Alignment.RoughArray04
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
noncomputable section
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
 

theorem source_global_literal_array_faces
    (hΓ : ∀ t i g,g∈Γ t i ↔ ∀ j,∃ z : ℤ,(c t i).coord g j=z)
    [∀ t,MetricSpace ((Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
      lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t))]
    (htop : ∀ t,(inferInstance : MetricSpace
      ((Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
        lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t))).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace (lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)))
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
    (pattern : ∀ t,ι t→Fin (v t+1)→ℤ) (hpat : ∀ t i,pattern t i 0=1)
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
      ∀ (e : Fin (q t)) (j : Fin (v t+1)) (d : ℕ),0<d → ∀ (pstar : ℕ→ℤ),
      (∀ k,(M (φ k):ℤ)∣pstar k-((z k).2:ℤ)) →
      (∀ k,|(pstar k:ℝ)-((z k).2:ℝ)|≤R (φ k)) →
      let state := fun k β=>literalState (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t)
        (M (φ k)) (L (φ k)) (label k) (fun l=>((zin k).1 l:ℤ)) (pstar k) (pattern t)
        (g t (φ k) (zout k) (label k)) (x t (φ k) (zout k) (label k))
        (slot t (φ k) (zout k) (label k)) (qval t (φ k) (zout k) (label k)) β
      ∀ (c₀ C₀ : ℝ),0<c₀ →0<C₀ →
      ∀ (lo hi : ℕ→Fin (v t+1)→ℝ) (res : ℕ→Fin (v t+1)→ℤ),
      (∀ᶠ k in atTop,(∀ i,c₀*Z k≤hi k i-lo k i) ∧
        (∀ i,-C₀*Z k≤lo k i ∧ hi k i≤C₀*Z k)) →
      ∀ F : C((Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
        lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t),ℂ),
      Tendsto (fun k=>mean (physicalResidueBox (lo k) (hi k) (res k) d)
        (fun β=>F (faceAction (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
          (pattern t) e j (QuotientGroup.mk (state k β))))-
      mean (physicalResidueBox (lo k) (hi k) (res k) d)
        (fun β=>F (QuotientGroup.mk (state k β)))) atTop (𝓝 0)
 := by
  classical
  obtain ⟨φ,hφ,z,hz,hgood⟩ := source_global_selected_faces G n q c hsk A w hA hw Γ hΓ htop
    a m h v perm w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX hZ hQ0 hSize hWM hM hMs
    hL hsm hWL hML hLexact hXL pattern g x
    (fun t N y b i=>offset0 (M N) (R N) b (slot t N y b i))
    (fun t N y b i=>offset1 (M N) (slot t N y b i)) qval hQ E ε hε hE
  refine ⟨φ,hφ,z,hz,?_⟩
  intro t
  dsimp only
  intro e j d hd pstar hpstar hpclose c₀ C₀ hc₀ hC₀ lo hi res hbox F
  let zout (k : ℕ) (l : Fin (h t)) := (z k).1 (perm t (l.natAdd (m t)))
  let zin (k : ℕ) : (Fin (m t)→ℕ)×ℕ :=
    (fun l=>(z k).1 (perm t (l.castAdd (h t))),(z k).2)
  let label (k : ℕ) := expose (L (φ k)) (M (φ k):ℤ) (R (φ k)) (zin k)
  let D (k : ℕ) := actualData (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t) (Γ t)
    (pattern t) (g t (φ k) (zout k) (label k)) (x t (φ k) (zout k) (label k))
    (fun i=>offset0 (M (φ k)) (R (φ k)) (label k) (slot t (φ k) (zout k) (label k) i))
    (fun i=>offset1 (M (φ k)) (slot t (φ k) (zout k) (label k) i))
    (fun u=>(qval t (φ k) (zout k) (label k) u:ℝ)/(M (φ k):ℝ))
    (fun u=>-(residueData (L (φ k)) (qval t (φ k) (zout k) (label k) u) (label k):ℝ)/(M (φ k):ℝ))
    e j (coarseOrigin (v t) (M (φ k)) (R (φ k)) (label k))
    (shift (M (φ k)) (L (φ k)) (qval t (φ k) (zout k) (label k) e) (label k))
  obtain ⟨chart,grid,hgridpos,hgrid,J,hJ,hdegree⟩ :=
    source_joint_geometry (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t) (Γ t) (hΓ t)
  obtain ⟨Λ,ec,hec,hΛ,hle,D',hD,hdeg⟩ := RoughCoveredFace.grid_second_degree_cover chart
    (lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)) grid hgridpos hgrid
  have hcompact : @CompactSpace ((Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
      lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t))
      (QuotientGroup.instTopologicalSpace (lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t))) := by
    obtain ⟨S,hS,hrep⟩ := compact_reps_of_integerCoordinates ec Λ hΛ
    apply CompactGroupProducts.HasCompactReps.quotient_compactSpace
    refine ⟨S,hS,fun _ _=>Subgroup.mem_top _,?_⟩
    intro u _
    obtain ⟨s,hs,hsa⟩ := hrep u
    exact ⟨s,hs,hle hsa⟩
  let := hcompact
  have hgridgood (b : ℕ) : ∀ᶠ k in atTop,
      ¬badPhysical (lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t))
        (m t) (v t+1) (1/((b:ℝ)+1)) ((b:ℝ)+1) (b+1) (1/((b:ℝ)+1))
        (R (φ k)/(M (φ k):ℝ)) d
        (physicalOrigin (v t) (M (φ k)) (R (φ k)) (label k) (∏ l,((zin k).1 l:ℤ)) (pstar k))
        (D k).P (D k).σ (fun l=>((zin k).1 l:ℤ)) := by
    filter_upwards [hgood t e j d hd b] with k hk
    intro hbad
    exact hk ⟨pstar k,hpstar k,hpclose k,hbad⟩
  have hh := physical_grid_continuous
    (lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)) (htop t)
    (m t) (v t+1) (fun k=>R (φ k)/(M (φ k):ℝ))
    (fun k=>div_nonneg (hR _).le (by positivity)) d
    (fun k=>physicalOrigin (v t) (M (φ k)) (R (φ k)) (label k) (∏ l,((zin k).1 l:ℤ)) (pstar k))
    (fun k=>(D k).P) (fun k=>(D k).σ) (fun k l=>((zin k).1 l:ℤ))
    hgridgood c₀ C₀ hc₀ hC₀ lo hi res hbox F
  have hzin (k : ℕ) : zin k∈fullDomain (fun l : Fin (m t)=>X (φ k) (perm t (l.castAdd (h t))))
      (Xp (φ k)) (primorial (w0 (φ k))) := by
    rcases Finset.mem_filter.mp (hz k).2 with ⟨hraw,hcop⟩
    rcases Finset.mem_product.mp hraw with ⟨ht,hp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,hp⟩,hcop⟩
    exact Fintype.mem_piFinset.mpr (fun l=>(Fintype.mem_piFinset.mp ht) _)
  have hcop (k : ℕ) : IsCoprime (∏ l,(label k).residue l) (L (φ k)) := by
    have hr := image_residues (fun l : Fin (m t)=>X (φ k) (perm t (l.castAdd (h t))))
      (Xp (φ k)) (primorial (w0 (φ k))) (L (φ k)) (M (φ k):ℤ) (R (φ k)) (hL (φ k))
      (by exact_mod_cast hM (φ k)) (hWL (φ k)) (hWM (φ k)) _
      (Finset.mem_image.mpr ⟨zin k,hzin k,rfl⟩)
    exact IsCoprime.prod_left (fun l _=>
      (IntegerAlignment.coprime_smooth_rough (hsm (φ k))
        ((rough_iff_coprime _ _).mpr (hr.2.2.1 l))).symm)
  have hstate (k : ℕ) (β : Fin (v t+1)→ℤ) :=
    source_literal_entire_array (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t)
      (M (φ k)) (hM (φ k)) (L (φ k)) (hL (φ k)) (hML (φ k)) (R (φ k)) (zin k) (hcop k)
      (pstar k) (hpstar k) (pattern t) (hpat t)
      (g t (φ k) (zout k) (label k)) (x t (φ k) (zout k) (label k))
      (slot t (φ k) (zout k) (label k)) (qval t (φ k) (zout k) (label k)) β
  dsimp only at hstate
  simpa only [D,actualData,Int.cast_natCast,label,hstate] using hh

end SourceIntegerArrays
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
variable (hw : ∀ i j,0<w i j) (Γ : ∀ i,Subgroup (G i)) (v : ℕ)

 
def cubeVertex (β : Fin (v+1)→ℤ) (S : Finset (Fin v)) : ℤ := β 0+∑ j∈S,β j.succ

def cubePattern (S : Finset (Fin v)) : Fin (v+1)→ℤ :=
  Fin.cases 1 (fun j=>if j∈S then 1 else 0)

abbrev CubeIndex := ι×Finset (Fin v)
abbrev DG (a : CubeIndex (ι:=ι) v) := G a.1
abbrev Dn (a : CubeIndex (ι:=ι) v) := n a.1
section
variable {G n}
abbrev Dc (a : CubeIndex (ι:=ι) v) := c a.1
end
section
variable {G n c}
abbrev Dhsk (a : CubeIndex (ι:=ι) v) := hsk a.1
end
section
variable {G}
abbrev DA (a : CubeIndex (ι:=ι) v) := A a.1
end
section
variable {n}
abbrev Dw (a : CubeIndex (ι:=ι) v) := w a.1
end
section
variable {G n c A w}
abbrev DhA (a : CubeIndex (ι:=ι) v) := hA a.1
end
section
variable {n w}
abbrev Dhw (a : CubeIndex (ι:=ι) v) := hw a.1
end
section
variable {G}
abbrev DΓ (a : CubeIndex (ι:=ι) v) := Γ a.1
end
abbrev CSpace := Carrier G n q c hsk A w hA
abbrev CLattice := lattice G n q c hsk A w hA Γ
abbrev DCspace := Carrier (DG G v) (Dn n v) q (Dc c v) (Dhsk hsk v) (DA A v) (Dw w v) (DhA hA v)
abbrev DClattice := lattice (DG G v) (Dn n v) q (Dc c v) (Dhsk hsk v) (DA A v) (Dw w v) (DhA hA v) (DΓ Γ v)

lemma cubePattern_dot (β : Fin (v+1)→ℤ) (S : Finset (Fin v)) :
    ∑ j,cubePattern v S j*β j=cubeVertex v β S := by
  rw [Fin.sum_univ_succ]
  simp [cubePattern,cubeVertex,Finset.sum_ite_mem]

 
def cubeProjection : C((DCspace G n q c hsk A w hA v)⧸DClattice G n q c hsk A w hA Γ v,
    Finset (Fin v)→(CSpace G n q c hsk A w hA)⧸CLattice G n q c hsk A w hA Γ) where
  toFun z S:=Quotient.map (fun f i=>f (i,S)) (by
    intro f g hfg
    apply QuotientGroup.leftRel_apply.mpr
    intro i
    exact (QuotientGroup.leftRel_apply.mp hfg) (i,S)) z
  continuous_toFun:=by
    apply continuous_pi
    intro S
    apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp (continuous_pi (fun i=>continuous_apply (i,S)))

omit [Fintype ι] in
lemma cubeProjection_mk (f : DCspace G n q c hsk A w hA v) (S : Finset (Fin v)) :
    cubeProjection G n q c hsk A w hA Γ v (QuotientGroup.mk f) S=
      QuotientGroup.mk (fun i=>f (i,S)) := rfl

omit [Fintype ι] in
lemma cubeProjection_face (e : Fin q) (j : Fin v)
    (y : (DCspace G n q c hsk A w hA v)⧸DClattice G n q c hsk A w hA Γ v)
    (S : Finset (Fin v)) :
      cubeProjection G n q c hsk A w hA Γ v
        (faceAction (DG G v) (Dn n v) q (Dc c v) (Dhsk hsk v) (DA A v) (Dw w v) (DhA hA v)
        (DΓ Γ v) (fun a=>cubePattern v a.2) e j.succ y) S=
      if j∈S then faceAction G n q c hsk A w hA Γ (fun _ (_ : Fin 1)=>1) e 0
        (cubeProjection G n q c hsk A w hA Γ v y S)
      else cubeProjection G n q c hsk A w hA Γ v y S := by
  induction y using Quotient.inductionOn with
  | h f =>
    by_cases hj : j∈S
    · simp only [hj,ite_true]
      apply congrArg QuotientGroup.mk
      funext i
      simp [faceMap,inputShift,cubePattern,hj,DG,Dn,Dc,DA,Dw]
    · simp only [hj,ite_false]
      apply congrArg QuotientGroup.mk
      funext i
      apply Subtype.ext
      funext u
      change (f (i,S)).val (u+fun k=>(((Pi.single e (cubePattern v S j.succ) : Fin q→ℤ) k):ℝ))=(f (i,S)).val u
      simp only [cubePattern,Fin.cases_succ,hj,ite_false,Pi.single_zero,Pi.zero_apply,Int.cast_zero]
      change (f (i,S)).val (u+0)=(f (i,S)).val u
      rw [add_zero]

omit [Fintype ι] in
lemma cubeProjection_literal {m : ℕ} (M : ℕ) (L : ℤ) (b : Label m) (tail : Fin m→ℤ)
    (pstar : ℤ) (g x : ∀ i,G i) (slot : ι→ℤ) (qval : Fin q→ℤ)
    (β : Fin (v+1)→ℤ) (S : Finset (Fin v)) :
    cubeProjection G n q c hsk A w hA Γ v
      (QuotientGroup.mk (literalState (DG G v) (Dn n v) q (Dc c v) (Dhsk hsk v) (DA A v)
        (Dw w v) (DhA hA v) (Dhw hw v) M L b tail pstar (fun a=>cubePattern v a.2)
        (fun a=>g a.1) (fun a=>x a.1) (fun a=>slot a.1) qval β)) S=
      QuotientGroup.mk (literalState G n q c hsk A w hA hw M L b tail pstar
        (fun _ (_ : Fin 1)=>1) g x slot qval (fun _=>cubeVertex v β S)) := by
  rw [cubeProjection_mk]
  apply congrArg QuotientGroup.mk
  funext i
  change PolynomialArrays.sourceElement (c i) (hsk i) (A i) (w i) (hA i) (hw i) (g i) (x i)
      (exponent M L b tail pstar (slot i) (cubePattern v S) β qval 0:ℝ) _ = _
  simp [literalState,exponent,cubePattern_dot]
 

omit [Fintype ι] in
theorem literal_cube_interpretation :
    ∃ π : C((DCspace G n q c hsk A w hA v)⧸DClattice G n q c hsk A w hA Γ v,
      Finset (Fin v)→(CSpace G n q c hsk A w hA)⧸CLattice G n q c hsk A w hA Γ),
    (∀ f S,π (QuotientGroup.mk f) S=QuotientGroup.mk (fun i=>f (i,S))) ∧
    (∀ (e : Fin q) (j : Fin v) y S,
      π (faceAction (DG G v) (Dn n v) q (Dc c v) (Dhsk hsk v) (DA A v) (Dw w v) (DhA hA v)
        (DΓ Γ v) (fun a=>cubePattern v a.2) e j.succ y) S=
      if j∈S then faceAction G n q c hsk A w hA Γ (fun _ (_ : Fin 1)=>1) e 0 (π y S)
      else π y S) ∧
    (∀ {m : ℕ} (M : ℕ) (L : ℤ) (b : Label m) (tail : Fin m→ℤ) (pstar : ℤ)
      (g x : ∀ i,G i) (slot : ι→ℤ) (qval : Fin q→ℤ) (β : Fin (v+1)→ℤ) S,
      π (QuotientGroup.mk (literalState (DG G v) (Dn n v) q (Dc c v) (Dhsk hsk v) (DA A v)
        (Dw w v) (DhA hA v) (Dhw hw v) M L b tail pstar (fun a=>cubePattern v a.2)
        (fun a=>g a.1) (fun a=>x a.1) (fun a=>slot a.1) qval β)) S=
      QuotientGroup.mk (literalState G n q c hsk A w hA hw M L b tail pstar
        (fun _ (_ : Fin 1)=>1) g x slot qval (fun _=>cubeVertex v β S)))
 := by
  exact ⟨cubeProjection G n q c hsk A w hA Γ v,
    cubeProjection_mk G n q c hsk A w hA Γ v,
    cubeProjection_face G n q c hsk A w hA Γ v,
    by
      intro m M L b tail pstar g x slot qval β S
      exact cubeProjection_literal G n q c hsk A w hA hw Γ v M L b tail pstar g x slot qval β S⟩

end SourceIntegerArrays

end

end OAI
