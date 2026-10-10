import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice23
import OAI.Combinatorics.SumProduct.Alignment.WordPlan04
import OAI.Combinatorics.SumProduct.Alignment.AllLevel15
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
end
 
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates
open ConstructedWordPlan.GlobalWordPlan
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a) {ι : Fin D.targets→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : Fin D.targets→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (Γ : ∀ t i,Subgroup (G t i)) (coord : ∀ e,Fin (q (D.owner e)))
abbrev Target (t : Fin D.targets) :=
  (Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
    lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)

private def slotBasis (t : Fin D.targets) (e : Fin D.pairs) : Fin (q t)→ℤ :=
  if h : D.owner e=t then h ▸ (Pi.single (coord e) 1) else 0

private def slotProjection (t : Fin D.targets) : Slots D →+ (Fin (q t)→ℤ) where
  toFun v := ∑ e,v e • slotBasis D q coord t e
  map_zero' := by simp
  map_add' v z := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]

private lemma slotProjection_unit (e : Fin D.pairs) :
    slotProjection D q coord (D.owner e) (Pi.single e 1)=Pi.single (coord e) 1 := by
  classical
  change ∑ f,(Pi.single e (1:ℤ) : Slots D) f • slotBasis D q coord (D.owner e) f= _
  rw [Finset.sum_eq_single e]
  · simp [slotBasis]
  · intro f _ hfe
    simp [Pi.single_eq_of_ne hfe]
  · simp

private def shiftAll (t : Fin D.targets) (v : Fin (q t)→ℤ) :
    Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) →*
    Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) where
  toFun f i:=PolynomialArrays.shift (c t i) (hsk t i) (A t i) (w t i) (hA t i)
    (fun j=>(v j:ℝ)) (f i)
  map_one':=by funext i;exact map_one _
  map_mul' _ _:=by funext i;exact map_mul _ _ _

omit [∀ t, Fintype (ι t)] in
private lemma shiftAll_continuous (t : Fin D.targets) (v : Fin (q t)→ℤ) :
    Continuous (shiftAll D G n q c hsk A w hA t v) :=
  continuous_pi (fun i=>(PolynomialArrays.shift_continuous (c t i) (hsk t i) (A t i) (w t i) (hA t i) _).comp
    (continuous_apply i))

private def translateTarget (t : Fin D.targets) (v : Fin (q t)→ℤ) :
    Target D G n q c hsk A w hA Γ t → Target D G n q c hsk A w hA Γ t :=
  Quotient.map (shiftAll D G n q c hsk A w hA t v) (by
    intro f g hfg
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv,← map_mul]
    intro i
    exact (PolynomialArrays.shift_lattice (c t i) (hsk t i) (A t i) (w t i) (hA t i) (Γ t i) v _).mpr
      ((QuotientGroup.leftRel_apply.mp hfg) i))

omit [∀ t,Fintype (ι t)] in
private lemma translateTarget_continuous (t : Fin D.targets) (v : Fin (q t)→ℤ) :
    Continuous (translateTarget D G n q c hsk A w hA Γ t v) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (shiftAll_continuous D G n q c hsk A w hA t v))

omit [∀ t, Fintype (ι t)] in
private lemma translateTarget_add (t : Fin D.targets) (v z : Fin (q t)→ℤ)
    (x : Target D G n q c hsk A w hA Γ t) :
    translateTarget D G n q c hsk A w hA Γ t (v+z) x=
    translateTarget D G n q c hsk A w hA Γ t v (translateTarget D G n q c hsk A w hA Γ t z x) := by
  induction x using Quotient.inductionOn with | h f =>
    apply congrArg QuotientGroup.mk
    funext i
    apply Subtype.ext
    funext u
    change (f i).val (u+(fun j=>((v+z) j:ℝ)))=(f i).val ((u+(fun j=>(v j:ℝ)))+(fun j=>(z j:ℝ)))
    apply congrArg (f i).val
    funext j
    simp only [Pi.add_apply,Int.cast_add]
    ring

omit [∀ t, Fintype (ι t)] in
private lemma translateTarget_zero (t : Fin D.targets) (x : Target D G n q c hsk A w hA Γ t) :
    translateTarget D G n q c hsk A w hA Γ t 0 x=x := by
  induction x using Quotient.inductionOn with | h f =>
    apply congrArg QuotientGroup.mk
    funext i
    apply Subtype.ext
    funext u
    change (f i).val (u+(fun _=>((0:ℤ):ℝ)))=(f i).val u
    apply congrArg (f i).val
    funext j
    simp

@[instance_reducible]
private def targetAction (t : Fin D.targets) : MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t) where
  smul v x:=translateTarget D G n q c hsk A w hA Γ t (slotProjection D q coord t v.toAdd) x
  one_smul x:=by
    change translateTarget D G n q c hsk A w hA Γ t (slotProjection D q coord t 0) x=x
    rw [map_zero,translateTarget_zero]
  mul_smul v z x:=by
    change translateTarget D G n q c hsk A w hA Γ t (slotProjection D q coord t (v.toAdd+z.toAdd)) x=_
    rw [map_add,translateTarget_add]
    rfl
 

omit [∀ t,Fintype (ι t)] in
theorem target_actions :
    ∃ act : ∀ t,MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t),
      (∀ t (v : Shifts D),letI:=act t;Continuous (fun x : Target D G n q c hsk A w hA Γ t=>v • x)) ∧
      (∀ e x,letI:=act (D.owner e);
        unitShift D e • x = faceAction (G (D.owner e)) (n (D.owner e)) (q (D.owner e))
          (c (D.owner e)) (hsk (D.owner e)) (A (D.owner e)) (w (D.owner e)) (hA (D.owner e)) (Γ (D.owner e))
          (fun _ (_ : Fin 1)=>1) (coord e) 0 x)
 := by
  classical
  refine ⟨targetAction D G n q c hsk A w hA Γ coord,?_,?_⟩
  · intro t v
    exact translateTarget_continuous D G n q c hsk A w hA Γ t _
  · intro e x
    change translateTarget D G n q c hsk A w hA Γ (D.owner e)
      (slotProjection D q coord (D.owner e) (Pi.single e 1)) x=_
    rw [slotProjection_unit]
    induction x using Quotient.inductionOn with | h f => rfl

end SourceIntegerArrays.GlobalJoint
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates
open ConstructedWordPlan.GlobalWordPlan
open AllLevelFactorization AllLevelFactorization.Factorization MeasureTheory
open scoped BigOperators Topology
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

def FactorizedPhysical (coord : ∀ e,Fin (q (D.owner e))) (s : ℕ) (P : ℕ→ℤ→Full G n q c hsk A w hA) (Z : ℕ→ℝ) : Prop :=
  ∃ d : RealCoordinates (Full G n q c hsk A w hA) (FullDim n q w),
  ∃ B : CoveredLattice d (FullLattice G n q c hsk A w hA Γ),
    SecondKind d ∧
    (∀ k f,f∈(FullFiltration G n q c hsk A w hA).level k ↔
      ∀ j,JointArrays.jointWeight (FlatN n) (FlatQ q) (FlatW w) j<k → d.coord f j=0) ∧
    (∀ f,IsRational d f → ∀ t (i : ι t) (u : Fin (q t)→ℤ),
      IsRational (c t i) ((f ⟨t,i⟩).val (fun j=>(u j:ℝ)))) ∧
    ∃ F : Factorization d B.small s (FullFiltration G n q c hsk A w hA) P Z,
    ∃ act : ∀ t,MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t),
      (∀ t (v : Shifts D),letI:=act t;Continuous (fun x : Target D G n q c hsk A w hA Γ t=>v • x)) ∧
      (∀ e x,letI:=act (D.owner e);
        unitShift D e • x = faceAction (G (D.owner e)) (n (D.owner e)) (q (D.owner e))
          (c (D.owner e)) (hsk (D.owner e)) (A (D.owner e)) (w (D.owner e)) (hA (D.owner e)) (Γ (D.owner e))
          (fun _ (_ : Fin 1)=>1) (coord e) 0 x) ∧
      letI : ∀ t,MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t):=act
      ∀ (r : Fin F.period) (C : F.ResidueCover r) (β : ℝ),
        Nonempty (CoveredPhysicalData D C.pivotChart.chart C.pointFiltration C.pointLattice
          (fun t=>targetCoset G n q c hsk A w hA Γ B.small B.le t) (C.pivotImage β) s)
include hw coord in
 

theorem factorized_physical
    (hmono : ∀ t i,Monotone (w t i))
    (hΓ : ∀ t i g,g∈Γ t i ↔ ∀ j,∃ z : ℤ,(c t i).coord g j=z)
    (s : ℕ) (P : ℕ→ℤ→Full G n q c hsk A w hA) (Z : ℕ→ℝ)
    (hh : FactorizedAllHaar G n q c hsk A w hA Γ s P Z) :
    FactorizedPhysical D G n q c hsk A w hA Γ coord s P Z
 := by
  classical
  obtain ⟨d,B,hd,hfil,hrational,F,hhaar⟩:=hh
  obtain ⟨dc,cover,hdc,hrat⟩:=target_geometry G n q c hsk A w hA hw Γ hmono hΓ d B hd
  obtain ⟨act,hcont,hunit⟩:=target_actions D G n q c hsk A w hA Γ coord
  refine ⟨d,B,hd,hfil,hrational,F,act,hcont,hunit,?_⟩
  let : ∀ t,MulAction (Shifts D) (Target D G n q c hsk A w hA Γ t):=act
  let : SecondCountableTopology (Full G n q c hsk A w hA):=coordinates_secondCountable d
  let : CompactSpace ((Full G n q c hsk A w hA)⧸B.small):=AbelianMalcevTorus.quotient_compact d B.small B.integer
  let : MeasurableSpace ((Full G n q c hsk A w hA)⧸B.small):=borel _
  let : BorelSpace ((Full G n q c hsk A w hA)⧸B.small):=⟨rfl⟩
  let Y:=Target D G n q c hsk A w hA Γ
  have htop (t) := joint_array_topology (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t) (Γ t) (hΓ t)
  let : ∀ t,SecondCountableTopology (Y t):=fun t=>(htop t).1
  let : ∀ t,T2Space (Y t):=fun t=>(htop t).2.1
  let : ∀ t,CompactSpace (Y t):=fun t=>(htop t).2.2.1
  let : ∀ t,TopologicalSpace.MetrizableSpace (Y t):=fun t=>(htop t).2.2.2
  let : ∀ t,MeasurableSpace (Y t):=fun t=>borel _
  let : ∀ t,BorelSpace (Y t):=fun t=>⟨rfl⟩
  intro r C β
  let : ∀ k : ℕ,MeasurableSpace (C.CubeSpace (ι:=Fin (k+1))):=fun _=>borel _
  let : ∀ k : ℕ,BorelSpace (C.CubeSpace (ι:=Fin (k+1))):=fun _=>⟨rfl⟩
  let TG t:=Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t)
  let Λ t:=lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
  let sym (e : Fin D.pairs) := faceMap (G (D.owner e)) (n (D.owner e)) (q (D.owner e))
    (c (D.owner e)) (hsk (D.owner e)) (A (D.owner e)) (w (D.owner e)) (hA (D.owner e))
    (fun _ (_ : Fin 1)=>1) (coord e) 0
  have hsym (e) : Continuous (sym e):=faceMap_continuous _ _ _ _ _ _ _ _ _ _ _
  have hsymΛ (e) (g : TG (D.owner e)) (hg : g∈Λ (D.owner e)) : sym e g∈Λ (D.owner e) := by
    intro i
    exact (PolynomialArrays.shift_lattice _ _ _ _ _ _ _ _).mpr (hg i)
  have hown (e) (f : TG (D.owner e)) :
      (QuotientGroup.mk (sym e f) : Y (D.owner e))=unitShift D e • (QuotientGroup.mk f : Y (D.owner e)) := by
    exact (hunit e (QuotientGroup.mk f)).symm
  refine ⟨C.physicalData_of_haar D (fun t=>targetCoset G n q c hsk A w hA Γ B.small B.le t)
    TG (fun t=>Fintype.card (FiniteProducts.Index (JointArrays.dimension (n t) (fun _=>q t) (w t))))
    dc Λ cover (targetHom G n q c hsk A w hA) (targetHom_continuous G n q c hsk A w hA)
    (fun t g hg=>targetHom_lattice G n q c hsk A w hA Γ t g (B.le hg)) hrat
    (fun _ x=>x) (fun _ _=>rfl) sym hsym hsymΛ hown β ?_⟩
  intro e k hk
  have ht (m : MeasurableSpace (Finset (Fin (k+1))→Y (D.owner e)))
      (hm : @BorelSpace (Finset (Fin (k+1))→Y (D.owner e)) _ m) :
      letI:=m
      letI:=hm
      Measure.map (PhysicalCubeMaps.upperFace (Fin.last k)
        (faceAction (G (D.owner e)) (n (D.owner e)) (q (D.owner e)) (c (D.owner e))
          (hsk (D.owner e)) (A (D.owner e)) (w (D.owner e)) (hA (D.owner e)) (Γ (D.owner e))
          (fun _ (_ : Fin 1)=>1) (coord e) 0))
        (C.marginalCubeHaar (ι:=Fin (k+1)) β (PhysicalCubeMaps.vertices (ι:=Fin (k+1)) (targetCoset G n q c hsk A w hA Γ B.small B.le (D.owner e)))
          : Measure (Finset (Fin (k+1))→Y (D.owner e)))=
        (C.marginalCubeHaar (ι:=Fin (k+1)) β (PhysicalCubeMaps.vertices (ι:=Fin (k+1)) (targetCoset G n q c hsk A w hA Γ B.small B.le (D.owner e)))
          : Measure (Finset (Fin (k+1))→Y (D.owner e))) := by
    have he:=hm.measurable_eq
    subst m
    exact hhaar (D.owner e) r C ⟨k,Nat.lt_succ_of_le hk⟩ (coord e) (Fin.last k) β
  exact ht _ inferInstance

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
theorem source_compact_physical
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
      ∀ pstar : Fin D.targets→ℕ→ℤ,
      (∀ t k,(M (φ k):ℤ)∣pstar t k-((z k).2:ℤ)) →
      (∀ t k,|(pstar t k:ℝ)-((z k).2:ℝ)|≤R (φ k)) →
      let zout := fun t k l=>(z k).1 (perm t (l.natAdd (m t)))
      let zin := fun t k=>((fun l=>(z k).1 (perm t (l.castAdd (h t)))),(z k).2)
      let label := fun t k=>expose (L (φ k)) (M (φ k):ℤ) (R (φ k)) (zin t k)
      FactorizedPhysical D G n q c hsk A w hA Γ coord s
        (fun k=>rawJoint G n q m c hsk A w hA hw (M (φ k)) (L (φ k))
          (fun t=>label t k) (fun t l=>((zin t k).1 l:ℤ)) (fun t=>pstar t k)
          (fun t=>slot t (φ k) (zout t k) (label t k))
          (fun t=>qval t (φ k) (zout t k) (label t k))
          (fun t=>g t (φ k) (zout t k) (label t k))
          (fun t=>x t (φ k) (zout t k) (label t k)))
        (fun k=>R (φ k)/(M (φ k):ℝ)) := by
  classical
  obtain ⟨φ,hφ,z,hz,f,huniform,herror,hgood⟩:=source_compact_factorized_haar G n q c hsk A w hA hw Γ
    hΓ hmono s h0 h1 hs a m h perm w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX hZ hQ0
    hSize hWM hM hMs hL hsm hWL hML hLexact hXL g x slot qval hQ Yobs Obs Kobs Bobs hLip hBound E ε hε hE
  refine ⟨φ,hφ,z,hz,f,huniform,herror,?_⟩
  intro pstar hpstar hpclose
  exact factorized_physical D G n q c hsk A w hA hw Γ coord hmono hΓ s _ _ (hgood pstar hpstar hpclose)

end SourceIntegerArrays

end
end

end OAI
