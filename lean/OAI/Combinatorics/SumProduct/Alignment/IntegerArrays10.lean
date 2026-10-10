import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays09
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint
open SourceResidueAlignment ProductExposureLabels SourceMacroSelection
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

 

structure LocalModels where
  m : Fin D.targets→ℕ
  M : ℕ
  R : ℕ
  L : ℤ
  H : Fin D.targets→ℕ
  z : ∀ t,(Fin (m t)→ℕ)×ℕ
  pstar : Fin D.targets→ℤ
  slot : ∀ t,ι t→ℤ
  qval : ∀ t,Fin (q t)→ℤ
  g : ∀ t i,ℤ→ℤ→G t i
  x : ∀ t i,ℤ→ℤ→G t i
  obs : ∀ t i,ℤ→ℤ→((G t i)⧸Γ t i) →ᵇ ℝ

namespace LocalModels
variable {D G q Γ}
variable (d : LocalModels D G q Γ)
def label (t : Fin D.targets) := expose d.L (d.M:ℤ) (d.R:ℝ) (d.z t)
def bin (t : Fin D.targets) := modelBin (d.H t) d.R (d.label t)
def residue (t : Fin D.targets) (i : ι t) := rSlot d.M (d.label t) (d.slot t i)
def frozenObs (t : Fin D.targets) (i : ι t) := d.obs t i (d.bin t) (d.residue t i)
def state (k : ℤ) : Full G n q c hsk A w hA :=
  rawJoint G n q d.m c hsk A w hA hw d.M d.L d.label
    (fun t j=>((d.z t).1 j:ℤ)) d.pstar d.slot d.qval
    (fun t i=>d.g t i (d.bin t) (d.residue t i))
    (fun t i=>d.x t i (d.bin t) (d.residue t i)) k
 
def value (k : ℤ) (t : Fin D.targets) (i : ι t) (u : Fin (q t)→ℤ) : ℝ :=
  pieceModel (Γ t i) d.M (d.H t) (d.g t i) (d.x t i) (fun b r=>d.obs t i b r)
    ((∏ j,((d.z t).1 j:ℤ))*(d.pstar t+(d.M:ℤ)*k+d.slot t i)+
      (d.M:ℤ)*(∑ e,shift d.M d.L (d.qval t e) (d.label t) (fun j=>((d.z t).1 j:ℤ))*u e))
 

def modelSuccess (k : ℤ) (s r : ℕ) (hs1 : 1 ≤ s)
    (formula : ∀ t,ℚ→Slots D→Fin r→ι t) (Fs : Finset (Scale a))
    (q₀ : ℕ) (b : Scale a) (τ : ℝ) : Prop :=
  ∃ p∈pivotOptions s r hs1 D Fs,∀ i : Comparison D Fs r,
    let t:=i.2.1.1
    let a₀:=blockProduct (scaleRun D 0 p b*i.1.val) (block D.index D.tail t)
    let v:=jumpSlot D q₀ p b
    let z:=terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val
    2*τ<d.value k t (formula t a₀ v i.2.2) 0 →
      τ<d.value k t (formula t a₀ (z.toAdd+v) i.2.2) (ownInput D q coord t z.toAdd)
end LocalModels

namespace LocalModels
variable {D G q Γ}
variable (d : LocalModels D G q Γ)
omit [∀ t,Fintype (ι t)] in
theorem actual_reading (k : ℤ) (t : Fin D.targets) (i : ι t) (u : Fin (q t)→ℤ)
    (hM : 0<d.M) (hR : 0<d.R) (hL : 0<d.L) (hML : (d.M:ℤ)∣d.L)
    (hH : 0<d.H t) (ht : ∀ j,0<(d.z t).1 j)
    (hst : Stable (2^(d.m t)+1) (d.H t) d.R (d.label t))
    (hcop : IsCoprime (∏ j,(d.label t).residue j) d.L)
    (hpstar : (d.M:ℤ)∣d.pstar t-((d.z t).2:ℤ))
    (K Q V : ℝ) (hK : 0≤K) (hQ : 0≤Q)
    (hV : (∏ j,((d.z t).1 j:ℝ))≤V)
    (hbase : |((d.pstar t+(d.M:ℤ)*k):ℝ)-((d.z t).2:ℝ)|≤d.R)
    (hslot : |(d.slot t i:ℝ)|≤K*(d.L:ℝ))
    (hq : ∀ e,|(d.qval t e:ℝ)|≤Q)
    (hsmall : 2*K*(Q+V*(d.L:ℝ))≤d.R) (hinput : (∑ e,|(u e:ℝ)|)≤K) :
    d.frozenObs t i
      (modelEval D G n q c hsk A w hA Γ t i u
        (targetCoset G n q c hsk A w hA Γ (FullLattice G n q c hsk A w hA Γ) le_rfl t
          (QuotientGroup.mk (d.state n c hsk A w hA hw k))))=d.value k t i u := by
  have hb:=source_numeric_window (v:=0) d.M d.L hL hML d.R hR (d.z t) ht hcop (d.pstar t)
    (d.slot t i) (fun _ : Fin 1=>1) (fun _=>k) (d.qval t) u K Q V hK hQ hV
    (by simpa only [Fin.sum_univ_one,one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.zero_add,one_nsmul] using hbase)
    hslot hinput hq hsmall
  have he:=source_literal_model_reading (v:=0) (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t)
    d.M hM d.L hML (2^(d.m t)+1) (d.H t) d.R hH (d.z t) hst (d.pstar t) hpstar
    (fun _ (_ : Fin 1)=>1) (d.slot t) (d.qval t) (fun _=>k) u (Γ t) (d.g t) (d.x t)
    (fun i b r=>d.obs t i b r) i hb
  change d.frozenObs t i (QuotientGroup.mk
    ((targetHom G n q c hsk A w hA t (d.state n c hsk A w hA hw k) i).val
      (fun e=>(u e:ℝ))))=d.value k t i u
  rw [state,target_rawJoint]
  simpa only [frozenObs,bin,residue,label,value,number,Fin.sum_univ_one,one_mul,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.zero_add,one_nsmul] using he.symm
end LocalModels

 

omit [∀ t,Fintype (ι t)] in
theorem source_model_event (d : LocalModels D G q Γ) (k : ℤ)
    (hM : 0<d.M) (hR : 0<d.R) (hL : 0<d.L) (hML : (d.M:ℤ)∣d.L)
    (hH : ∀ t,0<d.H t) (ht : ∀ t j,0<(d.z t).1 j)
    (hst : ∀ t,Stable (2^(d.m t)+1) (d.H t) d.R (d.label t))
    (hcop : ∀ t,IsCoprime (∏ j,(d.label t).residue j) d.L)
    (hpstar : ∀ t,(d.M:ℤ)∣d.pstar t-((d.z t).2:ℤ))
    (K Q : ℝ) (V : Fin D.targets→ℝ) (hK : 0≤K) (hQ : 0≤Q)
    (hV : ∀ t,(∏ j,((d.z t).1 j:ℝ))≤V t)
    (hbase : ∀ t,|((d.pstar t+(d.M:ℤ)*k):ℝ)-((d.z t).2:ℝ)|≤d.R)
    (hslot : ∀ t i,|(d.slot t i:ℝ)|≤K*(d.L:ℝ))
    (hq : ∀ t e,|(d.qval t e:ℝ)|≤Q)
    (hsmall : ∀ t,2*K*(Q+V t*(d.L:ℝ))≤d.R)
    (s r : ℕ) (hs1 : 1 ≤ s) (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (Fs : Finset (Scale a)) (q₀ : ℕ) (b : Scale a) (τ : ℝ)
    (hinput : ∀ p∈pivotOptions s r hs1 D Fs,∀ i : Comparison D Fs r,
      ∑ e,|(ownInput D q coord i.2.1.1
        (terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val).toAdd e:ℝ)|≤K) :
    QuotientGroup.mk (d.state n c hsk A w hA hw k)∈
      intrinsicSuccess D G n q c hsk A w hA Γ coord s r hs1 formula d.frozenObs Fs q₀ b τ ↔
    d.modelSuccess coord k s r hs1 formula Fs q₀ b τ

 := by
  classical
  have hc (p : Path D) (i : Comparison D Fs r) :
      centerReading D (Target D G n q c hsk A w hA Γ)
        (fun t x=>targetCoset G n q c hsk A w hA Γ (FullLattice G n q c hsk A w hA Γ) le_rfl t x)
        (modelRead D G n q c hsk A w hA Γ formula d.frozenObs) Fs q₀ b p i
        (QuotientGroup.mk (d.state n c hsk A w hA hw k)) =
      d.value k i.2.1.1
        (formula i.2.1.1 (blockProduct (scaleRun D 0 p b*i.1.val) (block D.index D.tail i.2.1.1))
          (jumpSlot D q₀ p b) i.2.2) 0 := by
    apply d.actual_reading n c hsk A w hA hw k _ _ _ hM hR hL hML (hH _) (ht _) (hst _) (hcop _)
      (hpstar _) K Q (V _) hK hQ (hV _) (hbase _) (hslot _ _) (hq _) (hsmall _)
    simpa using hK
  have ht' (p : Path D) (hp : p∈pivotOptions s r hs1 D Fs) (i : Comparison D Fs r) :
      intrinsicTerminal D G n q c hsk A w hA Γ coord formula d.frozenObs Fs q₀ b p i
        (QuotientGroup.mk (d.state n c hsk A w hA hw k)) =
      d.value k i.2.1.1
        (formula i.2.1.1 (blockProduct (scaleRun D 0 p b*i.1.val) (block D.index D.tail i.2.1.1))
          ((terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val).toAdd+jumpSlot D q₀ p b) i.2.2)
        (ownInput D q coord i.2.1.1 (terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val).toAdd) := by
    exact d.actual_reading n c hsk A w hA hw k _ _ _ hM hR hL hML (hH _) (ht _) (hst _) (hcop _)
      (hpstar _) K Q (V _) hK hQ (hV _) (hbase _) (hslot _ _) (hq _) (hsmall _) (hinput p hp i)
  simp only [intrinsicSuccess,Set.mem_iUnion,AlignmentMass.Success,Set.mem_ofPred_eq,
    LocalModels.modelSuccess]
  apply exists_congr
  intro p
  rw [exists_prop]
  apply and_congr_right
  intro hp
  apply forall_congr'
  intro i
  rw [hc p i,ht' p hp i]

end SourceIntegerArrays.GlobalJoint
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint
open SourceResidueAlignment ProductExposureLabels SourceMacroSelection
open RationalLattice MalcevCharacters RoughArrayFace RoughArrayCoordinates
open ConstructedWordPlan.GlobalWordPlan
open AllLevelFactorization AllLevelFactorization.Factorization MeasureTheory
open ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
open Filter
open scoped BigOperators Topology NNReal ENNReal BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
variable {a₀ : ℕ} (D : Pivot a₀) {ι : Fin D.targets→Type} [∀ t,Fintype (ι t)]
variable (G : ∀ t,ι t→Type) [∀ t i,Group (G t i)]
variable [∀ t i,TopologicalSpace (G t i)] [∀ t i,IsTopologicalGroup (G t i)]
variable (n : ∀ t,ι t→ℕ) (q : Fin D.targets→ℕ) (c : ∀ t i,RealCoordinates (G t i) (n t i))
variable (hsk : ∀ t i,SecondKind (c t i)) (A : ∀ t i,CubeFaces.Filtration (G t i))
variable (w : ∀ t i,Fin (n t i)→ℕ)
variable (hA : ∀ t i k (g : G t i),g∈(A t i).level k ↔ ∀ j,w t i j<k → (c t i).coord g j=0)
variable (hw : ∀ t i j,0<w t i j)
variable (Γ : ∀ t i,Subgroup (G t i)) (coord : ∀ e,Fin (q (D.owner e)))

 

structure RawModels (a : ℕ) where
  m : Fin D.targets→ℕ
  h : Fin D.targets→ℕ
  perm : ∀ t,Fin (m t+h t)≃Fin a
  M : ℕ
  J : ℕ
  R : ℕ
  L : ℤ
  H : Fin D.targets→ℕ
  slot : ∀ t,(Fin (h t)→ℕ)→Label (m t)→ι t→ℤ
  qval : ∀ t,(Fin (h t)→ℕ)→Label (m t)→Fin (q t)→ℤ
  g : ∀ t,(Fin (h t)→ℕ)→∀ i,ℤ→ℤ→G t i
  x : ∀ t,(Fin (h t)→ℕ)→∀ i,ℤ→ℤ→G t i
  obs : ∀ t,(Fin (h t)→ℕ)→∀ i,ℤ→ℤ→((G t i)⧸Γ t i) →ᵇ ℝ

namespace RawModels
variable {D G q Γ} {a : ℕ} (d : RawModels D G q Γ a)
def outer (z : (Fin a→ℕ)×ℕ) (t : Fin D.targets) (j : Fin (d.h t)) :=
  z.1 (d.perm t (j.natAdd (d.m t)))
def inner (z : (Fin a→ℕ)×ℕ) (t : Fin D.targets) : (Fin (d.m t)→ℕ)×ℕ :=
  (fun j=>z.1 (d.perm t (j.castAdd (d.h t))),z.2)
def exposure (z : (Fin a→ℕ)×ℕ) (t : Fin D.targets) :=
  expose d.L (d.M:ℤ) (d.R:ℝ) (d.inner z t)
def localModel (z : (Fin a→ℕ)×ℕ) : LocalModels D G q Γ :=
  ⟨d.m,d.M,d.R,d.L,d.H,d.inner z,fun _=>firstPivot d.M d.J z.2,
    fun t=>d.slot t (d.outer z t) (d.exposure z t),
    fun t=>d.qval t (d.outer z t) (d.exposure z t),
    fun t=>d.g t (d.outer z t),fun t=>d.x t (d.outer z t),fun t=>d.obs t (d.outer z t)⟩
def selectedG (t : Fin D.targets) (y : Fin (d.h t)→ℕ) (b : Label (d.m t)) (i : ι t) : G t i :=
  d.g t y i (modelBin (d.H t) d.R b) (rSlot d.M b (d.slot t y b i))
def selectedX (t : Fin D.targets) (y : Fin (d.h t)→ℕ) (b : Label (d.m t)) (i : ι t) : G t i :=
  d.x t y i (modelBin (d.H t) d.R b) (rSlot d.M b (d.slot t y b i))
def orbit (z : (Fin a→ℕ)×ℕ) (k : ℤ) : Full G n q c hsk A w hA :=
  rawLocalOrbit D G n q c hsk A w hA hw d.m d.h d.perm d.M d.J d.L (d.R:ℝ)
    d.selectedG d.selectedX d.slot d.qval z k
end RawModels

private lemma cellRatio_congr_on_cell (X W M J p : ℕ) (hW : 0<W) (hX : 4*W≤X)
    (hM : 0<M) (S T : Set ℕ) (hst : ∀ k,k<J → (k∈S ↔ k∈T)) :
    cellRatio X W M J p hW hX S=cellRatio X W M J p hW hX T := by
  have he : ((MicrocellFibers.point M (J*(p/(M*J))) (p%M) '' S)∩(sourceCell M J p:Set ℕ))=
      ((MicrocellFibers.point M (J*(p/(M*J))) (p%M) '' T)∩(sourceCell M J p:Set ℕ)) := by
    ext x
    constructor
    · rintro ⟨⟨k,hk,rfl⟩,hf⟩
      obtain ⟨l,hl⟩:=MicrocellFibers.represent M J (J*(p/(M*J))) (p%M) _ hM hf
      have he:=MicrocellFibers.point_injective M (J*(p/(M*J))) (p%M) hM hl
      have hlt : k<J:=he ▸ l.isLt
      exact ⟨⟨k,(hst k hlt).mp hk,rfl⟩,hf⟩
    · rintro ⟨⟨k,hk,rfl⟩,hf⟩
      obtain ⟨l,hl⟩:=MicrocellFibers.represent M J (J*(p/(M*J))) (p%M) _ hM hf
      have he:=MicrocellFibers.point_injective M (J*(p/(M*J))) (p%M) hM hl
      have hlt : k<J:=he ▸ l.isLt
      exact ⟨⟨k,(hst k hlt).mpr hk,rfl⟩,hf⟩
  unfold cellRatio
  rw [he]

private lemma firstPivot_inside (M J p k : ℕ) (hJ : 0<J) (hk : k<J) :
    |(((firstPivot M J p+(M:ℤ)*(k:ℤ)):ℤ):ℝ)-(p:ℝ)|≤(M:ℝ)*(J:ℝ) := by
  have hm : (0:ℝ)≤M:=Nat.cast_nonneg M
  have hk0 : (0:ℝ)≤k:=Nat.cast_nonneg k
  have hk1 : (k:ℝ)≤J:=by exact_mod_cast hk.le
  have hr0 : (0:ℝ)≤((p/M)%J:ℕ):=Nat.cast_nonneg _
  have hr1 : (((p/M)%J:ℕ):ℝ)≤J:=by exact_mod_cast (Nat.mod_lt (p/M) hJ).le
  simp only [firstPivot,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  rw [abs_le]
  constructor <;> nlinarith
 

omit [∀ t,Fintype (ι t)] in
theorem source_cell_model {a : ℕ} (d : RawModels D G q Γ a) (z : (Fin a→ℕ)×ℕ)
    (hM : 0<d.M) (hJ : 0<d.J) (hRJ : d.R=d.M*d.J)
    (hL : 0<d.L) (hML : (d.M:ℤ)∣d.L) (hH : ∀ t,0<d.H t)
    (ht : ∀ t j,0<(d.inner z t).1 j)
    (hst : ∀ t,Stable (2^(d.m t)+1) (d.H t) d.R (d.exposure z t))
    (hcop : ∀ t,IsCoprime (∏ j,(d.exposure z t).residue j) d.L)
    (K Q : ℝ) (V : Fin D.targets→ℝ) (hK : 0≤K) (hQ : 0≤Q)
    (hV : ∀ t,(∏ j,((d.inner z t).1 j:ℝ))≤V t)
    (hslot : ∀ t i,|(d.slot t (d.outer z t) (d.exposure z t) i:ℝ)|≤K*(d.L:ℝ))
    (hq : ∀ t e,|(d.qval t (d.outer z t) (d.exposure z t) e:ℝ)|≤Q)
    (hsmall : ∀ t,2*K*(Q+V t*(d.L:ℝ))≤d.R)
    (s r : ℕ) (hs1 : 1 ≤ s) (formula : ∀ t,ℚ→Slots D→Fin r→ι t)
    (Fs : Finset (Scale a₀)) (q₀ : ℕ) (b : Scale a₀) (τ : ℝ)
    (hinput : ∀ p∈pivotOptions s r hs1 D Fs,∀ i : Comparison D Fs r,
      ∑ e,|(ownInput D q coord i.2.1.1
        (terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val).toAdd e:ℝ)|≤K)
    (Xp W : ℕ) (hW : 0<W) (hXp : 4*W≤Xp) :
    cellRatio Xp W d.M d.J z.2 hW hXp
      {k | QuotientGroup.mk (d.orbit n c hsk A w hA hw z (k:ℤ))∈
        intrinsicSuccess D G n q c hsk A w hA Γ coord s r hs1 formula
          (d.localModel z).frozenObs Fs q₀ b τ} =
    cellRatio Xp W d.M d.J z.2 hW hXp
      {k | (d.localModel z).modelSuccess coord (k:ℤ) s r hs1 formula Fs q₀ b τ}

 := by
  apply cellRatio_congr_on_cell Xp W d.M d.J z.2 hW hXp hM
  intro k hk
  have hR : 0<d.R:=by rw [hRJ];exact Nat.mul_pos hM hJ
  have hbase : ∀ t,|(((d.localModel z).pstar t+((d.localModel z).M:ℤ)*(k:ℤ):ℤ):ℝ)-
      (((d.localModel z).z t).2:ℝ)|≤(d.localModel z).R := by
    intro t
    change |(((firstPivot d.M d.J z.2+(d.M:ℤ)*(k:ℤ):ℤ)):ℝ)-(z.2:ℝ)|≤(d.R:ℝ)
    rw [hRJ,Nat.cast_mul]
    exact firstPivot_inside d.M d.J z.2 k hJ hk
  have he:=source_model_event D G n q c hsk A w hA hw Γ coord (d.localModel z) (k:ℤ)
    hM hR hL hML hH ht hst hcop (fun _=>firstPivot_congruent d.M d.J z.2)
    K Q V hK hQ hV (by simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using hbase) hslot hq hsmall s r hs1 formula Fs q₀ b τ hinput
  exact he

end SourceIntegerArrays.GlobalJoint

end
end

end OAI
