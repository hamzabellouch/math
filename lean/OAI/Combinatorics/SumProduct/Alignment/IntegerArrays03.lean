import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PhysicalDecay01
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice22
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
noncomputable section
open scoped BigOperators
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
abbrev FlatG (a : Sigma ι) := G a.1 a.2
abbrev FlatN (a : Sigma ι) := n a.1 a.2
abbrev FlatQ (a : Sigma ι) := q a.1
abbrev FlatM (a : Sigma ι) := m a.1
section
variable {G n}
abbrev FlatC (a : Sigma ι) := c a.1 a.2
end
section
variable {G n c}
abbrev FlatSk (a : Sigma ι) := hsk a.1 a.2
end
section
variable {G}
abbrev FlatA (a : Sigma ι) := A a.1 a.2
abbrev FlatΓ (a : Sigma ι) := Γ a.1 a.2
end
section
variable {n}
abbrev FlatW (a : Sigma ι) := w a.1 a.2
end
section
variable {G n c A w}
abbrev FlatHA (a : Sigma ι) := hA a.1 a.2
end
section
variable {n w}
abbrev FlatHw (a : Sigma ι) := hw a.1 a.2
end
abbrev Full := JointArrays.Carrier (FlatG G) (FlatN n) (FlatQ q) (FlatC c)
  (FlatSk hsk) (FlatA A) (FlatW w) (FlatHA hA)
abbrev FullDim := Fintype.card (FiniteProducts.Index (JointArrays.dimension (FlatN n) (FlatQ q) (FlatW w)))
abbrev FullLattice := JointArrays.lattice (FlatG G) (FlatN n) (FlatQ q) (FlatC c)
  (FlatSk hsk) (FlatA A) (FlatW w) (FlatHA hA) (FlatΓ Γ)
abbrev FullFiltration := JointArrays.filtration (FlatG G) (FlatN n) (FlatQ q) (FlatC c)
  (FlatSk hsk) (FlatA A) (FlatW w) (FlatHA hA)

 
def targetHom (t : τ) : Full G n q c hsk A w hA →* Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) where
  toFun f i := f ⟨t,i⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Fintype τ] [∀ t,Fintype (ι t)] in
lemma targetHom_continuous (t : τ) : Continuous (targetHom G n q c hsk A w hA t) :=
  by
    change Continuous (fun f : Full G n q c hsk A w hA=>fun i=>f ⟨t,i⟩)
    exact continuous_pi (fun i=>continuous_apply (Sigma.mk t i))

omit [Fintype τ] [∀ t,Fintype (ι t)] in
lemma targetHom_lattice (t : τ) (f : Full G n q c hsk A w hA)
    (hf : f∈FullLattice G n q c hsk A w hA Γ) :
    targetHom G n q c hsk A w hA t f∈lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t) :=
  fun i=>hf ⟨t,i⟩

 

def targetCoset (Λ : Subgroup (Full G n q c hsk A w hA))
    (hle : Λ≤FullLattice G n q c hsk A w hA Γ) (t : τ) :
    C((Full G n q c hsk A w hA)⧸Λ,
      (Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
        lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)) :=
  NonnormalCoset.map Λ _ (targetHom G n q c hsk A w hA t)
    (targetHom_continuous G n q c hsk A w hA t)
    (fun f hf=>targetHom_lattice G n q c hsk A w hA Γ t f (hle hf))

def rawJoint (M : ℕ) (L : ℤ) (b : ∀ t,Label (m t)) (tail : ∀ t,Fin (m t)→ℤ)
    (pstar : τ→ℤ) (slot : ∀ t,ι t→ℤ) (qval : ∀ t,Fin (q t)→ℤ)
    (g x : ∀ t i,G t i) (u : ℤ) : Full G n q c hsk A w hA :=
  literalJoint (FlatG G) (FlatN n) (FlatQ q) (FlatM m) (FlatC c) (FlatSk hsk) (FlatA A) (FlatW w) (FlatHA hA) (FlatHw hw)
    M L (fun a=>b a.1) (fun a=>tail a.1) (fun a=>pstar a.1) (fun a=>slot a.1 a.2)
    (fun a=>qval a.1) (fun a=>g a.1 a.2) (fun a=>x a.1 a.2) u

omit [Fintype τ] [∀ t,Fintype (ι t)] in
lemma target_rawJoint (M : ℕ) (L : ℤ) (b : ∀ t,Label (m t)) (tail : ∀ t,Fin (m t)→ℤ)
    (pstar : τ→ℤ) (slot : ∀ t,ι t→ℤ) (qval : ∀ t,Fin (q t)→ℤ)
    (g x : ∀ t i,G t i) (u : ℤ) (t : τ) :
    targetHom G n q c hsk A w hA t (rawJoint G n q m c hsk A w hA hw M L b tail pstar slot qval g x u)=
    literalState (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t)
      M L (b t) (tail t) (pstar t) (fun _ (_ : Fin 1)=>1) (g t) (x t) (slot t) (qval t) (fun _=>u) := rfl

 

def FactorizedHaar (s : ℕ) (v : τ→ℕ) (P : ℕ→ℤ→Full G n q c hsk A w hA) (Z : ℕ→ℝ) : Prop :=
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
    ∀ t (r : Fin F.period) (C : F.ResidueCover r),
    letI : MeasurableSpace (C.CubeSpace (ι:=Fin (v t))):=borel _
    letI : BorelSpace (C.CubeSpace (ι:=Fin (v t))):=⟨rfl⟩
    let Y := (Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
        lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
    letI : MeasurableSpace (Finset (Fin (v t))→Y):=borel _
    letI : BorelSpace (Finset (Fin (v t))→Y):=⟨rfl⟩
    ∀ (e : Fin (q t)) (j : Fin (v t)) (β : ℝ),
      Measure.map (upperFace j (faceAction (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
        (fun _ (_ : Fin 1)=>1) e 0))
        (C.marginalCubeHaar (ι:=Fin (v t)) β (vertices (targetCoset G n q c hsk A w hA Γ B.small B.le t)) : Measure (Finset (Fin (v t))→Y))=
        (C.marginalCubeHaar (ι:=Fin (v t)) β (vertices (targetCoset G n q c hsk A w hA Γ B.small B.le t)) : Measure (Finset (Fin (v t))→Y))
end SourceIntegerArrays.GlobalJoint
end

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace SourcePhysicalDecay
open RationalLattice AllLevelFactorization AllLevelFactorization.Factorization
open CubeFaces CubeLocalHaar PhysicalCubeMaps SourceIntegerArrays
attribute [local instance] Classical.propDecidable
variable {Y : Type} [TopologicalSpace Y]
def AllCenteredHaar (L : ℕ→ℝ) (state : ℕ→ℤ→Y) (v : ℕ) (j : Fin v) (S : C(Y,Y)) : Prop :=
  letI : MeasurableSpace (Finset (Fin v)→Y):=borel _
  letI : BorelSpace (Finset (Fin v)→Y):=⟨rfl⟩
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H],
  ∀ (n s : ℕ) (c : RealCoordinates H n) (Λ : Subgroup H)
    [CompactSpace (H⧸Λ)] [SecondCountableTopology (H⧸Λ)],
  letI : MeasurableSpace (H⧸Λ):=borel _
  letI : BorelSpace (H⧸Λ):=⟨rfl⟩
  ∀ (K : Filtration H) (P : ℕ→ℤ→H) (F : Factorization c Λ s K P L)
    (p : C(H⧸Λ,Y)), (∀ N b,p (QuotientGroup.mk (P N b))=state N b) →
  ∀ (r : Fin F.period) (C : F.ResidueCover r),
  letI : MeasurableSpace (C.CubeSpace (ι:=Fin v)):=borel _
  letI : BorelSpace (C.CubeSpace (ι:=Fin v)):=⟨rfl⟩
  ∀ β : ℝ,
  Measure.map (upperFace j S) (C.marginalCubeHaar (ι:=Fin v) β (vertices (ι:=Fin v) p) : Measure (Finset (Fin v)→Y))=
    (C.marginalCubeHaar (ι:=Fin v) β (vertices (ι:=Fin v) p) : Measure (Finset (Fin v)→Y))

 

theorem compatible_haar_allCenters (L : ℕ→ℝ) (hL : ∀ N,0<L N)
    (state : ℕ→ℤ→Y) (v : ℕ) (j : Fin v) (S : C(Y,Y))
    (h : AllCompatibleHaar L state v j S) : AllCenteredHaar L state v j S
 := by
  classical
  intro H _ _ _ n s c Λ _ _
  let : MeasurableSpace (H⧸Λ):=borel _
  let : BorelSpace (H⧸Λ):=⟨rfl⟩
  intro K P F p hp r C
  let : MeasurableSpace (Finset (Fin v)→Y):=borel _
  let : BorelSpace (Finset (Fin v)→Y):=⟨rfl⟩
  let : MeasurableSpace (C.CubeSpace (ι:=Fin v)):=borel _
  let : BorelSpace (C.CubeSpace (ι:=Fin v)):=⟨rfl⟩
  intro β
  let a : Fin (v+1)→ℤ:=Fin.cases (r.val:ℤ) (fun _=>0)
  have ha : ∀ i,0≤a i ∧ a i<(F.period:ℤ) := by
    intro i
    refine Fin.cases ?_ (fun _=>?_) i
    · change 0≤(r.val:ℤ) ∧ (r.val:ℤ)<(F.period:ℤ)
      exact ⟨Int.natCast_nonneg _,by exact_mod_cast r.isLt⟩
    · change (0:ℤ)≤0 ∧ (0:ℤ)<(F.period:ℤ)
      exact ⟨le_rfl,by exact_mod_cast F.period_pos⟩
  let lo : ℝ→ℕ→Fin (v+1)→ℝ:=fun α N i=>(if i=0 then β-α else -α)*L (F.state.subseq N)
  let hi : ℝ→ℕ→Fin (v+1)→ℝ:=fun α N i=>(if i=0 then β+α else α)*L (F.state.subseq N)
  have hb : ∀ α : ℝ,0<α →∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧ ∀ᶠ N in atTop,
      (∀ i,c₀*L (F.state.subseq N)≤hi α N i-lo α N i) ∧
      (∀ i,-C₀*L (F.state.subseq N)≤lo α N i ∧ hi α N i≤C₀*L (F.state.subseq N)) := by
    intro α hα
    refine ⟨α,|β|+α+1,hα,by positivity,Filter.Eventually.of_forall ?_⟩
    intro N
    have hz:=(hL (F.state.subseq N)).le
    have hαz:=mul_nonneg hα.le hz
    constructor
    · intro i
      dsimp only [lo,hi]
      split_ifs <;> nlinarith
    · intro i
      dsimp only [lo,hi]
      have hβ₁:=mul_le_mul_of_nonneg_right (le_abs_self β) hz
      have hβ₂:=mul_le_mul_of_nonneg_right (neg_abs_le β) hz
      have hβ₀:=mul_nonneg (abs_nonneg β) hz
      split_ifs <;> constructor <;> nlinarith
  have hgeo : ∀ α : ℝ,0<α →∀ᶠ N in atTop,
      ∀ b∈physicalResidueRectangle (lo α N) (hi α N) a F.period,∀ u : Finset (Fin v),
        dist ((cubeVertex v b u:ℝ)/L (F.state.subseq N)) β≤(v+1:ℝ)*α := by
    intro α hα
    apply Filter.Eventually.of_forall
    intro N b hb u
    have hbd:=(physicalResidueRectangle_mem _ _ _ _ _).mp hb |>.1
    have hz:=hL (F.state.subseq N)
    have hbase : |(b 0:ℝ)/L (F.state.subseq N)-β|≤α := by
      have hl:= (hbd 0).1
      have hh:= (hbd 0).2.le
      simp [lo,hi] at hl hh
      rw [abs_le]
      constructor
      · have hh':= (le_div_iff₀ hz).mpr hl
        linarith
      · have hh':= (div_le_iff₀ hz).mpr hh
        linarith
    have hinc (i : Fin v) : |(b i.succ:ℝ)/L (F.state.subseq N)|≤α := by
      have hl:=(hbd i.succ).1
      have hh:=(hbd i.succ).2.le
      simp only [lo,hi,Fin.succ_ne_zero,ite_false] at hl hh
      exact abs_le.mpr ⟨(le_div_iff₀ hz).mpr hl,(div_le_iff₀ hz).mpr hh⟩
    have hsum : |∑ i∈u,(b i.succ:ℝ)/L (F.state.subseq N)|≤(v:ℝ)*α := by
      calc
        _ ≤ ∑ i∈u,|(b i.succ:ℝ)/L (F.state.subseq N)|:=Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i∈u,α:=Finset.sum_le_sum (fun i _=>hinc i)
        _ = (u.card:ℝ)*α:=by simp
        _ ≤ (v:ℝ)*α:=mul_le_mul_of_nonneg_right (by exact_mod_cast (show u.card≤v by simpa using Finset.card_le_univ u)) hα.le
    rw [Real.dist_eq]
    have he : (cubeVertex v b u:ℝ)/L (F.state.subseq N)-β=
        ((b 0:ℝ)/L (F.state.subseq N)-β)+∑ i∈u,(b i.succ:ℝ)/L (F.state.subseq N) := by
      simp only [cubeVertex,Int.cast_add,Int.cast_sum,add_div,Finset.sum_div]
      ring
    rw [he]
    calc
      _ ≤ |(b 0:ℝ)/L (F.state.subseq N)-β|+|∑ i∈u,(b i.succ:ℝ)/L (F.state.subseq N)|:=abs_add_le _ _
      _ ≤ α+(v:ℝ)*α:=add_le_add hbase hsum
      _ = (v+1:ℝ)*α:=by ring
  apply h H n s c Λ K P F p hp r C F.period F.period_pos a ha (dvd_refl _) ?_ ?_ lo hi hb β (v+1) hgeo
  · simp only [a,Fin.cases_zero]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast r.isLt)
  · intro i
    simp [a]

end SourcePhysicalDecay
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
 

theorem source_global_all_order_haar
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
    (E : ℕ→Set ((Fin a→ℕ)×ℕ)) (ε : ℝ≥0∞) (hε : 0<ε)
    (hE : ∀ N,ε≤(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)) (E N)) :
    ∃ φ : ℕ→ℕ,StrictMono φ ∧ ∃ z : ℕ→(Fin a→ℕ)×ℕ,
      (∀ k,z k∈E (φ k) ∧ z k∈fullDomain (X (φ k)) (Xp (φ k)) (primorial (w0 (φ k)))) ∧
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
  obtain ⟨φ,hφ,z,hz,hgood⟩:=source_global_literal_haar
    (τ:=τ×Fin (s+1)) (ι:=fun t=>ι t.1)
    (fun t=>G t.1) (fun t=>n t.1) (fun t=>q t.1) (fun t=>c t.1)
    (fun t=>hsk t.1) (fun t=>A t.1) (fun t=>w t.1) (fun t=>hA t.1) (fun t=>hw t.1) (fun t=>Γ t.1)
    (fun t=>hΓ t.1) a (fun t=>m t.1) (fun t=>h t.1) (fun t=>t.2.val+1)
    (fun t=>perm t.1) w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX
    (fun t=>hZ t.1) hQ0 (fun t=>hSize t.1) hWM hM hMs hL hsm hWL hML hLexact
    (fun t=>hXL t.1) (fun t=>g t.1) (fun t=>x t.1) (fun t=>slot t.1) (fun t=>qval t.1)
    (fun t=>hQ t.1) E ε hε hE
  refine ⟨φ,hφ,z,hz,?_⟩
  intro t k
  dsimp only
  intro e j pstar hpstar hpclose
  apply SourcePhysicalDecay.compatible_haar_allCenters _ (fun N=>div_pos (hR _) (by exact_mod_cast hM _))
  exact hgood (t,k) e j pstar hpstar hpclose

end SourceIntegerArrays

end

end OAI
