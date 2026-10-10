import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel09
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open MeasureTheory Topology
end
 
end

noncomputable section
open Filter
open scoped Topology BigOperators
namespace SourcePhysicalDecay
open RoughSamplingWeights FinitePieceAverages
variable {Y : Type} [TopologicalSpace Y] {v : ℕ}
 

def AllBoxes (Z : ℕ→ℝ) (state : ℕ→(Fin v→ℤ)→Y) (S : C(Y,Y)) : Prop :=
  ∀ (d : ℕ),0<d → ∀ (c C : ℝ),0<c →0<C →
  ∀ (lo hi : ℕ→Fin v→ℝ) (res : ℕ→Fin v→ℤ),
  (∀ᶠ N in atTop,(∀ i,c*Z N≤hi N i-lo N i) ∧
    (∀ i,-C*Z N≤lo N i ∧ hi N i≤C*Z N)) →
  ∀ f : C(Y,ℂ),Tendsto (fun N=>mean (physicalResidueBox (lo N) (hi N) (res N) d)
    (fun b=>f (S (state N b)))-mean (physicalResidueBox (lo N) (hi N) (res N) d)
    (fun b=>f (state N b))) atTop (𝓝 0)

 

theorem allBoxes_subsequence (Z : ℕ→ℝ) (hZ : ∀ N,0≤Z N)
    (state : ℕ→(Fin v→ℤ)→Y) (S : C(Y,Y))
    (h : AllBoxes Z state S) (ψ : ℕ→ℕ) (hψ : StrictMono ψ) :
    AllBoxes (Z∘ψ) (state∘ψ) S
 := by
  classical
  intro d hd c C hc hC lo hi res hb f
  let lo' := Function.extend ψ lo (fun N (_ : Fin v)=>-(c+C)*Z N)
  let hi' := Function.extend ψ hi (fun N (_ : Fin v)=>(c+C)*Z N)
  let res' := Function.extend ψ res (fun _ (_ : Fin v)=>0)
  have hlo (k : ℕ) : lo' (ψ k)=lo k := hψ.injective.extend_apply _ _ _
  have hhi (k : ℕ) : hi' (ψ k)=hi k := hψ.injective.extend_apply _ _ _
  have hres (k : ℕ) : res' (ψ k)=res k := hψ.injective.extend_apply _ _ _
  have hb' : ∀ᶠ N in atTop,(∀ i,c*Z N≤hi' N i-lo' N i) ∧
      (∀ i,-(c+C)*Z N≤lo' N i ∧ hi' N i≤(c+C)*Z N) := by
    obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hb
    apply eventually_atTop.mpr
    refine ⟨ψ N₀,fun N hN=>?_⟩
    by_cases hn : ∃ k,ψ k=N
    · obtain ⟨k,rfl⟩:=hn
      have hk:=hN₀ k (hψ.le_iff_le.mp hN)
      rw [hlo,hhi]
      refine ⟨hk.1,fun i=>?_⟩
      have hz:=hZ (ψ k)
      have hcz:=mul_nonneg hc.le hz
      constructor <;> dsimp only [Function.comp_apply] at hk
      · nlinarith [(hk.2 i).1]
      · nlinarith [(hk.2 i).2]
    · have hl : lo' N=(fun _ : Fin v=>-(c+C)*Z N) := Function.extend_apply' _ _ _ hn
      have hr : hi' N=(fun _ : Fin v=>(c+C)*Z N) := Function.extend_apply' _ _ _ hn
      rw [hl,hr]
      refine ⟨fun _=>?_,fun _=>⟨le_rfl,le_rfl⟩⟩
      have hz:=hZ N
      have hc':=mul_nonneg hc.le hz
      have hC':=mul_nonneg hC.le hz
      nlinarith
  have hh:=(h d hd c (c+C) hc (add_pos hc hC) lo' hi' res' hb' f).comp hψ.tendsto_atTop
  simpa only [Function.comp_def,hlo,hhi,hres] using hh

end SourcePhysicalDecay
end

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace SourcePhysicalDecay
attribute [local instance] Classical.propDecidable
open RoughSamplingWeights FinitePieceAverages CubeLocalHaar
lemma physical_box_eq_rectangle {v : ℕ} (lo hi : Fin v→ℝ) (a : Fin v→ℤ) (d : ℕ)
    (ha : ∀ i,0≤a i ∧ a i<(d:ℤ)) :
    physicalResidueBox lo hi a d=physicalResidueRectangle lo hi a d := by
  classical
  ext b
  simp only [physicalResidueBox,Finset.mem_filter,mem_boxIndices _ _ _ _ zero_lt_one,
    physicalResidueRectangle_mem,zero_add,one_mul,Int.ModEq,Int.emod_eq_of_lt (ha _).1 (ha _).2]

lemma mean_eq_expect {α : Type*} (s : Finset α) (f : α→ℂ) : mean s f=𝔼 x∈s,f x := by
  rw [mean,Finset.expect_eq_sum_div_card,div_eq_mul_inv,mul_comm]

lemma mean_ofReal {α : Type*} (s : Finset α) (f : α→ℝ) :
    mean s (fun x=>(f x:ℂ))=((𝔼 x∈s,f x : ℝ):ℂ) := by
  rw [mean_eq_expect]
  exact (map_expect (Complex.ofRealCLM.toLinearMap.restrictScalars ℚ≥0) f s).symm
end SourcePhysicalDecay
end
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace SourcePhysicalDecay
open RationalLattice CubeFaces CubeTaylorExpansion CubeLocalHaar RoughSamplingWeights FinitePieceAverages
open AllLevelFactorization AllLevelFactorization.Factorization AllLevelFactorization.Factorization.ResidueCover
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ→ℤ→G} {L : ℕ→ℝ}
variable {F : Factorization c Γ s K P L} {r : Fin F.period} (C : F.ResidueCover r)
variable [MeasurableSpace (C.CubeSpace (ι:=ι))] [BorelSpace (C.CubeSpace (ι:=ι))]
variable [CompactSpace (G⧸Γ)] [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
variable [SecondCountableTopology (G⧸Γ)]
variable {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [CompactSpace Y] [HasOuterApproxClosed Y]
 

omit [CompactSpace (G⧸Γ)] [CompactSpace Y] in
theorem haar_invariant_of_allBoxes (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
    {v : ℕ} (e : Option ι≃Fin v) (π : C((Finset ι→G⧸Γ),Y)) (S : C(Y,Y))
    (h : AllBoxes L (fun N b=>π (fun w=>QuotientGroup.mk (P N (vertex (fun i=>b (e i)) w)))) S)
    (d : ℕ) (hd : 0<d) (a : Fin v→ℤ) (ha : ∀ i,0≤a i ∧ a i<(d:ℤ))
    (hdp : F.period∣d) (ha0 : a (e none)%(F.period:ℤ)=(r.val:ℤ))
    (hai : ∀ i,a (e (some i))%(F.period:ℤ)=0)
    (lo hi : ℝ→ℕ→Fin v→ℝ)
    (hb : ∀ α : ℝ,0<α →∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧ ∀ᶠ N in atTop,
      (∀ i,c₀*L (F.state.subseq N)≤hi α N i-lo α N i) ∧
      (∀ i,-C₀*L (F.state.subseq N)≤lo α N i ∧ hi α N i≤C₀*L (F.state.subseq N)))
    (β B : ℝ)
    (hgeo : ∀ α : ℝ,0<α →∀ᶠ N in atTop,
      ∀ b∈physicalResidueRectangle (lo α N) (hi α N) a d,∀ w : Finset ι,
        dist ((vertex (fun i=>b (e i)) w:ℝ)/L (F.state.subseq N)) β≤B*α) :
    Measure.map S (C.marginalCubeHaar β π : Measure Y)=(C.marginalCubeHaar β π : Measure Y)
 := by
  apply C.marginal_haar_invariant hL ht e d hd a ha hdp ha0 hai lo hi hb β B hgeo π S
  intro α hα f
  obtain ⟨c₀,C₀,hc₀,hC₀,hbα⟩ := hb α hα
  let ff : C(Y,ℂ):=⟨fun y=>(f y:ℂ),Complex.continuous_ofReal.comp f.continuous⟩
  have hh:=(allBoxes_subsequence L (fun N=>(hL N).le) _ S h F.state.subseq F.state.strictmono)
    d hd c₀ C₀ hc₀ hC₀ (lo α) (hi α) (fun _=>a) hbα ff
  have he (N : ℕ) :
      (mean (physicalResidueBox (lo α N) (hi α N) a d)
        (fun b=>ff (S (π (fun w=>QuotientGroup.mk
          (P (F.state.subseq N) (vertex (fun i=>b (e i)) w))))))-
      mean (physicalResidueBox (lo α N) (hi α N) a d)
        (fun b=>ff (π (fun w=>QuotientGroup.mk
          (P (F.state.subseq N) (vertex (fun i=>b (e i)) w))))))=
      ((marginalBoxAverage (F:=F) e d a lo hi π α N (f.comp S)-
        marginalBoxAverage (F:=F) e d a lo hi π α N f:ℝ):ℂ) := by
    rw [physical_box_eq_rectangle _ _ _ _ ha]
    dsimp only [ff,ContinuousMap.coe_mk]
    rw [mean_ofReal,mean_ofReal,←Complex.ofReal_sub]
    rfl
  have hn:=hh.norm
  simpa only [Function.comp_apply,he,norm_zero,Complex.norm_real,Real.norm_eq_abs] using hn

end SourcePhysicalDecay
end

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace SourcePhysicalDecay
open RationalLattice AllLevelFactorization AllLevelFactorization.Factorization
open CubeFaces CubeLocalHaar PhysicalCubeMaps SourceIntegerArrays
attribute [local instance] Classical.propDecidable
variable {Y : Type} [TopologicalSpace Y]
 

def AllCompatibleHaar (L : ℕ→ℝ) (state : ℕ→ℤ→Y) (v : ℕ) (j : Fin v) (S : C(Y,Y)) : Prop :=
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
  ∀ (d : ℕ),0<d → ∀ (a : Fin (v+1)→ℤ),
  (∀ i,0≤a i ∧ a i<(d:ℤ)) → F.period∣d → a 0%(F.period:ℤ)=(r.val:ℤ) →
  (∀ i : Fin v,a i.succ%(F.period:ℤ)=0) →
  ∀ (lo hi : ℝ→ℕ→Fin (v+1)→ℝ),
  (∀ α : ℝ,0<α →∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧ ∀ᶠ N in atTop,
    (∀ i,c₀*L (F.state.subseq N)≤hi α N i-lo α N i) ∧
    (∀ i,-C₀*L (F.state.subseq N)≤lo α N i ∧ hi α N i≤C₀*L (F.state.subseq N))) →
  ∀ (β B : ℝ),
  (∀ α : ℝ,0<α →∀ᶠ N in atTop,
    ∀ b∈physicalResidueRectangle (lo α N) (hi α N) a d,∀ w : Finset (Fin v),
      dist ((cubeVertex v b w:ℝ)/L (F.state.subseq N)) β≤B*α) →
  Measure.map (upperFace j S) (C.marginalCubeHaar (ι:=Fin v) β (vertices (ι:=Fin v) p) : Measure (Finset (Fin v)→Y))=
    (C.marginalCubeHaar (ι:=Fin v) β (vertices (ι:=Fin v) p) : Measure (Finset (Fin v)→Y))

 

theorem compatible_haar_of_allBoxes [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    (L : ℕ→ℝ) (hL : ∀ N,0<L N) (hLt : Tendsto L atTop atTop)
    (state : ℕ→ℤ→Y) (v : ℕ) (j : Fin v) (S : C(Y,Y))
    (h : AllBoxes L (fun N b w=>state N (cubeVertex v b w)) (upperFace j S)) :
    AllCompatibleHaar L state v j S
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
  intro d hd a ha hdp ha0 hai lo hi hb β B hgeo
  let e : Option (Fin v)≃Fin (v+1):=(finSuccEquiv v).symm
  have he (b : Fin (v+1)→ℤ) (w : Finset (Fin v)) :
      vertex (fun i=>b (e i)) w=cubeVertex v b w := by simp [vertex,cubeVertex,e]
  have hh : AllBoxes L (fun N b=>vertices p
      (fun w=>QuotientGroup.mk (P N (vertex (fun i=>b (e i)) w)))) (upperFace j S) := by
    have heq : (fun N b=>vertices p (fun w=>QuotientGroup.mk
        (P N (vertex (fun i=>b (e i)) w))))=(fun N b w=>state N (cubeVertex v b w)) := by
      funext N b w
      simp only [vertices_apply,he,hp]
    rw [heq]
    exact h
  apply haar_invariant_of_allBoxes C hL hLt e (vertices p) (upperFace j S) hh d hd a ha hdp
    (by simpa [e] using ha0) (by simpa [e] using hai) lo hi hb β B
  simpa only [he] using hgeo

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
 

theorem source_global_literal_haar
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
      ∀ (e : Fin (q t)) (j : Fin (v t)) (pstar : ℕ→ℤ),
      (∀ k,(M (φ k):ℤ)∣pstar k-((z k).2:ℤ)) →
      (∀ k,|(pstar k:ℝ)-((z k).2:ℝ)|≤R (φ k)) →
      let state := fun k b=>QuotientGroup.mk
        (literalState (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t)
          (M (φ k)) (L (φ k)) (label k) (fun l=>((zin k).1 l:ℤ)) (pstar k)
          (fun _ (_ : Fin 1)=>1)
          (g t (φ k) (zout k) (label k)) (x t (φ k) (zout k) (label k))
          (slot t (φ k) (zout k) (label k)) (qval t (φ k) (zout k) (label k)) (fun _=>b))
      SourcePhysicalDecay.AllCompatibleHaar Z state (v t) j
        (faceAction (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
          (fun _ (_ : Fin 1)=>1) e 0)
 := by
  classical
  obtain ⟨φ,hφ,z,hz,hgood⟩:=source_global_literal_cube_faces G n q c hsk A w hA hw Γ hΓ
    a m h v perm w0 M Xp X R Q L hw0 hX hXp hXt hXpt hR hRX hZ hQ0 hSize hWM hM hMs
    hL hsm hWL hML hLexact hXL g x slot qval hQ E ε hε hE
  refine ⟨φ,hφ,z,hz,?_⟩
  intro t
  dsimp only
  intro e j pstar hpstar hpclose
  let Y := (Carrier (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t))⧸
    lattice (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (Γ t)
  have htop:=joint_array_topology (G t) (n t) (q t) (c t) (hsk t) (A t) (w t) (hA t) (hw t) (Γ t) (hΓ t)
  let : CompactSpace Y:=htop.2.2.1
  let : TopologicalSpace.MetrizableSpace Y:=htop.2.2.2
  have hZpos (N : ℕ) : 0<R N/(M N:ℝ):=div_pos (hR N) (by exact_mod_cast hM N)
  have hZT : Tendsto (fun N=>R N/(M N:ℝ)) atTop atTop := by
    have ht : Tendsto (fun N=>(R N/(M N:ℝ))/
        (1+∑ j : Fin (m t),(X N (perm t (j.castAdd (h t))):ℝ)^2)) atTop atTop := by
      simpa only [Real.rpow_one] using hZ t 1 zero_lt_one
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [ht.eventually (eventually_ge_atTop B)] with N hN
    apply hN.trans
    apply div_le_self (hZpos N).le
    have hn : 0≤∑ j : Fin (m t),(X N (perm t (j.castAdd (h t))):ℝ)^2:=
      Finset.sum_nonneg (fun _ _=>sq_nonneg _)
    linarith
  apply SourcePhysicalDecay.compatible_haar_of_allBoxes _ (fun k=>hZpos (φ k))
    (hZT.comp hφ.tendsto_atTop)
  intro d hd c₀ C₀ hc₀ hC₀ lo hi res hbox F
  exact hgood t e j d hd pstar hpstar hpclose c₀ C₀ hc₀ hC₀ lo hi res hbox F

end SourceIntegerArrays

end

end OAI
