import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel08
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open scoped BigOperators Topology NNReal
open Filter MeasureTheory
end
 
end

section
 

 

noncomputable section
open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
namespace TwoScaleInvariance
variable {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [HasOuterApproxClosed Y]
variable (ν : ProbabilityMeasure Y) (S : C(Y,Y))
variable (A : ℝ → ℕ → C(Y,ℝ) → ℝ)
variable (hloc : ∀ f : C(Y,ℝ),∀ δ : ℝ,0<δ →
  ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
    |A α N f-∫ y,f y ∂(ν : Measure Y)|<δ)
variable (hinv : ∀ α : ℝ,0<α → ∀ f : C(Y,ℝ),
  Tendsto (fun N=>|A α N (f.comp S)-A α N f|) atTop (𝓝 0))

include hloc hinv in
omit [BorelSpace Y] [HasOuterApproxClosed Y] in
lemma integral_eq (f : C(Y,ℝ)) :
    (∫ y,f (S y) ∂(ν : Measure Y))=∫ y,f y ∂(ν : Measure Y) := by
  let u : ℝ:=∫ y,f (S y) ∂(ν : Measure Y)
  let v : ℝ:=∫ y,f y ∂(ν : Measure Y)
  change u=v
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hδ3 : 0<δ/3 := by positivity
  have he : ∀ᶠ α : ℝ in 𝓝[>] 0,0<α ∧
      (∀ᶠ N : ℕ in atTop,|A α N f-v|<δ/3) ∧
      (∀ᶠ N : ℕ in atTop,|A α N (f.comp S)-u|<δ/3) := by
    filter_upwards [self_mem_nhdsWithin,hloc f (δ/3) hδ3,
      hloc (f.comp S) (δ/3) hδ3] with α hα h1 h2
    exact ⟨hα,h1,h2⟩
  obtain ⟨α,hα,h1,h2⟩:=he.exists
  have hi:= (hinv α hα f).eventually (gt_mem_nhds hδ3)
  obtain ⟨N,h1,h2,hi⟩:=(h1.and (h2.and hi)).exists
  have htri:=abs_sub_le u (A α N (f.comp S)) v
  have htri2:=abs_sub_le (A α N (f.comp S)) (A α N f) v
  have hs : |u-A α N (f.comp S)|<δ/3 := by
    simpa only [abs_sub_comm u (A α N (f.comp S))] using h2
  linarith

include hloc hinv in
 

theorem map_eq : Measure.map S (ν : Measure Y)=(ν : Measure Y) := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map S.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact integral_eq ν S A hloc hinv f.toContinuousMap

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [T2Space Y]
variable (μ : ProbabilityMeasure X) [(μ : Measure X).IsOpenPosMeasure]
variable (q : C(X,Y))

 

omit [HasOuterApproxClosed Y] in
theorem range_preservation
    (hinv : Measure.map S (Measure.map q (μ : Measure X))=Measure.map q (μ : Measure X)) :
    ∀ x : X,∃ y : X,S (q x)=q y := by
  intro x
  have hc : IsClosed (Set.range q) := (isCompact_range q.continuous).isClosed
  let U : Set Y:=(Set.range q)ᶜ
  have hU : IsOpen U:=hc.isOpen_compl
  have hz : (Measure.map q (μ : Measure X)) U=0 := by
    rw [Measure.map_apply q.continuous.measurable hU.measurableSet]
    have he : q ⁻¹' U=∅ := by ext z; simp [U]
    rw [he,measure_empty]
  have hz' : (μ : Measure X) ((S.comp q) ⁻¹' U)=0 := by
    have he:=congrArg (fun m : Measure Y=>m U) hinv
    rw [Measure.map_apply S.continuous.measurable hU.measurableSet,
      Measure.map_apply q.continuous.measurable
        (S.continuous.measurable hU.measurableSet),hz] at he
    exact he
  by_contra! hn
  have hm : (S.comp q) ⁻¹' U ≠∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    refine ⟨x,?_⟩
    change S (q x)∉Set.range q
    simpa only [Set.mem_range,not_exists,eq_comm] using hn
  exact ((hU.preimage (S.comp q).continuous).measure_ne_zero (μ : Measure X)
    (Set.nonempty_iff_ne_empty.mpr hm)) hz'

end TwoScaleInvariance
end
 
end

section
 

 

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators NNReal
namespace AllLevelFactorization.Factorization.ResidueCover
open RationalLattice CubeFaces CubeTaylorExpansion ComparableBoxLeibman CubeLocalHaar
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable {F : Factorization c Γ s K P L} {r : Fin F.period} (C : F.ResidueCover r)
variable [MeasurableSpace (C.CubeSpace (ι:=ι))] [BorelSpace (C.CubeSpace (ι:=ι))]
variable [CompactSpace (G⧸Γ)] [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
variable [SecondCountableTopology (G⧸Γ)]
variable (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
variable {v : ℕ} (e : Option ι≃Fin v) (d : ℕ) (hd : 0<d) (a : Fin v → ℤ)
variable (ha : ∀ i,0≤a i ∧ a i<(d:ℤ))
variable (hdp : F.period∣d) (ha0 : a (e none)%(F.period:ℤ)=(r.val:ℤ))
variable (hai : ∀ i,a (e (some i))%(F.period:ℤ)=0)
variable (lo hi : ℝ → ℕ → Fin v → ℝ)
variable (hb : ∀ α : ℝ,0<α → ∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧ ∀ᶠ N in atTop,
  (∀ i,c₀*L (F.state.subseq N)≤hi α N i-lo α N i) ∧
  (∀ i,-C₀*L (F.state.subseq N)≤lo α N i ∧ hi α N i≤C₀*L (F.state.subseq N)))
variable (β B : ℝ)
variable (hgeo : ∀ α : ℝ,0<α → ∀ᶠ N in atTop,
  ∀ b∈physicalResidueRectangle (lo α N) (hi α N) a d,∀ w : Finset ι,
    dist ((vertex (fun i=>b (e i)) w:ℝ)/L (F.state.subseq N)) β≤B*α)
variable {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [CompactSpace Y] [HasOuterApproxClosed Y]
variable (π : C((Finset ι → G⧸Γ),Y))

def marginalBoxAverage (α : ℝ) (N : ℕ) (f : C(Y,ℝ)) : ℝ :=
  𝔼 b∈physicalResidueRectangle (lo α N) (hi α N) a d,
    f (π (fun w=>QuotientGroup.mk (P (F.state.subseq N) (vertex (fun i=>b (e i)) w))))

def marginalCubeHaar : ProbabilityMeasure Y :=
  (C.cubeHaar (ι:=ι) β).map π

include hL ht hd ha hdp ha0 hai hb hgeo in
omit [CompactSpace (G⧸Γ)] [CompactSpace Y] [HasOuterApproxClosed Y] in
lemma marginal_local_law (f : C(Y,ℝ)) :
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N in atTop,
      |marginalBoxAverage (F:=F) e d a lo hi π α N f-
        ∫ y,f y ∂(marginalCubeHaar C β π : Measure Y)|<ε := by
  let ff : C((Finset ι → G⧸Γ),ℂ):=
    ⟨fun x=>(f (π x):ℂ),Complex.continuous_ofReal.comp (f.continuous.comp π.continuous)⟩
  have hbb : ∀ α : ℝ,0<α → ∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧ ∀ᶠ N in atTop,
      ∀ _ : Unit,(∀ i,c₀*L (F.state.subseq N)≤hi α N i-lo α N i) ∧
        (∀ i,-C₀*L (F.state.subseq N)≤lo α N i ∧ hi α N i≤C₀*L (F.state.subseq N)) := by
    intro α hα
    obtain ⟨c₀,C₀,hc,hC,hb⟩:=hb α hα
    exact ⟨c₀,C₀,hc,hC,hb.mono (fun _ h _=>h)⟩
  have hgg : ∀ α : ℝ,0<α → ∀ᶠ N in atTop,∀ _ : Unit,
      ∀ b∈physicalResidueRectangle (lo α N) (hi α N) a d,∀ w : Finset ι,
        dist ((vertex (fun i=>b (e i)) w:ℝ)/L (F.state.subseq N)) β≤B*α :=
    fun α hα=>(hgeo α hα).mono (fun _ h _=>h)
  have H:=C.local_physical_uniform hL ht e d hd a ha hdp ha0 hai
    (fun _ _=>Unit) (fun α N _=>lo α N) (fun α N _=>hi α N) hbb β B hgg ff
  intro ε hε
  filter_upwards [H ε hε] with α hα
  filter_upwards [hα] with N hN
  have hh:=hN ()
  rw [←C.integral_cubeHaar β ff] at hh
  have hexp : (𝔼 b∈physicalResidueRectangle (lo α N) (hi α N) a d,
      ff (fun w=>QuotientGroup.mk (P (F.state.subseq N) (vertex (fun i=>b (e i)) w))))=
      (marginalBoxAverage (F:=F) e d a lo hi π α N f:ℂ) := by
    exact (map_expect (Complex.ofRealCLM.toLinearMap.restrictScalars ℚ≥0) _ _).symm
  rw [hexp] at hh
  have hint : (∫ x,ff x ∂(C.cubeHaar (ι:=ι) β : Measure _))=
      ((∫ y,f y ∂(marginalCubeHaar C β π : Measure Y) : ℝ):ℂ) := by
    change (∫ x,(f (π x):ℂ) ∂(C.cubeHaar (ι:=ι) β : Measure _))=_
    rw [integral_complex_ofReal]
    congr 1
    exact (integral_map π.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable).symm
  rw [hint,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hh
  exact hh

include hL ht hd ha hdp ha0 hai hb hgeo in
 

omit [CompactSpace (G⧸Γ)] [CompactSpace Y] in
theorem marginal_haar_invariant (S : C(Y,Y))
    (hinv : ∀ α : ℝ,0<α → ∀ f : C(Y,ℝ),Tendsto
      (fun N=>|marginalBoxAverage (F:=F) e d a lo hi π α N (f.comp S)-
        marginalBoxAverage (F:=F) e d a lo hi π α N f|) atTop (𝓝 0)) :
    Measure.map S (marginalCubeHaar C β π : Measure Y)=
      (marginalCubeHaar C β π : Measure Y) :=
  TwoScaleInvariance.map_eq (marginalCubeHaar C β π) S
    (marginalBoxAverage (F:=F) e d a lo hi π)
    (C.marginal_local_law hL ht e d hd a ha hdp ha0 hai lo hi hb β B hgeo π) hinv

end AllLevelFactorization.Factorization.ResidueCover
end
 
end

section
 

 

noncomputable section
open MeasureTheory Topology
namespace AllLevelFactorization.Factorization.ResidueCover
open RationalLattice CubeFaces
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable {F : Factorization c Γ s K P L} {r : Fin F.period} (C : F.ResidueCover r)
variable [MeasurableSpace (C.CubeSpace (ι:=ι))] [BorelSpace (C.CubeSpace (ι:=ι))]

instance haar_fullSupport : (C.haar (ι:=ι) : Measure (C.CubeSpace (ι:=ι))).IsOpenPosMeasure := by
  constructor
  intro U hU hne
  exact ne_of_gt (measure_isOpen_pos_of_smulInvariant_of_compact_ne_zero
    (CubeGroup (ι:=ι) (F:=F)) isCompact_univ (by simp) hU hne)

variable [CompactSpace (G⧸Γ)] [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
variable [SecondCountableTopology (G⧸Γ)]

def cubePhysical (β : ℝ) : C(C.CubeSpace (ι:=ι),(Finset ι → G⧸Γ)) :=
  ⟨EmbeddedCubeHaar.haarImage F.state.domain.embed F.state.domain.filtration Γ
      (F.residue r) C.lattice C.le_induced (fun _=>F.smoothLimit β),
    (EmbeddedCubeHaar.haarImage_continuous F.state.domain.embed F.state.domain.continuous
      F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced).comp
      (continuous_const.prodMk continuous_id)⟩

omit [MeasurableSpace (C.CubeSpace (ι:=ι))] [BorelSpace (C.CubeSpace (ι:=ι))]
  [CompactSpace (G⧸Γ)] [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
  [SecondCountableTopology (G⧸Γ)] in
@[simp] lemma cubePhysical_mk (β : ℝ) (f : CubeGroup (ι:=ι) (F:=F)) (w : Finset ι) :
    C.cubePhysical β (QuotientGroup.mk f) w=
      QuotientGroup.mk (F.smoothLimit β*F.state.domain.embed (f.val w)*F.residue r) :=
  by
  change EmbeddedCubeHaar.haarImage F.state.domain.embed F.state.domain.filtration Γ
    (F.residue r) C.lattice C.le_induced (fun _=>F.smoothLimit β) (QuotientGroup.mk f) w=_
  exact EmbeddedCubeHaar.haarImage_mk _ _ _ _ _ _ _ f w

variable {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y] [HasOuterApproxClosed Y]
variable (β : ℝ) (π : C((Finset ι → G⧸Γ),Y)) (S : C(Y,Y))

 

omit [CompactSpace (G⧸Γ)] [HasOuterApproxClosed Y] in
theorem physical_cube_image_preserved
    (hinv : Measure.map S (C.marginalCubeHaar β π : Measure Y)=
      (C.marginalCubeHaar β π : Measure Y))
    (f : CubeGroup (ι:=ι) (F:=F)) :
    ∃ g : CubeGroup (ι:=ι) (F:=F),
      S (π (fun w=>QuotientGroup.mk (F.smoothLimit β*F.state.domain.embed (f.val w)*F.residue r)))=
        π (fun w=>QuotientGroup.mk (F.smoothLimit β*F.state.domain.embed (g.val w)*F.residue r)) := by
  let q : C(C.CubeSpace (ι:=ι),Y):=π.comp (C.cubePhysical β)
  have hm : (C.marginalCubeHaar β π : Measure Y)=Measure.map q (C.haar (ι:=ι) : Measure _) := by
    rw [marginalCubeHaar,ProbabilityMeasure.toMeasure_map]
    have hc : (C.cubeHaar (ι:=ι) β : Measure (Finset ι → G⧸Γ))=
        Measure.map (C.cubePhysical β) (C.haar (ι:=ι) : Measure (C.CubeSpace (ι:=ι))) := by
      rw [cubeHaar,EmbeddedCubeHaar.imageProbability,ProbabilityMeasure.toMeasure_map]
      rfl
    rw [hc]
    exact Measure.map_map π.continuous.measurable (C.cubePhysical β).continuous.measurable
  rw [hm] at hinv
  obtain ⟨y,hy⟩:=TwoScaleInvariance.range_preservation S (C.haar (ι:=ι)) q hinv (QuotientGroup.mk f)
  induction y using Quotient.inductionOn with | h g =>
    refine ⟨g,?_⟩
    have hq (g : CubeGroup (ι:=ι) (F:=F)) : q (QuotientGroup.mk g)=
        π (fun w=>QuotientGroup.mk (F.smoothLimit β*F.state.domain.embed (g.val w)*F.residue r)) := by
      change π (C.cubePhysical β (QuotientGroup.mk g))=_
      congr 1
      funext w
      exact C.cubePhysical_mk β g w
    change S (q (QuotientGroup.mk f))=q (QuotientGroup.mk g) at hy
    simpa only [hq] using hy

end AllLevelFactorization.Factorization.ResidueCover

end
end

end OAI
