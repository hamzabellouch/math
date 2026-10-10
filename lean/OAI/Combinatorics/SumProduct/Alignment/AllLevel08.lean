import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel07
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter
namespace ComparableBoxLeibman

lemma halfOpen_bounds_scaled_uniform {v : ℕ} (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (c C : ℝ) (hc : 0 < c) (J : ℕ → Type*) (lo hi : ∀ N,J N → Fin v → ℝ)
    (hb : ∀ᶠ N : ℕ in atTop,∀ j : J N,
      (∀ i,c*L N ≤ hi N j i-lo N j i) ∧
      (∀ i,-C*L N ≤ lo N j i ∧ hi N j i ≤ C*L N)) :
    ∀ᶠ N : ℕ in atTop,∀ j : J N,
      (∀ i,(c/2)*L N ≤ ((⌈hi N j i⌉:ℝ)-1)-lo N j i) ∧
      (∀ i,-C*L N ≤ lo N j i ∧ ((⌈hi N j i⌉:ℝ)-1) ≤ C*L N) := by
  filter_upwards [hb,hL.eventually (eventually_ge_atTop (2/c))] with N hN hn
  have hn' : 2 ≤ c*L N := by
    have := (div_le_iff₀ hc).mp hn
    nlinarith
  intro j
  have hN:=hN j
  constructor
  · intro i
    have hceil:=Int.le_ceil (hi N j i)
    linarith [hN.1 i]
  · intro i
    constructor
    · exact (hN.2 i).1
    · have hceil:=Int.ceil_lt_add_one (hi N j i)
      linarith [(hN.2 i).2]

lemma affine_bounds_scaled_uniform {v : ℕ} (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C) (d : ℕ) (hd : 0 < d)
    (r : Fin v → ℤ) (J : ℕ → Type*) (lo hi : ∀ N,J N → Fin v → ℝ)
    (hb : ∀ᶠ N : ℕ in atTop,∀ j : J N,
      (∀ i,c*L N ≤ hi N j i-lo N j i) ∧
      (∀ i,-C*L N ≤ lo N j i ∧ hi N j i ≤ C*L N)) :
    ∃ c' C' : ℝ,0 < c' ∧ 0 < C' ∧ ∀ᶠ N : ℕ in atTop,∀ j : J N,
      (∀ i,c'*L N ≤ (hi N j i-(r i:ℝ))/(d:ℝ)-(lo N j i-(r i:ℝ))/(d:ℝ)) ∧
      (∀ i,-C'*L N ≤ (lo N j i-(r i:ℝ))/(d:ℝ) ∧
        (hi N j i-(r i:ℝ))/(d:ℝ) ≤ C'*L N) := by
  have hdR : 0 < (d:ℝ):=by exact_mod_cast hd
  let M : ℝ:=1+∑ i : Fin v,|(r i:ℝ)|
  have hM : 0 < M:=by dsimp [M]; positivity
  have hr (i : Fin v) : |(r i:ℝ)| ≤ M := by
    have hh : |(r i:ℝ)| ≤ ∑ j : Fin v,|(r j:ℝ)|:=
      Finset.single_le_sum (f:=fun j : Fin v=>|(r j:ℝ)|) (fun j _=>abs_nonneg _) (Finset.mem_univ i)
    dsimp [M]
    linarith
  refine ⟨c/d,(C+M)/d,div_pos hc hdR,div_pos (add_pos hC hM) hdR,?_⟩
  filter_upwards [hb,hL.eventually (eventually_ge_atTop 1)] with N hN hl
  intro j
  have hN:=hN j
  constructor
  · intro i
    rw [←sub_div]
    have he : (c/(d:ℝ))*L N=(c*L N)/(d:ℝ):=by ring
    rw [he]
    apply div_le_div_of_nonneg_right _ hdR.le
    linarith [hN.1 i]
  · intro i
    have hri:=abs_le.mp (hr i)
    have hML : M ≤ M*L N:=by nlinarith
    constructor
    · apply (le_div_iff₀ hdR).mpr
      have he : (-((C+M)/(d:ℝ))*L N)*(d:ℝ)=-(C+M)*L N:=by field_simp
      rw [he]
      nlinarith [hri.2,(hN.2 i).1]
    · apply (div_le_iff₀ hdR).mpr
      have he : ((C+M)/(d:ℝ)*L N)*(d:ℝ)=(C+M)*L N:=by field_simp
      rw [he]
      nlinarith [hri.1,(hN.2 i).2]

end ComparableBoxLeibman
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology NNReal
open Filter MeasureTheory
namespace AllLevelFactorization.Factorization.ResidueCover
open RationalLattice CubeFaces CubeTaylorExpansion ComparableBoxLeibman CubeLocalHaar
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable {F : Factorization c Γ s K P L} {r : Fin F.period} (C : F.ResidueCover r)
variable [MeasurableSpace (C.CubeSpace (ι:=ι))] [BorelSpace (C.CubeSpace (ι:=ι))]

theorem local_halfOpen_uniform (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    {v : ℕ} (e : Option ι ≃ Fin v) (d : ℕ) (hd : 0 < d) (a : Fin v → ℤ)
    (hdp : F.period∣d) (ha0 : a (e none)%(F.period:ℤ)=(r.val:ℤ))
    (hai : ∀ i,a (e (some i))%(F.period:ℤ)=0)
    (J : ℝ → ℕ → Type*) (lo hi : ∀ α N,J α N → Fin v → ℝ)
    (hb : ∀ α : ℝ,0 < α → ∃ c₀ C₀ : ℝ,0 < c₀ ∧ 0 < C₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,(∀ i,c₀*L (F.state.subseq N) ≤ hi α N j i-lo α N j i) ∧
      (∀ i,-C₀*L (F.state.subseq N) ≤ lo α N j i ∧ hi α N j i ≤ C₀*L (F.state.subseq N)))
    (β B : ℝ)
    (hgeo : ∀ α : ℝ,0 < α → ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈halfOpenBox v (lo α N j) (hi α N j),∀ w : Finset ι,
        dist ((vertex (fun i=>a (e i)+(d:ℤ)*z (e i)) w:ℝ)/L (F.state.subseq N)) β ≤ B*α)
    (f : C((Finset ι → G⧸Γ),ℂ)) :
    ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 z∈halfOpenBox v (lo α N j) (hi α N j),
        f (fun w=>QuotientGroup.mk (P (F.state.subseq N)
          (vertex (fun i=>a (e i)+(d:ℤ)*z (e i)) w))))-C.limitIntegral f β‖ < ε := by
  apply C.local_integerBox_uniform hL ht e d hd a hdp ha0 hai J lo
    (fun α N j i=>(⌈hi α N j i⌉:ℝ)-1) ?_ β B hgeo f
  intro α hα
  obtain ⟨c₀,C₀,hc₀,hC₀,hb⟩:=hb α hα
  exact ⟨c₀/2,C₀,by positivity,hC₀,halfOpen_bounds_scaled_uniform
    (L∘F.state.subseq) (ht.comp F.state.strictmono.tendsto_atTop) c₀ C₀ hc₀ (J α)
      (lo α) (hi α) hb⟩

theorem local_physical_uniform (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    {v : ℕ} (e : Option ι ≃ Fin v) (d : ℕ) (hd : 0 < d) (a : Fin v → ℤ)
    (ha : ∀ i,0 ≤ a i ∧ a i < (d:ℤ))
    (hdp : F.period∣d) (ha0 : a (e none)%(F.period:ℤ)=(r.val:ℤ))
    (hai : ∀ i,a (e (some i))%(F.period:ℤ)=0)
    (J : ℝ → ℕ → Type*) (lo hi : ∀ α N,J α N → Fin v → ℝ)
    (hb : ∀ α : ℝ,0 < α → ∃ c₀ C₀ : ℝ,0 < c₀ ∧ 0 < C₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,(∀ i,c₀*L (F.state.subseq N) ≤ hi α N j i-lo α N j i) ∧
      (∀ i,-C₀*L (F.state.subseq N) ≤ lo α N j i ∧ hi α N j i ≤ C₀*L (F.state.subseq N)))
    (β B : ℝ)
    (hgeo : ∀ α : ℝ,0 < α → ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ b∈physicalResidueRectangle (lo α N j) (hi α N j) a d,∀ w : Finset ι,
        dist ((vertex (fun i=>b (e i)) w:ℝ)/L (F.state.subseq N)) β ≤ B*α)
    (f : C((Finset ι → G⧸Γ),ℂ)) :
    ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 b∈physicalResidueRectangle (lo α N j) (hi α N j) a d,
        f (fun w=>QuotientGroup.mk (P (F.state.subseq N) (vertex (fun i=>b (e i)) w))))-
          C.limitIntegral f β‖ < ε := by
  let lo' : ∀ α N,J α N → Fin v → ℝ:=fun α N j i=>(lo α N j i-(a i:ℝ))/(d:ℝ)
  let hi' : ∀ α N,J α N → Fin v → ℝ:=fun α N j i=>(hi α N j i-(a i:ℝ))/(d:ℝ)
  have hb' : ∀ α : ℝ,0 < α → ∃ c₀ C₀ : ℝ,0 < c₀ ∧ 0 < C₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,(∀ i,c₀*L (F.state.subseq N) ≤ hi' α N j i-lo' α N j i) ∧
      (∀ i,-C₀*L (F.state.subseq N) ≤ lo' α N j i ∧ hi' α N j i ≤ C₀*L (F.state.subseq N)) := by
    intro α hα
    obtain ⟨c₀,C₀,hc₀,hC₀,hb⟩:=hb α hα
    exact affine_bounds_scaled_uniform (L∘F.state.subseq)
      (ht.comp F.state.strictmono.tendsto_atTop) c₀ C₀ hc₀ hC₀ d hd a (J α) (lo α) (hi α) hb
  have hg' : ∀ α : ℝ,0 < α → ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈halfOpenBox v (lo' α N j) (hi' α N j),∀ w : Finset ι,
        dist ((vertex (fun i=>a (e i)+(d:ℤ)*z (e i)) w:ℝ)/L (F.state.subseq N)) β ≤ B*α := by
    intro α hα
    filter_upwards [hgeo α hα] with N hN
    intro j z hz
    have hz' : (fun i=>a i+(d:ℤ)*z i)∈physicalResidueRectangle (lo α N j) (hi α N j) a d:=
      (physicalResidueRectangle_affine (lo α N j) (hi α N j) a d hd ha z).mpr hz
    exact hN j (fun i=>a i+(d:ℤ)*z i) hz'
  have he:=C.local_halfOpen_uniform hL ht e d hd a hdp ha0 hai J lo' hi' hb' β B hg' f
  intro ε hε
  filter_upwards [he ε hε] with α hα
  filter_upwards [hα] with N hN
  intro j
  rw [physicalResidueRectangle_expect _ _ a d hd ha]
  exact hN j

variable [CompactSpace (G⧸Γ)] [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)] [SecondCountableTopology (G⧸Γ)]

def cubeHaar (β : ℝ) : ProbabilityMeasure (Finset ι → G⧸Γ) :=
  EmbeddedCubeHaar.imageProbability F.state.domain.embed
    F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced C.haar
      (fun _=>F.smoothLimit β)

omit [CompactSpace (G⧸Γ)] in
lemma integral_cubeHaar (β : ℝ) (f : C((Finset ι → G⧸Γ),ℂ)) :
    (∫ x,f x ∂(C.cubeHaar (ι:=ι) β : Measure (Finset ι → G⧸Γ)))=C.limitIntegral f β :=
  EmbeddedCubeHaar.integral_imageProbability F.state.domain.embed F.state.domain.continuous
    F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced C.haar
      (fun _=>F.smoothLimit β) f

omit [CompactSpace (G⧸Γ)] in
theorem local_physical_compact (hΓ : ∀ x : G,x∈Γ ↔ ∀ i,∃ z : ℤ,c.coord x i=z)
    (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    {v : ℕ} (e : Option ι ≃ Fin v) (d : ℕ) (hd : 0 < d) (a : Fin v → ℤ)
    (ha : ∀ i,0 ≤ a i ∧ a i < (d:ℤ))
    (hdp : F.period∣d) (ha0 : a (e none)%(F.period:ℤ)=(r.val:ℤ))
    (hai : ∀ i,a (e (some i))%(F.period:ℤ)=0)
    (J : ℝ → ℕ → Type*) (lo hi : ∀ α N,J α N → Fin v → ℝ)
    (hb : ∀ α : ℝ,0 < α → ∃ c₀ C₀ : ℝ,0 < c₀ ∧ 0 < C₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,(∀ i,c₀*L (F.state.subseq N) ≤ hi α N j i-lo α N j i) ∧
      (∀ i,-C₀*L (F.state.subseq N) ≤ lo α N j i ∧ hi α N j i ≤ C₀*L (F.state.subseq N)))
    (β B : ℝ)
    (hgeo : ∀ α : ℝ,0 < α → ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ b∈physicalResidueRectangle (lo α N j) (hi α N j) a d,∀ w : Finset ι,
        dist ((vertex (fun i=>b (e i)) w:ℝ)/L (F.state.subseq N)) β ≤ B*α)
    (T : Set C((Finset ι → G⧸Γ),ℂ)) (hT : IsCompact T) :
    ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ∀ f∈T,‖(𝔼 b∈physicalResidueRectangle (lo α N j) (hi α N j) a d,
        f (fun w=>QuotientGroup.mk (P (F.state.subseq N) (vertex (fun i=>b (e i)) w))))-
          (∫ x,f x ∂(C.cubeHaar (ι:=ι) β : Measure (Finset ι → G⧸Γ)))‖ < ε := by
  let : MetricSpace (G⧸Γ):=coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ):=AbelianMalcevTorus.quotient_compact c Γ hΓ
  apply FiniteHaarTests.compact_two_scale_uniform (C.cubeHaar (ι:=ι) β : Measure (Finset ι → G⧸Γ))
    J (fun α N j=>physicalResidueRectangle (lo α N j) (hi α N j) a d)
    (fun _ N _ b w=>QuotientGroup.mk (P (F.state.subseq N) (vertex (fun i=>b (e i)) w))) ?_ T hT
  intro f
  change ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
    ‖(𝔼 b∈physicalResidueRectangle (lo α N j) (hi α N j) a d,
      f (fun w=>QuotientGroup.mk (P (F.state.subseq N) (vertex (fun i=>b (e i)) w))))-
        (∫ x,f x ∂(C.cubeHaar (ι:=ι) β : Measure (Finset ι → G⧸Γ)))‖ < ε
  rw [C.integral_cubeHaar]
  exact C.local_physical_uniform hL ht e d hd a ha hdp ha0 hai J lo hi hb β B hgeo f

 

theorem source_physical_cube_law
    (hΓ : ∀ x : G,x∈Γ ↔ ∀ i,∃ z : ℤ,c.coord x i=z)
    (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    {v : ℕ} (e : Option ι ≃ Fin v) (d : ℕ) (hd : 0 < d) (a : Fin v → ℤ)
    (ha : ∀ i,0 ≤ a i ∧ a i < (d:ℤ))
    (hdp : F.period∣d) (ha0 : a (e none)%(F.period:ℤ)=(r.val:ℤ))
    (hai : ∀ i,a (e (some i))%(F.period:ℤ)=0)
    (β cBox CBox B : ℝ) (hcBox : 0 < cBox) (hCBox : 0 < CBox) (hB : 0 ≤ B)
    (mtr : MetricSpace (G⧸Γ))
    (hmtr : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
    (Lip : ℝ≥0) (Sup : ℝ) :
    letI : MetricSpace (G⧸Γ):=MetricSpace.replaceTopology mtr hmtr.symm
    ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ∀ lo hi : Fin v → ℝ,
        (∀ i,(cBox*α)*L (F.state.subseq N) ≤ hi i-lo i) →
        (∀ i,-CBox*L (F.state.subseq N) ≤ lo i ∧ hi i ≤ CBox*L (F.state.subseq N)) →
        (∀ b∈physicalResidueRectangle lo hi a d,
          |((b (e none):ℝ)/L (F.state.subseq N))-β| ≤ B*α ∧
          ∀ i : ι,|(b (e (some i)):ℝ)/L (F.state.subseq N)| ≤ B*α) →
        ∀ f : C((Finset ι → G⧸Γ),ℂ),LipschitzWith Lip f → ‖f‖ ≤ Sup →
          ‖(𝔼 b∈physicalResidueRectangle lo hi a d,
            f (fun w=>QuotientGroup.mk (P (F.state.subseq N) (vertex (fun i=>b (e i)) w))))-
              (∫ x,f x ∂(C.cubeHaar (ι:=ι) β : Measure (Finset ι → G⧸Γ)))‖ < ε := by
  let : MetricSpace (G⧸Γ):=MetricSpace.replaceTopology mtr hmtr.symm
  let : CompactSpace (G⧸Γ):=AbelianMalcevTorus.quotient_compact c Γ hΓ
  let J : ℝ → ℕ → Type:=fun α N=>{p : (Fin v → ℝ)×(Fin v → ℝ) //
    (∀ i,(cBox*α)*L (F.state.subseq N) ≤ p.2 i-p.1 i) ∧
    (∀ i,-CBox*L (F.state.subseq N) ≤ p.1 i ∧ p.2 i ≤ CBox*L (F.state.subseq N)) ∧
    (∀ b∈physicalResidueRectangle p.1 p.2 a d,
      |((b (e none):ℝ)/L (F.state.subseq N))-β| ≤ B*α ∧
      ∀ i : ι,|(b (e (some i)):ℝ)/L (F.state.subseq N)| ≤ B*α)}
  let lo : ∀ α N,J α N → Fin v → ℝ:=fun _ _ j=>j.val.1
  let hi : ∀ α N,J α N → Fin v → ℝ:=fun _ _ j=>j.val.2
  have hb : ∀ α : ℝ,0 < α → ∃ c₀ C₀ : ℝ,0 < c₀ ∧ 0 < C₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,(∀ i,c₀*L (F.state.subseq N) ≤ hi α N j i-lo α N j i) ∧
        (∀ i,-C₀*L (F.state.subseq N) ≤ lo α N j i ∧ hi α N j i ≤ C₀*L (F.state.subseq N)) := by
    intro α hα
    exact ⟨cBox*α,CBox,mul_pos hcBox hα,hCBox,Eventually.of_forall
      (fun N j=>⟨j.property.1,j.property.2.1⟩)⟩
  have hgeo : ∀ α : ℝ,0 < α → ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ b∈physicalResidueRectangle (lo α N j) (hi α N j) a d,∀ w : Finset ι,
        dist ((vertex (fun i=>b (e i)) w:ℝ)/L (F.state.subseq N)) β ≤
          ((1+(Fintype.card ι:ℝ))*B)*α := by
    intro α hα
    apply Eventually.of_forall
    intro N j b hb w
    have hg:=j.property.2.2 b hb
    have hw:=normalized_vertex_close
      (fun i=>(b (e i):ℝ)/L (F.state.subseq N)) β (B*α) (mul_nonneg hB hα.le) hg.1 hg.2 w
    simpa only [vertex,Int.cast_add,Int.cast_sum,add_div,Finset.sum_div,mul_assoc] using hw
  obtain ⟨T,hT,hcover⟩:=BoundedLipschitzCompact.compact_envelope (X:=Finset ι → G⧸Γ) Lip Sup
  have hlocal:=C.local_physical_compact hΓ hL ht e d hd a ha hdp ha0 hai J lo hi hb β
    ((1+(Fintype.card ι:ℝ))*B) hgeo T hT
  intro ε hε
  filter_upwards [hlocal ε hε] with α hα
  filter_upwards [hα] with N hN
  intro lo' hi' hs ho hg f hf hsup
  exact hN ⟨(lo',hi'),hs,ho,hg⟩ f (hcover f hf hsup)

end AllLevelFactorization.Factorization.ResidueCover

end
end

end OAI
