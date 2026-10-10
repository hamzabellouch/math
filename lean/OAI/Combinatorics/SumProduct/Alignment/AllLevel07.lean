import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel06
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
namespace AllLevelFactorization.Factorization
open RationalLattice CubeFaces CubeTaylorExpansion CubeLocalHaar
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (F : Factorization c Γ s K P L)

lemma realization_of_residue (N : ℕ) (z : ℤ) (r : Fin F.period)
    (hz : z%(F.period:ℤ)=(r.val:ℤ)) :
    (QuotientGroup.mk (P (F.state.subseq N) z) : G⧸Γ)=
      QuotientGroup.mk (F.smoothPart N z*F.state.domain.embed (F.structuredPart N z)*F.residue r) := by
  obtain ⟨r',hr',he⟩:=F.realization N z
  have hr : r'=r:=Fin.ext (by exact_mod_cast hr'.trans hz)
  simpa only [hr] using he

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def vertex (b : Option ι → ℤ) (w : Finset ι) : ℤ:=b none+∑ i∈w,b (some i)

omit [Fintype ι] [DecidableEq ι] in
lemma vertex_mod (p : ℤ) (b : Option ι → ℤ) (r : ℤ)
    (hbase : b none%p=r) (hinc : ∀ i,b (some i)%p=0) (w : Finset ι) :
    vertex b w%p=r := by
  have hs : p∣∑ i∈w,b (some i):=
    Finset.dvd_sum (fun i _=>Int.dvd_of_emod_eq_zero (hinc i))
  simp only [vertex,Int.add_emod,Int.emod_eq_zero_of_dvd hs,add_zero,Int.emod_emod]
  exact hbase

omit [IsTopologicalGroup G] [Fintype ι] [DecidableEq ι] in
lemma affine_vertex_mod {v : ℕ} (e : Option ι ≃ Fin v) (d : ℕ) (a : Fin v → ℤ)
    (hdp : F.period∣d) (r : Fin F.period)
    (ha0 : a (e none)%(F.period:ℤ)=(r.val:ℤ))
    (hai : ∀ i,a (e (some i))%(F.period:ℤ)=0)
    (z : Fin v → ℤ) (w : Finset ι) :
    vertex (fun i=>a (e i)+(d:ℤ)*z (e i)) w%(F.period:ℤ)=(r.val:ℤ) := by
  have hd : (F.period:ℤ)∣(d:ℤ):=by exact_mod_cast hdp
  have hem (x y : ℤ) : (x+(d:ℤ)*y)%(F.period:ℤ)=x%(F.period:ℤ) := by
    rw [Int.add_emod,Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_left hd y),add_zero,Int.emod_emod]
  exact vertex_mod _ _ _ (by simpa only [hem] using ha0)
    (fun i=>by simpa only [hem] using hai i) w

namespace ResidueCover
variable {F} {r : Fin F.period} (C : F.ResidueCover r)

lemma cube_realization (N : ℕ) (b : Option ι → ℤ)
    (hb : ∀ w : Finset ι,vertex b w%(F.period:ℤ)=(r.val:ℤ)) :
    (fun w : Finset ι=>(QuotientGroup.mk (P (F.state.subseq N) (vertex b w)) : G⧸Γ))=
      EmbeddedCubeHaar.haarImage F.state.domain.embed F.state.domain.filtration Γ
        (F.residue r) C.lattice C.le_induced
        (fun w=>F.smoothPart N (vertex b w)) (C.cubePoint N b) := by
  funext w
  rw [F.realization_of_residue N _ r (hb w)]
  unfold cubePoint
  rw [EmbeddedCubeHaar.haarImage_mk,cubePolynomial_integer_vertex]
  rfl

end ResidueCover

end AllLevelFactorization.Factorization
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace AllLevelFactorization.Factorization.ResidueCover
open RationalLattice CubeFaces CubeTaylorExpansion ComparableBoxLeibman CubeLocalHaar
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable {F : Factorization c Γ s K P L} {r : Fin F.period} (C : F.ResidueCover r)
variable [MeasurableSpace (C.CubeSpace (ι:=ι))] [BorelSpace (C.CubeSpace (ι:=ι))]

def limitIntegral (f : C((Finset ι → G⧸Γ),ℂ)) (β : ℝ) : ℂ :=
  ∫ x,EmbeddedCubeHaar.frozenTest F.state.domain.embed F.state.domain.continuous
    F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced f
    (fun _=>F.smoothLimit β) x ∂(C.haar (ι:=ι) : Measure (C.CubeSpace (ι:=ι)))

 

theorem local_integerBox (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    {v : ℕ} (e : Option ι ≃ Fin v) (d : ℕ) (hd : 0 < d) (a : Fin v → ℤ)
    (hdp : F.period∣d) (ha0 : a (e none)%(F.period:ℤ)=(r.val:ℤ))
    (hai : ∀ i,a (e (some i))%(F.period:ℤ)=0)
    (lo hi : ℝ → ℕ → Fin v → ℝ)
    (hb : ∀ α : ℝ,0 < α → ∃ c₀ C₀ : ℝ,0 < c₀ ∧ 0 < C₀ ∧ ∀ᶠ N : ℕ in atTop,
      (∀ i,c₀*L (F.state.subseq N) ≤ hi α N i-lo α N i) ∧
      (∀ i,-C₀*L (F.state.subseq N) ≤ lo α N i ∧ hi α N i ≤ C₀*L (F.state.subseq N)))
    (β B : ℝ)
    (hgeo : ∀ α : ℝ,0 < α → ∀ᶠ N : ℕ in atTop,
      ∀ z∈integerBox v (lo α N) (hi α N),∀ w : Finset ι,
        dist ((vertex (fun i=>a (e i)+(d:ℤ)*z (e i)) w:ℝ)/L (F.state.subseq N)) β ≤ B*α)
    (f : C((Finset ι → G⧸Γ),ℂ)) :
    ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ‖(𝔼 z∈integerBox v (lo α N) (hi α N),
        f (fun w=>QuotientGroup.mk (P (F.state.subseq N)
          (vertex (fun i=>a (e i)+(d:ℤ)*z (e i)) w))))-C.limitIntegral f β‖ < ε := by
  let T : ℝ → ℕ → Finset (Fin v → ℤ):=fun α N=>integerBox v (lo α N) (hi α N)
  let b : (Fin v → ℤ) → Option ι → ℤ:=fun z i=>a (e i)+(d:ℤ)*z (e i)
  let t : ℝ → ℕ → (Fin v → ℤ) → Finset ι → ℝ:=
    fun _ N z w=>(vertex (b z) w:ℝ)/L (F.state.subseq N)
  have hu:=F.smooth_neighborhood hL ht β T t B hgeo
  have hm (N : ℕ) (z : Fin v → ℤ) (w : Finset ι) :
      L (F.state.subseq N)*((vertex (b z) w:ℝ)/L (F.state.subseq N))=(vertex (b z) w:ℝ) := by
    field_simp [ne_of_gt (hL (F.state.subseq N))]
  simp only [t,hm] at hu
  have he:=C.two_scale hL ht e d hd a lo hi hb
    (fun _ N z w=>F.smoothPart N (vertex (b z) w)) (fun _=>F.smoothLimit β) hu f
  have himage (N : ℕ) (z : Fin v → ℤ) :
      EmbeddedCubeHaar.haarImage F.state.domain.embed F.state.domain.filtration Γ
        (F.residue r) C.lattice C.le_induced
        (fun w=>F.smoothPart N (vertex (b z) w)) (C.cubePoint N (b z))=
      fun w : Finset ι=>QuotientGroup.mk (P (F.state.subseq N) (vertex (b z) w)) :=
    (C.cube_realization N (b z) (fun w=>F.affine_vertex_mod e d a hdp r ha0 hai z w)).symm
  change ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
    ‖(𝔼 z∈integerBox v (lo α N) (hi α N),f (EmbeddedCubeHaar.haarImage
      F.state.domain.embed F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced
      (fun w=>F.smoothPart N (vertex (b z) w)) (C.cubePoint N (b z))))-C.limitIntegral f β‖ < ε at he
  simpa only [himage,b] using he

end AllLevelFactorization.Factorization.ResidueCover
end
 
end

section
 

 
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace CompactTwoScale
variable {X P κ : Type*} [TopologicalSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [TopologicalSpace P]
variable (μ : Measure X) [IsProbabilityMeasure μ]
omit [BorelSpace X] [IsProbabilityMeasure μ] in
theorem freezing_uniform (F : P→C(X,ℂ)) (hF : Continuous F) (a₀ : P)
    (J : ℝ→ℕ→Type*)
    (T : ∀ α N,J α N→Finset κ) (p : ∀ α N,J α N→κ→X)
    (a : ∀ α N,J α N→κ→P)
    (hbase : ∀ α : ℝ,0<α → ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 z∈T α N j,F a₀ (p α N j z))-(∫ x,F a₀ x ∂μ)‖<ε)
    (hsm : ∀ U∈𝓝 a₀,∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈T α N j,a α N j z∈U) :
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 z∈T α N j,F (a α N j z) (p α N j z))-(∫ x,F a₀ x ∂μ)‖<ε := by
  intro ε hε
  have hε3 : 0<ε/3 := by positivity
  let U : Set P := F ⁻¹' Metric.ball (F a₀) (ε/3)
  have hU : U∈𝓝 a₀ := hF.continuousAt.preimage_mem_nhds
    (Metric.ball_mem_nhds _ hε3)
  filter_upwards [hsm U hU,(self_mem_nhdsWithin : Set.Ioi (0:ℝ)∈𝓝[>] 0)] with α hα ha
  filter_upwards [hα,hbase α ha (ε/3) hε3] with N hN hb
  intro j
  have hb := hb j
  have hp (z : κ) (hz : z∈T α N j) :
      ‖F (a α N j z) (p α N j z)-F a₀ (p α N j z)‖≤ε/3 := by
    apply (ContinuousMap.norm_coe_le_norm (F (a α N j z)-F a₀) (p α N j z)).trans
    exact le_of_lt (by simpa only [U,Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using hN j z hz)
  have hm : ‖𝔼 z∈T α N j,(F (a α N j z) (p α N j z)-F a₀ (p α N j z))‖≤ε/3 := by
    by_cases hn : (T α N j).Nonempty
    · exact (RCLike.norm_expect_le (K := ℂ)).trans (Finset.expect_le hn hp)
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.expect_empty,norm_zero]
      positivity
  rw [Finset.expect_sub_distrib] at hm
  change ‖(𝔼 z∈T α N j,F a₀ (p α N j z))-(∫ x,F a₀ x ∂μ)‖<ε/3 at hb
  calc
    _ = ‖((𝔼 z∈T α N j,F (a α N j z) (p α N j z))-(𝔼 z∈T α N j,F a₀ (p α N j z)))+
          ((𝔼 z∈T α N j,F a₀ (p α N j z))-(∫ x,F a₀ x ∂μ))‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < ε := by linarith only [hm,hb,hε]

end CompactTwoScale

namespace AllLevelFactorization.Factorization
open AllLevelDomains AllLevelStates RationalLattice CubeFaces MalcevCharacters
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (F : Factorization c Γ s K P L)

 theorem smooth_neighborhood_uniform {κ τ : Type*} [Fintype τ]
    (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    (β : ℝ) (J : ℝ → ℕ → Type*)
    (T : ∀ α N,J α N → Finset κ) (t : ∀ α N,J α N → κ → τ → ℝ) (C : ℝ)
    (hpos : ∀ α : ℝ,0 < α → ∀ᶠ N : ℕ in atTop,∀ j : J α N,∀ z∈T α N j,∀ w,
      dist (t α N j z w) β ≤ C*α) :
    ∀ U∈𝓝 (fun _ : τ=>F.smoothLimit β),∀ᶠ α : ℝ in 𝓝[>] 0,
      ∀ᶠ N : ℕ in atTop,∀ j : J α N,∀ z∈T α N j,
        (fun w=>F.smoothPart N (L (F.state.subseq N)*t α N j z w))∈U := by
  let f : (τ → Fin n → ℝ) → (τ → G) := fun u w=>c.coord.symm (u w)
  have hf : Continuous f := continuous_pi fun w=>c.coord.symm.continuous.comp (continuous_apply w)
  intro U hU
  have hpre : f ⁻¹' U∈𝓝 (fun _ : τ=>c.coord (F.smoothLimit β)) := by
    apply hf.continuousAt.preimage_mem_nhds
    simpa [f] using hU
  have hc : ContinuousAt (fun t=>c.coord (F.smoothLimit t)) β :=
    (c.coord.continuous.comp F.smoothLimit_continuous).continuousAt
  have hh (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop,∀ t : ℝ,dist t β < 1 →
      dist (c.coord (F.smoothPart N (L (F.state.subseq N)*t)))
        (c.coord (F.smoothLimit t)) < ε := by
    filter_upwards [F.smooth_coord_uniform hL ht (Set.Icc (β-1) (β+1)) isCompact_Icc ε hε] with N hN
    intro t ht
    apply hN t
    rw [Real.dist_eq,abs_lt] at ht
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hv:=CubeLocalHaar.smooth_local_freezing_uniform
    (fun N t=>c.coord (F.smoothPart N (L (F.state.subseq N)*t)))
    (fun t=>c.coord (F.smoothLimit t)) β hc 1 zero_lt_one hh J T t C hpos
    (f ⁻¹' U) hpre
  simpa only [Set.mem_preimage,f,Homeomorph.symm_apply_apply] using hv

end AllLevelFactorization.Factorization
namespace AllLevelFactorization.Factorization.ResidueCover
open RationalLattice CubeFaces CubeTaylorExpansion ComparableBoxLeibman CubeLocalHaar
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable {F : Factorization c Γ s K P L} {r : Fin F.period} (C : F.ResidueCover r)

variable [MeasurableSpace (C.CubeSpace (ι:=ι))] [BorelSpace (C.CubeSpace (ι:=ι))]
theorem two_scale_uniform (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    {v : ℕ} (e : Option ι ≃ Fin v) (d : ℕ) (hd : 0 < d) (a : Fin v → ℤ)
    (J : ℝ → ℕ → Type*) (lo hi : ∀ α N,J α N → Fin v → ℝ)
    (hb : ∀ α : ℝ,0 < α → ∃ c₀ C₀ : ℝ,0 < c₀ ∧ 0 < C₀ ∧ ∀ᶠ N : ℕ in atTop,∀ j : J α N,
      (∀ i,c₀*L (F.state.subseq N) ≤ hi α N j i-lo α N j i) ∧
      (∀ i,-C₀*L (F.state.subseq N) ≤ lo α N j i ∧ hi α N j i ≤ C₀*L (F.state.subseq N)))
    (u : ∀ α N,J α N → (Fin v → ℤ) → Finset ι → G) (u₀ : Finset ι → G)
    (hu : ∀ U∈𝓝 u₀,∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈integerBox v (lo α N j) (hi α N j),u α N j z∈U)
    (f : C((Finset ι → G⧸Γ),ℂ)) :
    ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 z∈integerBox v (lo α N j) (hi α N j),
        f (EmbeddedCubeHaar.haarImage F.state.domain.embed F.state.domain.filtration Γ
          (F.residue r) C.lattice C.le_induced (u α N j z)
          (C.cubePoint N (fun i=>a (e i)+(d:ℤ)*z (e i)))))-
        (∫ x,EmbeddedCubeHaar.frozenTest F.state.domain.embed F.state.domain.continuous
          F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced f u₀ x
          ∂(C.haar (ι:=ι) : Measure (C.CubeSpace (ι:=ι))))‖ < ε := by
  apply CompactTwoScale.freezing_uniform (C.haar (ι:=ι) : Measure (C.CubeSpace (ι:=ι)))
    (EmbeddedCubeHaar.frozenTest F.state.domain.embed F.state.domain.continuous
      F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced f)
    (EmbeddedCubeHaar.frozenTest_continuous F.state.domain.embed F.state.domain.continuous
      F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced f)
    u₀ J (fun α N j=>integerBox v (lo α N j) (hi α N j))
    (fun _ N _ z=>C.cubePoint N (fun i=>a (e i)+(d:ℤ)*z (e i))) u ?_ hu
  intro α hα ε hε
  obtain ⟨c₀,C₀,hc₀,hC₀,hbox⟩:=hb α hα
  let f₀:=EmbeddedCubeHaar.frozenTest F.state.domain.embed F.state.domain.continuous
    F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced f u₀
  filter_upwards [C.haar_limit hL ht e c₀ C₀ hc₀ hC₀ d hd a {f₀} isCompact_singleton ε hε,
    hbox] with N hN hbN
  intro j
  exact hN (lo α N j) (hi α N j) (hbN j).1 (hbN j).2 f₀ rfl

theorem local_integerBox_uniform (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    {v : ℕ} (e : Option ι ≃ Fin v) (d : ℕ) (hd : 0 < d) (a : Fin v → ℤ)
    (hdp : F.period∣d) (ha0 : a (e none)%(F.period:ℤ)=(r.val:ℤ))
    (hai : ∀ i,a (e (some i))%(F.period:ℤ)=0)
    (J : ℝ → ℕ → Type*) (lo hi : ∀ α N,J α N → Fin v → ℝ)
    (hb : ∀ α : ℝ,0 < α → ∃ c₀ C₀ : ℝ,0 < c₀ ∧ 0 < C₀ ∧ ∀ᶠ N : ℕ in atTop,∀ j : J α N,
      (∀ i,c₀*L (F.state.subseq N) ≤ hi α N j i-lo α N j i) ∧
      (∀ i,-C₀*L (F.state.subseq N) ≤ lo α N j i ∧ hi α N j i ≤ C₀*L (F.state.subseq N)))
    (β B : ℝ)
    (hgeo : ∀ α : ℝ,0 < α → ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈integerBox v (lo α N j) (hi α N j),∀ w : Finset ι,
        dist ((vertex (fun i=>a (e i)+(d:ℤ)*z (e i)) w:ℝ)/L (F.state.subseq N)) β ≤ B*α)
    (f : C((Finset ι → G⧸Γ),ℂ)) :
    ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 z∈integerBox v (lo α N j) (hi α N j),
        f (fun w=>QuotientGroup.mk (P (F.state.subseq N)
          (vertex (fun i=>a (e i)+(d:ℤ)*z (e i)) w))))-C.limitIntegral f β‖ < ε := by
  let T : ∀ α N,J α N → Finset (Fin v → ℤ):=fun α N j=>integerBox v (lo α N j) (hi α N j)
  let b : (Fin v → ℤ) → Option ι → ℤ:=fun z i=>a (e i)+(d:ℤ)*z (e i)
  let t : ∀ α N,J α N → (Fin v → ℤ) → Finset ι → ℝ:=
    fun _ N _ z w=>(vertex (b z) w:ℝ)/L (F.state.subseq N)
  have hu:=F.smooth_neighborhood_uniform hL ht β J T t B hgeo
  have hm (N : ℕ) (z : Fin v → ℤ) (w : Finset ι) :
      L (F.state.subseq N)*((vertex (b z) w:ℝ)/L (F.state.subseq N))=(vertex (b z) w:ℝ) := by
    field_simp [ne_of_gt (hL (F.state.subseq N))]
  simp only [t,hm] at hu
  have he:=C.two_scale_uniform hL ht e d hd a J lo hi hb
    (fun _ N _ z w=>F.smoothPart N (vertex (b z) w)) (fun _=>F.smoothLimit β) hu f
  have himage (N : ℕ) (z : Fin v → ℤ) :
      EmbeddedCubeHaar.haarImage F.state.domain.embed F.state.domain.filtration Γ
        (F.residue r) C.lattice C.le_induced
        (fun w=>F.smoothPart N (vertex (b z) w)) (C.cubePoint N (b z))=
      fun w : Finset ι=>QuotientGroup.mk (P (F.state.subseq N) (vertex (b z) w)) :=
    (C.cube_realization N (b z) (fun w=>F.affine_vertex_mod e d a hdp r ha0 hai z w)).symm
  change ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
    ‖(𝔼 z∈integerBox v (lo α N j) (hi α N j),f (EmbeddedCubeHaar.haarImage
      F.state.domain.embed F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced
      (fun w=>F.smoothPart N (vertex (b z) w)) (C.cubePoint N (b z))))-C.limitIntegral f β‖ < ε at he
  simpa only [himage,b] using he

end AllLevelFactorization.Factorization.ResidueCover

end
end

end OAI
