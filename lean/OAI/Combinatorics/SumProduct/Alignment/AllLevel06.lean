import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.EmbeddedCube01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open scoped Topology

end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
namespace CubeTaylorExpansion
open RationalLattice CubeFaces NilpotentTaylor
variable {G ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (H : Filtration G)

lemma choose_cast_int (z : ℤ) (k : ℕ) :
    Ring.choose (z:ℝ) k=((Ring.choose z k:ℤ):ℝ) :=
  (Ring.map_choose (Int.castRingHom ℝ) z k).symm

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma word_eq_list (a : ℕ → G) (d : ℕ) (z : ℤ) :
    word a d z=((List.range d).map (fun k=>a k^Ring.choose z k)).prod := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [List.prod_range_succ]
    exact congrArg (fun v=>v*a d^Ring.choose z d) ih

omit [IsTopologicalGroup G] in
lemma taylorPolynomial_int (a : ∀ k : ℕ,H.level k) (s : ℕ) (z : ℤ) :
    taylorPolynomial c H a s (z:ℝ)=word (fun k=>(a k).val) (s+1) z := by
  rw [word_eq_list]
  simp only [taylorPolynomial,choose_cast_int,realPower_int]

variable [Fintype ι] [DecidableEq ι]
variable (S : ℕ→Set (Fin n))
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i∈S k,c.coord g i=0)

omit [IsTopologicalGroup G] in
lemma cubePolynomial_integer_vertex (a : ∀ k : ℕ,H.level k) (s : ℕ)
    (b : Option ι→ℤ) (v : Finset ι) :
    ((cubePolynomial c H S hH a s (fun i=>(b i:ℝ)) : cube H Finset.univ 0) : Finset ι→G) v=
      word (fun k=>(a k).val) (s+1) (b none+∑ i∈v,b (some i)) := by
  rw [cubePolynomial_vertex,← taylorPolynomial_int c H]
  congr 1
  push_cast
  rfl

end CubeTaylorExpansion
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter
namespace AllLevelFactorization.Factorization
open AllLevelDomains AllLevelStates RationalLattice CubeFaces MalcevCharacters
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (F : Factorization c Γ s K P L)

lemma smoothLimit_continuous : Continuous F.smoothLimit := by
  have hc : Continuous (fun β=>c.coord (F.smoothLimit β)) :=
    continuous_pi fun i=>(F.limit_smooth i).continuous
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using c.coord.symm.continuous.comp hc

lemma smooth_coord_uniform (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    (A : Set ℝ) (hA : IsCompact A) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,∀ t∈A,
      dist (c.coord (F.smoothPart N (L (F.state.subseq N)*t)))
        (c.coord (F.smoothLimit t)) < ε := by
  have hi (i : Fin n) : ∀ᶠ N : ℕ in atTop,∀ t∈A,
      dist (c.coord (F.smoothPart N (L (F.state.subseq N)*t)) i)
        (c.coord (F.smoothLimit t) i) < ε := by
    have hu := F.smooth_limit hL ht 0 i A hA
    simpa only [iteratedDeriv_zero,dist_comm] using (Metric.tendstoUniformlyOn_iff.mp hu ε hε)
  filter_upwards [eventually_all.mpr hi] with N hN
  intro t ht
  rw [dist_pi_lt_iff hε]
  exact fun i=>hN i t ht

 

 theorem smooth_neighborhood {κ τ : Type*} [Fintype τ]
    (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    (β : ℝ) (T : ℝ → ℕ → Finset κ) (t : ℝ → ℕ → κ → τ → ℝ) (C : ℝ)
    (hpos : ∀ α : ℝ,0 < α → ∀ᶠ N : ℕ in atTop,∀ z∈T α N,∀ w,
      dist (t α N z w) β ≤ C*α) :
    ∀ U∈𝓝 (fun _ : τ=>F.smoothLimit β),∀ᶠ α : ℝ in 𝓝[>] 0,
      ∀ᶠ N : ℕ in atTop,∀ z∈T α N,
        (fun w=>F.smoothPart N (L (F.state.subseq N)*t α N z w))∈U := by
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
  have hv:=CubeLocalHaar.smooth_local_freezing
    (fun N t=>c.coord (F.smoothPart N (L (F.state.subseq N)*t)))
    (fun t=>c.coord (F.smoothLimit t)) β hc 1 zero_lt_one hh T t C hpos
    (f ⁻¹' U) hpre
  simpa only [Set.mem_preimage,f,Homeomorph.symm_apply_apply] using hv

end AllLevelFactorization.Factorization
end
 
end

section
 

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace CompactTwoScale
variable {X A κ : Type*} [TopologicalSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [TopologicalSpace A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

 

omit [BorelSpace X] [IsProbabilityMeasure μ] in
theorem freezing (F : A → C(X,ℂ)) (hF : Continuous F) (a₀ : A)
    (T : ℝ → ℕ → Finset κ) (p : ℝ → ℕ → κ → X) (a : ℝ → ℕ → κ → A)
    (hbase : ∀ α : ℝ,0 < α → ∀ ε : ℝ,0 < ε → ∀ᶠ N : ℕ in atTop,
      ‖(𝔼 z∈T α N,F a₀ (p α N z))-(∫ x,F a₀ x ∂μ)‖ < ε)
    (hsm : ∀ U∈𝓝 a₀,∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ∀ z∈T α N,a α N z∈U) :
    ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ‖(𝔼 z∈T α N,F (a α N z) (p α N z))-(∫ x,F a₀ x ∂μ)‖ < ε := by
  intro ε hε
  have hε3 : 0 < ε/3:=by positivity
  let U : Set A:=F ⁻¹' Metric.ball (F a₀) (ε/3)
  have hU : U∈𝓝 a₀:=hF.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε3)
  filter_upwards [hsm U hU,(self_mem_nhdsWithin : Set.Ioi (0:ℝ)∈𝓝[>] 0)] with α hα ha
  filter_upwards [hα,hbase α ha (ε/3) hε3] with N hN hb
  have hp (z : κ) (hz : z∈T α N) :
      ‖F (a α N z) (p α N z)-F a₀ (p α N z)‖ ≤ ε/3 := by
    apply (ContinuousMap.norm_coe_le_norm (F (a α N z)-F a₀) (p α N z)).trans
    exact le_of_lt (by simpa only [U,Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using hN z hz)
  have hm : ‖𝔼 z∈T α N,(F (a α N z) (p α N z)-F a₀ (p α N z))‖ ≤ ε/3 := by
    by_cases hn : (T α N).Nonempty
    · exact (RCLike.norm_expect_le (K:=ℂ)).trans (Finset.expect_le hn hp)
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.expect_empty,norm_zero]
      positivity
  rw [Finset.expect_sub_distrib] at hm
  calc
    _ = ‖((𝔼 z∈T α N,F (a α N z) (p α N z))-(𝔼 z∈T α N,F a₀ (p α N z)))+
          ((𝔼 z∈T α N,F a₀ (p α N z))-(∫ x,F a₀ x ∂μ))‖:=by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < ε := by linarith only [hm,hb,hε]
end CompactTwoScale

namespace EmbeddedCubeHaar
open CubeFaces CubeLocalHaar RationalLattice
variable {G H ι : Type} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable [Fintype ι] [DecidableEq ι]
variable (f : H →* G) (hc : Continuous f) (K : Filtration H) (Λ : Subgroup G) (σ : G)
variable (Δ : Subgroup H) (hle : Δ ≤ inducedLattice f Λ σ)

def frozenTest (F : C((Finset ι→G⧸Λ),ℂ)) (a : Finset ι→G) :
    C(((cube K (Finset.univ : Finset ι) 0)⧸cubeLattice K Δ),ℂ) :=
  ⟨fun x=>F (haarImage f K Λ σ Δ hle a x),F.continuous.comp
    ((haarImage_continuous f hc K Λ σ Δ hle).comp (continuous_const.prodMk continuous_id))⟩

omit [IsTopologicalGroup H] in
lemma frozenTest_continuous (F : C((Finset ι→G⧸Λ),ℂ)) :
    Continuous (frozenTest f hc K Λ σ Δ hle F) :=
  (ContinuousMap.curry ⟨_,F.continuous.comp (haarImage_continuous f hc K Λ σ Δ hle)⟩).continuous

end EmbeddedCubeHaar

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

abbrev CubeGroup := cube F.state.domain.filtration (Finset.univ : Finset ι) 0
abbrev CubeSpace := (CubeGroup (ι:=ι) (F:=F))⧸cubeLattice F.state.domain.filtration C.lattice

def cubePoint (N : ℕ) (b : Option ι → ℤ) : C.CubeSpace (ι:=ι) :=
  QuotientGroup.mk (cubePolynomial C.chart F.state.domain.filtration
    (fun k=>{i : Fin F.state.domain.dim | i.val < F.state.domain.cutoff k})
    (fun k g=>C.adapted k g) (F.state.coeff N) s (fun i=>(b i:ℝ)))

instance compact_cubeSpace : CompactSpace (C.CubeSpace (ι:=ι)) :=
  CubeLocalHaar.cubeQuotient_compact F.state.domain.filtration C.lattice
    (BaseCubeLaw.level_compact_reps C.chart F.state.domain.filtration F.state.domain.cutoff
      C.adapted C.lattice C.integer_lattice)

variable [MeasurableSpace (C.CubeSpace (ι:=ι))] [BorelSpace (C.CubeSpace (ι:=ι))]

def haar : ProbabilityMeasure (C.CubeSpace (ι:=ι)) :=
  Classical.choose (BaseCubeLaw.exists_scaled_cube_law (ι:=ι) C.chart F.state.domain.filtration
    F.state.domain.cutoff C.adapted C.lattice C.integer_lattice
    (F.state.domain.zero_top.trans F.state.domain.one_top.symm) s F.state.domain.terminal)

instance haar_invariant : SMulInvariantMeasure (CubeGroup (ι:=ι) (F:=F)) _
    (C.haar (ι:=ι) : Measure (C.CubeSpace (ι:=ι))) :=
  (Classical.choose_spec (BaseCubeLaw.exists_scaled_cube_law (ι:=ι) C.chart F.state.domain.filtration
    F.state.domain.cutoff C.adapted C.lattice C.integer_lattice
    (F.state.domain.zero_top.trans F.state.domain.one_top.symm) s F.state.domain.terminal)).1

omit [IsTopologicalGroup G] in
lemma haar_limit (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    {v : ℕ} (e : Option ι ≃ Fin v) (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (d : ℕ) (hd : 0 < d) (a : Fin v → ℤ) (T : Set C(C.CubeSpace (ι:=ι),ℂ))
    (hT : IsCompact T) :
    ∀ ε : ℝ,0 < ε → ∀ᶠ N : ℕ in atTop,∀ lo hi : Fin v → ℝ,
      (∀ i,c₀*L (F.state.subseq N) ≤ hi i-lo i) →
      (∀ i,-C₀*L (F.state.subseq N) ≤ lo i ∧ hi i ≤ C₀*L (F.state.subseq N)) →
      ∀ f : C(C.CubeSpace (ι:=ι),ℂ),f∈T →
        ‖(𝔼 x∈integerBox v lo hi,f (C.cubePoint N (fun i=>a (e i)+(d:ℤ)*x (e i))))-
          (∫ y,f y ∂(C.haar (ι:=ι) : Measure (C.CubeSpace (ι:=ι))))‖ < ε := by
  exact (Classical.choose_spec (BaseCubeLaw.exists_scaled_cube_law (ι:=ι) C.chart
    F.state.domain.filtration F.state.domain.cutoff C.adapted C.lattice C.integer_lattice
    (F.state.domain.zero_top.trans F.state.domain.one_top.symm) s F.state.domain.terminal)).2
      v e (L∘F.state.subseq) (ht.comp F.state.strictmono.tendsto_atTop)
      F.state.coeff (C.irrational hL) c₀ C₀ hc₀ hC₀ d hd a T hT

 

theorem two_scale (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    {v : ℕ} (e : Option ι ≃ Fin v) (d : ℕ) (hd : 0 < d) (a : Fin v → ℤ)
    (lo hi : ℝ → ℕ → Fin v → ℝ)
    (hb : ∀ α : ℝ,0 < α → ∃ c₀ C₀ : ℝ,0 < c₀ ∧ 0 < C₀ ∧ ∀ᶠ N : ℕ in atTop,
      (∀ i,c₀*L (F.state.subseq N) ≤ hi α N i-lo α N i) ∧
      (∀ i,-C₀*L (F.state.subseq N) ≤ lo α N i ∧ hi α N i ≤ C₀*L (F.state.subseq N)))
    (u : ℝ → ℕ → (Fin v → ℤ) → Finset ι → G) (u₀ : Finset ι → G)
    (hu : ∀ U∈𝓝 u₀,∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ∀ z∈integerBox v (lo α N) (hi α N),u α N z∈U)
    (f : C((Finset ι → G⧸Γ),ℂ)) :
    ∀ ε : ℝ,0 < ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ‖(𝔼 z∈integerBox v (lo α N) (hi α N),
        f (EmbeddedCubeHaar.haarImage F.state.domain.embed F.state.domain.filtration Γ
          (F.residue r) C.lattice C.le_induced (u α N z)
          (C.cubePoint N (fun i=>a (e i)+(d:ℤ)*z (e i)))))-
        (∫ x,EmbeddedCubeHaar.frozenTest F.state.domain.embed F.state.domain.continuous
          F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced f u₀ x
          ∂(C.haar (ι:=ι) : Measure (C.CubeSpace (ι:=ι))))‖ < ε := by
  apply CompactTwoScale.freezing (C.haar (ι:=ι) : Measure (C.CubeSpace (ι:=ι)))
    (EmbeddedCubeHaar.frozenTest F.state.domain.embed F.state.domain.continuous
      F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced f)
    (EmbeddedCubeHaar.frozenTest_continuous F.state.domain.embed F.state.domain.continuous
      F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced f)
    u₀ (fun α N=>integerBox v (lo α N) (hi α N))
    (fun _ N z=>C.cubePoint N (fun i=>a (e i)+(d:ℤ)*z (e i))) u ?_ hu
  intro α hα ε hε
  obtain ⟨c₀,C₀,hc₀,hC₀,hbox⟩:=hb α hα
  let f₀:=EmbeddedCubeHaar.frozenTest F.state.domain.embed F.state.domain.continuous
    F.state.domain.filtration Γ (F.residue r) C.lattice C.le_induced f u₀
  filter_upwards [C.haar_limit hL ht e c₀ C₀ hc₀ hC₀ d hd a {f₀} isCompact_singleton ε hε,
    hbox] with N hN hbN
  exact hN (lo α N) (hi α N) hbN.1 hbN.2 f₀ rfl

end AllLevelFactorization.Factorization.ResidueCover

end
end

end OAI
