import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeLocal02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators Topology commutatorElement NNReal
end
end
 

 
section

noncomputable section
open scoped BigOperators Topology
namespace FiniteHaarTests
open Filter MeasureTheory
variable {X P κ : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [TopologicalSpace P]
variable (μ : Measure X) [IsProbabilityMeasure μ]

 

theorem two_scale_freezing_uniform (F : P→C(X,ℂ)) (hF : Continuous F) (a₀ : P)
    (J : ℝ→ℕ→Type*)
    (T : ∀ α N,J α N→Finset κ) (p : ∀ α N,J α N→κ→X)
    (a : ∀ α N,J α N→κ→P)
    (hbase : ∀ α : ℝ,0<α → ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖discrepancy μ (T α N j) (p α N j) (F a₀)‖<ε)
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

end FiniteHaarTests
end
end
 

 
section
noncomputable section
open scoped BigOperators Topology commutatorElement
namespace CubeLocalHaar
open CubeFaces LeibmanSquare CubeTaylorExpansion CubeHorizontalIrrationality
open RationalLattice MeasureTheory Filter ComparableBoxLeibman MalcevCharacters AbelianMalcevTorus
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n t d v : ℕ} (c : RealCoordinates G n) (H : Filtration G)
variable (S : ℕ→Set (Fin n))
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i∈S k,c.coord g i=0)
variable (Λ : Subgroup G) (σ : G) (h01 : H.level 0=H.level 1)
variable (s : ℕ) (hs : H.level (s+1)=⊥) (e : Option ι≃Fin v)
variable (cc : RealCoordinates (cube H (Finset.univ : Finset ι) 0) (t+d))
variable (hsk : SecondKind cc)
variable (q : ℕ→ℕ) (hqbound : ∀ k,q k ≤ t+d)
variable (hq : ∀ k (g : cube H (Finset.univ : Finset ι) 0),
  g∈(CubeMaxFiltration.filtration H Finset.univ).level k ↔
    ∀ i : Fin (t+d),i.val < q k → cc.coord g i=0)
variable (hΓ : ∀ g : cube H (Finset.univ : Finset ι) 0,
  g∈cubeLattice H (conjugateLattice Λ σ) ↔ ∀ i,∃ z : ℤ,cc.coord g i=z)
variable [MeasurableSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))]
variable [hBorel : @BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)) (QuotientGroup.instTopologicalSpace (cubeLattice H (conjugateLattice Λ σ))) inferInstance]
variable (mtr : MetricSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)))
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace (cubeLattice H (conjugateLattice Λ σ)))

include h01 hs hsk hqbound hq hΓ htop in
 

theorem two_scale_cube_haar_uniform
    (μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)))
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure (cube H (Finset.univ : Finset ι) 0) _ μ]
    (a : ℕ→∀ k : ℕ,H.level k)
    (hirr : ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
      ξ≠1 → Continuous ξ → RationalCharacter (conjugateLattice Λ σ) ξ →
      (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
      Tendsto (fun N : ℕ => ‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(N:ℝ)^j)
        atTop atTop)

    (d₀ : ℕ) (hd₀ : 0<d₀) (r : Fin v→ℤ)
    (J : ℝ→ℕ→Type*)
    (lo hi : ∀ α N,J α N→Fin v→ℝ)
    (hb : ∀ α : ℝ,0<α → ∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧
      ∀ᶠ N : ℕ in atTop,∀ j : J α N,
        (∀ i,c₀*(N:ℝ)≤hi α N j i-lo α N j i) ∧
        (∀ i,-C₀*(N:ℝ)≤lo α N j i ∧ hi α N j i≤C₀*(N:ℝ)))
    (u : ∀ α N,J α N→(Fin v→ℤ)→Finset ι→G) (u₀ : Finset ι→G)
    (hu : ∀ U∈𝓝 u₀,∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈integerBox v (lo α N j) (hi α N j),u α N j z∈U)
    (F : C((Finset ι→G⧸Λ),ℂ)) :
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 z∈integerBox v (lo α N j) (hi α N j),
          F (haarImage H Λ σ (u α N j z) (QuotientGroup.mk
            (cubePolynomial c H S hH (a N) s
              (fun i => ((r (e i)+(d₀:ℤ)*z (e i):ℤ):ℝ))))))-
        (∫ x,frozenTest H Λ σ F u₀ x ∂μ)‖<ε := by
  let : MetricSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)) :=
    MetricSpace.replaceTopology mtr htop.symm
  let : CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)) :=
    metric_compact cc (cubeLattice H (conjugateLattice Λ σ)) hΓ inferInstance rfl
  let p : ∀ α N,J α N→(Fin v→ℤ)→((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)) :=
    fun _ N _ z => QuotientGroup.mk (cubePolynomial c H S hH (a N) s
      (fun i => ((r (e i)+(d₀:ℤ)*z (e i):ℤ):ℝ)))
  apply FiniteHaarTests.two_scale_freezing_uniform μ (frozenTest H Λ σ F)
    (frozenTest_continuous H Λ σ F) u₀ J
    (fun α N j => integerBox v (lo α N j) (hi α N j)) p u _ hu
  intro α hα ε hε
  obtain ⟨c₀,C₀,hc₀,hC₀,hbox⟩ := hb α hα
  have he := haar_limit_compact c H S hH (conjugateLattice Λ σ) h01 s hs e cc hsk q hqbound hq hΓ
    rfl μ a hirr c₀ C₀ hc₀ hC₀ d₀ hd₀ r
    {frozenTest H Λ σ F u₀} isCompact_singleton ε hε
  filter_upwards [he,hbox] with N he hbox
  intro j
  have hbox := hbox j
  exact he (lo α N j) (hi α N j) hbox.1 hbox.2 _ (Set.mem_singleton _)

end CubeLocalHaar
end
end
 

 
section

noncomputable section
open scoped Topology BigOperators
open Filter
namespace CubeLocalHaar

 

theorem smooth_local_freezing_uniform {G κ τ : Type*} [PseudoMetricSpace G] [Fintype τ]
    (g : ℕ→ℝ→G) (h : ℝ→G) (β : ℝ) (hh : ContinuousAt h β)
    (ρ : ℝ) (hρ : 0<ρ)
    (hg : ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,
      ∀ t : ℝ,dist t β<ρ → dist (g N t) (h t)<ε)
    (J : ℝ→ℕ→Type*)
    (T : ∀ α N,J α N→Finset κ) (t : ∀ α N,J α N→κ→τ→ℝ) (C : ℝ)
    (ht : ∀ α : ℝ,0<α → ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈T α N j,∀ w,dist (t α N j z w) β≤C*α) :
    ∀ U∈𝓝 (fun _ : τ => h β),∀ᶠ α : ℝ in 𝓝[>] 0,
      ∀ᶠ N : ℕ in atTop,∀ j : J α N,∀ z∈T α N j,(fun w => g N (t α N j z w))∈U := by
  intro U hU
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  have hε2 : 0<ε/2 := by positivity
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp hh (ε/2) hε2
  have hlim : Tendsto (fun α : ℝ => C*α) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun α : ℝ => C*α) := continuous_const.mul continuous_id
    simpa only [mul_zero] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  filter_upwards [hlim.eventually_lt_const (lt_min hδ hρ),
    (self_mem_nhdsWithin : Set.Ioi (0:ℝ)∈𝓝[>] 0)] with α hα ha
  filter_upwards [hg (ε/2) hε2,ht α ha] with N hgN htN
  intro j z hz
  apply hball
  rw [Metric.mem_ball,dist_pi_lt_iff hε]
  intro w
  have hd := (htN j z hz w).trans_lt hα
  have hg' := hgN (t α N j z w) ((lt_min_iff.mp hd).2)
  have hh' := hcont ((lt_min_iff.mp hd).1)
  exact (dist_triangle _ _ _).trans_lt (by linarith only [hg',hh'])

end CubeLocalHaar
end
end
 

 
section
noncomputable section
open scoped BigOperators Topology commutatorElement
namespace CubeLocalHaar
open CubeFaces LeibmanSquare CubeTaylorExpansion CubeHorizontalIrrationality
open RationalLattice MeasureTheory Filter ComparableBoxLeibman MalcevCharacters AbelianMalcevTorus
variable {G ι : Type} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n t d v : ℕ} (c : RealCoordinates G n) (H : Filtration G)
variable (S : ℕ→Set (Fin n))
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i∈S k,c.coord g i=0)
variable (Λ : Subgroup G) (σ : G) (h01 : H.level 0=H.level 1)
variable (s : ℕ) (hs : H.level (s+1)=⊥) (e : Option ι≃Fin v)
variable (cc : RealCoordinates (cube H (Finset.univ : Finset ι) 0) (t+d))
variable (hsk : SecondKind cc)
variable (q : ℕ→ℕ) (hqbound : ∀ k,q k ≤ t+d)
variable (hq : ∀ k (g : cube H (Finset.univ : Finset ι) 0),
  g∈(CubeMaxFiltration.filtration H Finset.univ).level k ↔
    ∀ i : Fin (t+d),i.val < q k → cc.coord g i=0)
variable (hΓ : ∀ g : cube H (Finset.univ : Finset ι) 0,
  g∈cubeLattice H (conjugateLattice Λ σ) ↔ ∀ i,∃ z : ℤ,cc.coord g i=z)
variable [MeasurableSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))]
variable [hBorel : @BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)) (QuotientGroup.instTopologicalSpace (cubeLattice H (conjugateLattice Λ σ))) inferInstance]
variable (mtr : MetricSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)))
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace (cubeLattice H (conjugateLattice Λ σ)))

include S hH h01 hs hsk hqbound hq hΓ htop in
 

theorem smooth_cube_haar_uniform
    (μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)))
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure (cube H (Finset.univ : Finset ι) 0) _ μ]
    (a : ℕ→∀ k : ℕ,H.level k)
    (hirr : ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
      ξ≠1 → Continuous ξ → RationalCharacter (conjugateLattice Λ σ) ξ →
      (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
      Tendsto (fun N : ℕ => ‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(N:ℝ)^j)
        atTop atTop)

    (d₀ : ℕ) (hd₀ : 0<d₀) (r : Fin v→ℤ)
    (J : ℝ→ℕ→Type*)
    (lo hi : ∀ α N,J α N→Fin v→ℝ)
    (hb : ∀ α : ℝ,0<α → ∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧
      ∀ᶠ N : ℕ in atTop,∀ j : J α N,
        (∀ i,c₀*(N:ℝ)≤hi α N j i-lo α N j i) ∧
        (∀ i,-C₀*(N:ℝ)≤lo α N j i ∧ hi α N j i≤C₀*(N:ℝ)))

    (C : ℝ) (hC : 0≤C)
    (g : ℕ→ℝ→G) (h : ℝ→G) (β : ℝ) (hh : ContinuousAt h β)
    (ρ : ℝ) (hρ : 0<ρ)
    (hg : ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,
      ∀ t : ℝ,dist t β<ρ → dist (g N t) (h t)<ε)
    (hgeo : ∀ α : ℝ,0<α → ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈integerBox v (lo α N j) (hi α N j),
        |(((r (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ))-β|≤C*α ∧
        ∀ i : ι,|(((r (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))|≤C*α)
    (F : C((Finset ι→G⧸Λ),ℂ)) :
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 z∈integerBox v (lo α N j) (hi α N j),
          F (fun w : Finset ι => QuotientGroup.mk
            (g N (((r (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ)+
                ∑ i∈w,(((r (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))) *
              taylorPolynomial c H (a N) s
                (((r (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)+
                  ∑ i∈w,((r (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)) * σ)))-
        (∫ x,frozenTest H Λ σ F (fun _ => h β) x ∂μ)‖<ε := by
  let T : ∀ α N,J α N→Finset (Fin v→ℤ) := fun α N j => integerBox v (lo α N j) (hi α N j)
  let b : (Fin v→ℤ)→Option ι→ℝ := fun z i => ((r (e i)+(d₀:ℤ)*z (e i):ℤ):ℝ)
  let t : ∀ α N,J α N→(Fin v→ℤ)→Finset ι→ℝ :=
    fun _ N _ z w => b z none/(N:ℝ)+∑ i∈w,b z (some i)/(N:ℝ)
  have ht : ∀ α : ℝ,0<α → ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈T α N j,∀ w,dist (t α N j z w) β≤((1+(Fintype.card ι:ℝ))*C)*α := by
    intro α hα
    filter_upwards [hgeo α hα] with N hN
    intro j z hz w
    simpa only [mul_assoc] using normalized_vertex_close (fun i => b z i/(N:ℝ)) β (C*α) (mul_nonneg hC hα.le)
      (hN j z hz).1 (hN j z hz).2 w
  have hu := smooth_local_freezing_uniform g h β hh ρ hρ hg J T t ((1+(Fintype.card ι:ℝ))*C) ht
  have hlimit := two_scale_cube_haar_uniform c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ mtr htop
    μ a hirr d₀ hd₀ r J lo hi hb (fun α N j z w => g N (t α N j z w)) (fun _ => h β) hu F
  have himage (α : ℝ) (N : ℕ) (j : J α N) (z : Fin v→ℤ) :
      haarImage H Λ σ (fun w => g N (t α N j z w))
        (QuotientGroup.mk (cubePolynomial c H S hH (a N) s (b z))) =
      fun w : Finset ι => QuotientGroup.mk
        (g N (t α N j z w)*taylorPolynomial c H (a N) s
          (b z none+∑ i∈w,b z (some i))*σ) := by
    funext w
    rw [haarImage_mk,cubePolynomial_vertex]
  change ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 z∈integerBox v (lo α N j) (hi α N j),
        F (haarImage H Λ σ (fun w => g N (t α N j z w))
          (QuotientGroup.mk (cubePolynomial c H S hH (a N) s (b z)))))-
        (∫ x,frozenTest H Λ σ F (fun _ => h β) x ∂μ)‖<ε at hlimit
  simp_rw [himage] at hlimit
  exact hlimit

end CubeLocalHaar

end
end
end
end
end

end OAI
