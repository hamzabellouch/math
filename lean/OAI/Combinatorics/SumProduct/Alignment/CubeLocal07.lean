import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeLocal03
import OAI.Combinatorics.SumProduct.Alignment.CubeLocal06
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators Topology commutatorElement
end
end
 

 
section
noncomputable section
open scoped Topology
open Filter
namespace ComparableBoxLeibman
 

lemma halfOpen_bounds_uniform {v : ℕ} (c C : ℝ) (hc : 0<c)
    (J : ℕ→Type*) (lo hi : ∀ N,J N→Fin v→ℝ)
    (hb : ∀ᶠ N : ℕ in atTop,∀ j : J N,
      (∀ i,c*(N:ℝ)≤hi N j i-lo N j i) ∧
      (∀ i,-C*(N:ℝ)≤lo N j i ∧ hi N j i≤C*(N:ℝ))) :
    ∀ᶠ N : ℕ in atTop,∀ j : J N,
      (∀ i,(c/2)*(N:ℝ)≤((⌈hi N j i⌉:ℝ)-1)-lo N j i) ∧
      (∀ i,-C*(N:ℝ)≤lo N j i ∧ ((⌈hi N j i⌉:ℝ)-1)≤C*(N:ℝ)) := by
  have hn : ∀ᶠ N : ℕ in atTop,2/c≤(N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2/c))
  filter_upwards [hb,hn] with N hN hn
  have hn' : 2≤c*(N:ℝ) := by
    have := (div_le_iff₀ hc).mp hn
    nlinarith
  intro j
  have hN := hN j
  constructor
  · intro i
    have hh := Int.le_ceil (hi N j i)
    have hh' := hN.1 i
    nlinarith
  · intro i
    refine ⟨(hN.2 i).1,?_⟩
    have hh := Int.ceil_lt_add_one (hi N j i)
    have hh' := (hN.2 i).2
    linarith

end ComparableBoxLeibman
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
 

theorem smooth_halfOpen_cube_haar_uniform
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
      ∀ j : J α N,∀ z∈halfOpenBox v (lo α N j) (hi α N j),
        |(((r (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ))-β|≤C*α ∧
        ∀ i : ι,|(((r (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))|≤C*α)
    (F : C((Finset ι→G⧸Λ),ℂ)) :
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 z∈halfOpenBox v (lo α N j) (hi α N j),
          F (fun w : Finset ι => QuotientGroup.mk
            (g N (((r (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ)+
                ∑ i∈w,(((r (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))) *
              taylorPolynomial c H (a N) s
                (((r (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)+
                  ∑ i∈w,((r (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)) * σ)))-
        (∫ x,frozenTest H Λ σ F (fun _ => h β) x ∂μ)‖<ε := by
  have hb' : ∀ α : ℝ,0<α → ∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧
      ∀ᶠ N : ℕ in atTop,∀ j : J α N,
        (∀ i,c₀*(N:ℝ)≤((⌈hi α N j i⌉:ℝ)-1)-lo α N j i) ∧
        (∀ i,-C₀*(N:ℝ)≤lo α N j i ∧ ((⌈hi α N j i⌉:ℝ)-1)≤C₀*(N:ℝ)) := by
    intro α hα
    obtain ⟨c₀,C₀,hc₀,hC₀,hbα⟩ := hb α hα
    exact ⟨c₀/2,C₀,by positivity,hC₀,halfOpen_bounds_uniform c₀ C₀ hc₀ (J α) (lo α) (hi α) hbα⟩
  exact smooth_cube_haar_uniform c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ mtr htop
    μ a hirr d₀ hd₀ r J lo (fun α N j i => (⌈hi α N j i⌉:ℝ)-1) hb'
    C hC g h β hh ρ hρ hg hgeo F

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
 

theorem source_box_family_local_cube_haar
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

    (d₀ r₀ : ℕ) (hd₀ : 0<d₀) :
    r₀<d₀ → ∀ β : ℝ, β∈Set.Icc (0:ℝ) 1 →
    ∀ (J : ℝ→ℕ→Type*) (lo hi : ∀ α N,J α N→Fin v→ℝ),
    (∀ α : ℝ,0<α → ∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧
      ∀ᶠ N : ℕ in atTop,∀ j : J α N,
        (∀ i,c₀*(N:ℝ)≤hi α N j i-lo α N j i) ∧
        (∀ i,-C₀*(N:ℝ)≤lo α N j i ∧ hi α N j i≤C₀*(N:ℝ))) →
    ∀ C : ℝ, 0≤C →
    (∀ α : ℝ,0<α → ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈halfOpenBox v (lo α N j) (hi α N j),
        |(((sourceResidue e r₀ (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ))-β|≤C*α ∧
        ∀ i : ι,|(((sourceResidue e r₀ (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))|≤C*α) →
    ∀ (g : ℕ→ℝ→G) (h : ℝ→G), ContinuousAt h β →
    ∀ ρ : ℝ, 0<ρ →
    (∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,
      ∀ t : ℝ,dist t β<ρ → dist (g N t) (h t)<ε) →

    ∀ F : C((Finset ι→G⧸Λ),ℂ),
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 z∈halfOpenBox v (lo α N j) (hi α N j),
          F (fun w : Finset ι => QuotientGroup.mk
            (g N ((sourceVertex e d₀ r₀ z w:ℝ)/(N:ℝ)) *
              taylorPolynomial c H (a N) s (sourceVertex e d₀ r₀ z w:ℝ) * σ)))-
        (∫ x,frozenTest H Λ σ F (fun _ => h β) x ∂μ)‖<ε := by
  intro _ β _ J lo hi hb C hC hgeo g h hh ρ hρ hg F
  have he := smooth_halfOpen_cube_haar_uniform c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ mtr htop
    μ a hirr d₀ hd₀ (sourceResidue e r₀) J lo hi hb C hC
    g h β hh ρ hρ hg hgeo F
  simpa only [sourceVertex_real,sourceVertex_normalized] using he

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

variable [MeasurableSpace (G⧸Λ)] [BorelSpace (G⧸Λ)]
variable [SecondCountableTopology (G⧸Λ)]

include S hH h01 hs hsk hqbound hq hΓ htop in
 

theorem source_box_family_factored_cube_haar
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

    (d₀ r₀ : ℕ) (hd₀ : 0<d₀) (hr₀ : r₀<d₀)
    (β : ℝ) (hβ : β∈Set.Icc (0:ℝ) 1)
    (J : ℝ→ℕ→Type*) (lo hi : ∀ α N,J α N→Fin v→ℝ)
    (hb : ∀ α : ℝ,0<α → ∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧
      ∀ᶠ N : ℕ in atTop,∀ j : J α N,
        (∀ i,c₀*(N:ℝ)≤hi α N j i-lo α N j i) ∧
        (∀ i,-C₀*(N:ℝ)≤lo α N j i ∧ hi α N j i≤C₀*(N:ℝ)))
    (C : ℝ) (hC : 0≤C)
    (hgeo : ∀ α : ℝ,0<α → ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈halfOpenBox v (lo α N j) (hi α N j),
        |(((sourceResidue e r₀ (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ))-β|≤C*α ∧
        ∀ i : ι,|(((sourceResidue e r₀ (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))|≤C*α)
    (g : ℕ→ℝ→G) (h : ℝ→G) (hh : ContinuousAt h β)
    (ρ : ℝ) (hρ : 0<ρ)
    (hg : ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,
      ∀ t : ℝ,dist t β<ρ → dist (g N t) (h t)<ε)

    (P γ : ℕ→ℤ→G)
    (hfactor : ∀ N : ℕ,∀ b : ℤ,
      QuotientGroup.mk (P N b) = (QuotientGroup.mk
        (g N ((b:ℝ)/(N:ℝ))*taylorPolynomial c H (a N) s (b:ℝ)*γ N b) : G⧸Λ))
    (hperiod : ∀ N : ℕ,∀ b : ℤ,b%(d₀:ℤ)=(r₀:ℤ) →
      QuotientGroup.mk (γ N b)=(QuotientGroup.mk σ:G⧸Λ))
    (F : C((Finset ι→G⧸Λ),ℂ)) :
    let m : ProbabilityMeasure (Finset ι→G⧸Λ) :=
      imageProbability H Λ σ ⟨μ,inferInstance⟩ (fun _ => h β)
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ j : J α N,
      ‖(𝔼 z∈halfOpenBox v (lo α N j) (hi α N j),
          F (fun w : Finset ι => QuotientGroup.mk (P N (sourceVertex e d₀ r₀ z w))))-
        (∫ y,F y ∂(m:Measure (Finset ι→G⧸Λ)))‖<ε := by
  let : CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)) := by
    let := MetricSpace.replaceTopology mtr htop.symm
    exact metric_compact cc (cubeLattice H (conjugateLattice Λ σ)) hΓ inferInstance rfl
  intro m
  have hm : (∫ y,F y ∂(m:Measure (Finset ι→G⧸Λ))) =
      ∫ x,frozenTest H Λ σ F (fun _ => h β) x ∂μ :=
    integral_imageProbability H Λ σ ⟨μ,inferInstance⟩ (fun _ => h β) F
  rw [hm]
  have hv (N : ℕ) (z : Fin v→ℤ) (w : Finset ι) :
      QuotientGroup.mk (P N (sourceVertex e d₀ r₀ z w)) =
      (QuotientGroup.mk (g N ((sourceVertex e d₀ r₀ z w:ℝ)/(N:ℝ))*
        taylorPolynomial c H (a N) s (sourceVertex e d₀ r₀ z w:ℝ)*σ):G⧸Λ) := by
    rw [hfactor]
    exact congrArg (fun x : G⧸Λ =>
      (g N ((sourceVertex e d₀ r₀ z w:ℝ)/(N:ℝ))*
        taylorPolynomial c H (a N) s (sourceVertex e d₀ r₀ z w:ℝ)) • x)
      (hperiod N _ (sourceVertex_emod e d₀ r₀ hr₀ z w))
  simp_rw [hv]
  exact source_box_family_local_cube_haar c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ mtr htop
    μ a hirr d₀ r₀ hd₀ hr₀ β hβ J lo hi hb C hC hgeo g h hh ρ hρ hg F

end CubeLocalHaar

end
end
end
end
end

end OAI
