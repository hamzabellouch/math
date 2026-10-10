import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeLocal03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped Topology
open Filter
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
 

theorem source_local_cube_haar
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
    (g : ℕ→ℝ→G) (h : ℝ→G) (hh : ContinuousAt h β)
    (ρ : ℝ) (hρ : 0<ρ)
    (hg : ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,
      ∀ t : ℝ,dist t β<ρ → dist (g N t) (h t)<ε)

    (F : C((Finset ι→G⧸Λ),ℂ)) :
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ‖(𝔼 z∈halfOpenBox v
          (progressionLo (sourceCenter e β) (sourceResidue e r₀) d₀ N)
          (progressionHi (sourceCenter e β) (sourceResidue e r₀) d₀ α N),
          F (fun w : Finset ι => QuotientGroup.mk
            (g N ((sourceVertex e d₀ r₀ z w:ℝ)/(N:ℝ)) *
              taylorPolynomial c H (a N) s (sourceVertex e d₀ r₀ z w:ℝ) * σ)))-
        (∫ x,frozenTest H Λ σ F (fun _ => h β) x ∂μ)‖<ε := by
  have he := smooth_halfOpen_cube_haar c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ mtr htop
    μ a hirr d₀ hd₀ (sourceResidue e r₀)
    (fun _ N => progressionLo (sourceCenter e β) (sourceResidue e r₀) d₀ N)
    (fun α N => progressionHi (sourceCenter e β) (sourceResidue e r₀) d₀ α N)
    (fun α hα => source_box_bounds e β hβ d₀ r₀ hd₀ hr₀ α hα)
    g h β hh ρ hρ hg (fun α _ => source_box_geometry e β d₀ r₀ hd₀ α) F
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
 

theorem source_factored_cube_haar
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
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ‖(𝔼 z∈halfOpenBox v
          (progressionLo (sourceCenter e β) (sourceResidue e r₀) d₀ N)
          (progressionHi (sourceCenter e β) (sourceResidue e r₀) d₀ α N),
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
  exact source_local_cube_haar c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ mtr htop
    μ a hirr d₀ r₀ hd₀ hr₀ β hβ g h hh ρ hρ hg F

end CubeLocalHaar
end
end
 

 
section

noncomputable section
open scoped Topology BigOperators
namespace FiniteHaarTests
open Filter MeasureTheory
variable {X κ : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

 

theorem compact_two_scale
    (T : ℝ→ℕ→Finset κ) (p : ℝ→ℕ→κ→X)
    (hl : ∀ F : C(X,ℂ),∀ ε : ℝ,0<ε →
      ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
        ‖discrepancy μ (T α N) (p α N) F‖<ε)
    (K : Set C(X,ℂ)) (hK : IsCompact K) :
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ∀ F∈K,‖discrepancy μ (T α N) (p α N) F‖<ε := by
  intro ε hε
  obtain ⟨S,hS,η,hη,htest⟩ := CompactFamilyDescent.finite_unit_lipschitz_obstruction
    K hK ε 2 hε (by norm_num)
  have hα : ∀ᶠ α : ℝ in 𝓝[>] 0,∀ F∈S,∀ᶠ N : ℕ in atTop,
      ‖discrepancy μ (T α N) (p α N) F‖<η :=
    (Filter.eventually_all_finset S).mpr (fun F _ => hl F η hη)
  filter_upwards [hα] with α hα
  have hN : ∀ᶠ N : ℕ in atTop,∀ F∈S,
      ‖discrepancy μ (T α N) (p α N) F‖<η :=
    (Filter.eventually_all_finset S).mpr hα
  filter_upwards [hN] with N hN
  intro F hF
  by_contra he
  obtain ⟨φ,hφ,hdisc⟩ := htest (discrepancy μ (T α N) (p α N))
    (discrepancy_bound μ (T α N) (p α N)) ⟨F,hF,le_of_not_gt he⟩
  exact (not_le_of_gt (hN φ hφ)) hdisc

end FiniteHaarTests
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

variable [CompactSpace (G⧸Λ)]
variable (qmtr : MetricSpace (G⧸Λ))
variable (hqtop : qmtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Λ)

include S hH h01 hs hsk hqbound hq hΓ htop hqtop in
 

theorem source_compact_cube_haar
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

    (K : Set C((Finset ι→G⧸Λ),ℂ)) (hK : IsCompact K) :
    let m : ProbabilityMeasure (Finset ι→G⧸Λ) :=
      imageProbability H Λ σ ⟨μ,inferInstance⟩ (fun _ => h β)
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ F∈K,
      ‖(𝔼 z∈halfOpenBox v
          (progressionLo (sourceCenter e β) (sourceResidue e r₀) d₀ N)
          (progressionHi (sourceCenter e β) (sourceResidue e r₀) d₀ α N),
          F (fun w : Finset ι => QuotientGroup.mk (P N (sourceVertex e d₀ r₀ z w))))-
        (∫ y,F y ∂(m:Measure (Finset ι→G⧸Λ)))‖<ε := by
  let : MetricSpace (G⧸Λ) := MetricSpace.replaceTopology qmtr hqtop.symm
  intro m
  apply FiniteHaarTests.compact_two_scale (m:Measure (Finset ι→G⧸Λ))
    (fun α N => halfOpenBox v
      (progressionLo (sourceCenter e β) (sourceResidue e r₀) d₀ N)
      (progressionHi (sourceCenter e β) (sourceResidue e r₀) d₀ α N))
    (fun _ N z w => QuotientGroup.mk (P N (sourceVertex e d₀ r₀ z w))) _ K hK
  intro F
  exact source_factored_cube_haar c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ mtr htop
    μ a hirr d₀ r₀ hd₀ hr₀ β hβ g h hh ρ hρ hg P γ hfactor hperiod F

end CubeLocalHaar

end
end
end
end
end

end OAI
