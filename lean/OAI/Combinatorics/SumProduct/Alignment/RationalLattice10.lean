import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeLocal09
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators
end
end
 

 
section
noncomputable section
open scoped BigOperators Topology commutatorElement NNReal
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
 

theorem source_comparable_physical_cube_haar
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
    (cBox CBox C : ℝ) (hcBox : 0<cBox) (hCBox : 0<CBox) (hC : 0≤C)
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

    (L : ℝ≥0) (B : ℝ) :
    letI : MetricSpace (G⧸Λ) := MetricSpace.replaceTopology qmtr hqtop.symm
    let m : ProbabilityMeasure (Finset ι→G⧸Λ) :=
      imageProbability H Λ σ ⟨μ,inferInstance⟩ (fun _ => h β)
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,
      ∀ lo hi : Fin v→ℝ,
      (∀ i,(cBox*α)*(N:ℝ)≤hi i-lo i) →
      (∀ i,-CBox*(N:ℝ)≤lo i ∧ hi i≤CBox*(N:ℝ)) →
      (∀ b∈physicalResidueRectangle lo hi (sourceResidue e r₀) d₀,
        |((b (e none):ℝ)/(N:ℝ))-β|≤C*α ∧
        ∀ i : ι,|((b (e (some i)):ℝ)/(N:ℝ))|≤C*α) →
      ∀ F : C((Finset ι→G⧸Λ),ℂ),
      LipschitzWith L F → ‖F‖≤B →
      ‖(𝔼 b∈physicalResidueRectangle lo hi (sourceResidue e r₀) d₀,
          F (fun w : Finset ι => QuotientGroup.mk
            (P N (b (e none)+∑ i∈w,b (e (some i))))))-
        (∫ y,F y ∂(m:Measure (Finset ι→G⧸Λ)))‖<ε := by
  let : MetricSpace (G⧸Λ) := MetricSpace.replaceTopology qmtr hqtop.symm
  intro m
  have hd : 0<(d₀:ℝ) := by exact_mod_cast hd₀
  have hr : ∀ i : Fin v,0 ≤ sourceResidue e r₀ i ∧ sourceResidue e r₀ i<(d₀:ℤ) := by
    intro i
    have hd' : (0:ℤ)<d₀ := by exact_mod_cast hd₀
    have hr' : (r₀:ℤ)<d₀ := by exact_mod_cast hr₀
    unfold sourceResidue
    split_ifs
    · exact ⟨by positivity,hr'⟩
    · exact ⟨le_refl 0,hd'⟩
  let C' : ℝ := (CBox+(d₀:ℝ))/(d₀:ℝ)
  have hC' : 0<C' := div_pos (add_pos hCBox hd) hd
  have he := source_comparable_boxes_cube_haar c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ
    mtr htop qmtr hqtop μ a hirr d₀ r₀ hd₀ hr₀ β hβ
    (cBox/(d₀:ℝ)) C' C (div_pos hcBox hd) hC' hC
    g h hh ρ hρ hg P γ hfactor hperiod L B
  have hv (z : Fin v→ℤ) (w : Finset ι) :
      sourceResidue e r₀ (e none)+(d₀:ℤ)*z (e none)+
        ∑ i∈w,(sourceResidue e r₀ (e (some i))+(d₀:ℤ)*z (e (some i))) =
          sourceVertex e d₀ r₀ z w := by
    simp [sourceResidue,sourceVertex,mul_add,Finset.mul_sum,add_assoc]
  intro ε hε
  filter_upwards [he ε hε] with α hα
  filter_upwards [hα,Filter.eventually_ge_atTop (1:ℕ)] with N hN hN1
  intro lo hi hside habs hlocal F hL hB
  let lo' : Fin v→ℝ := fun i => (lo i-(sourceResidue e r₀ i:ℝ))/(d₀:ℝ)
  let hi' : Fin v→ℝ := fun i => (hi i-(sourceResidue e r₀ i:ℝ))/(d₀:ℝ)
  have hs' : ∀ i,((cBox/(d₀:ℝ))*α)*(N:ℝ)≤hi' i-lo' i := by
    intro i
    have hh := div_le_div_of_nonneg_right (hside i) hd.le
    dsimp only [hi',lo']
    have h₁ : ((cBox/(d₀:ℝ))*α)*(N:ℝ)=((cBox*α)*(N:ℝ))/(d₀:ℝ) := by ring
    have h₂ : (hi i-(sourceResidue e r₀ i:ℝ))/(d₀:ℝ)-
        (lo i-(sourceResidue e r₀ i:ℝ))/(d₀:ℝ)=(hi i-lo i)/(d₀:ℝ) := by ring
    rw [h₁,h₂]
    exact hh
  have ha' : ∀ i,-C'*(N:ℝ)≤lo' i ∧ hi' i≤C'*(N:ℝ) := by
    intro i
    have hn : (1:ℝ)≤N := by exact_mod_cast hN1
    have hr0 : (0:ℝ)≤(sourceResidue e r₀ i:ℝ) := by exact_mod_cast (hr i).1
    have hrd : (sourceResidue e r₀ i:ℝ)<(d₀:ℝ) := by exact_mod_cast (hr i).2
    dsimp only [lo',hi',C']
    rw [le_div_iff₀ hd,div_le_iff₀ hd]
    have hx : -((CBox+(d₀:ℝ))/(d₀:ℝ))*(N:ℝ)*(d₀:ℝ)=
        -(CBox+(d₀:ℝ))*(N:ℝ) := by field_simp
    have hy : ((CBox+(d₀:ℝ))/(d₀:ℝ))*(N:ℝ)*(d₀:ℝ)=
        (CBox+(d₀:ℝ))*(N:ℝ) := by field_simp
    rw [hx,hy]
    constructor <;> nlinarith [(habs i).1,(habs i).2]
  have hl' : ∀ z∈halfOpenBox v lo' hi',
      |(((sourceResidue e r₀ (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ))-β|≤C*α ∧
      ∀ i : ι,|(((sourceResidue e r₀ (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))|≤C*α := by
    intro z hz
    exact hlocal _ ((physicalResidueRectangle_affine lo hi (sourceResidue e r₀) d₀ hd₀ hr z).mpr hz)
  rw [physicalResidueRectangle_expect lo hi (sourceResidue e r₀) d₀ hd₀ hr]
  simp_rw [hv]
  exact hN lo' hi' hs' ha' hl' F hL hB

end CubeLocalHaar
end
end
 
 
end

section
 

 
noncomputable section
namespace RationalLattice
variable {G K : Type*} [Group G] [Group K] [TopologicalSpace G] [TopologicalSpace K]
variable {m n : ℕ}

lemma scaledCoordinates_rational (d : RealCoordinates K n) (w : Fin n → ℕ)
    (hpos : ∀ i,0<w i) (g : K) :
    IsRational (scaledCoordinates d w hpos) g ↔ IsRational d g := by
  constructor
  · intro hg i
    obtain ⟨q,hq⟩:=hg i
    refine ⟨(w i:ℚ)*q,?_⟩
    push_cast
    change (w i:ℝ)*q=d.coord g i
    change (q:ℝ)=d.coord g i/(w i:ℝ) at hq
    rw [hq]
    exact mul_div_cancel₀ _ (by exact_mod_cast (hpos i).ne')
  · intro hg i
    obtain ⟨q,hq⟩:=hg i
    refine ⟨q/(w i:ℚ),?_⟩
    push_cast
    change (q:ℝ)/(w i:ℝ)=d.coord g i/(w i:ℝ)
    rw [hq]

lemma secondCoordinates_rational [IsTopologicalGroup K] (d : RealCoordinates K n) (g : K) :
    IsRational (secondCoordinates d) g ↔ IsRational d g := by
  constructor
  · intro h
    have he:=expProduct_rational d h
    change IsRational d (expProduct d (expCoordinates d g)) at he
    rwa [expProduct_expCoordinates] at he
  · exact expCoordinates_rational d

variable (c : RealCoordinates G m) (d : RealCoordinates K n)
variable (F : K →* G)
variable (hpoly : ∀ i,RationalPolynomialMap.IsPolynomial
  (fun x : Fin n → ℝ => c.coord (F (d.coord.symm x)) i))

include hpoly in
lemma rationalHom_rational {g : K} (hg : IsRational d g) : IsRational c (F g) := by
  intro i
  obtain ⟨P,hP⟩:=hpoly i
  obtain ⟨q,hq⟩:=eval_rational P (d.coord g) hg
  refine ⟨q,?_⟩
  rw [hq,←hP]
  simp

variable [IsTopologicalGroup G] [IsTopologicalGroup K]
variable (Γ : Subgroup G)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (hc : Continuous F) (hinj : Function.Injective F)
include hpoly hΓ hc hinj in
 

theorem exists_integer_sublattice_rational :
    ∃ Λ : Subgroup K,∃ e : RealCoordinates K n,
      (∀ g : K,g∈Λ ↔ ∀ i,∃ z : ℤ,e.coord g i=z) ∧
      Λ≤Γ.comap F ∧ (Λ.subgroupOf (Γ.comap F)).FiniteIndex ∧
      (∀ g : K,∀ i,e.coord g i=0 ↔ d.coord g i=0) ∧
      (∀ g : K,IsRational e g ↔ IsRational d g) := by
  classical
  obtain ⟨E,hE,hgrid⟩:=rationalHom_origin_grid c d F hpoly
  obtain ⟨w,hpos,hEw,hw⟩:=exists_lattice_weights d E hE
  let Λ:=weightedLattice d w hw
  let e:=scaledCoordinates d w hpos
  have hΛ : ∀ g : K,g∈Λ ↔ ∀ i,∃ z : ℤ,e.coord g i=z :=
    weightedLattice_iff d w hw hpos
  have hle : Λ≤Γ.comap F := by
    intro g hg
    apply (hΓ (F g)).mpr
    have hx : ∀ j,∃ z : ℤ,d.coord g j=(E:ℝ)*(z:ℝ) := by
      intro j
      obtain ⟨a,ha⟩:=hg j
      obtain ⟨b,hb⟩:=hEw j
      refine ⟨(b:ℤ)*a,?_⟩
      rw [ha,hb]
      push_cast
      ring
    simpa using hgrid (d.coord g) hx
  let : T2Space K:=d.coord.symm.t2Space
  let : DiscreteTopology Γ:=integerCoordinates_discrete c Γ hΓ
  let : DiscreteTopology (Γ.comap F):=
    DiscreteTopology.preimage_of_continuous_injective (Γ:Set G) hc hinj
  obtain ⟨C,hC,hrep⟩:=compact_reps_of_integerCoordinates e Λ hΛ
  have hi:=TriangularDenominators.finiteIndex_of_compact_reps Λ (Γ.comap F) hle C hC hrep
  refine ⟨Λ,e,hΛ,hle,hi,?_,scaledCoordinates_rational d w hpos⟩
  intro g i
  change d.coord g i/(w i:ℝ)=0 ↔ d.coord g i=0
  rw [div_eq_zero_iff]
  have hn : (w i:ℝ)≠0 := by exact_mod_cast (hpos i).ne'
  simp [hn]

end RationalLattice

end
end
end
end

end OAI
