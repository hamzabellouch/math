import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeFaces02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped Topology commutatorElement
end
end
 

 
section

noncomputable section
open scoped Topology
namespace CubeLocalHaar
open CubeFaces MeasureTheory
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]

 
def conjugateLattice (Λ : Subgroup G) (σ : G) : Subgroup G :=
  Λ.comap (MulAut.conj σ⁻¹).toMonoidHom

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma mem_conjugateLattice [TopologicalSpace G] [IsTopologicalGroup G]
    (Λ : Subgroup G) (σ g : G) :
    g∈conjugateLattice Λ σ ↔ σ⁻¹*g*σ∈Λ := by
  simp [conjugateLattice,mul_assoc]

 

def baseImage (H : Filtration G) (Λ : Subgroup G) (σ : G) :
    ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)) →
      (Finset ι→G⧸Λ) :=
  Quotient.lift (fun g w => QuotientGroup.mk ((g.val w)*σ)) (by
    intro g h he
    funext w
    apply QuotientGroup.eq.mpr
    have hh := (QuotientGroup.leftRel_apply.mp he) w
    change (g.val w)⁻¹*h.val w∈conjugateLattice Λ σ at hh
    simpa only [mem_conjugateLattice,mul_inv_rev,inv_inv,mul_assoc] using hh)

@[simp] lemma baseImage_mk (H : Filtration G) (Λ : Subgroup G) (σ : G)
    (g : cube H (Finset.univ : Finset ι) 0) (w : Finset ι) :
    baseImage H Λ σ (QuotientGroup.mk g) w=QuotientGroup.mk (g.val w*σ) := rfl

lemma baseImage_continuous (H : Filtration G) (Λ : Subgroup G) (σ : G) :
    Continuous (baseImage (ι := ι) H Λ σ) := by
  apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
  apply continuous_pi
  intro w
  exact QuotientGroup.continuous_mk.comp
    (((continuous_apply w).comp continuous_subtype_val).mul continuous_const)

lemma baseImage_injective (H : Filtration G) (Λ : Subgroup G) (σ : G) :
    Function.Injective (baseImage (ι := ι) H Λ σ) := by
  intro x y he
  induction x using Quotient.inductionOn with | h g =>
    induction y using Quotient.inductionOn with | h h =>
      apply QuotientGroup.eq.mpr
      intro w
      have hh := QuotientGroup.eq.mp (congrFun he w)
      change (g.val w*σ)⁻¹*(h.val w*σ)∈Λ at hh
      change (g.val w)⁻¹*h.val w∈conjugateLattice Λ σ
      simpa only [mem_conjugateLattice,mul_inv_rev,inv_inv,mul_assoc] using hh

 

def haarImage (H : Filtration G) (Λ : Subgroup G) (σ : G) (a : Finset ι→G)
    (x : (cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)) :
    Finset ι→G⧸Λ := fun w => a w • baseImage H Λ σ x w

@[simp] lemma haarImage_mk (H : Filtration G) (Λ : Subgroup G) (σ : G)
    (a : Finset ι→G) (g : cube H (Finset.univ : Finset ι) 0) (w : Finset ι) :
    haarImage H Λ σ a (QuotientGroup.mk g) w=QuotientGroup.mk (a w*g.val w*σ) := by
  change QuotientGroup.mk (a w*(g.val w*σ))=QuotientGroup.mk (a w*g.val w*σ)
  rw [mul_assoc]

lemma haarImage_continuous (H : Filtration G) (Λ : Subgroup G) (σ : G) :
    Continuous (fun p : (Finset ι→G)×
      ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)) =>
        haarImage H Λ σ p.1 p.2) := by
  apply continuous_pi
  intro w
  exact ((continuous_apply w).comp continuous_fst).smul
    ((continuous_apply w).comp ((baseImage_continuous H Λ σ).comp continuous_snd))

end CubeLocalHaar
end
end
 

 
section

noncomputable section
open scoped BigOperators Topology
namespace FiniteHaarTests
open MeasureTheory Filter
variable {X κ : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

def discrepancy (T : Finset κ) (p : κ→X) : C(X,ℂ)→ₗ[ℂ]ℂ where
  toFun F := (𝔼 z∈T,F (p z))-(∫ x,F x ∂μ)
  map_add' F G := by
    change (𝔼 z∈T,(F (p z)+G (p z)))-(∫ x,F x+G x ∂μ)=_
    rw [Finset.expect_add_distrib,integral_add
      (F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F))
      (G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace G))]
    ring
  map_smul' z F := by
    change (𝔼 x∈T,z • F (p x))-(∫ x,z • F x ∂μ)=_
    rw [←Finset.smul_expect,integral_smul]
    simp only [RingHom.id_apply,smul_sub]

lemma discrepancy_bound (T : Finset κ) (p : κ→X) (F : C(X,ℂ)) :
    ‖discrepancy μ T p F‖≤2*‖F‖ := by
  have hm : ‖𝔼 z∈T,F (p z)‖≤‖F‖ := by
    by_cases hT : T.Nonempty
    · exact (RCLike.norm_expect_le (K := ℂ)).trans
        (Finset.expect_le hT (fun _ _ => F.norm_coe_le_norm _))
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.expect_empty,norm_zero]
      exact norm_nonneg _
  have hi : ‖∫ x,F x ∂μ‖≤‖F‖ := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := μ)
      (Eventually.of_forall F.norm_coe_le_norm)
  exact (norm_sub_le _ _).trans (by linarith only [hm,hi])

 

theorem compact_tests (K : Set C(X,ℂ)) (hK : IsCompact K) (ε : ℝ) (hε : 0<ε) :
    ∃ η : ℝ,0<η ∧ ∀ (T : Finset κ) (p : κ→X),
      (∀ F : C(X,ℂ),LipschitzWith 1 F → ‖F‖≤1 → ‖discrepancy μ T p F‖<η) →
      ∀ F∈K,‖discrepancy μ T p F‖<ε := by
  obtain ⟨S,hS,η,hη,htest⟩ := CompactFamilyDescent.finite_unit_lipschitz_obstruction
    K hK ε 2 hε (by norm_num)
  refine ⟨η,hη,?_⟩
  intro T p hh F hF
  by_contra he
  obtain ⟨φ,hφ,hdisc⟩ := htest (discrepancy μ T p) (discrepancy_bound μ T p)
    ⟨F,hF,le_of_not_gt he⟩
  exact (not_le_of_gt (hh φ (hS φ hφ).1 (hS φ hφ).2)) hdisc

 

theorem continuous_test {l : Filter ℕ} (T : ℕ→Finset κ) (p : ℕ→κ→X)
    (hu : ∀ ε : ℝ,0<ε → ∀ᶠ N in l,
      ∀ F : C(X,ℂ),LipschitzWith 1 F → ‖F‖≤1 → ‖discrepancy μ (T N) (p N) F‖<ε)
    (F : C(X,ℂ)) : Tendsto (fun N => discrepancy μ (T N) (p N) F) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η,hη,hηtest⟩ := compact_tests (κ := κ) μ {F} (isCompact_singleton) ε hε
  filter_upwards [hu η hη] with N hN
  simpa only [dist_zero_right] using hηtest (T N) (p N) hN F (Set.mem_singleton F)

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
variable (Γ : Subgroup G) (h01 : H.level 0=H.level 1)
variable (s : ℕ) (hs : H.level (s+1)=⊥) (e : Option ι≃Fin v)
variable (cc : RealCoordinates (cube H (Finset.univ : Finset ι) 0) (t+d))
variable (hsk : SecondKind cc)
variable (q : ℕ→ℕ) (hqbound : ∀ k,q k ≤ t+d)
variable (hq : ∀ k (g : cube H (Finset.univ : Finset ι) 0),
  g∈(CubeMaxFiltration.filtration H Finset.univ).level k ↔
    ∀ i : Fin (t+d),i.val < q k → cc.coord g i=0)
variable (hΓ : ∀ g : cube H (Finset.univ : Finset ι) 0,
  g∈cubeLattice H Γ ↔ ∀ i,∃ z : ℤ,cc.coord g i=z)
variable [MeasurableSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)]
variable [hBorel : @BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) (QuotientGroup.instTopologicalSpace (cubeLattice H Γ)) inferInstance]
variable [mtr : MetricSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace (cubeLattice H Γ))
local instance compactCubeTopology : TopologicalSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
  mtr.toUniformSpace.toTopologicalSpace

include h01 hs hsk hqbound hq hΓ htop in
 

theorem haar_limit_compact
    (μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ))
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure (cube H (Finset.univ : Finset ι) 0) _ μ]
    (a : ℕ→∀ k : ℕ,H.level k)
    (hirr : ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
      ξ≠1 → Continuous ξ → RationalCharacter Γ ξ →
      (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
      Tendsto (fun N : ℕ => ‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(N:ℝ)^j)
        atTop atTop)
    (c₀ C₀ : ℝ) (hc₀ : 0<c₀) (hC₀ : 0<C₀)
    (d₀ : ℕ) (hd₀ : 0<d₀) (r : Fin v→ℤ)
    (K : Set C(((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ),ℂ))
    (hK : IsCompact K) :
    letI : CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
      metric_compact cc (cubeLattice H Γ) hΓ mtr htop
    letI : BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
      metric_borelSpace (cubeLattice H Γ) mtr htop
    ∀ η : ℝ,0<η → ∀ᶠ N : ℕ in atTop,
      ∀ lo hi : Fin v→ℝ,
      (∀ i,c₀*(N:ℝ)≤hi i-lo i) →
      (∀ i,-C₀*(N:ℝ)≤lo i ∧ hi i≤C₀*(N:ℝ)) →
      ∀ F : C(((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ),ℂ),
        F∈K →
        ‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk
          (cubePolynomial c H S hH (a N) s
            (fun i => ((r (e i)+(d₀:ℤ)*x (e i):ℤ):ℝ)))))-(∫ y,F y ∂μ)‖<η  := by
  let : CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
    metric_compact cc (cubeLattice H Γ) hΓ mtr htop
  let : BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
    metric_borelSpace (cubeLattice H Γ) mtr htop
  intro η hη
  obtain ⟨δ,hδ,htest⟩ := FiniteHaarTests.compact_tests (κ := Fin v→ℤ) μ K hK η hη
  have hh := haar_limit c H S hH Γ h01 s hs e cc hsk q hqbound hq hΓ htop μ a hirr
    c₀ C₀ 1 hc₀ hC₀ (by norm_num) d₀ hd₀ r δ hδ
  filter_upwards [hh] with N hN
  intro lo hi hlo hhi F hF
  apply htest (integerBox v lo hi)
    (fun x => QuotientGroup.mk (cubePolynomial c H S hH (a N) s
      (fun i => ((r (e i)+(d₀:ℤ)*x (e i):ℤ):ℝ)))) _ F hF
  intro φ hφ hφn
  exact hN lo hi hlo hhi φ hφ hφn

end CubeLocalHaar
end
end
 

 
section

noncomputable section
open scoped Topology
namespace CubeLocalHaar
open CubeFaces CompactGroupProducts MeasureTheory Filter
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]

lemma cubeQuotient_compact (H : Filtration G) (Γ : Subgroup G)
    (hr : ∀ j,HasCompactReps (H.level j) Γ) :
    CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) := by
  have hh : HasCompactReps ⊤ (cubeLattice (ι := ι) H Γ) := by
    simpa only [CubeMaxFiltration.filtration_zero] using
      CubeMaxFiltration.hasCompactReps_level (ι := ι) H Γ hr 0
  exact hh.quotient_compactSpace

variable (H : Filtration G) (Λ : Subgroup G) (σ : G)

 

def frozenTest (F : C((Finset ι→G⧸Λ),ℂ)) (a : Finset ι→G) :
    C(((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)),ℂ) :=
  ⟨fun x => F (haarImage H Λ σ a x),F.continuous.comp
    ((haarImage_continuous H Λ σ).comp (continuous_const.prodMk continuous_id))⟩

lemma frozenTest_continuous (F : C((Finset ι→G⧸Λ),ℂ)) :
    Continuous (frozenTest H Λ σ F) := by
  exact (ContinuousMap.curry ⟨_,F.continuous.comp (haarImage_continuous H Λ σ)⟩).continuous

variable [CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))]

 

theorem uniform_freezing (F : C((Finset ι→G⧸Λ),ℂ)) (a₀ : Finset ι→G)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ a in 𝓝 a₀,∀ x,
      ‖F (haarImage H Λ σ a x)-F (haarImage H Λ σ a₀ x)‖<ε := by
  have he := (frozenTest_continuous H Λ σ F).continuousAt.preimage_mem_nhds
    (Metric.ball_mem_nhds (frozenTest H Λ σ F a₀) hε)
  filter_upwards [he] with a ha
  intro x
  exact (ContinuousMap.norm_coe_le_norm
    (frozenTest H Λ σ F a-frozenTest H Λ σ F a₀) x).trans_lt
    (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using ha)

variable [MeasurableSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))]
variable [BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))]
variable [MeasurableSpace (G⧸Λ)] [BorelSpace (G⧸Λ)]
variable [SecondCountableTopology (G⧸Λ)]

 

def imageProbability (μ : ProbabilityMeasure
    ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)))
    (a : Finset ι→G) : ProbabilityMeasure (Finset ι→G⧸Λ) :=
  μ.map (haarImage H Λ σ a)

omit [CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))] in
lemma integral_imageProbability
    [CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))]
    (μ : ProbabilityMeasure
    ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)))
    (a : Finset ι→G) (F : C((Finset ι→G⧸Λ),ℂ)) :
    (∫ y,F y ∂(imageProbability H Λ σ μ a : Measure (Finset ι→G⧸Λ)))=
      ∫ x,frozenTest H Λ σ F a x ∂(μ : Measure _) := by
  exact integral_map (φ := haarImage H Λ σ a) (μ := (μ : Measure _))
    (((haarImage_continuous H Λ σ).comp
    (continuous_const.prodMk continuous_id)).measurable.aemeasurable)
    F.continuous.aestronglyMeasurable

end CubeLocalHaar

end
end
end
end
end

end OAI
