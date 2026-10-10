import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeLocal08
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
 

theorem source_comparable_boxes_cube_haar
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
      (∀ z∈halfOpenBox v lo hi,
        |(((sourceResidue e r₀ (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ))-β|≤C*α ∧
        ∀ i : ι,|(((sourceResidue e r₀ (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))|≤C*α) →
      ∀ F : C((Finset ι→G⧸Λ),ℂ),
      LipschitzWith L F → ‖F‖≤B →
      ‖(𝔼 z∈halfOpenBox v lo hi,
          F (fun w : Finset ι => QuotientGroup.mk (P N (sourceVertex e d₀ r₀ z w))))-
        (∫ y,F y ∂(m:Measure (Finset ι→G⧸Λ)))‖<ε := by
  let : MetricSpace (G⧸Λ) := MetricSpace.replaceTopology qmtr hqtop.symm
  intro m
  let J (α : ℝ) (N : ℕ) := {b : (Fin v→ℝ)×(Fin v→ℝ) //
    (∀ i,(cBox*α)*(N:ℝ)≤b.2 i-b.1 i) ∧
    (∀ i,-CBox*(N:ℝ)≤b.1 i ∧ b.2 i≤CBox*(N:ℝ)) ∧
    ∀ z∈halfOpenBox v b.1 b.2,
      |(((sourceResidue e r₀ (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ))-β|≤C*α ∧
      ∀ i : ι,|(((sourceResidue e r₀ (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))|≤C*α}
  let lo : ∀ α N,J α N→Fin v→ℝ := fun _ _ j => j.val.1
  let hi : ∀ α N,J α N→Fin v→ℝ := fun _ _ j => j.val.2
  have hb (α : ℝ) (hα : 0<α) : ∃ c₀ C₀ : ℝ,0<c₀ ∧ 0<C₀ ∧
      ∀ᶠ N : ℕ in atTop,∀ j : J α N,
        (∀ i,c₀*(N:ℝ)≤hi α N j i-lo α N j i) ∧
        (∀ i,-C₀*(N:ℝ)≤lo α N j i ∧ hi α N j i≤C₀*(N:ℝ)) :=
    ⟨cBox*α,CBox,mul_pos hcBox hα,hCBox,
      Filter.Eventually.of_forall (fun N j => ⟨j.property.1,j.property.2.1⟩)⟩
  have hgbox (α : ℝ) (_ha : 0<α) : ∀ᶠ N : ℕ in atTop,
      ∀ j : J α N,∀ z∈halfOpenBox v (lo α N j) (hi α N j),
        |(((sourceResidue e r₀ (e none)+(d₀:ℤ)*z (e none):ℤ):ℝ)/(N:ℝ))-β|≤C*α ∧
        ∀ i : ι,|(((sourceResidue e r₀ (e (some i))+(d₀:ℤ)*z (e (some i)):ℤ):ℝ)/(N:ℝ))|≤C*α :=
    Filter.Eventually.of_forall (fun N j => j.property.2.2)
  have he := source_box_family_bounded_cube_haar c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ
    mtr htop qmtr hqtop μ a hirr d₀ r₀ hd₀ hr₀ β hβ J lo hi hb C hC hgbox
    g h hh ρ hρ hg P γ hfactor hperiod L B
  intro ε hε
  filter_upwards [he ε hε] with α hα
  filter_upwards [hα] with N hN
  intro l u hside horigin hlocal F hL hB
  exact hN ⟨(l,u),hside,horigin,hlocal⟩ F hL hB

end CubeLocalHaar
end
end
 

 
section

noncomputable section
open scoped Topology BoundedContinuousFunction
namespace CubeLocalHaar
open CubeFaces MeasureTheory
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [FirstCountableTopology G]
variable [Fintype ι] [DecidableEq ι]
variable (H : Filtration G) (Λ : Subgroup G) (σ : G)
variable [CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))]
variable [MeasurableSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))]
variable [BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))]
variable [MeasurableSpace (G⧸Λ)] [BorelSpace (G⧸Λ)]
variable [SecondCountableTopology (G⧸Λ)]

 

omit [CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))] in
theorem imageProbability_continuous
    [CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))]
    (μ : ProbabilityMeasure
    ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ))) :
    Continuous (imageProbability (ι := ι) H Λ σ μ) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro F
  have he (a : Finset ι→G) :
      (∫ y,F y ∂(imageProbability H Λ σ μ a : Measure (Finset ι→G⧸Λ)))=
        ∫ x,F (haarImage H Λ σ a x) ∂(μ : Measure _) := by
    exact integral_map
      (((haarImage_continuous H Λ σ).comp
        (continuous_const.prodMk continuous_id)).measurable.aemeasurable)
      F.continuous.aestronglyMeasurable
  simp_rw [he]
  apply continuous_of_dominated (bound := fun _ => ‖F‖)
  · intro a
    exact (F.continuous.comp ((haarImage_continuous H Λ σ).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · intro a
    exact Filter.Eventually.of_forall (fun x => F.norm_coe_le_norm _)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun x => F.continuous.comp
      ((haarImage_continuous H Λ σ).comp (continuous_id.prodMk continuous_const)))

variable [CompactSpace (G⧸Λ)]
 

omit [FirstCountableTopology G] in
theorem haar_image_integral_continuous [FirstCountableTopology G] (μ : ProbabilityMeasure
    ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)))
    {X : Type} [TopologicalSpace X] [FirstCountableTopology X] (h : X→G) (hh : Continuous h)
    (F : C((Finset ι→G⧸Λ),ℂ)) :
    Continuous (fun β => ∫ y,F y ∂(imageProbability H Λ σ μ
      (fun _ => h β) : Measure (Finset ι→G⧸Λ))) := by
  simp_rw [integral_imageProbability]
  apply continuous_of_dominated (bound := fun _ => ‖F‖)
  · intro β
    exact (frozenTest H Λ σ F (fun _ => h β)).continuous.aestronglyMeasurable
  · intro β
    exact Filter.Eventually.of_forall (fun x => ContinuousMap.norm_coe_le_norm F _)
  · exact integrable_const _
  · refine Filter.Eventually.of_forall (fun x => ?_)
    exact F.continuous.comp ((haarImage_continuous H Λ σ).comp
      ((continuous_pi (fun _ => hh)).prodMk continuous_const))

 
theorem haar_image_intervalIntegrable (μ : ProbabilityMeasure
    ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H (conjugateLattice Λ σ)))
    (h : ℝ→G) (hh : Continuous h) (F : C((Finset ι→G⧸Λ),ℂ)) :
    IntervalIntegrable (fun β => ∫ y,F y ∂(imageProbability H Λ σ μ
      (fun _ => h β) : Measure (Finset ι→G⧸Λ))) volume 0 1 :=
  (haar_image_integral_continuous H Λ σ μ h hh F).intervalIntegrable 0 1

end CubeLocalHaar
end
end
 

 
section

noncomputable section
open scoped BigOperators
namespace CubeLocalHaar
open ComparableBoxLeibman

 

def physicalResidueRectangle {v : ℕ} (lo hi : Fin v→ℝ) (r : Fin v→ℤ) (d : ℕ) :
    Finset (Fin v→ℤ) :=
  (halfOpenBox v lo hi).filter (fun b => ∀ i,b i%(d:ℤ)=r i)

lemma physicalResidueRectangle_mem {v : ℕ} (lo hi : Fin v→ℝ) (r : Fin v→ℤ)
    (d : ℕ) (b : Fin v→ℤ) :
    b∈physicalResidueRectangle lo hi r d ↔
      (∀ i,lo i≤(b i:ℝ) ∧ (b i:ℝ)<hi i) ∧ ∀ i,b i%(d:ℤ)=r i := by
  simp only [physicalResidueRectangle,Finset.mem_filter,mem_halfOpenBox]

lemma physicalResidueRectangle_affine {v : ℕ} (lo hi : Fin v→ℝ) (r : Fin v→ℤ)
    (d : ℕ) (hd : 0<d) (hr : ∀ i,0 ≤ r i ∧ r i<(d:ℤ)) (z : Fin v→ℤ) :
    (fun i => r i+(d:ℤ)*z i)∈physicalResidueRectangle lo hi r d ↔
      z∈halfOpenBox v (fun i => (lo i-(r i:ℝ))/(d:ℝ))
        (fun i => (hi i-(r i:ℝ))/(d:ℝ)) := by
  have hd' : 0<(d:ℝ) := by exact_mod_cast hd
  rw [physicalResidueRectangle_mem,mem_halfOpenBox]
  have hmod : ∀ i,(r i+(d:ℤ)*z i)%(d:ℤ)=r i := by
    intro i
    simp only [Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (hr i).1 (hr i).2
  simp only [hmod,implies_true,and_true,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  apply forall_congr'
  intro i
  rw [div_le_iff₀ hd',lt_div_iff₀ hd']
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

 
theorem physicalResidueRectangle_expect {v : ℕ} (lo hi : Fin v→ℝ) (r : Fin v→ℤ)
    (d : ℕ) (hd : 0<d) (hr : ∀ i,0 ≤ r i ∧ r i<(d:ℤ))
    (F : (Fin v→ℤ)→ℂ) :
    (𝔼 b∈physicalResidueRectangle lo hi r d,F b) =
      (𝔼 z∈halfOpenBox v (fun i => (lo i-(r i:ℝ))/(d:ℝ))
        (fun i => (hi i-(r i:ℝ))/(d:ℝ)),F (fun i => r i+(d:ℤ)*z i)) := by
  classical
  symm
  apply Finset.expect_bij (fun z _ i => r i+(d:ℤ)*z i)
  · intro z hz
    exact (physicalResidueRectangle_affine lo hi r d hd hr z).mpr hz
  · intro z hz
    rfl
  · intro z₁ hz₁ z₂ hz₂ he
    funext i
    have hi := congrFun he i
    have hdne : (d:ℤ)≠0 := by exact_mod_cast (ne_of_gt hd)
    exact mul_left_cancel₀ hdne (add_left_cancel hi)
  · intro b hb
    let z : Fin v→ℤ := fun i => b i/(d:ℤ)
    have he : (fun i => r i+(d:ℤ)*z i)=b := by
      funext i
      have hh := Int.emod_add_ediv_mul (b i) (d:ℤ)
      rw [(physicalResidueRectangle_mem lo hi r d b).mp hb |>.2 i] at hh
      simpa only [z,mul_comm] using hh
    refine ⟨z,(physicalResidueRectangle_affine lo hi r d hd hr z).mp ?_,he⟩
    rw [he]
    exact hb

end CubeLocalHaar

end
end
end
end
end

end OAI
