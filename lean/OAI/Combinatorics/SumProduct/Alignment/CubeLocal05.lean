import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeLocal04
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
open scoped Topology NNReal BoundedContinuousFunction
namespace BoundedLipschitzCompact
variable {X : Type*} [MetricSpace X] [CompactSpace X]

 

theorem compact_envelope (L : ℝ≥0) (B : ℝ) :
    ∃ K : Set C(X,ℂ), IsCompact K ∧
      ∀ F : C(X,ℂ), LipschitzWith L F → ‖F‖ ≤ B → F ∈ K := by
  let E := ContinuousMap.isometryEquivBoundedOfCompact X ℂ
  let A : Set (X →ᵇ ℂ) := {F | LipschitzWith L F ∧ ‖F‖ ≤ B}
  have hA : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 B)
      (isCompact_closedBall _ _) A
    · intro F x hF
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        (BoundedContinuousFunction.norm_coe_le_norm F x).trans hF.2
    · exact (LipschitzWith.uniformEquicontinuous
        (fun F : A => (F.val : X → ℂ)) L (fun F => F.property.1)).equicontinuous
  refine ⟨E.symm '' closure A, hA.image E.symm.continuous, ?_⟩
  intro F hL hB
  refine ⟨E F, subset_closure ?_, E.symm_apply_apply F⟩
  change LipschitzWith L (E F) ∧ ‖E F‖ ≤ B
  constructor
  · exact hL
  · change ‖BoundedContinuousFunction.mkOfCompact F‖ ≤ B
    simpa only [BoundedContinuousFunction.norm_mkOfCompact] using hB

end BoundedLipschitzCompact
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
 

theorem source_bounded_lipschitz_cube_haar
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

    (L : ℝ≥0) (B : ℝ) :
    letI : MetricSpace (G⧸Λ) := MetricSpace.replaceTopology qmtr hqtop.symm
    let m : ProbabilityMeasure (Finset ι→G⧸Λ) :=
      imageProbability H Λ σ ⟨μ,inferInstance⟩ (fun _ => h β)
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ F : C((Finset ι→G⧸Λ),ℂ),
      LipschitzWith L F → ‖F‖≤B →
      ‖(𝔼 z∈halfOpenBox v
          (progressionLo (sourceCenter e β) (sourceResidue e r₀) d₀ N)
          (progressionHi (sourceCenter e β) (sourceResidue e r₀) d₀ α N),
          F (fun w : Finset ι => QuotientGroup.mk (P N (sourceVertex e d₀ r₀ z w))))-
        (∫ y,F y ∂(m:Measure (Finset ι→G⧸Λ)))‖<ε := by
  let : MetricSpace (G⧸Λ) := MetricSpace.replaceTopology qmtr hqtop.symm
  intro m
  obtain ⟨K,hK,hcover⟩ := BoundedLipschitzCompact.compact_envelope
    (X := Finset ι→G⧸Λ) L B
  have hhK := source_compact_cube_haar c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ
    mtr htop qmtr hqtop μ a hirr d₀ r₀ hd₀ hr₀ β hβ g h hh ρ hρ hg P γ hfactor hperiod K hK
  intro ε hε
  filter_upwards [hhK ε hε] with α hα
  filter_upwards [hα] with N hN
  intro F hL hB
  exact hN F (hcover F hL hB)

end CubeLocalHaar
end
end
 

 
section

noncomputable section
open scoped BigOperators
namespace CubeLocalHaar
open ComparableBoxLeibman

 

def physicalProgressionBox {v : ℕ} (a : Fin v→ℝ) (r : Fin v→ℤ) (d : ℕ)
    (α : ℝ) (N : ℕ) : Finset (Fin v→ℤ) :=
  (halfOpenBox v (fun i => a i*(N:ℝ)) (fun i => (a i+α)*(N:ℝ))).filter
    (fun b => ∀ i,b i%(d:ℤ)=r i)

lemma physicalProgressionBox_mem {v : ℕ} (a : Fin v→ℝ) (r : Fin v→ℤ)
    (d : ℕ) (α : ℝ) (N : ℕ) (b : Fin v→ℤ) :
    b∈physicalProgressionBox a r d α N ↔
      (∀ i,a i*(N:ℝ)≤(b i:ℝ) ∧ (b i:ℝ)<(a i+α)*(N:ℝ)) ∧
      ∀ i,b i%(d:ℤ)=r i := by
  simp only [physicalProgressionBox,Finset.mem_filter,mem_halfOpenBox]

lemma physicalProgressionBox_affine {v : ℕ} (a : Fin v→ℝ) (r : Fin v→ℤ)
    (d : ℕ) (hd : 0<d) (hr : ∀ i,0≤r i ∧ r i<(d:ℤ))
    (α : ℝ) (N : ℕ) (z : Fin v→ℤ) :
    (fun i => r i+(d:ℤ)*z i)∈physicalProgressionBox a r d α N ↔
      z∈halfOpenBox v (progressionLo a r d N) (progressionHi a r d α N) := by
  have hd' : 0<(d:ℝ) := by exact_mod_cast hd
  rw [physicalProgressionBox_mem,mem_halfOpenBox]
  have hmod : ∀ i,(r i+(d:ℤ)*z i)%(d:ℤ)=r i := by
    intro i
    simp only [Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (hr i).1 (hr i).2
  simp only [hmod,implies_true,and_true,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  apply forall_congr'
  intro i
  dsimp only [progressionLo,progressionHi]
  rw [div_le_iff₀ hd',lt_div_iff₀ hd']
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

 

theorem physicalProgressionBox_expect {v : ℕ} (a : Fin v→ℝ) (r : Fin v→ℤ)
    (d : ℕ) (hd : 0<d) (hr : ∀ i,0≤r i ∧ r i<(d:ℤ))
    (α : ℝ) (N : ℕ) (F : (Fin v→ℤ)→ℂ) :
    (𝔼 b∈physicalProgressionBox a r d α N,F b) =
      (𝔼 z∈halfOpenBox v (progressionLo a r d N) (progressionHi a r d α N),
        F (fun i => r i+(d:ℤ)*z i)) := by
  classical
  symm
  apply Finset.expect_bij (fun z _ i => r i+(d:ℤ)*z i)
  · intro z hz
    exact (physicalProgressionBox_affine a r d hd hr α N z).mpr hz
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
      rw [(physicalProgressionBox_mem a r d α N b).mp hb |>.2 i] at hh
      simpa only [z,mul_comm] using hh
    refine ⟨z,(physicalProgressionBox_affine a r d hd hr α N z).mp ?_,he⟩
    rw [he]
    exact hb

end CubeLocalHaar
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
 

theorem source_physical_cube_haar
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

    (L : ℝ≥0) (B : ℝ) :
    letI : MetricSpace (G⧸Λ) := MetricSpace.replaceTopology qmtr hqtop.symm
    let m : ProbabilityMeasure (Finset ι→G⧸Λ) :=
      imageProbability H Λ σ ⟨μ,inferInstance⟩ (fun _ => h β)
    ∀ ε : ℝ,0<ε → ∀ᶠ α : ℝ in 𝓝[>] 0,∀ᶠ N : ℕ in atTop,∀ F : C((Finset ι→G⧸Λ),ℂ),
      LipschitzWith L F → ‖F‖≤B →
      ‖(𝔼 b∈physicalProgressionBox (sourceCenter e β) (sourceResidue e r₀) d₀ α N,
          F (fun w : Finset ι => QuotientGroup.mk
            (P N (b (e none)+∑ i∈w,b (e (some i))))))-
        (∫ y,F y ∂(m:Measure (Finset ι→G⧸Λ)))‖<ε := by
  let : MetricSpace (G⧸Λ) := MetricSpace.replaceTopology qmtr hqtop.symm
  intro m
  have he := source_bounded_lipschitz_cube_haar c H S hH Λ σ h01 s hs e cc hsk q hqbound hq hΓ
    mtr htop qmtr hqtop μ a hirr d₀ r₀ hd₀ hr₀ β hβ g h hh ρ hρ hg P γ hfactor hperiod L B
  have hr : ∀ i : Fin v,0 ≤ sourceResidue e r₀ i ∧ sourceResidue e r₀ i<(d₀:ℤ) := by
    intro i
    have hd' : (0:ℤ)<d₀ := by exact_mod_cast hd₀
    have hr' : (r₀:ℤ)<d₀ := by exact_mod_cast hr₀
    unfold sourceResidue
    split_ifs
    · exact ⟨by positivity,hr'⟩
    · exact ⟨le_refl 0,hd'⟩
  have hv (z : Fin v→ℤ) (w : Finset ι) :
      sourceResidue e r₀ (e none)+(d₀:ℤ)*z (e none)+
        ∑ i∈w,(sourceResidue e r₀ (e (some i))+(d₀:ℤ)*z (e (some i))) =
          sourceVertex e d₀ r₀ z w := by
    simp [sourceResidue,sourceVertex,mul_add,Finset.mul_sum,add_assoc]
  intro ε hε
  filter_upwards [he ε hε] with α hα
  filter_upwards [hα] with N hN
  intro F hL hB
  rw [physicalProgressionBox_expect (sourceCenter e β) (sourceResidue e r₀) d₀ hd₀ hr]
  simp_rw [hv]
  exact hN F hL hB

end CubeLocalHaar

end
end
end
end
end

end OAI
