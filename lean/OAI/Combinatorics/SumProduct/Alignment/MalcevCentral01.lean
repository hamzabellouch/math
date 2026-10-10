import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AbelianMalcev02
import OAI.Combinatorics.SumProduct.Alignment.TorusVertical01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section

end
 

 
section
noncomputable section
namespace AbelianMalcevTorus
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (hadd : ∀ g h : G, ∀ i : Fin n, c.coord (g*h) i=c.coord g i+c.coord h i)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [Γ.Normal]

omit [IsTopologicalGroup G] in
lemma quotientHomeomorph_one : quotientHomeomorph c hadd Γ hΓ 1=0 :=
  torusProjection_one c

omit [IsTopologicalGroup G] in
lemma quotientHomeomorph_mul (x y : G⧸Γ) :
    quotientHomeomorph c hadd Γ hΓ (x*y)=
      quotientHomeomorph c hadd Γ hΓ x+quotientHomeomorph c hadd Γ hΓ y := by
  induction x using Quotient.inductionOn with | h g =>
    induction y using Quotient.inductionOn with | h a =>
      exact torusProjection_mul c hadd g a

omit [IsTopologicalGroup G] in
lemma quotientHomeomorph_symm_zero : (quotientHomeomorph c hadd Γ hΓ).symm 0=1 := by
  apply (quotientHomeomorph c hadd Γ hΓ).injective
  rw [Homeomorph.apply_symm_apply,quotientHomeomorph_one]

omit [IsTopologicalGroup G] in
lemma quotientHomeomorph_symm_add (x y : UnitAddTorus (Fin n)) :
    (quotientHomeomorph c hadd Γ hΓ).symm (x+y)=
      (quotientHomeomorph c hadd Γ hΓ).symm x*(quotientHomeomorph c hadd Γ hΓ).symm y := by
  apply (quotientHomeomorph c hadd Γ hΓ).injective
  rw [quotientHomeomorph_mul]
  simp only [Homeomorph.apply_symm_apply]
end AbelianMalcevTorus

namespace MalcevCentralTorus
open RationalLattice AbelianMalcevTorus MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (N Γ : Subgroup G) (hN : N ≤ Subgroup.center G)
variable [(Γ.comap N.subtype).Normal]
variable {d : ℕ} (c : RealCoordinates N d)
variable (hadd : ∀ g h : N, ∀ i, c.coord (g*h) i=c.coord g i+c.coord h i)
variable (hΓ : ∀ g : N, g∈Γ.comap N.subtype ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)

 

@[instance_reducible]
def addAction : AddAction (UnitAddTorus (Fin d)) (G⧸Γ) := by
  letI := CentralQuotientAction.action N Γ hN
  let e := quotientHomeomorph c hadd (Γ.comap N.subtype) hΓ
  exact { vadd := fun t x => e.symm t • x
          zero_vadd := fun x => by
            change e.symm 0 • x=x
            rw [quotientHomeomorph_symm_zero,one_smul]
          add_vadd := fun s t x => by
            change e.symm (s+t) • x=e.symm s • (e.symm t • x)
            rw [quotientHomeomorph_symm_add,mul_smul] }

lemma continuous_addAction :
    letI := addAction N Γ hN c hadd hΓ
    ContinuousVAdd (UnitAddTorus (Fin d)) (G⧸Γ) := by
  let := addAction N Γ hN c hadd hΓ
  let := CentralQuotientAction.action N Γ hN
  let := CentralQuotientAction.continuous_action N Γ hN
  constructor
  exact ((quotientHomeomorph c hadd (Γ.comap N.subtype) hΓ).symm.continuous.comp continuous_fst).smul continuous_snd

omit [IsTopologicalGroup G] in
lemma torusProjection_vadd (n : N) (g : G) :
    letI := addAction N Γ hN c hadd hΓ
    torusProjection c n +ᵥ (QuotientGroup.mk g : G⧸Γ) = QuotientGroup.mk (g*n.val) := by
  let := addAction N Γ hN c hadd hΓ
  let := CentralQuotientAction.action N Γ hN
  change (quotientHomeomorph c hadd (Γ.comap N.subtype) hΓ).symm
    (quotientHomeomorph c hadd (Γ.comap N.subtype) hΓ (QuotientGroup.mk n)) • QuotientGroup.mk g = _
  rw [Homeomorph.symm_apply_apply]
  change QuotientGroup.mk (n.val*g)=QuotientGroup.mk (g*n.val)
  rw [Subgroup.mem_center_iff.mp (hN n.property) g]

omit [IsTopologicalGroup G] in
lemma invariant_addAction [MeasurableSpace (G⧸Γ)]
    (μ : Measure (G⧸Γ)) [SMulInvariantMeasure G (G⧸Γ) μ] :
    letI := addAction N Γ hN c hadd hΓ
    VAddInvariantMeasure (UnitAddTorus (Fin d)) (G⧸Γ) μ := by
  let := addAction N Γ hN c hadd hΓ
  let := CentralQuotientAction.action N Γ hN
  let : N.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_center_iff.mp (hN hx) g,mul_assoc,mul_inv_cancel,mul_one]
    exact hx⟩
  let := CentralQuotientAction.invariant_central_action N Γ hN μ
  constructor
  intro t s hs
  exact SMulInvariantMeasure.measure_preimage_smul (μ:=μ)
    ((quotientHomeomorph c hadd (Γ.comap N.subtype) hΓ).symm t) hs

end MalcevCentralTorus
end
end
 

 
section
noncomputable section
namespace MalcevCentralTorus
open RationalLattice MalcevCharacters RationalTailCoordinates AbelianMalcevTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r d : ℕ} (c : RealCoordinates G (r+d)) (hsk : SecondKind c)
variable (N Γ : Subgroup G) (hcent : N ≤ Subgroup.center G)
variable (hN : ∀ g : G, g∈N ↔ ∀ i : Fin (r+d), i.val<r → c.coord g i=0)
variable (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)

include hcent in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma central_commutative : IsMulCommutative N :=
  IsMulCommutative.of_comm (fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp (hcent a.property) b.val).symm))

include hcent in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma central_lattice_normal : (Γ.comap N.subtype).Normal := by
  constructor
  intro a ha b
  have he : b*a=a*b := Subtype.ext ((Subgroup.mem_center_iff.mp (hcent b.property) a.val).symm)
  rw [he,mul_assoc,mul_inv_cancel,mul_one]
  exact ha

include hsk hcent hN in
lemma tail_additive : ∀ a b : N, ∀ i,
    (tailCoordinates c N hN).coord (a*b) i=
    (tailCoordinates c N hN).coord a i+(tailCoordinates c N hN).coord b i := by
  apply coordinates_additive_of_commutator_bot (tailCoordinates c N hN) (tail_secondKind c N hN hsk)
  exact ((commutator_eq_bot_iff N).mpr (central_commutative N hcent)).le

@[instance_reducible]
def tailAction : AddAction (UnitAddTorus (Fin d)) (G⧸Γ) :=
  letI := central_lattice_normal N Γ hcent
  addAction N Γ hcent (tailCoordinates c N hN) (tail_additive c hsk N hcent hN)
    (tailCoordinates_lattice c N hN Γ hΓ)

lemma continuous_tailAction :
    letI := tailAction c hsk N Γ hcent hN hΓ
    ContinuousVAdd (UnitAddTorus (Fin d)) (G⧸Γ) := by
  let := central_lattice_normal N Γ hcent
  exact continuous_addAction N Γ hcent (tailCoordinates c N hN) (tail_additive c hsk N hcent hN)
    (tailCoordinates_lattice c N hN Γ hΓ)

lemma tailProjection_vadd (a : N) (g : G) :
    letI := tailAction c hsk N Γ hcent hN hΓ
    torusProjection (tailCoordinates c N hN) a +ᵥ (QuotientGroup.mk g : G⧸Γ)=QuotientGroup.mk (g*a.val) := by
  let := central_lattice_normal N Γ hcent
  exact torusProjection_vadd N Γ hcent (tailCoordinates c N hN) (tail_additive c hsk N hcent hN)
    (tailCoordinates_lattice c N hN Γ hΓ) a g

lemma invariant_tailAction [MeasurableSpace (G⧸Γ)] (μ : MeasureTheory.Measure (G⧸Γ))
    [MeasureTheory.SMulInvariantMeasure G (G⧸Γ) μ] :
    letI := tailAction c hsk N Γ hcent hN hΓ
    MeasureTheory.VAddInvariantMeasure (UnitAddTorus (Fin d)) (G⧸Γ) μ := by
  let := central_lattice_normal N Γ hcent
  exact invariant_addAction N Γ hcent (tailCoordinates c N hN) (tail_additive c hsk N hcent hN)
    (tailCoordinates_lattice c N hN Γ hΓ) μ

end MalcevCentralTorus
end
end
 

 
section
noncomputable section
namespace TorusVerticalFourier
open UnitAddTorus AddCircle
variable {d : Type*} [Fintype d]

lemma character_norm (k : d→ℤ) (s : UnitAddTorus d) : ‖mFourier k s‖=1 := by
  simp only [mFourier,ContinuousMap.coe_mk,norm_prod,fourier_apply,Circle.norm_coe,Finset.prod_const_one]

lemma character_nontrivial {k : d→ℤ} (hk : k≠0) : ∃ s : UnitAddTorus d, mFourier k s≠1 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, k i≠0 := by
    contrapose! hk
    exact funext hk
  let s : UnitAddTorus d := Pi.single i (((1 / 2 / (k i : ℝ) : ℝ) : UnitAddCircle))
  have hs : mFourier k s = -1 := by
    rw [mFourier]
    simp only [ContinuousMap.coe_mk]
    rw [Finset.prod_eq_single i]
    · simp only [s,Pi.single_eq_same]
      simpa only [zero_add,fourier_eval_zero] using
        (fourier_add_half_inv_index (T := 1) hi (by norm_num) (0 : UnitAddCircle))
    · intro j _ hji
      simp [s,Pi.single_eq_of_ne hji]
    · simp
  exact ⟨s,by rw [hs]; norm_num⟩

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [AddAction (UnitAddTorus d) X] [ContinuousVAdd (UnitAddTorus d) X]
omit [CompactSpace X] [ContinuousVAdd (UnitAddTorus d) X] in
lemma HasWeight.smul {k : d→ℤ} {F : C(X,ℂ)} (hF : HasWeight k F) (z : ℂ) : HasWeight k (z • F) := by
  intro s x
  change z*F (s+ᵥx)=mFourier k s*(z*F x)
  rw [hF]
  ring

end TorusVerticalFourier
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace AbelianMalcevTorus
open RationalLattice CubeFaces LeibmanSquare MeasureTheory MalcevHorizontal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (hadd : ∀ g h : G, ∀ i : Fin n, c.coord (g*h) i=c.coord g i+c.coord h i)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hadd hΓ htop in
 

theorem quantitative_abelian_compact_producer (H : Filtration G) (s : ℕ) (hs : H.level (s+1)=⊥)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (K : Set C(G⧸Γ,ℂ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G →* Multiplicative ℝ),
      (∀ χ∈U, Continuous χ ∧ (∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z)) ∧
    ∃ A : ℝ, 0<A ∧ ∀ N : ℕ, 0<N → ∀ f : ℤ → G, Polynomial H 0 f →
      (∃ F∈K, δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ χ∈U, χ≠1 ∧ ∃ P : ℝ[X], P.natDegree ≤ s ∧
        (∀ z : ℤ, P.eval (z:ℝ)=(χ (f z)).toAdd) ∧
        ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨S,hS,η,hη,ht⟩ := CompactFamilyDescent.finite_unit_lipschitz_obstruction K hK δ 2 hδ (by norm_num)
  obtain ⟨U,hU,A,hA,hprod⟩ := quantitative_abelian_producer c hadd Γ hΓ htop H s hs μ η hη
  refine ⟨U,hU,A,hA,?_⟩
  intro N hN f hf hdisc
  apply hprod N hN f hf
  obtain ⟨F,hF,hlarge⟩ := ht (FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)))
    (FourierObstruction.discrepancy_bound μ N hN _) hdisc
  exact ⟨F,(hS F hF).1,(hS F hF).2,hlarge⟩

end AbelianMalcevTorus

end
end
end
end
end

end OAI
