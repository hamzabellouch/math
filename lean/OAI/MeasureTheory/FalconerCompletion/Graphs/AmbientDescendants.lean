import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Recursion.FarCommonDepthUpper

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory

noncomputable def ambientDescendantsND {d : ℕ} (a b : ℕ) (P : Fin d → ℤ) :
    Finset (Fin d → ℤ) := by
  classical
  exact Fintype.piFinset (fun i => Finset.Icc (P i*(2:ℤ)^(b-a)) ((P i+1)*(2:ℤ)^(b-a)-1))

lemma mem_ambientDescendantsND_iff {d a b : ℕ} {P Q : Fin d → ℤ} :
    Q∈ambientDescendantsND a b P ↔ ambientAncestor b a Q=P := by
  classical
  simp only [ambientDescendantsND,Fintype.mem_piFinset,Finset.mem_Icc]
  constructor
  · intro h
    funext i
    apply le_antisymm
    · apply (Int.ediv_le_iff_le_mul (by positivity : (0:ℤ)<(2:ℤ)^(b-a))).mpr
      have hi := (h i).2
      nlinarith
    · exact (Int.le_ediv_iff_mul_le (by positivity : (0:ℤ)<(2:ℤ)^(b-a))).mpr (h i).1
  · intro h i
    exact ambientAncestor_coordinate h i

lemma ambientDescendantsND_card {d : ℕ} (a b : ℕ) (P : Fin d → ℤ) :
    (ambientDescendantsND a b P).card=2^((b-a)*d) := by
  classical
  have hi (i : Fin d) :
      (Finset.Icc (P i*(2:ℤ)^(b-a)) ((P i+1)*(2:ℤ)^(b-a)-1)).card=2^(b-a) := by
    rw [Int.card_Icc]
    have he : (P i+1)*(2:ℤ)^(b-a)-1+1-P i*(2:ℤ)^(b-a)=(2:ℤ)^(b-a) := by ring
    rw [he]
    norm_cast
  simp only [ambientDescendantsND,Fintype.card_piFinset,hi,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,← pow_mul]

lemma ambientDescendantsND_subset {d a b : ℕ} (hab : a≤b)
    {P Q : Fin d → ℤ} (hQ : Q∈ambientDescendantsND a b P) :
    ambientGridCell b Q⊆ambientGridCell a P := by
  have h := ambientGridCell_subset_ancestor hab Q
  change ambientGridCell b Q⊆ambientGridCell a (ambientAncestor b a Q) at h
  rwa [mem_ambientDescendantsND_iff.mp hQ] at h

lemma ambientDescendantsND_mem_of_point {d a b : ℕ} (hab : a≤b)
    {P Q : Fin d → ℤ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x∈ambientGridCell a P) (hQ : x∈ambientGridCell b Q) :
    Q∈ambientDescendantsND a b P := by
  apply mem_ambientDescendantsND_iff.mpr
  have hh := ambientGridCell_subset_ancestor hab Q hQ
  funext i
  exact ((mem_ambientGridCell_iff.mp hh) i).symm.trans ((mem_ambientGridCell_iff.mp hx) i)

theorem ambientDescendantsND_cover {d a b : ℕ} (hab : a≤b) (P : Fin d → ℤ) :
    (⋃ Q∈ambientDescendantsND a b P, ambientGridCell b Q)=ambientGridCell a P := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨Q,hQ,hxQ⟩ := mem_iUnion₂.mp hx
    exact ambientDescendantsND_subset hab hQ hxQ
  · intro x hx
    let Q : Fin d → ℤ := fun i => ⌊(2:ℝ)^b*x i⌋
    have hQ : x∈ambientGridCell b Q := mem_ambientGridCell_floorND b x
    exact mem_iUnion₂.mpr ⟨Q,ambientDescendantsND_mem_of_point hab hx hQ,hQ⟩

noncomputable def farParentPairsND {d : ℕ} (a b : ℕ) (K : ℝ) (P : Fin d → ℤ) :
    Finset ((Fin d → ℤ) × (Fin d → ℤ)) := by
  classical
  exact ((ambientDescendantsND a b P).product (ambientDescendantsND a b P)).filter
    (fun q => farSeparatedGridND b K q.1 q.2)

lemma mem_farParentPairsND_iff {d a b : ℕ} {K : ℝ}
    {P : Fin d → ℤ} {q : (Fin d → ℤ) × (Fin d → ℤ)} :
    q∈farParentPairsND a b K P ↔
      q.1∈ambientDescendantsND a b P ∧ q.2∈ambientDescendantsND a b P ∧
        farSeparatedGridND b K q.1 q.2 := by
  classical
  simp only [farParentPairsND,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,and_assoc]

theorem far_comparable_finite_coverND {d a h k : ℕ}
    (hK : 16*(d+1:ℝ)≤(2:ℝ)^k) {X Y : Fin d → ℤ}
    {x x' y y' : EuclideanSpace ℝ (Fin d)}
    (hx : x∈ambientGridCell a X) (hx' : x'∈ambientGridCell a X)
    (hy : y∈ambientGridCell a Y) (hy' : y'∈ambientGridCell a Y)
    (hfar : 1/(4*(2:ℝ)^h)≤ max (dist x x') (dist y y'))
    (hcomp : max (dist x x') (dist y y')≤2*min (dist x x') (dist y y')) :
    ∃ b∈Finset.Icc (a+1) (h+k+2),
      ∃ p∈farParentPairsND a b ((2:ℝ)^k) X,
        ∃ q∈farParentPairsND a b ((2:ℝ)^k) Y,
          x∈ambientGridCell b p.1 ∧ x'∈ambientGridCell b p.2 ∧
          y∈ambientGridCell b q.1 ∧ y'∈ambientGridCell b q.2 := by
  obtain ⟨b,hb,P,P',Q,Q',hxP,hxP',hyQ,hyQ',_,_,_,_,hPP,hQQ⟩ :=
    exists_far_grid_coverND hK hx hx' hy hy' hfar hcomp
  have hab : a≤b := by have hh := (Finset.mem_Icc.mp hb).1; omega
  exact ⟨b,hb,(P,P'),mem_farParentPairsND_iff.mpr
    ⟨ambientDescendantsND_mem_of_point hab hx hxP,ambientDescendantsND_mem_of_point hab hx' hxP',hPP⟩,
    (Q,Q'),mem_farParentPairsND_iff.mpr
    ⟨ambientDescendantsND_mem_of_point hab hy hyQ,ambientDescendantsND_mem_of_point hab hy' hyQ',hQQ⟩,
    hxP,hxP',hyQ,hyQ'⟩

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory

def firstCoverBinND {V : Type*} (S : Set V) (I : Finset ℕ) (G : ℕ → Set V) (b : ℕ) : Set V :=
  (S∩G b) \ ⋃ c∈I.filter (fun c => c<b), G c

lemma mem_firstCoverBinND {V : Type*} {S : Set V} {I : Finset ℕ} {G : ℕ → Set V}
    {b : ℕ} {x : V} :
    x∈firstCoverBinND S I G b ↔ x∈S ∧ x∈G b ∧ ∀ c∈I, c<b → x∉G c := by
  simp only [firstCoverBinND,mem_sdiff,mem_inter_iff,mem_iUnion,Finset.mem_filter,
    not_exists,and_imp,and_assoc]

lemma firstCoverBinND_subset {V : Type*} (S : Set V) (I : Finset ℕ) (G : ℕ → Set V) (b : ℕ) :
    firstCoverBinND S I G b⊆S ∩ G b := by
  intro x hx
  exact ⟨(mem_firstCoverBinND.mp hx).1,(mem_firstCoverBinND.mp hx).2.1⟩

lemma firstCoverBinND_disjoint {V : Type*} (S : Set V) (I : Finset ℕ) (G : ℕ → Set V) :
    (I : Set ℕ).PairwiseDisjoint (firstCoverBinND S I G) := by
  intro b hb c hc hbc
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨_,hxb,hbx⟩ := mem_firstCoverBinND.mp hx
  obtain ⟨_,hxc,hcx⟩ := mem_firstCoverBinND.mp hy
  rcases lt_or_gt_of_ne hbc with hlt | hgt
  · exact hcx b hb hlt hxb
  · exact hbx c hc hgt hxc

lemma firstCoverBinND_cover {V : Type*} (S : Set V) (I : Finset ℕ) (G : ℕ → Set V)
    (hcover : S⊆⋃ b∈I, G b) : (⋃ b∈I, firstCoverBinND S I G b)=S := by
  classical
  apply subset_antisymm
  · intro x hx
    obtain ⟨b,_,hb⟩ := mem_iUnion₂.mp hx
    exact (firstCoverBinND_subset S I G b hb).1
  · intro x hx
    have he : ∃ b, b∈I ∧ x∈G b := by
      obtain ⟨b,hb,hxb⟩ := mem_iUnion₂.mp (hcover hx)
      exact ⟨b,hb,hxb⟩
    let b := Nat.find he
    have hb : b∈I ∧ x∈G b := Nat.find_spec he
    refine mem_iUnion₂.mpr ⟨b,hb.1,mem_firstCoverBinND.mpr ⟨hx,hb.2,?_⟩⟩
    intro c hc hcb hxc
    have hh := Nat.find_min' he (show c∈I ∧ x∈G c from ⟨hc,hxc⟩)
    exact (not_lt_of_ge hh) hcb

lemma measurableSet_firstCoverBinND {V : Type*} [MeasurableSpace V]
    {S : Set V} (hS : MeasurableSet S) (I : Finset ℕ) (G : ℕ → Set V)
    (hG : ∀ b∈I, MeasurableSet (G b)) {b : ℕ} (hb : b∈I) :
    MeasurableSet (firstCoverBinND S I G b) := by
  apply (hS.inter (hG b hb)).diff
  exact MeasurableSet.biUnion (Finset.finite_toSet _).countable (fun c hc => hG c (Finset.mem_filter.mp hc).1)

theorem integral_firstCoverBinND {V : Type*} [MeasurableSpace V] (μ : Measure V)
    {S : Set V} (hS : MeasurableSet S) (I : Finset ℕ) (G : ℕ → Set V)
    (hG : ∀ b∈I, MeasurableSet (G b)) (hcover : S⊆⋃ b∈I, G b)
    (F : V → ℂ) (hF : IntegrableOn F S μ) :
    (∫ x in S, F x ∂μ)=∑ b∈I, ∫ x in firstCoverBinND S I G b, F x ∂μ := by
  have hh := integral_biUnion_finset I
    (fun b hb => measurableSet_firstCoverBinND hS I G hG hb)
    (firstCoverBinND_disjoint S I G)
    (fun b _ => hF.mono_set (fun x hx => (firstCoverBinND_subset S I G b hx).1))
  rw [firstCoverBinND_cover S I G hcover] at hh
  exact hh

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory

def farComparableSetND {d : ℕ} (a h : ℕ) (X Y : Fin d → ℤ) :
    Set ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :=
  ((ambientGridCell a X ×ˢ ambientGridCell a X) ×ˢ
    (ambientGridCell a Y ×ˢ ambientGridCell a Y)) ∩
    {x | 1/(4*(2:ℝ)^h)≤ max (dist x.1.1 x.1.2) (dist x.2.1 x.2.2) ∧
      max (dist x.1.1 x.1.2) (dist x.2.1 x.2.2)≤2* min (dist x.1.1 x.1.2) (dist x.2.1 x.2.2)}

lemma farComparableSetND_measurable {d : ℕ} (a h : ℕ) (X Y : Fin d → ℤ) :
    MeasurableSet (farComparableSetND a h X Y) := by
  apply (((measurableSet_ambientGridCell a X).prod (measurableSet_ambientGridCell a X)).prod
    ((measurableSet_ambientGridCell a Y).prod (measurableSet_ambientGridCell a Y))).inter
  have hd₁ : Continuous (fun x : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) => dist x.1.1 x.1.2) := by fun_prop
  have hd₂ : Continuous (fun x : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) => dist x.2.1 x.2.2) := by fun_prop
  exact (isClosed_le continuous_const (hd₁.max hd₂)).measurableSet.inter
    (isClosed_le (hd₁.max hd₂) (continuous_const.mul (hd₁.min hd₂))).measurableSet

noncomputable def farParentRegionND {d : ℕ} (a b : ℕ) (K : ℝ) (X Y : Fin d → ℤ) :
    Set ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :=
  ⋃ pq∈(farParentPairsND a b K X).product (farParentPairsND a b K Y),
    (ambientGridCell b pq.1.1 ×ˢ ambientGridCell b pq.1.2) ×ˢ
      (ambientGridCell b pq.2.1 ×ˢ ambientGridCell b pq.2.2)

lemma farParentRegionND_measurable {d : ℕ} (a b : ℕ) (K : ℝ) (X Y : Fin d → ℤ) :
    MeasurableSet (farParentRegionND a b K X Y) := by
  exact MeasurableSet.biUnion (Finset.finite_toSet _).countable (fun pq _ =>
    ((measurableSet_ambientGridCell b pq.1.1).prod (measurableSet_ambientGridCell b pq.1.2)).prod
      ((measurableSet_ambientGridCell b pq.2.1).prod (measurableSet_ambientGridCell b pq.2.2)))

theorem farComparableSetND_cover {d a h k : ℕ} (hK : 16*(d+1:ℝ)≤(2:ℝ)^k)
    (X Y : Fin d → ℤ) :
    farComparableSetND a h X Y ⊆ ⋃ b∈Finset.Icc (a+1) (h+k+2),
      farParentRegionND a b ((2:ℝ)^k) X Y := by
  intro x hx
  obtain ⟨hp,hl,hc⟩ := hx
  obtain ⟨b,hb,p,hp',q,hq',hx₁,hx₂,hy₁,hy₂⟩ :=
    far_comparable_finite_coverND hK hp.1.1 hp.1.2 hp.2.1 hp.2.2 hl hc
  exact mem_iUnion₂.mpr ⟨b,hb,mem_iUnion₂.mpr
    ⟨(p,q),Finset.mem_product.mpr ⟨hp',hq'⟩,⟨⟨hx₁,hx₂⟩,hy₁,hy₂⟩⟩⟩

theorem integral_farComparable_binsND {d a h k : ℕ} (hK : 16*(d+1:ℝ)≤(2:ℝ)^k)
    (X Y : Fin d → ℤ)
    (μ : Measure ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))))
    {S : Set ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))}
    (hS : MeasurableSet S) (hSsub : S⊆farComparableSetND a h X Y)
    (F : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) → ℂ)
    (hF : IntegrableOn F S μ) :
    (∫ x in S, F x ∂μ)=∑ b∈Finset.Icc (a+1) (h+k+2),
      ∫ x in firstCoverBinND S (Finset.Icc (a+1) (h+k+2))
        (fun b => farParentRegionND a b ((2:ℝ)^k) X Y) b, F x ∂μ :=
  integral_firstCoverBinND μ hS _ _ (fun b _ => farParentRegionND_measurable a b _ X Y)
    (hSsub.trans (farComparableSetND_cover hK X Y)) F hF

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory

lemma ae_ambientGridCell_nonzeroND {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d))) :
    ∀ᵐ x ∂ρ, ∀ b : ℕ, ∀ Q : Fin d → ℤ,
      x∈ambientGridCell b Q → ρ (ambientGridCell b Q)≠0 := by
  simp only [ae_all_iff]
  intro b Q
  by_cases hq : ρ (ambientGridCell b Q)=0
  · have hh : ∀ᵐ x ∂ρ, x∉ambientGridCell b Q := by
      rw [ae_iff]
      simpa only [not_not,ofPred_mem_eq] using hq
    filter_upwards [hh] with x hx hxc
    exact (hx hxc).elim
  · exact Filter.Eventually.of_forall (fun _ _ => hq)

noncomputable def occupiedDescendantsND {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (a b : ℕ) (X : Fin d → ℤ) : Finset (Fin d → ℤ) := by
  classical
  exact (ambientDescendantsND a b X).filter (fun Q => ρ (ambientGridCell b Q)≠0)

noncomputable def occupiedFarPairsND {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (a b : ℕ) (K : ℝ) (X : Fin d → ℤ) : Finset ((Fin d → ℤ) × (Fin d → ℤ)) := by
  classical
  exact (farParentPairsND a b K X).filter
    (fun p => ρ (ambientGridCell b p.1)≠0 ∧ ρ (ambientGridCell b p.2)≠0)

lemma occupiedFarPairsND_first {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    {a b : ℕ} {K : ℝ} {X : Fin d → ℤ} {p : (Fin d → ℤ) × (Fin d → ℤ)}
    (hp : p∈occupiedFarPairsND ρ a b K X) : p.1∈occupiedDescendantsND ρ a b X := by
  classical
  have hh := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨(mem_farParentPairsND_iff.mp hh.1).1,hh.2.1⟩

noncomputable def occupiedFarRegionND {d : ℕ}
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) (a b : ℕ) (K : ℝ) (X Y : Fin d → ℤ) :
    Set ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :=
  ⋃ pq∈(occupiedFarPairsND ρ a b K X).product (occupiedFarPairsND κ a b K Y),
    (ambientGridCell b pq.1.1 ×ˢ ambientGridCell b pq.1.2) ×ˢ
      (ambientGridCell b pq.2.1 ×ˢ ambientGridCell b pq.2.2)

lemma occupiedFarRegionND_measurable {d : ℕ}
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) (a b : ℕ) (K : ℝ) (X Y : Fin d → ℤ) :
    MeasurableSet (occupiedFarRegionND ρ κ a b K X Y) := by
  exact MeasurableSet.biUnion (Finset.finite_toSet _).countable (fun pq _ =>
    ((measurableSet_ambientGridCell b pq.1.1).prod (measurableSet_ambientGridCell b pq.1.2)).prod
      ((measurableSet_ambientGridCell b pq.2.1).prod (measurableSet_ambientGridCell b pq.2.2)))

theorem occupiedFarRegionND_ae_cover {d a h k : ℕ} (hK : 16*(d+1:ℝ)≤(2:ℝ)^k)
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (X Y : Fin d → ℤ) :
    ∀ᵐ x ∂(ρ.prod ρ).prod (κ.prod κ), x∈farComparableSetND a h X Y →
      x∈⋃ b∈Finset.Icc (a+1) (h+k+2), occupiedFarRegionND ρ κ a b ((2:ℝ)^k) X Y := by
  classical
  filter_upwards [
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae (ae_ambientGridCell_nonzeroND ρ)),
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae (ae_ambientGridCell_nonzeroND ρ)),
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae (ae_ambientGridCell_nonzeroND κ)),
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae (ae_ambientGridCell_nonzeroND κ))]
      with x hx₁ hx₂ hy₁ hy₂ hx
  obtain ⟨hp,hl,hc⟩ := hx
  obtain ⟨b,hb,p,hp',q,hq',hxP,hxP',hyQ,hyQ'⟩ :=
    far_comparable_finite_coverND hK hp.1.1 hp.1.2 hp.2.1 hp.2.2 hl hc
  have hp'' : p∈occupiedFarPairsND ρ a b ((2:ℝ)^k) X :=
    Finset.mem_filter.mpr ⟨hp',hx₁ b p.1 hxP,hx₂ b p.2 hxP'⟩
  have hq'' : q∈occupiedFarPairsND κ a b ((2:ℝ)^k) Y :=
    Finset.mem_filter.mpr ⟨hq',hy₁ b q.1 hyQ,hy₂ b q.2 hyQ'⟩
  exact mem_iUnion₂.mpr ⟨b,hb,mem_iUnion₂.mpr
    ⟨(p,q),Finset.mem_product.mpr ⟨hp'',hq''⟩,⟨⟨hxP,hxP'⟩,hyQ,hyQ'⟩⟩⟩

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
