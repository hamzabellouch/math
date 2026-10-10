import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PivotPaths03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
noncomputable section
open scoped BigOperators
open MeasureTheory Filter Function
noncomputable section
open scoped BigOperators
noncomputable section
open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
open scoped Topology BigOperators
noncomputable section
open scoped Topology BoundedContinuousFunction NNReal
open Topology
namespace SourceFiniteMenu
variable {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)]
  [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  (Γ : ∀ i, Subgroup (G i))

abbrev productLattice : Subgroup (∀ i, G i) := Subgroup.pi Set.univ Γ

 

def quotientPi : ((∀ i, G i) ⧸ productLattice G Γ) → ∀ i, G i ⧸ Γ i :=
  Quotient.lift (fun g i => QuotientGroup.mk (g i)) (by
    intro g h hgh
    funext i
    apply QuotientGroup.eq.mpr
    exact (Subgroup.mem_pi Set.univ).mp
      (QuotientGroup.leftRel_apply.mp hgh) i (Set.mem_univ i))

omit [∀ i, IsTopologicalGroup (G i)] in
@[simp] lemma quotientPi_mk [∀ i, IsTopologicalGroup (G i)] (g : ∀ i, G i) (i : ι) :
    quotientPi G Γ (QuotientGroup.mk g) i = QuotientGroup.mk (g i) := rfl

omit [∀ i, IsTopologicalGroup (G i)] in
lemma quotientPi_bijective [∀ i, IsTopologicalGroup (G i)] : Function.Bijective (quotientPi G Γ) := by
  constructor
  · intro g h hgh
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective h
    apply QuotientGroup.eq.mpr
    apply (Subgroup.mem_pi Set.univ).mpr
    intro i hi
    exact QuotientGroup.eq.mp (congrFun hgh i)
  · intro x
    choose g hg using fun i => QuotientGroup.mk_surjective (x i)
    exact ⟨QuotientGroup.mk g, funext hg⟩

omit [∀ i, IsTopologicalGroup (G i)] in
lemma quotientPi_continuous [∀ i, IsTopologicalGroup (G i)] : Continuous (quotientPi G Γ) := by
  exact (continuous_pi (fun i => QuotientGroup.continuous_mk.comp (continuous_apply i))).quotient_lift _

 
def quotientPiHomeomorph :
    ((∀ i, G i) ⧸ productLattice G Γ) ≃ₜ (∀ i, G i ⧸ Γ i) := by
  let e := Equiv.ofBijective (quotientPi G Γ) (quotientPi_bijective G Γ)
  refine { e with continuous_toFun := quotientPi_continuous G Γ, continuous_invFun := ?_ }
  apply (IsOpenQuotientMap.piMap (fun i => QuotientGroup.isOpenQuotientMap_mk (N := Γ i))).isQuotientMap.continuous_iff.mpr
  have he : e.symm ∘ Pi.map (fun i => (QuotientGroup.mk : G i → G i ⧸ Γ i)) =
      (QuotientGroup.mk : (∀ i, G i) → (∀ i, G i) ⧸ productLattice G Γ) := by
    funext g
    exact e.symm_apply_eq.mpr rfl
  change Continuous (e.symm ∘ Pi.map (fun i => (QuotientGroup.mk : G i → G i ⧸ Γ i)))
  rw [he]
  exact QuotientGroup.continuous_mk

@[simp] lemma quotientPiHomeomorph_mk (g : ∀ i, G i) (i : ι) :
    quotientPiHomeomorph G Γ (QuotientGroup.mk g) i = QuotientGroup.mk (g i) := rfl

 
omit [∀ i, IsTopologicalGroup (G i)] in
lemma product_step [∀ i, IsTopologicalGroup (G i)] [Fintype ι] [∀ i, Group.IsNilpotent (G i)]
    (s : ℕ) (hs : ∀ i, Group.nilpotencyClass (G i) ≤ s) :
    Group.nilpotencyClass (∀ i, G i) ≤ s := by
  rw [Group.nilpotencyClass_pi]
  exact Finset.sup_le fun i _ => hs i

section Metric
variable [Fintype ι]
  (metric : ∀ i, MetricSpace (G i ⧸ Γ i))
  (hmetric : ∀ i, QuotientGroup.instTopologicalSpace (Γ i) =
    (metric i).toUniformSpace.toTopologicalSpace)

 

@[instance_reducible] def productMetric : MetricSpace ((∀ i, G i) ⧸ productLattice G Γ) :=
  letI : ∀ i, MetricSpace (G i ⧸ Γ i) := fun i => (metric i).replaceTopology (hmetric i)
  (quotientPiHomeomorph G Γ).isEmbedding.comapMetricSpace (quotientPiHomeomorph G Γ)

lemma productMetric_compatible :
    QuotientGroup.instTopologicalSpace (productLattice G Γ) =
      (productMetric G Γ metric hmetric).toUniformSpace.toTopologicalSpace := rfl

lemma quotientPi_isometry :
    letI : ∀ i, MetricSpace (G i ⧸ Γ i) := fun i => (metric i).replaceTopology (hmetric i)
    letI : MetricSpace ((∀ i, G i) ⧸ productLattice G Γ) := productMetric G Γ metric hmetric
    Isometry (quotientPi G Γ) := by
  let : ∀ i, MetricSpace (G i ⧸ Γ i) := fun i => (metric i).replaceTopology (hmetric i)
  let : MetricSpace ((∀ i, G i) ⧸ productLattice G Γ) := productMetric G Γ metric hmetric
  intro x y
  rfl

lemma projection_lipschitz (i : ι) :
    letI : ∀ i, MetricSpace (G i ⧸ Γ i) := fun i => (metric i).replaceTopology (hmetric i)
    letI : MetricSpace ((∀ i, G i) ⧸ productLattice G Γ) := productMetric G Γ metric hmetric
    LipschitzWith 1 (fun z => quotientPi G Γ z i) := by
  let : ∀ i, MetricSpace (G i ⧸ Γ i) := fun i => (metric i).replaceTopology (hmetric i)
  let : MetricSpace ((∀ i, G i) ⧸ productLattice G Γ) := productMetric G Γ metric hmetric
  simpa only [one_mul, Function.comp_def, Function.eval] using (LipschitzWith.eval i).comp (quotientPi_isometry G Γ metric hmetric).lipschitzWith

end Metric

 

def paddedObservable (i : ι) (F : (G i ⧸ Γ i) →ᵇ ℝ) :
    ((∀ i, G i) ⧸ productLattice G Γ) →ᵇ ℝ :=
  F.compContinuous ⟨fun z => quotientPi G Γ z i,
    (continuous_apply i).comp (quotientPi_continuous G Γ)⟩

@[simp] lemma paddedObservable_apply (i : ι) (F : (G i ⧸ Γ i) →ᵇ ℝ)
    (z : (∀ i, G i) ⧸ productLattice G Γ) :
    paddedObservable G Γ i F z = F (quotientPi G Γ z i) := rfl

 
lemma padded_orbit [DecidableEq ι] (i : ι) (F : (G i ⧸ Γ i) →ᵇ ℝ)
    (g x : G i) (k : ℤ) :
    paddedObservable G Γ i F (QuotientGroup.mk ((Pi.mulSingle i g)^k * Pi.mulSingle i x)) =
      F (QuotientGroup.mk (g^k*x)) := by
  simp [Pi.mul_apply, Pi.pow_apply]

lemma padded_lipschitz [Fintype ι]
    (metric : ∀ i, MetricSpace (G i ⧸ Γ i))
    (hmetric : ∀ i, QuotientGroup.instTopologicalSpace (Γ i) =
      (metric i).toUniformSpace.toTopologicalSpace) :
    letI : ∀ i, MetricSpace (G i ⧸ Γ i) := fun i => (metric i).replaceTopology (hmetric i)
    letI : MetricSpace ((∀ i, G i) ⧸ productLattice G Γ) := productMetric G Γ metric hmetric
    ∀ (i : ι) (F : (G i ⧸ Γ i) →ᵇ ℝ) (K : ℝ≥0), LipschitzWith K F →
      LipschitzWith K (paddedObservable G Γ i F) := by
  let : ∀ i, MetricSpace (G i ⧸ Γ i) := fun i => (metric i).replaceTopology (hmetric i)
  let : MetricSpace ((∀ i, G i) ⧸ productLattice G Γ) := productMetric G Γ metric hmetric
  intro i F K hF
  change LipschitzWith K (fun z => F (quotientPi G Γ z i))
  simpa only [mul_one, Function.comp_def] using hF.comp (projection_lipschitz G Γ metric hmetric i)

 

theorem finite_menu_padding [Fintype ι]
    (metric : ∀ i, MetricSpace (G i ⧸ Γ i))
    (hmetric : ∀ i, QuotientGroup.instTopologicalSpace (Γ i) =
      (metric i).toUniformSpace.toTopologicalSpace)
    {κ : Type*} (select : κ → ι) (g x : ∀ p, G (select p))
    (F : ∀ p, (G (select p) ⧸ Γ (select p)) →ᵇ ℝ) (K : ℝ≥0) (B : ℝ) :
    letI : ∀ i, MetricSpace (G i ⧸ Γ i) := fun i => (metric i).replaceTopology (hmetric i)
    letI : MetricSpace ((∀ i, G i) ⧸ productLattice G Γ) := productMetric G Γ metric hmetric
    (∀ p, LipschitzWith K (F p)) → (∀ p z, |F p z| ≤ B) →
    ∃ (g' x' : κ → ∀ i, G i)
      (F' : κ → ((∀ i, G i) ⧸ productLattice G Γ) →ᵇ ℝ),
      (∀ p, LipschitzWith K (F' p)) ∧ (∀ p z, |F' p z| ≤ B) ∧
      (∀ (p : κ) (k : ℤ), F' p (QuotientGroup.mk ((g' p)^k*x' p)) =
        F p (QuotientGroup.mk ((g p)^k*x p))) := by
  let : ∀ i, MetricSpace (G i ⧸ Γ i) := fun i => (metric i).replaceTopology (hmetric i)
  let : MetricSpace ((∀ i, G i) ⧸ productLattice G Γ) := productMetric G Γ metric hmetric
  intro hLip hBound
  classical
  refine ⟨fun p => Pi.mulSingle (select p) (g p),
    fun p => Pi.mulSingle (select p) (x p),
    fun p => paddedObservable G Γ (select p) (F p), ?_, ?_, ?_⟩
  · intro p
    exact padded_lipschitz G Γ metric hmetric _ _ K (hLip p)
  · intro p z
    exact hBound p _
  · intro p k
    exact padded_orbit G Γ (select p) (F p) (g p) (x p) k

 
lemma product_compact [∀ i, CompactSpace (G i ⧸ Γ i)] :
    CompactSpace ((∀ i, G i) ⧸ productLattice G Γ) :=
  (quotientPiHomeomorph G Γ).symm.compactSpace

 

def subgroupPiHomeomorph : productLattice G Γ ≃ₜ (∀ i, Γ i) where
  toFun g i := ⟨g.val i, (Subgroup.mem_pi Set.univ).mp g.property i (Set.mem_univ i)⟩
  invFun g := ⟨fun i => (g i).val, (Subgroup.mem_pi Set.univ).mpr (fun i _ => (g i).property)⟩
  left_inv g := by rfl
  right_inv g := by rfl
  continuous_toFun := continuous_pi (fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_pi (fun i =>
    continuous_subtype_val.comp (continuous_apply i))).subtype_mk _

omit [∀ i, IsTopologicalGroup (G i)] in
lemma product_discrete [∀ i, IsTopologicalGroup (G i)] [Finite ι] [∀ i, DiscreteTopology (Γ i)] :
    DiscreteTopology (productLattice G Γ) :=
  (subgroupPiHomeomorph G Γ).symm.discreteTopology

end SourceFiniteMenu
end

 

 

 

noncomputable section
open scoped Topology BigOperators commutatorElement
namespace SourceProductChart
open RationalLattice MalcevCharacters CubeFaces SourceProductCoordinates
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

 

variable (n : Fin d → ℕ) (wt : ∀ i, Fin (n i) → ℕ)

def key (z : Σ i, Fin (n i)) : ℕ ×ₗ (Fin d ×ₗ ℕ) :=
  toLex (wt z.1 z.2, toLex (z.1,z.2.val))

lemma key_injective : Function.Injective (key n wt) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  have hi : i=i' := congrArg (fun z => (ofLex (ofLex z).2).1) h
  subst i'
  have hj : j.val = j'.val := congrArg (fun z => (ofLex (ofLex z).2).2) h
  exact congrArg (Sigma.mk i) (Fin.ext hj)

 

def Index := Σ i, Fin (n i)
instance : Fintype (Index n) := inferInstanceAs (Fintype (Σ i, Fin (n i)))

@[instance_reducible] def sortedOrder : LinearOrder (Index n) :=
  LinearOrder.lift' (key n wt) (key_injective n wt)

def orderedEnumeration : letI := sortedOrder n wt
    Fin (Fintype.card (Index n)) ≃o Index n := by
  letI := sortedOrder n wt
  exact Fintype.orderIsoFinOfCardEq (Index n) rfl

 
def enumeration : Fin (Fintype.card (Σ i, Fin (n i))) ≃ Σ i, Fin (n i) := by
  exact (orderedEnumeration n wt).toEquiv

lemma enumeration_local (hw : ∀ i, Monotone (wt i)) (i : Fin d) :
    StrictMono (fun j : Fin (n i) => (enumeration n wt).symm ⟨i,j⟩) := by
  let := sortedOrder n wt
  intro j k hjk
  change (orderedEnumeration n wt).symm ⟨i,j⟩ <
    (orderedEnumeration n wt).symm ⟨i,k⟩
  apply (orderedEnumeration n wt).symm.strictMono
  change key n wt ⟨i,j⟩ < key n wt ⟨i,k⟩
  rw [key, key, Prod.Lex.toLex_lt_toLex]
  rcases lt_or_eq_of_le (hw i hjk.le) with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h,?_⟩
    exact Prod.Lex.right i hjk

lemma enumeration_weights :
    Monotone (fun k => wt (enumeration n wt k).1 (enumeration n wt k).2) := by
  let := sortedOrder n wt
  intro k l hkl
  have h := (orderedEnumeration n wt).monotone hkl
  change key n wt (enumeration n wt k) ≤ key n wt (enumeration n wt l) at h
  rw [key,key,Prod.Lex.toLex_le_toLex] at h
  exact h.elim (fun h => h.le) (fun h => h.1.le)

section Product
variable (G : Fin d → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  (Γ : ∀ i, Subgroup (G i)) (H : ∀ i, Filtration (G i))

def filtration : Filtration (∀ i, G i) where
  level k := Subgroup.pi Set.univ (fun i => (H i).level k)
  antitone := by
    intro k l hkl g hg
    apply (Subgroup.mem_pi _).mpr
    intro i hi
    exact (H i).antitone hkl ((Subgroup.mem_pi _).mp hg i hi)
  commutator_le k l := Subgroup.commutator_le.mpr (by
    intro g hg h hh
    apply (Subgroup.mem_pi _).mpr
    intro i hi
    have hc := (H i).commutator_le k l (Subgroup.commutator_mem_commutator
      ((Subgroup.mem_pi _).mp hg i hi) ((Subgroup.mem_pi _).mp hh i hi))
    simpa only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply] using hc)

omit [∀ i, TopologicalSpace (G i)] in
@[simp] lemma filtration_mem [∀ i, TopologicalSpace (G i)] (k : ℕ) (g : ∀ i, G i) :
    g ∈ (filtration G H).level k ↔ ∀ i, g i ∈ (H i).level k := by
  simp [filtration, Subgroup.mem_pi]

lemma filtration_top (k : ℕ) (hk : ∀ i, (H i).level k = ⊤) :
    (filtration G H).level k = ⊤ := by
  ext g
  simp [filtration_mem, hk]

lemma filtration_bot (k : ℕ) (hk : ∀ i, (H i).level k = ⊥) :
    (filtration G H).level k = ⊥ := by
  ext g
  simp only [filtration_mem, hk, Subgroup.mem_bot]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

variable {s : ℕ} (C : ∀ i, Chart s (G i) (Γ i))

 
def product : Chart s (∀ i, G i) (SourceFiniteMenu.productLattice G Γ) := by
  let n := fun i => (C i).dim
  let wt := fun i => (C i).weight
  let e := enumeration n wt
  have he := enumeration_local n wt (fun i => (C i).weight_mono)
  let c := coordinates n G (fun i => (C i).coords) e he
  refine {
    dim := Fintype.card (Σ i, Fin (n i))
    coords := c
    second := secondKind n G (fun i => (C i).coords) e he (fun i => (C i).second)
    filtration := filtration G (fun i => (C i).filtration)
    weight := fun k => wt (e k).1 (e k).2
    weight_pos := fun k => (C (e k).1).weight_pos (e k).2
    weight_mono := enumeration_weights n wt
    level0 := filtration_top G _ 0 (fun i => (C i).level0)
    level1 := filtration_top G _ 1 (fun i => (C i).level1)
    step := filtration_bot G _ (s+1) (fun i => (C i).step)
    level_iff := ?_
    lattice_iff := ?_ }
  · intro k g
    rw [filtration_mem]
    constructor
    · intro h j hj
      exact ((C (e j).1).level_iff k _).mp (h (e j).1) (e j).2 hj
    · intro h i
      apply ((C i).level_iff k _).mpr
      intro j hj
      have hh := h (e.symm ⟨i,j⟩)
      change wt (e (e.symm ⟨i,j⟩)).1 (e (e.symm ⟨i,j⟩)).2 < k →
        (C (e (e.symm ⟨i,j⟩)).1).coords.coord (g (e (e.symm ⟨i,j⟩)).1)
          (e (e.symm ⟨i,j⟩)).2 = 0 at hh
      have hwj := congrArg (fun z : Σ i, Fin (n i) => wt z.1 z.2) (e.apply_symm_apply ⟨i,j⟩)
      have hcj := congrArg (fun z : Σ i, Fin (n i) => (C z.1).coords.coord (g z.1) z.2)
        (e.apply_symm_apply ⟨i,j⟩)
      rw [hwj, hcj] at hh
      exact hh hj
  · intro g
    change (∀ i ∈ Set.univ, g i ∈ Γ i) ↔ _
    constructor
    · intro h j
      exact ((C (e j).1).lattice_iff _).mp (h (e j).1 (Set.mem_univ _)) (e j).2
    · intro h i hi
      apply ((C i).lattice_iff _).mpr
      intro j
      have hh := h (e.symm ⟨i,j⟩)
      change ∃ z : ℤ, (C (e (e.symm ⟨i,j⟩)).1).coords.coord
        (g (e (e.symm ⟨i,j⟩)).1) (e (e.symm ⟨i,j⟩)).2 = z at hh
      have hcj := congrArg (fun z : Σ i, Fin (n i) => (C z.1).coords.coord (g z.1) z.2)
        (e.apply_symm_apply ⟨i,j⟩)
      rwa [hcj] at hh

end Product
end SourceProductChart

 

 

 

end
end
end
end
end
end
end
end

end OAI
