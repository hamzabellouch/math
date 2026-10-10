import Mathlib
import OAI.NumberTheory.PrimePackets.RootCharts

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace PrimeDegreePackets

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

 
def scaleBaseKernel (κ : Kernel α β) (w : α → ℝ≥0∞) (hw : Measurable w) : Kernel α β where
  toFun a := w a • κ a
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simpa only [Measure.smul_apply,smul_eq_mul,Pi.mul_apply] using hw.fun_mul (κ.measurable_coe hS)

lemma scaleBaseKernel_apply (κ : Kernel α β) (w : α → ℝ≥0∞) (hw : Measurable w) (a : α) :
    scaleBaseKernel κ w hw a = w a • κ a := rfl

lemma scaleBaseKernel_finite (κ : Kernel α β) [IsFiniteKernel κ]
    (w : α → ℝ≥0∞) (hw : Measurable w) (hw1 : ∀ a, w a ≤ 1) :
    IsFiniteKernel (scaleBaseKernel κ w hw) := by
  refine ⟨⟨κ.bound,κ.bound_lt_top,fun a => ?_⟩⟩
  change w a * κ a univ ≤ κ.bound
  calc
    _ ≤ 1 * κ a univ := mul_le_mul_of_nonneg_right (hw1 a) (bot_le)
    _ ≤ κ.bound := by simpa only [one_mul] using κ.measure_le_bound a univ

lemma compProd_scaleBaseKernel (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsSFiniteKernel κ] (w : α → ℝ≥0∞) (hw : Measurable w)
    [IsSFiniteKernel (scaleBaseKernel κ w hw)] :
    μ ⊗ₘ scaleBaseKernel κ w hw = μ.withDensity w ⊗ₘ κ := by
  ext S hS
  rw [Measure.compProd_apply hS,Measure.compProd_apply hS,
    lintegral_withDensity_eq_lintegral_mul μ hw (Kernel.measurable_kernel_prodMk_left hS)]
  rfl

lemma compProd_restrict_rectangle (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ]
    {U : Set α} {V : Set β} (hU : MeasurableSet U) (hV : MeasurableSet V) :
    (μ ⊗ₘ κ).restrict (U ×ˢ V) = μ.restrict U ⊗ₘ κ.restrict hV := by
  ext S hS
  rw [Measure.restrict_apply hS,Measure.compProd_apply (hS.inter (hU.prod hV)),
    Measure.compProd_apply hS,← lintegral_indicator hU]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ U
  · simp only [indicator_of_mem ha,Kernel.restrict_apply,
      Measure.restrict_apply (measurable_prodMk_left hS)]
    congr 1
    ext b
    simp [ha]
  · simp only [indicator_of_notMem ha]
    have he : Prod.mk a ⁻¹' (S ∩ U ×ˢ V) = ∅ := by ext b; simp [ha]
    rw [he,measure_empty]

lemma fst_compProd_withDensity (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).fst = μ.withDensity (fun a => κ a univ) := by
  ext U hU
  rw [Measure.fst_apply hU,withDensity_apply _ hU]
  rw [←Set.prod_univ]
  exact Measure.compProd_apply_prod hU MeasurableSet.univ

 

lemma restricted_conditional_marginal [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    {U : Set α} {V : Set β} (hU : MeasurableSet U) (hV : MeasurableSet V) :
    (ρ.restrict (U ×ˢ V)).fst =
      (ρ.fst.restrict U).withDensity (fun a => ρ.condKernel a V) := by
  have H := compProd_restrict_rectangle ρ.fst ρ.condKernel hU hV
  rw [Measure.disintegrate] at H
  rw [H,fst_compProd_withDensity]
  congr 1
  funext a
  simp only [Kernel.restrict_apply,Measure.restrict_apply MeasurableSet.univ,univ_inter]

 

theorem restricted_conditional_kernel [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    {U : Set α} {V : Set β} (hU : MeasurableSet U) (hV : MeasurableSet V) :
    ∀ᵐ a ∂ρ.fst.restrict U,
      ρ.condKernel a V • (ρ.restrict (U ×ˢ V)).condKernel a =
        (ρ.condKernel a).restrict V := by
  let σ := ρ.restrict (U ×ˢ V)
  let r : α → ℝ≥0∞ := fun a => ρ.condKernel a V
  have hr : Measurable r := ρ.condKernel.measurable_coe hV
  have hr1 : ∀ a, r a ≤ 1 := fun a => prob_le_one
  let κ := scaleBaseKernel σ.condKernel r hr
  have : IsFiniteKernel κ := scaleBaseKernel_finite σ.condKernel r hr hr1
  have he : ρ.fst.restrict U ⊗ₘ κ = ρ.fst.restrict U ⊗ₘ ρ.condKernel.restrict hV := by
    calc
      _ = (ρ.fst.restrict U).withDensity r ⊗ₘ σ.condKernel :=
        compProd_scaleBaseKernel _ _ r hr
      _ = σ.fst ⊗ₘ σ.condKernel := by
        rw [restricted_conditional_marginal ρ hU hV]
      _ = σ := Measure.disintegrate σ σ.condKernel
      _ = ρ.fst.restrict U ⊗ₘ ρ.condKernel.restrict hV := by
        rw [←compProd_restrict_rectangle _ _ hU hV,Measure.disintegrate]
  exact Kernel.ae_eq_of_compProd_eq he

end PrimeDegreePackets


namespace PrimeDegreePackets.RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

def shrink (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) : RootBox hij k :=
  ⟨U,V,hU,hV,B.embedding.comp (Topology.IsOpenEmbedding.inclusion
    (Set.prod_mono hUB hVB) ((hU.prod hV).preimage continuous_subtype_val))⟩

 

theorem shrink_coordinateMeasure (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n)) :
    (B.shrink U V hU hV hUB hVB).coordinateMeasure μ =
      (B.coordinateMeasure μ).restrict (U ×ˢ V) := by
  ext S hS
  rw [Measure.restrict_apply hS,coordinateMeasure_apply _ μ hS,
    coordinateMeasure_apply _ μ (hS.inter (hU.measurableSet.prod hV.measurableSet))]
  congr 2
  change S ∩ U ×ˢ V = (S ∩ U ×ˢ V) ∩ B.domain
  exact (Set.inter_eq_left.mpr ((Set.inter_subset_right).trans (Set.prod_mono hUB hVB))).symm

 

theorem shrink_conditionalKernel (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst.restrict U,
      B.conditionalKernel μ s V •
        (B.shrink U V hU hV hUB hVB).conditionalKernel μ s =
          (B.conditionalKernel μ s).restrict V := by
  simp only [conditionalKernel,shrink_coordinateMeasure]
  exact restricted_conditional_kernel _ hU.measurableSet hV.measurableSet

 

theorem shrink_marginal (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ((B.shrink U V hU hV hUB hVB).coordinateMeasure μ).fst =
      ((B.coordinateMeasure μ).fst.restrict U).withDensity
        (fun s => B.conditionalKernel μ s V) := by
  rw [shrink_coordinateMeasure,restricted_conditional_marginal _ hU.measurableSet hV.measurableSet]
  rfl

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets

lemma transitive_eigenfunction_ne_zero
    {H I : Type*} [Group H] [Fintype I] [MulAction H I] [MulAction.IsPretransitive H I]
    (χ : H →* ℝˣ) (v : I → ℝ)
    (hv : v ≠ 0) (heq : ∀ g i, v (g • i) = (χ g : ℝ)*v i) :
    ∀ i, v i ≠ 0 := by
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv
  intro i hi
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H i j
  have H := heq g i
  rw [hg,hi,mul_zero] at H
  exact hj H

 

theorem transitive_eigencharacter_pow_card
    {H I : Type*} [Group H] [Fintype I] [MulAction H I] [MulAction.IsPretransitive H I]
    (χ : H →* ℝˣ) (v : I → ℝ)
    (hv : v ≠ 0) (heq : ∀ g i, v (g • i) = (χ g : ℝ)*v i) (g : H) :
    (χ g : ℝ) ^ Fintype.card I = 1 := by
  have hn : (∏ i, v i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => transitive_eigenfunction_ne_zero χ v hv heq i)
  have hp := Equiv.prod_comp (MulAction.toPerm g) v
  change (∏ i, v (g • i)) = ∏ i, v i at hp
  simp only [heq,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hp
  exact (mul_right_cancel₀ hn (hp.trans (one_mul _).symm))

 

theorem odd_transitive_quadratic_eigencharacter_trivial
    {H I : Type*} [Group H] [Fintype I] [MulAction H I] [MulAction.IsPretransitive H I]
    (hodd : Odd (Fintype.card I)) (χ : H →* ℝˣ)
    (hχ : ∀ g, (χ g : ℝ)^2 = 1) (v : I → ℝ)
    (hv : v ≠ 0) (heq : ∀ g i, v (g • i) = (χ g : ℝ)*v i) :
    χ = 1 := by
  ext g
  have hp := transitive_eigencharacter_pow_card χ v hv heq g
  obtain ⟨k,hk⟩ := hodd
  rw [hk,pow_add,pow_mul,hχ,one_pow,pow_one,one_mul] at hp
  exact hp

end PrimeDegreePackets

open Set Filter Topology
namespace PrimeDegreePackets

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space B]

lemma localHomeomorph_collision_free_isOpen {f : A → B} (hf : IsLocalHomeomorph f) :
    IsOpen {p : A × A | f p.1 ≠ f p.2 ∨ p.1 = p.2} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨x,y⟩ (hne | heq)
  · exact mem_of_superset
      ((isOpen_ne_fun (hf.continuous.comp continuous_fst)
        (hf.continuous.comp continuous_snd)).mem_nhds hne)
      (fun _ h => Or.inl h)
  · change x = y at heq
    subst y
    obtain ⟨U,hU,hemb⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hf x
    apply mem_of_superset (prod_mem_nhds hU hU)
    rintro ⟨a,b⟩ ⟨ha,hb⟩
    by_cases h : f a = f b
    · have H : (⟨a,ha⟩ : U) = ⟨b,hb⟩ := hemb.injective h
      exact Or.inr (congrArg Subtype.val H)
    · exact Or.inl h

 

theorem compact_injective_localHomeomorph_neighborhood {f : A → B}
    (hf : IsLocalHomeomorph f) {K : Set A} (hK : IsCompact K) (hi : Set.InjOn f K) :
    ∃ U : Set A, IsOpen U ∧ K ⊆ U ∧ Topology.IsOpenEmbedding (U.domRestrict f) := by
  have hc : K ×ˢ K ⊆ {p : A × A | f p.1 ≠ f p.2 ∨ p.1 = p.2} := by
    rintro ⟨a,b⟩ ⟨ha,hb⟩
    by_cases h : f a = f b
    · exact Or.inr (hi ha hb h)
    · exact Or.inl h
  obtain ⟨U,V,hU,hV,hKU,hKV,hUV⟩ := generalized_tube_lemma hK hK
    (localHomeomorph_collision_free_isOpen hf) hc
  refine ⟨U ∩ V,hU.inter hV,fun _ hx => ⟨hKU hx,hKV hx⟩,?_⟩
  apply (hf.comp (hU.inter hV).isOpenEmbedding_subtypeVal.isLocalHomeomorph).isOpenEmbedding_of_injective
  intro a b hab
  apply Subtype.ext
  have H := hUV (show (a.val,b.val) ∈ U ×ˢ V from ⟨a.prop.1,b.prop.2⟩)
  exact H.resolve_left (fun hne => hne hab)

end PrimeDegreePackets

open Set Filter Topology MeasureTheory
namespace PrimeDegreePackets

lemma root_time_injective_of_free {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (s : RootSlice i j k) (a : ℝ)
    (hfree : ∀ v : ℝ,
      rightAction (rootQuotientParametrization hij (s,a))
        (Matrix.SpecialLinearGroup.transvection hij v) =
          rootQuotientParametrization hij (s,a) → v = 0) :
    Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t)) := by
  intro t u heq
  have H := congrArg (fun x => rightAction x
    (Matrix.SpecialLinearGroup.transvection hij (a-u))) heq
  rw [←rootQuotientParametrization_add hij s t (a-u),
    ←rootQuotientParametrization_add hij s u (a-u)] at H
  have ht : t+(a-u)=a+(t-u) := by ring
  have hu : u+(a-u)=a := by ring
  rw [ht,hu,rootQuotientParametrization_add hij s a (t-u)] at H
  exact sub_eq_zero.mp (hfree (t-u) H)

 

theorem rootBox_contains_compact_time {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (s : RootSlice i j k)
    (hinj : Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t)))
    (a b : ℝ) :
    ∃ B : RootBox hij k, s ∈ B.transverse ∧ Icc a b ⊆ B.time := by
  have hf := rootQuotientParametrization_localHomeomorph (k := k) hij
  have hi : Set.InjOn (rootQuotientParametrization hij) ({s} ×ˢ Icc a b) := by
    rintro ⟨s₁,t₁⟩ ⟨hs₁,ht₁⟩ ⟨s₂,t₂⟩ ⟨hs₂,ht₂⟩ heq
    have h₁ : s₁ = s := hs₁
    have h₂ : s₂ = s := hs₂
    subst s₁
    subst s₂
    exact Prod.ext rfl (hinj heq)
  obtain ⟨W,hW,hKW,hemb⟩ := compact_injective_localHomeomorph_neighborhood hf
    (isCompact_singleton.prod isCompact_Icc) hi
  obtain ⟨U,V,hU,hV,hsU,hTV,hUV⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({s} : Set (RootSlice i j k)))
    (isCompact_Icc : IsCompact (Icc a b)) hW hKW
  have he := hemb.comp (Topology.IsOpenEmbedding.inclusion hUV
    ((hU.prod hV).preimage continuous_subtype_val))
  exact ⟨⟨U,V,hU,hV,he⟩,hsU (Set.mem_singleton s),hTV⟩

 

theorem rootBox_arbitrary_length_of_free {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x : X n) (hfree : ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (R : ℝ) :
    ∃ (k : Fin n) (B : RootBox hij k) (s : RootSlice i j k) (t : ℝ),
      s ∈ B.transverse ∧ Icc (t-R) (t+R) ⊆ B.time ∧
        rootQuotientParametrization hij (s,t) = x := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨k,hk⟩ := exists_rootPivot i g
    let z := rootPivotHomeomorph (j := j) hij (⟨g,hk⟩ : RootPivot i k)
    have hz : rootQuotientParametrization hij z = Quotient.mk _ g := by
      unfold rootQuotientParametrization z
      rw [Homeomorph.symm_apply_apply]
    have hi := root_time_injective_of_free hij z.1 z.2 (hz ▸ hfree)
    obtain ⟨B,hs,hT⟩ := rootBox_contains_compact_time hij z.1 hi (z.2-R) (z.2+R)
    exact ⟨k,B,z.1,z.2,hs,hT,hz⟩

 

theorem ae_rootBox_arbitrary_length (d : ℕ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ) :
    ∀ᵐ x ∂μ, ∀ (i j : Fin (d+1)) (hij : i ≠ j) (R : ℝ),
      ∃ (k : Fin (d+1)) (B : RootBox hij k) (s : RootSlice i j k) (t : ℝ),
        s ∈ B.transverse ∧ Icc (t-R) (t+R) ⊆ B.time ∧
          rootQuotientParametrization hij (s,t) = x := by
  filter_upwards [ae_root_stabilizer_trivial d μ hA] with x hx
  intro i j hij R
  exact rootBox_arbitrary_length_of_free hij x (hx i j hij) R

end PrimeDegreePackets

open MeasureTheory Set Filter Topology
namespace PrimeDegreePackets

variable {A : Type*} [TopologicalSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A]

omit [BorelSpace A] in
lemma measure_eq_of_ae_local_restrict_eq (μ ν : Measure A) [IsFiniteMeasure μ]
    (hmass : μ univ = ν univ)
    (hloc : ∀ᵐ x ∂μ, ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ μ.restrict U = ν.restrict U) :
    μ = ν := by
  let S : Set (Set A) := {U | IsOpen U ∧ μ.restrict U = ν.restrict U}
  obtain ⟨T,hTc,hTS,hTU⟩ := TopologicalSpace.isOpen_sUnion_countable S (fun U hU => hU.1)
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃₀ T := by
    filter_upwards [hloc] with x hx
    obtain ⟨U,hU,hxU,heq⟩ := hx
    rw [hTU]
    exact mem_sUnion.mpr ⟨U,⟨hU,heq⟩,hxU⟩
  have heq : μ.restrict (⋃₀ T) = ν.restrict (⋃₀ T) :=
    (Measure.restrict_sUnion_congr hTc).mpr (fun U hU => (hTS hU).2)
  rw [Measure.restrict_eq_self_of_ae_mem hae] at heq
  exact Measure.eq_of_le_of_measure_univ_eq (heq.le.trans Measure.restrict_le_self) hmass

 

theorem homeomorph_measurePreserving_of_ae_local (μ : Measure A) [IsFiniteMeasure μ]
    (h : A ≃ₜ A)
    (hloc : ∀ᵐ x ∂μ, ∃ U : Set A, IsOpen U ∧ x ∈ U ∧
      ∀ S : Set A, MeasurableSet S → S ⊆ U → μ (h '' S) = μ S) :
    MeasurePreserving h μ μ := by
  have he : μ = Measure.comap h μ := by
    apply measure_eq_of_ae_local_restrict_eq
    · rw [h.measurableEmbedding.comap_apply, Set.image_univ, h.surjective.range_eq]
    · filter_upwards [hloc] with x hx
      obtain ⟨U,hU,hxU,hsets⟩ := hx
      refine ⟨U,hU,hxU,?_⟩
      ext S hS
      rw [Measure.restrict_apply hS,Measure.restrict_apply hS,
        h.measurableEmbedding.comap_apply]
      exact (hsets (S ∩ U) (hS.inter hU.measurableSet) inter_subset_right).symm
  refine ⟨h.continuous.measurable,?_⟩
  conv_lhs => rw [he]
  rw [h.measurableEmbedding.map_comap]
  simp only [h.surjective.range_eq,Measure.restrict_univ]

end PrimeDegreePackets

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
namespace PrimeDegreePackets.RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

def HasHaarConditionals (B : RootBox hij k) (μ : Measure (X n)) [IsFiniteMeasure μ] : Prop :=
  ∃ c : ℝ≥0, ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
    B.conditionalKernel μ s = c • (volume.restrict B.time)

lemma coordinateMeasure_of_haarConditionals (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] (hhaar : B.HasHaarConditionals μ) :
    ∃ c : ℝ≥0, B.coordinateMeasure μ =
      ((B.coordinateMeasure μ).fst.prod (c • (volume : Measure ℝ))).restrict (univ ×ˢ B.time) := by
  obtain ⟨c,hc⟩ := hhaar
  refine ⟨c,?_⟩
  calc
    B.coordinateMeasure μ = (B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ := by
      rw [conditionalKernel,Measure.disintegrate]
    _ = (B.coordinateMeasure μ).fst ⊗ₘ Kernel.const _ (c • volume.restrict B.time) :=
      Measure.compProd_congr hc
    _ = _ := by
      rw [Measure.compProd_const,←Measure.restrict_smul,←Measure.prod_restrict,Measure.restrict_univ]

def timeTranslation (a : ℝ) : (RootSlice i j k × ℝ) ≃ₜ (RootSlice i j k × ℝ) :=
  (Homeomorph.refl _).prodCongr (Homeomorph.addRight a)

lemma timeTranslation_apply (a : ℝ) (z : RootSlice i j k × ℝ) :
    timeTranslation a z = (z.1,z.2+a) := rfl

lemma prod_volume_timeTranslation_invariant (ν : Measure (RootSlice i j k)) [SFinite ν]
    (c : ℝ≥0) (a : ℝ) :
    Measure.map (timeTranslation (i := i) (j := j) (k := k) a)
      (ν.prod (c • (volume : Measure ℝ))) = ν.prod (c • volume) := by
  change Measure.map (Prod.map id (fun t : ℝ => t+a)) _ = _
  rw [←Measure.map_prod_map ν _ measurable_id (by fun_prop),Measure.map_id,
    Measure.map_smul c (μ := (volume : Measure ℝ)) (f := fun t : ℝ => t + a)
      (measurable_id.add_const a).aemeasurable,
    map_add_right_eq_self]

 

theorem coordinateMeasure_translate_of_haar (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] (hhaar : B.HasHaarConditionals μ) (a : ℝ)
    {S : Set (RootSlice i j k × ℝ)} (hS : MeasurableSet S)
    (hSB : S ⊆ B.domain) (hTB : timeTranslation a '' S ⊆ B.domain) :
    B.coordinateMeasure μ (timeTranslation a '' S) = B.coordinateMeasure μ S := by
  obtain ⟨c,hc⟩ := B.coordinateMeasure_of_haarConditionals μ hhaar
  let ρ := (B.coordinateMeasure μ).fst.prod (c • (volume : Measure ℝ))
  have hT : MeasurableSet (timeTranslation a '' S) :=
    (timeTranslation a).measurableEmbedding.measurableSet_image.mpr hS
  have H := congrArg (fun m : Measure (RootSlice i j k × ℝ) => m (timeTranslation a '' S))
    (prod_volume_timeTranslation_invariant (B.coordinateMeasure μ).fst c a)
  rw [Measure.map_apply (timeTranslation a).continuous.measurable hT,
    (timeTranslation a).injective.preimage_image] at H
  rw [hc,Measure.restrict_apply hT,Measure.restrict_apply hS]
  rw [Set.inter_eq_left.mpr (hTB.trans (Set.prod_mono (subset_univ _) subset_rfl)),
    Set.inter_eq_left.mpr (hSB.trans (Set.prod_mono (subset_univ _) subset_rfl))]
  exact H.symm

end PrimeDegreePackets.RootBox
end
end

end OAI
