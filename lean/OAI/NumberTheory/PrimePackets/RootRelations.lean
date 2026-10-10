import Mathlib
import OAI.NumberTheory.PrimePackets.RootSubgroups
import OAI.NumberTheory.PrimePackets.ZetaDerivatives

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
namespace PrimeDegreePackets

 

lemma finite_pretransitive_relation_symmetric {J V : Type*} [Group J] [Finite V]
    [MulAction J V] [MulAction.IsPretransitive J V]
    (R : V → V → Prop) (hrefl : ∀ a, R a a) (htrans : ∀ ⦃a b c⦄, R a b → R b c → R a c)
    (heq : ∀ (g : J) a b, R a b → R (g • a) (g • b)) : ∀ ⦃a b⦄, R a b → R b a := by
  intro a b hab
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J a b
  let f : {x // R a x} → {x // R a x} := fun x =>
    ⟨g • x.val,htrans (hg ▸ hab) (heq g a x.val x.prop)⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact (MulAction.injective g) (congrArg Subtype.val h)
  obtain ⟨y,hy⟩ := (Finite.surjective_of_injective hf) ⟨a,hrefl a⟩
  have hgy : g • y.val = a := congrArg Subtype.val hy
  simpa only [hg,hgy] using heq g a y.val y.prop

 

lemma prime_pretransitive_relation_universal {J V : Type*} [Group J] [Finite V]
    [MulAction J V] [MulAction.IsPretransitive J V]
    (hp : (Nat.card V).Prime) (R : V → V → Prop)
    (hrefl : ∀ a, R a a) (htrans : ∀ ⦃a b c⦄, R a b → R b c → R a c)
    (heq : ∀ (g : J) a b, R a b → R (g • a) (g • b))
    (hnontrivial : ∃ a b, a ≠ b ∧ R a b) : ∀ a b, R a b := by
  have hsym := finite_pretransitive_relation_symmetric R hrefl htrans heq
  let : MulAction.IsPreprimitive J V := MulAction.IsPreprimitive.of_prime_card hp
  let B (a : V) : Set V := {x | R a x}
  have htranslate (g : J) (a : V) : g • B a = B (g • a) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact heq g a y hy
    · intro hx
      refine ⟨g⁻¹ • x,?_,by simp⟩
      change R a (g⁻¹ • x)
      simpa using heq g⁻¹ (g • a) x hx
  have hblock (a : V) : MulAction.IsBlock J (B a) := by
    intro g h hne
    rw [htranslate,htranslate,Set.disjoint_left]
    intro x hx hy
    apply hne
    rw [htranslate,htranslate]
    ext y
    constructor
    · intro hgy
      exact htrans (htrans hy (hsym hx)) hgy
    · intro hhy
      exact htrans (htrans hx (hsym hy)) hhy
  obtain ⟨a,b,hab,hRab⟩ := hnontrivial
  have hBa : B a = Set.univ := by
    rcases (hblock a).subsingleton_or_eq_univ with h | h
    · exact (hab (h (hrefl a) hRab)).elim
    · exact h
  intro x y
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq J a x
  have hall : B (g • a) = Set.univ := by rw [←htranslate,hBa]; simp
  change y ∈ B (g • a)
  rw [hall]
  trivial

 

theorem full_invariance_of_prime_root_symmetries {n : ℕ} (hn : 2 ≤ n) (hp : n.Prime)
    (J : Type*) [Group J] [MulAction J (Fin n)] [MulAction.IsPretransitive J (Fin n)]
    (μ : Measure (X n))
    (hsym : ∀ (g : J) i j, rootInvarianceRelation μ i j →
      rootInvarianceRelation μ (g • i) (g • j))
    (hroot : ∃ i j, i ≠ j ∧ rootInvarianceRelation μ i j) :
    ∀ g : G n, Measure.map (fun x => rightAction x g) μ = μ := by
  have H := prime_pretransitive_relation_universal (J := J) (by simpa using hp)
    (rootInvarianceRelation μ) (fun i => Or.inl rfl) (rootInvarianceRelation_trans μ) hsym hroot
  apply right_invariant_of_all_roots hn μ
  intro i j hij a
  rcases H i j with he | ⟨_,H⟩
  · exact (hij he).elim
  · exact H a

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma vecMul_mem_pointLattice_rightAction {n : ℕ} (x : X n) (h : G n)
    (v : Fin n → ℝ) (hv : v ∈ pointLattice x) :
    v ᵥ* h.1 ∈ pointLattice (rightAction x h) := by
  induction x using Quotient.inductionOn with
  | h g =>
    rw [pointLattice_mk,← integerRowMap_range] at hv
    obtain ⟨z,rfl⟩ := hv
    change integerRowMap g.1 z ᵥ* h.1 ∈ rowLattice (g*h).1
    rw [←integerRowMap_range]
    refine ⟨z,?_⟩
    simp only [integerRowMap_apply,Matrix.SpecialLinearGroup.coe_mul,Matrix.vecMul_vecMul]

lemma vecMul_transvection_apply {n : ℕ} (v : Fin n → ℝ) (i j k : Fin n) (a : ℝ) :
    (v ᵥ* Matrix.transvection i j a) k = v k + if j=k then v i*a else 0 := by
  simp only [Matrix.transvection,Matrix.vecMul_add,Matrix.vecMul_one,Pi.add_apply]
  congr 1
  by_cases hjk : j=k
  · subst k
    simp [Matrix.vecMul,dotProduct,Matrix.single_apply,mul_ite]
  · simp [Matrix.vecMul,dotProduct,hjk]

 
lemma root_stabilizer_trivial_of_no_coordinate_zero {n : ℕ} (x : X n)
    (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0)
    (i j : Fin n) (hij : i ≠ j) (a : ℝ)
    (ha : rightAction x (Matrix.SpecialLinearGroup.transvection hij a) = x) :
    a = 0 := by
  by_contra hane
  have hex : ∃ v ∈ pointLattice x, v i ≠ 0 := by
    induction x using Quotient.inductionOn with
    | h g =>
      obtain ⟨z,hz⟩ := exists_integer_row_no_zero_coordinate g
      refine ⟨integerRowMap g.1 z,?_,?_⟩
      · rw [pointLattice_mk,←integerRowMap_range]
        exact ⟨z,rfl⟩
      · simpa only [integerRowMap_apply] using hz i
  obtain ⟨v,hv,hvi⟩ := hex
  let w := v ᵥ* Matrix.transvection i j a - v
  have hw : w ∈ pointLattice x := by
    apply Submodule.sub_mem _ _ hv
    have H := vecMul_mem_pointLattice_rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a) v hv
    simpa only [ha,Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection] using H
  have hwj : w j = v i*a := by simp [w,vecMul_transvection_apply]
  have hw0 : w ≠ 0 := by
    intro H
    exact mul_ne_zero hvi hane (hwj.symm.trans (congrFun H j))
  apply hx w hw hw0 i
  simp [w,vecMul_transvection_apply,hij.symm]

 

theorem ae_root_stabilizer_trivial (d : ℕ) (μ : Measure (X (d+1)))
    [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ) :
    ∀ᵐ x ∂μ, ∀ (i j : Fin (d+1)) (hij : i ≠ j) (a : ℝ),
      rightAction x (Matrix.SpecialLinearGroup.transvection hij a) = x → a = 0 := by
  filter_upwards [ae_no_coordinate_zero d μ hA] with x hx
  exact root_stabilizer_trivial_of_no_coordinate_zero x hx

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma observationEntropy_map {Y Z α : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [Fintype α] (μ : Measure Y) (f : Y → Z) (hf : Measurable f)
    (P : Z → α) (hP : ∀ a, MeasurableSet {z | P z = a}) :
    observationEntropy (Measure.map f μ) P = observationEntropy μ (P ∘ f) := by
  unfold observationEntropy finiteShannon
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (Measure.map f μ {z | P z = a}).toReal = _
  rw [Measure.map_apply hf (hP a)]
  rfl

lemma orbitName_semiconj {Y Z α : Type*} (f : Y → Z) (S : Y → Y) (T : Z → Z)
    (h : ∀ y, f (S y) = T (f y)) (P : Z → α) (N : ℕ) :
    orbitName T P N ∘ f = orbitName S (P ∘ f) N := by
  have H (n : ℕ) (y : Y) : f (S^[n] y) = T^[n] (f y) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply',h,ih]
  ext y j
  exact congrArg P (H j.val y).symm

lemma observationEntropyRate_map_semiconj {Y Z α : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z] [Fintype α]
    (μ : Measure Y) (f : Y → Z) (hf : Measurable f)
    (S : Y → Y) (T : Z → Z) (hT : Measurable T)
    (h : ∀ y, f (S y) = T (f y))
    (P : Z → α) (hP : ∀ a, MeasurableSet {z | P z = a}) :
    observationEntropyRate (Measure.map f μ) T P =
      observationEntropyRate μ S (P ∘ f) := by
  unfold observationEntropyRate
  congr 3
  funext N
  rw [observationEntropy_map μ f hf _ (orbitName_measurable_fiber hT hP N),
    orbitName_semiconj f S T h P N]

 
theorem measureEntropy_map_semiconj_le {Y Z : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure Y) (f : Y → Z) (hf : Measurable f)
    (S : Y → Y) (T : Z → Z) (hT : Measurable T)
    (h : ∀ y, f (S y) = T (f y)) :
    measureEntropy (Measure.map f μ) T ≤ measureEntropy μ S := by
  unfold measureEntropy
  refine iSup_le fun k => iSup_le fun P => iSup_le fun hP => ?_
  rw [observationEntropyRate_map_semiconj μ f hf S T hT h P hP]
  apply le_iSup_of_le k
  apply le_iSup_of_le (P ∘ f)
  exact le_iSup_of_le (fun a => (hP a).preimage hf) le_rfl

end PrimeDegreePackets


namespace PrimeDegreePackets

instance periodSubmodule_addSubgroup_discrete {d : ℕ} (x : X (d+1)) :
    DiscreteTopology (periodGroup x).toIntSubmodule.toAddSubgroup :=
  inferInstanceAs (DiscreteTopology (periodGroup x).toIntSubmodule)

 
def orbitQuotientMap {d : ℕ} (x : X (d+1)) :
    LogCoordinates d ⧸ (periodGroup x).toIntSubmodule.toAddSubgroup → X (d+1) :=
  Quotient.lift (orbitMap x) (by
    intro u v huv
    have hp : v-u ∈ periodGroup x := by
      have H := QuotientAddGroup.leftRel_apply.mp huv
      simpa only [sub_eq_neg_add,AddSubgroup.toIntSubmodule_toAddSubgroup] using H
    have H := orbitMap_add x (v-u) u
    rw [show orbitMap x (v-u) = x from hp] at H
    simpa using H.symm)

@[simp] lemma orbitQuotientMap_mk {d : ℕ} (x : X (d+1)) (u : LogCoordinates d) :
    orbitQuotientMap x (QuotientAddGroup.mk u) = orbitMap x u := rfl

lemma continuous_orbitQuotientMap {d : ℕ} (x : X (d+1)) :
    Continuous (orbitQuotientMap x) :=
  (QuotientAddGroup.isQuotientMap_mk ((periodGroup x).toIntSubmodule.toAddSubgroup)).continuous_iff.mpr
    (continuous_orbitMap x)

lemma orbitQuotientMap_add {d : ℕ} (x : X (d+1)) (u : LogCoordinates d)
    (v : LogCoordinates d ⧸ (periodGroup x).toIntSubmodule.toAddSubgroup) :
    orbitQuotientMap x (QuotientAddGroup.mk u + v) =
      rightAction (orbitQuotientMap x v) (diagonalFlow u) := by
  obtain ⟨v,rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [← QuotientAddGroup.mk_add,orbitQuotientMap_mk,orbitQuotientMap_mk]
  change orbitMap x (u+v) = orbitMap (orbitMap x v) u
  rw [add_comm u v,orbitMap_add]

lemma orbitProbability_eq_map_quotient {d : ℕ} (x : X (d+1))
    (h : HasAddFundamentalDomain (periodGroup x) (LogCoordinates d) volume) :
    orbitProbability x = Measure.map (orbitQuotientMap x)
      (normalizedLatticeQuotientMeasure (periodGroup x).toIntSubmodule
        h.ExistsIsAddFundamentalDomain.choose) := by
  unfold orbitProbability orbitVolume orbitalHaar normalizedLatticeQuotientMeasure
  rw [dite_eq_left h,Measure.map_smul _ (continuous_orbitQuotientMap x).measurable.aemeasurable,Measure.map_map
    (continuous_orbitQuotientMap x).measurable QuotientAddGroup.continuous_mk.measurable]
  simp only [addCovolume,dite_eq_left h]
  rfl

 

theorem orbitProbability_entropy_eq_zero {d : ℕ} (x : X (d+1))
    [IsZLattice ℝ (periodGroup x).toIntSubmodule] (u : LogCoordinates d) :
    measureEntropy (orbitProbability x) (fun y => rightAction y (diagonalFlow u)) = 0 := by
  let h := periodGroup_hasFundamentalDomain x
  let s := h.ExistsIsAddFundamentalDomain.choose
  have hs : IsAddFundamentalDomain (periodGroup x).toIntSubmodule s volume := h.ExistsIsAddFundamentalDomain.choose_spec
  let ν := normalizedLatticeQuotientMeasure (periodGroup x).toIntSubmodule s
  let := compact_quotient_of_isZLattice (periodGroup x).toIntSubmodule
  let := normalizedLatticeQuotientMeasure_probability (periodGroup x).toIntSubmodule
    (periodGroup x).toIntSubmodule hs
  let := normalizedLatticeQuotientMeasure_invariant (periodGroup x).toIntSubmodule
    (periodGroup x).toIntSubmodule le_rfl hs
  let a : LogCoordinates d ⧸ (periodGroup x).toIntSubmodule.toAddSubgroup := QuotientAddGroup.mk u
  have hzero : measureEntropy ν (fun v => a+v) = 0 :=
    measureEntropy_eq_zero_of_isometry ν (measurePreserving_add_left ν a) (isometry_add_left a)
  apply le_antisymm _ bot_le
  rw [orbitProbability_eq_map_quotient x h]
  exact (measureEntropy_map_semiconj_le ν (orbitQuotientMap x)
    (continuous_orbitQuotientMap x).measurable (fun v => a+v)
    (fun y => rightAction y (diagonalFlow u))
    (continuous_rightAction (diagonalFlow u)).measurable (orbitQuotientMap_add x u)).trans_eq hzero

 

theorem latticePoint_orbitProbability_entropy_eq_zero {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (u : LogCoordinates d) :
    measureEntropy (orbitProbability (latticePoint M σ))
      (fun y => rightAction y (diagonalFlow u)) = 0 := by
  let := latticePoint_period_isZLattice M σ hn hodd
  exact orbitProbability_entropy_eq_zero (latticePoint M σ) u

end PrimeDegreePackets

open scoped Topology Classical ENNReal
namespace PrimeDegreePackets

lemma measureEntropy_finite_mixture_zero {Y ι : Type*} [MeasurableSpace Y] [Fintype ι]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (ν : ι → Measure Y) [∀ i, IsProbabilityMeasure (ν i)] (c : ι → ℝ≥0∞)
    (hc : ∀ i, c i ≠ ⊤) (hmix : μ = ∑ i, c i • ν i)
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (hν : ∀ i, MeasurePreserving T (ν i) (ν i))
    (hzero : ∀ i, measureEntropy (ν i) T = 0) : measureEntropy μ T = 0 := by
  have hcsum : ∑ i, c i = 1 := by
    have H := congrArg (fun m : Measure Y => m Set.univ) hmix
    simpa only [measure_univ,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,mul_one] using H.symm
  have hwsum : ∑ i, (c i).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun i _ => hc i),hcsum,ENNReal.toReal_one]
  apply le_antisymm _ bot_le
  unfold measureEntropy
  refine iSup_le fun k => iSup_le fun P => iSup_le fun hP => ?_
  have HR (i : ι) : observationEntropyRate (ν i) T P = 0 := by
    have H : ENNReal.ofReal (observationEntropyRate (ν i) T P) ≤ measureEntropy (ν i) T :=
      le_iSup_of_le k (le_iSup_of_le P (le_iSup_of_le hP le_rfl))
    rw [hzero i] at H
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp (le_antisymm H bot_le))
      (observationEntropyRate_nonneg (ν i) (hν i).measurable P hP)
  have HM : μ = ∑ i, ENNReal.ofReal (c i).toReal • ν i := by
    simpa only [ENNReal.ofReal_toReal (hc _)] using hmix
  have H := observationEntropyRate_finite_mixture μ ν (fun i => (c i).toReal)
    (fun i => ENNReal.toReal_nonneg) hwsum HM hT hν P hP
  simp only [HR,mul_zero,Finset.sum_const_zero] at H
  rw [H, ENNReal.ofReal_zero]
  exact le_rfl

 

theorem packetMeasure_entropy_eq_zero {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (u : LogCoordinates d) :
    measureEntropy (packetMeasure M σ) (fun y => rightAction y (diagonalFlow u)) = 0 := by
  let := (packetOrbits_finite M σ hn hodd).fintype
  let := packetMeasure_isProbabilityMeasure M σ hn hodd
  let ν := fun O : packetOrbits M σ => orbitProbability (orbitBasepoint O)
  let : ∀ O, IsProbabilityMeasure (ν O) := fun O => packetBasepoint_probability hn hodd O
  let V := ∑' O : packetOrbits M σ, orbitVolume (orbitBasepoint O)
  let c := fun O : packetOrbits M σ => V⁻¹ * orbitVolume (orbitBasepoint O)
  have hc : ∀ O, c O ≠ ⊤ := by
    intro O
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (packetVolume_ne_zero_ne_top M σ hn hodd).1)
      (packetBasepoint_volume_pos_finite hn hodd O).2
  have hmix : packetMeasure M σ = ∑ O, c O • ν O := by
    simp only [packetMeasure,Measure.sum_fintype,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro O _
    exact smul_smul _ _ _
  apply measureEntropy_finite_mixture_zero (packetMeasure M σ) ν c hc hmix
  · exact ⟨(continuous_rightAction _).measurable,packetMeasure_invariant M σ u⟩
  · intro O
    exact ⟨(continuous_rightAction _).measurable,orbitProbability_invariant (orbitBasepoint O) u⟩
  · intro O
    let := packetBasepoint_period_isZLattice hn hodd O
    exact orbitProbability_entropy_eq_zero (orbitBasepoint O) u

end PrimeDegreePackets

open scoped Matrix Topology Classical
namespace PrimeDegreePackets

lemma continuous_rootTransvection {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Continuous (fun t : ℝ => Matrix.SpecialLinearGroup.transvection hij t) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.single i j t)
  apply continuous_const.add
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  simp only [Matrix.single_apply]
  split_ifs <;> fun_prop

lemma root_mul_entry {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (r s : Fin n) (t : ℝ) :
    (g * Matrix.SpecialLinearGroup.transvection hij t).1 r s =
      g.1 r s + if s = j then g.1 r i * t else 0 := by
  change (g.1 * Matrix.transvection i j t) r s = _
  by_cases h : s = j
  · subst s
    simp [Matrix.mul_transvection_apply_same,mul_comm]
  · simp [Matrix.mul_transvection_apply_of_ne,h]

 
abbrev RootPivot {n : ℕ} (i k : Fin n) := {g : G n // g.1 k i ≠ 0}

 
abbrev RootSlice {n : ℕ} (i j k : Fin n) := {g : G n // g.1 k i ≠ 0 ∧ g.1 k j = 0}

def rootParameter {n : ℕ} (i j k : Fin n) (g : G n) : ℝ := g.1 k j / g.1 k i

def rootPivotTranslate {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (g : RootPivot i k) (t : ℝ) : RootPivot i k :=
  ⟨g.val * Matrix.SpecialLinearGroup.transvection hij t, by
    simpa only [root_mul_entry,ite_eq_right hij,add_zero] using g.prop⟩

lemma rootParameter_translate {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (g : RootPivot i k) (t : ℝ) :
    rootParameter i j k (rootPivotTranslate hij g t).val = rootParameter i j k g.val + t := by
  simp only [rootParameter,rootPivotTranslate,root_mul_entry,ite_true,ite_eq_right hij,add_zero]
  field_simp [g.prop]

 
def rootSliceRepresentative {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (g : RootPivot i k) : RootSlice i j k :=
  ⟨g.val * Matrix.SpecialLinearGroup.transvection hij (-rootParameter i j k g.val), by
    constructor
    · simpa only [root_mul_entry,ite_eq_right hij,add_zero] using g.prop
    · simp only [root_mul_entry,ite_true,rootParameter]
      field_simp [g.prop]
      ring⟩

lemma rootSliceRepresentative_translate {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (g : RootPivot i k) (t : ℝ) :
    rootSliceRepresentative hij (rootPivotTranslate hij g t) = rootSliceRepresentative hij g := by
  apply Subtype.ext
  change (g.val * Matrix.SpecialLinearGroup.transvection hij t) *
    Matrix.SpecialLinearGroup.transvection hij (-rootParameter i j k (rootPivotTranslate hij g t).val) = _
  rw [rootParameter_translate,mul_assoc,←Matrix.SpecialLinearGroup.transvection_add]
  congr 2
  ring

lemma continuous_rootParameter {n : ℕ} {i j k : Fin n} :
    Continuous (fun g : RootPivot i k => rootParameter i j k g.val) := by
  have hc : Continuous (fun g : RootPivot i k => (g.val : Matrix (Fin n) (Fin n) ℝ)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous.comp continuous_subtype_val
  unfold rootParameter
  apply Continuous.div
  · exact (continuous_apply j).comp ((continuous_apply k).comp hc)
  · exact (continuous_apply i).comp ((continuous_apply k).comp hc)
  · exact fun g => g.prop

lemma continuous_rootSliceRepresentative {n : ℕ} {i j k : Fin n} (hij : i ≠ j) :
    Continuous (rootSliceRepresentative (k := k) hij) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.mul
    ((continuous_rootTransvection hij).comp continuous_rootParameter.neg)

 

def rootPivotHomeomorph {n : ℕ} {i j k : Fin n} (hij : i ≠ j) :
    RootPivot i k ≃ₜ RootSlice i j k × ℝ where
  toFun g := (rootSliceRepresentative hij g, rootParameter i j k g.val)
  invFun z := rootPivotTranslate hij ⟨z.1.val,z.1.prop.1⟩ z.2
  left_inv g := by
    apply Subtype.ext
    change (g.val * Matrix.SpecialLinearGroup.transvection hij (-rootParameter i j k g.val)) *
      Matrix.SpecialLinearGroup.transvection hij (rootParameter i j k g.val) = _
    rw [mul_assoc,←Matrix.SpecialLinearGroup.transvection_add,neg_add_cancel,
      Matrix.SpecialLinearGroup.transvection_coeff_zero,mul_one]
  right_inv z := by
    have hp : rootParameter i j k z.1.val = 0 := by
      simp only [rootParameter,z.1.prop.2,zero_div]
    apply Prod.ext
    · change rootSliceRepresentative hij (rootPivotTranslate hij ⟨z.1.val,z.1.prop.1⟩ z.2) = z.1
      rw [rootSliceRepresentative_translate]
      apply Subtype.ext
      change z.1.val * Matrix.SpecialLinearGroup.transvection hij (-rootParameter i j k z.1.val) = _
      rw [hp,neg_zero,Matrix.SpecialLinearGroup.transvection_coeff_zero,mul_one]
    · simpa only [hp,zero_add] using rootParameter_translate hij ⟨z.1.val,z.1.prop.1⟩ z.2
  continuous_toFun := (continuous_rootSliceRepresentative hij).prodMk continuous_rootParameter
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_rootTransvection hij).comp continuous_snd)

lemma rootPivotHomeomorph_translate {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (g : RootPivot i k) (t : ℝ) :
    rootPivotHomeomorph hij (rootPivotTranslate hij g t) =
      ((rootPivotHomeomorph hij g).1,(rootPivotHomeomorph hij g).2+t) := by
  exact Prod.ext (rootSliceRepresentative_translate hij g t) (rootParameter_translate hij g t)

end PrimeDegreePackets
end
end

end OAI
