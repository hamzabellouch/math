import Mathlib
import OAI.Probability.UnimodularPercolation.Transport.TrajectoryMass

namespace OAI

/-! Endpoint Kernels for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SeparatedTracePair
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_trace_pair_separated_le [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k n M : ℕ)
    (Q : Finset E) (p : unitInterval)
    (A₁ A₂ : Finset (SpliceState E)) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (hA₁ : A₁ ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hA₂ : A₂ ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hbin : ∀ s ∈ A₁, (cluster G s.1 x).Finite ∧ n ≤ (cluster G s.1 x).ncard ∧
      (cluster G s.1 x).ncard < 2*n)
    (hcap₁ : ∀ s ∈ A₁, ∀ i, 1 ≤ i → i ≤ k → (cluster G (s.2 i) (y₁ s.2 i)).Finite)
    (hcap₂ : ∀ s ∈ A₂, ∀ i, 1 ≤ i → i ≤ k → (cluster G (s.2 i) (y₂ s.2 i)).Finite ∧
      (cluster G (s.2 i) (y₂ s.2 i)).ncard ≤ M) :
    (∑ a : FiniteTraceIndex G x k Q A₁ (fun s => y₁ s.2),
      ∑ b : FiniteTraceIndex G x k Q A₂ (fun s => y₂ s.2),
      if (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a).1 =
          (traceIndexOutput G x k Q A₂ (fun s => y₂ s.2) b).1 ∧
        a.2.val ≠ [] ∧ b.2.val ≠ [] ∧
        GraphSeparated G
          (cluster G (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a).1 x \ cluster G a.1.val.1 x)
          (cluster G (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a).1 x \ cluster G b.1.val.1 x)
      then jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
        (pairSpliceOutput (traceIndexOutput G x k Q A₁ (fun s => y₁ s.2) a)
          (traceIndexOutput G x k Q A₂ (fun s => y₂ s.2) b)) *
        (m₁ a.1.val.2 * traceIndexMass G x k Q A₁ (fun s => y₁ s.2) a) *
        (m₂ b.1.val.2 * traceIndexMass G x k Q A₂ (fun s => y₂ s.2) b) else 0) ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ η) k).Nonempty then m₁ η else 0) *
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ η) k).Nonempty then m₂ η else 0) else 0) := by
  let T₁ := FiniteTraceIndex G x k Q A₁ (fun s => y₁ s.2)
  let T₂ := FiniteTraceIndex G x k Q A₂ (fun s => y₂ s.2)
  let out₁ := traceIndexOutput G x k Q A₁ (fun s => y₁ s.2)
  let out₂ := traceIndexOutput G x k Q A₂ (fun s => y₂ s.2)
  let P (a : T₁ × T₂) := (out₁ a.1).1 = (out₂ a.2).1 ∧ a.1.2.val ≠ [] ∧ a.2.2.val ≠ [] ∧
    GraphSeparated G (cluster G (out₁ a.1).1 x \ cluster G a.1.1.val.1 x)
      (cluster G (out₁ a.1).1 x \ cluster G a.2.1.val.1 x)
  let I := {a : T₁ × T₂ // P a}
  let η₁ (a : I) := a.val.1.1.val.2
  let η₂ (a : I) := a.val.2.1.val.2
  let ω₁ (a : I) := a.val.1.1.val.1
  let ω₂ (a : I) := a.val.2.1.val.1
  let ωf (a : I) := (out₁ a.val.1).1
  let c₁ (a : I) := a.val.1.2.val
  let c₂ (a : I) := a.val.2.2.val
  have hout (a : I) : jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
      (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) = pairSpliceOutput (out₁ a.val.1) (out₂ a.val.2) := rfl
  have hinj : Function.Injective (fun a : I =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),c₁ a,c₂ a)) := by
    intro a b he
    dsimp only at he
    rw [hout a,hout b] at he
    have ho₁ : out₁ a.val.1 = out₁ b.val.1 := Prod.ext
      (congrArg (fun z : JointSpliceState E × List (ℕ × E) × List (ℕ × E) => z.1.1) he)
      (congrArg (fun z : JointSpliceState E × List (ℕ × E) × List (ℕ × E) => z.1.2.1) he)
    have ho₂ : out₂ a.val.2 = out₂ b.val.2 := Prod.ext
      (a.property.1.symm.trans ((congrArg Prod.fst ho₁).trans b.property.1))
      (congrArg (fun z : JointSpliceState E × List (ℕ × E) × List (ℕ × E) => z.1.2.2) he)
    apply Subtype.ext
    exact Prod.ext
      (traceIndex_output_code_injective G x k Q A₁ (fun s => y₁ s.2)
        (Prod.ext ho₁ (congrArg (fun z => z.2.1) he)))
      (traceIndex_output_code_injective G x k Q A₂ (fun s => y₂ s.2)
        (Prod.ext ho₂ (congrArg (fun z => z.2.2) he)))
  have htr₁ (a : I) : SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a) :=
    (traceIndex_valid G x k Q A₁ (fun s => y₁ s.2) a.val.1).1
  have htr₂ (a : I) : SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a) := by
    change SpliceTrace G x _ _ _ _ _ _ (out₁ a.val.1).1
    rw [a.property.1]
    exact (traceIndex_valid G x k Q A₂ (fun s => y₂ s.2) a.val.2).1
  have hs₁ (a : I) := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) _).mp (hA₁ a.val.1.1.property)
  have hs₂ (a : I) := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) _).mp (hA₂ a.val.2.1.property)
  have hb := finite_separated_weighted_contact_second_moment_le G hloc x k n M p Q η₁ η₂ y₁ y₂
    (fun _ => True) (fun _ => True) m₁ m₂ hm₁ hm₂ ω₁ ω₂ ωf c₁ c₂ hinj htr₁ htr₂
    (fun a => a.property.2.1) (fun a => a.property.2.2.1) (fun a => a.property.2.2.2)
    (fun a => hbin _ a.val.1.1.property) (fun a => hcap₁ _ a.val.1.1.property)
    (fun a => hcap₂ _ a.val.2.1.property) (fun _ => trivial) (fun _ => trivial)
    (fun a => (hs₁ a).1) (fun a => (hs₂ a).1) (fun a => (hs₁ a).2.1)
    (fun a => (hs₂ a).2.1) (fun a => (hs₁ a).2.2) (fun a => (hs₂ a).2.2)
  simp only [true_and] at hb
  apply le_trans _ hb
  let w (a : T₁ × T₂) := jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
    (pairSpliceOutput (out₁ a.1) (out₂ a.2)) *
    (m₁ a.1.1.val.2 * traceIndexMass G x k Q A₁ (fun s => y₁ s.2) a.1) *
    (m₂ a.2.1.val.2 * traceIndexMass G x k Q A₂ (fun s => y₂ s.2) a.2)
  have he := Finset.sum_subtype (p := P) (F := inferInstance) (Finset.univ.filter P)
    (by intro a; simp) w
  rw [Finset.sum_filter,Fintype.sum_prod_type] at he
  change (∑ a : T₁, ∑ b : T₂, if P (a,b) then w (a,b) else 0) ≤ _
  rw [he]
  apply Finset.sum_le_sum
  intro a _
  rw [hout a]
  change w a.val ≤ _
  simp only [w,traceIndexMass,η₁,η₂,ωf,c₁,c₂,out₁,out₂]
  rw [← a.property.1]
  exact le_of_eq (by ring)

end SeparatedTracePair

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ChoiceSeparatedMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P₁ P₂ : Type*} [Fintype P₁] [Fintype P₂]

 
noncomputable def finiteChoiceSeparatedPairMass
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E) (p : ℝ)
    (A₁ : P₁ → Finset (SpliceState E)) (A₂ : P₂ → Finset (SpliceState E))
    (y₁ : P₁ → (ℕ → Set E) → ℕ → V) (y₂ : P₂ → (ℕ → Set E) → ℕ → V)
    (m₁ : P₁ → (ℕ → Set E) → ℝ) (m₂ : P₂ → (ℕ → Set E) → ℝ) : ℝ :=
  ∑ a : FiniteChoiceTraceIndex G x k Q A₁ (fun r s => y₁ r s.2),
    ∑ b : FiniteChoiceTraceIndex G x k Q A₂ (fun r s => y₂ r s.2),
    if (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a).1 =
        (choiceTraceOutput G x k Q A₂ (fun r s => y₂ r s.2) b).1 ∧
      choiceTraceCode G x k Q A₁ (fun r s => y₁ r s.2) a ≠ [] ∧
      choiceTraceCode G x k Q A₂ (fun r s => y₂ r s.2) b ≠ [] ∧
      GraphSeparated G
        (cluster G (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a).1 x \
          cluster G (choiceTraceInput G x k Q A₁ (fun r s => y₁ r s.2) a).1 x)
        (cluster G (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a).1 x \
          cluster G (choiceTraceInput G x k Q A₂ (fun r s => y₂ r s.2) b).1 x)
    then jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (pairSpliceOutput (choiceTraceOutput G x k Q A₁ (fun r s => y₁ r s.2) a)
        (choiceTraceOutput G x k Q A₂ (fun r s => y₂ r s.2) b)) *
      choiceTraceMass G x k Q A₁ (fun r s => y₁ r s.2) (fun s r => m₁ r s.2) a *
      choiceTraceMass G x k Q A₂ (fun r s => y₂ r s.2) (fun s r => m₂ r s.2) b else 0

 
noncomputable def finiteChoiceHit (G : BondGraph V E) (k : ℕ) (Q : Finset E) (p : ℝ)
    (y : P₁ → (ℕ → Set E) → ℕ → V) (m : P₁ → (ℕ → Set E) → ℝ) (B : Set V) : ℝ :=
  ∑ r, finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    if (B ∩ trajectoryUnion G η (y r η) k).Nonempty then m r η else 0)

 

theorem finiteChoiceSeparatedPairMass_le [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k n M : ℕ)
    (Q : Finset E) (p : unitInterval)
    (A₁ : P₁ → Finset (SpliceState E)) (A₂ : P₂ → Finset (SpliceState E))
    (y₁ : P₁ → (ℕ → Set E) → ℕ → V) (y₂ : P₂ → (ℕ → Set E) → ℕ → V)
    (m₁ : P₁ → (ℕ → Set E) → ℝ) (m₂ : P₂ → (ℕ → Set E) → ℝ)
    (hm₁ : ∀ r η, 0 ≤ m₁ r η) (hm₂ : ∀ r η, 0 ≤ m₂ r η)
    (hA₁ : ∀ r, A₁ r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hA₂ : ∀ r, A₂ r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hbin : ∀ r s, s ∈ A₁ r → (cluster G s.1 x).Finite ∧ n ≤ (cluster G s.1 x).ncard ∧
      (cluster G s.1 x).ncard < 2*n)
    (hcap₁ : ∀ r s, s ∈ A₁ r → ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (s.2 i) (y₁ r s.2 i)).Finite)
    (hcap₂ : ∀ r s, s ∈ A₂ r → ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (s.2 i) (y₂ r s.2 i)).Finite ∧ (cluster G (s.2 i) (y₂ r s.2 i)).ncard ≤ M) :
    finiteChoiceSeparatedPairMass G x k Q p A₁ A₂ y₁ y₂ m₁ m₂ ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteChoiceHit G k Q p y₁ m₁ (cluster G (finiteFieldSet Q ω) x) *
        finiteChoiceHit G k Q p y₂ m₂ (cluster G (finiteFieldSet Q ω) x) else 0) := by
  let R (ω : FiniteField Q) := (cluster G (finiteFieldSet Q ω) x).Finite ∧
    n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
    (cluster G (finiteFieldSet Q ω) x).ncard < 2*n
  let H₁ (r : P₁) (ω : FiniteField Q) := finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    if (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ r η) k).Nonempty then m₁ r η else 0)
  let H₂ (r : P₂) (ω : FiniteField Q) := finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η =>
    if (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ r η) k).Nonempty then m₂ r η else 0)
  have hb : finiteChoiceSeparatedPairMass G x k Q p A₁ A₂ y₁ y₂ m₁ m₂ ≤
      ∑ r : P₁, ∑ s : P₂, ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
        (if R ω then H₁ r ω * H₂ s ω else 0) := by
    unfold finiteChoiceSeparatedPairMass
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro r _
    conv_lhs => arg 2; ext a; rw [Fintype.sum_sigma]
    conv_lhs => rw [Finset.sum_comm]
    simp only [choiceTraceOutput,choiceTraceInput,choiceTraceCode,choiceTraceMass,
      traceIndexInput,traceIndexCode]
    apply Finset.sum_le_sum
    intro s _
    exact finite_trace_pair_separated_le G hloc x k n M Q p (A₁ r) (A₂ s)
      (y₁ r) (y₂ s) (m₁ r) (m₂ s) (hm₁ r) (hm₂ s) (hA₁ r) (hA₂ s)
      (hbin r) (hcap₁ r) (hcap₂ s)
  apply hb.trans_eq
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext s; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  change (∑ s : P₂, ∑ r : P₁, finiteFieldWeight Q p ω * (if R ω then H₁ r ω * H₂ s ω else 0)) =
    finiteFieldWeight Q p ω * (if R ω then (∑ r : P₁, H₁ r ω) * (∑ s : P₂, H₂ s ω) else 0)
  by_cases h : R ω
  · simp only [ite_eq_left h,← Finset.mul_sum,← Finset.sum_mul]
  · simp only [ite_eq_right h,mul_zero,Finset.sum_const_zero]

end ChoiceSeparatedMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalEndpointRule
attribute [local instance] Classical.propDecidable Classical.decEq

 

structure LocalEndpointRule (G : BondGraph V E) (hloc : LocallyFinite G)
    (O : Set V) (M : ℕ) (L : ℝ) where
  mass : Set E → V → V → ℝ
  radius : ℕ
  nonneg : ∀ ω x y, 0 ≤ mass ω x y
  row_le_one : ∀ ω x, (∑' y, mass ω x y) ≤ 1
  support : ∀ ω x y, mass ω x y ≠ 0 → x ∈ O ∧ y ∈ O ∧ Conn G ω x y ∧
    (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L
  locality : ∀ ω x y, mass ω x y =
    mass (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x radius).toFinset : Set E)) x y
  covariance : ∀ (a : V ≃ V) (b : E ≃ E), IsAut G a b → ∀ ω x y,
    mass (b ⁻¹' ω) x y = mass ω (a x) (a y)

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

theorem outside_ball_zero (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x y : V)
    (hy : y ∉ reachBall G x M) : q.mass ω x y = 0 := by
  by_contra h
  obtain ⟨_,_,hc,hfin,hcap,_⟩ := q.support ω x y h
  exact hy (finite_cluster_subset_reachBall G ω x hfin M hcap hc)

theorem summable_mass (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x : V) :
    Summable (q.mass ω x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  apply q.outside_ball_zero ω x y
  simpa only [Set.Finite.mem_toFinset] using hy

theorem mass_le_one (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x y : V) :
    q.mass ω x y ≤ 1 := by
  have h := (q.summable_mass ω x).sum_le_tsum ({y} : Finset V) (fun z _ => q.nonneg ω x z)
  simpa only [Finset.sum_singleton] using h.trans (q.row_le_one ω x)

 
theorem measurable_mass (q : LocalEndpointRule G hloc O M L) (x y : V) :
    Measurable (fun ω => q.mass ω x y) := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset
  let f : Set (Q : Set E) → ℝ := fun η => q.mass (Subtype.val '' η) x y
  have hm : Measurable f := measurable_of_finite f
  have he : (fun ω => q.mass ω x y) = f ∘ (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set (Q : Set E)) := by
    funext ω
    rw [q.locality ω x y]
    congr 1
    ext e
    simp [Q,and_comm]
  rw [he]
  exact hm.comp (measurable_set_restrict (Q : Set E))

theorem integrable_mass (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V) :
    Integrable (fun ω => q.mass ω x y) (law p) := by
  apply Integrable.of_bound (q.measurable_mass x y).aestronglyMeasurable 1
  exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs,abs_of_nonneg (q.nonneg ω x y)] using q.mass_le_one ω x y

 

noncomputable def kernel (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, q.mass ω x y ∂law p

theorem kernel_nonneg (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V) :
    0 ≤ q.kernel p x y := integral_nonneg (fun ω => q.nonneg ω x y)

theorem kernel_outside_ball_zero (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V)
    (hy : y ∉ reachBall G x M) : q.kernel p x y = 0 := by
  simp only [kernel,q.outside_ball_zero _ x y hy,integral_zero]

theorem summable_kernel (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    Summable (q.kernel p x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  apply q.kernel_outside_ball_zero p x y
  simpa only [Set.Finite.mem_toFinset] using hy

 

theorem kernel_row_integral (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    (∑' y, q.kernel p x y) = ∫ ω, (∑' y, q.mass ω x y) ∂law p := by
  let B := (finite_reachBall hloc x M).toFinset
  have h₁ : (∑' y, q.kernel p x y) = ∑ y ∈ B, q.kernel p x y :=
    tsum_eq_sum fun y hy => q.kernel_outside_ball_zero p x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
  have h₂ (ω : Set E) : (∑' y, q.mass ω x y) = ∑ y ∈ B, q.mass ω x y :=
    tsum_eq_sum fun y hy => q.outside_ball_zero ω x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
  rw [h₁]
  simp_rw [h₂]
  exact (integral_finsetSum B (fun y _ => q.integrable_mass p x y)).symm

theorem kernel_row_le_one (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    (∑' y, q.kernel p x y) ≤ 1 := by
  rw [q.kernel_row_integral p x]
  have hi : Integrable (fun ω => ∑' y, q.mass ω x y) (law p) := by
    let B := (finite_reachBall hloc x M).toFinset
    have he (ω : Set E) : (∑' y, q.mass ω x y) = ∑ y ∈ B, q.mass ω x y :=
      tsum_eq_sum fun y hy => q.outside_ball_zero ω x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
    simp_rw [he]
    exact integrable_finsetSum B (fun y _ => q.integrable_mass p x y)
  calc
    _ ≤ ∫ _, (1:ℝ) ∂law p := integral_mono hi (integrable_const _) (q.row_le_one · x)
    _ = 1 := by simp

end LocalEndpointRule
end LocalEndpointRule

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section LocalEndpointKernel
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

theorem outside_reverse_ball_zero (q : LocalEndpointRule G hloc O M L) (ω : Set E) (x y : V)
    (hx : x ∉ reachBall G y M) : q.mass ω x y = 0 := by
  by_contra h
  obtain ⟨_,_,hc,hfin,hcap,_⟩ := q.support ω x y h
  have he := cluster_eq_of_conn G ω hc
  rw [he] at hfin hcap
  exact hx (finite_cluster_subset_reachBall G ω y hfin M hcap (conn_symm G ω hc))

theorem kernel_outside_reverse_ball_zero (q : LocalEndpointRule G hloc O M L)
    (p : unitInterval) (x y : V) (hx : x ∉ reachBall G y M) : q.kernel p x y = 0 := by
  simp only [kernel,q.outside_reverse_ball_zero _ x y hx,integral_zero]

theorem summable_kernel_column (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (y : V) :
    Summable (fun x => q.kernel p x y) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y M).toFinset)
  intro x hx
  apply q.kernel_outside_reverse_ball_zero p x y
  simpa only [Set.Finite.mem_toFinset] using hx

theorem mass_zero_of_start_not_mem (q : LocalEndpointRule G hloc O M L) (ω : Set E)
    (x y : V) (hx : x ∉ O) : q.mass ω x y = 0 := by
  by_contra h
  exact hx (q.support ω x y h).1

theorem mass_zero_of_end_not_mem (q : LocalEndpointRule G hloc O M L) (ω : Set E)
    (x y : V) (hy : y ∉ O) : q.mass ω x y = 0 := by
  by_contra h
  exact hy (q.support ω x y h).2.1

theorem kernel_zero_of_start_not_mem (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (x y : V) (hx : x ∉ O) : q.kernel p x y = 0 := by
  simp only [kernel,q.mass_zero_of_start_not_mem _ x y hx,integral_zero]

theorem kernel_zero_of_end_not_mem (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (x y : V) (hy : y ∉ O) : q.kernel p x y = 0 := by
  simp only [kernel,q.mass_zero_of_end_not_mem _ x y hy,integral_zero]

 

theorem kernel_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (ha : IsAut G a b) (x y : V) :
    q.kernel p (a x) (a y) = q.kernel p x y := by
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable
    (q.measurable_mass x y).aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [kernel,q.covariance a b ha] using h.symm

noncomputable def successProbability (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) : ℝ :=
  ∑' y, q.kernel p x y

theorem successProbability_nonneg (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    0 ≤ q.successProbability p x := tsum_nonneg (q.kernel_nonneg p x)

theorem successProbability_le_one (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x : V) :
    q.successProbability p x ≤ 1 := q.kernel_row_le_one p x

theorem successProbability_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (ha : IsAut G a b) (x : V) :
    q.successProbability p (a x) = q.successProbability p x := by
  unfold successProbability
  rw [← a.tsum_eq (fun y => q.kernel p (a x) y)]
  exact tsum_congr (q.kernel_covariant p a b ha x)

theorem successProbability_orbit (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (o x : V) (hx : x ∈ vertexOrbit G o) : q.successProbability p x = q.successProbability p o := by
  obtain ⟨a,b,ha,rfl⟩ := hx
  exact q.successProbability_covariant p a b ha o

theorem kernel_column_covariant (q : LocalEndpointRule G hloc O M L) (p : unitInterval)
    (a : V ≃ V) (b : E ≃ E) (ha : IsAut G a b) (y : V) :
    (∑' x, q.kernel p x (a y)) = ∑' x, q.kernel p x y := by
  rw [← a.tsum_eq (fun x => q.kernel p x (a y))]
  exact tsum_congr (fun x => q.kernel_covariant p a b ha x y)

end LocalEndpointRule
end LocalEndpointKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointTransport
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem kernel_column_orbit (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)
    (p : unitInterval) (y : V) (hy : y ∈ vertexOrbit G o) :
    (∑' x, q.kernel p x y) = ∑' x, q.kernel p x o := by
  obtain ⟨a,b,ha,rfl⟩ := hy
  exact q.kernel_column_covariant p a b ha o

 

theorem kernel_column_eq_success {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (p : unitInterval) (y : V) (hy : y ∈ vertexOrbit G (root i₀)) :
    (∑' x, q.kernel p x y) = q.successProbability p (root i₀) := by
  let O := vertexOrbit G (root i₀)
  let w : ι → ℝ := fun i => if root i ∈ O then weight i else 0
  have ho : root i₀ ∈ O := by
    refine ⟨Equiv.refl V,Equiv.refl E,?_,rfl⟩
    intro e
    simp
  have hw' (i : ι) : 0 ≤ w i := by
    dsimp [w]
    split_ifs
    · exact hw i
    · exact le_rfl
  have hpos : 0 < ∑ i, w i := by
    have hi : w i₀ ≤ ∑ i, w i := Finset.single_le_sum (fun i _ => hw' i) (Finset.mem_univ i₀)
    have he : w i₀ = weight i₀ := ite_eq_left ho
    rw [he] at hi
    exact hw₀.trans_le hi
  have ht := htr.real root weight Γ (q.kernel p)
    (by intro a ha x z; obtain ⟨b,hb⟩ := hΓ a ha; exact q.kernel_covariant p a b hb x z)
    (q.summable_kernel p) (q.summable_kernel_column p)
  have hr (i : ι) : weight i * (∑' z, q.kernel p (root i) z) =
      w i * q.successProbability p (root i₀) := by
    by_cases hi : root i ∈ O
    · have he := q.successProbability_orbit p (root i₀) (root i) hi
      change weight i * q.successProbability p (root i) = _
      rw [he]
      simp only [w,ite_eq_left hi]
    · simp only [w,ite_eq_right hi,zero_mul]
      have he : (∑' z, q.kernel p (root i) z) = 0 := by
        simp only [q.kernel_zero_of_start_not_mem p _ _ hi,tsum_zero]
      rw [he,mul_zero]
  have hc (i : ι) : weight i * (∑' x, q.kernel p x (root i)) =
      w i * (∑' x, q.kernel p x (root i₀)) := by
    by_cases hi : root i ∈ O
    · rw [q.kernel_column_orbit (root i₀) p (root i) hi]
      simp only [w,ite_eq_left hi]
    · simp only [w,ite_eq_right hi,zero_mul]
      have he : (∑' x, q.kernel p x (root i)) = 0 := by
        simp only [q.kernel_zero_of_end_not_mem p _ _ hi,tsum_zero]
      rw [he,mul_zero]
  simp_rw [hr,hc] at ht
  rw [← Finset.sum_mul,← Finset.sum_mul] at ht
  rw [q.kernel_column_orbit (root i₀) p y hy]
  exact (mul_left_cancel₀ (ne_of_gt hpos) ht).symm

 
theorem kernel_column_le_success {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (p : unitInterval) (y : V) :
    (∑' x, q.kernel p x y) ≤ q.successProbability p (root i₀) := by
  by_cases hy : y ∈ vertexOrbit G (root i₀)
  · exact (q.kernel_column_eq_success root weight Γ htr hΓ hw i₀ hw₀ p y hy).le
  · simpa only [q.kernel_zero_of_end_not_mem p _ _ hy,tsum_zero] using
      q.successProbability_nonneg p (root i₀)

end LocalEndpointRule
end EndpointTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section EndpointSchur
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem kernel_row_le_success (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval) (x : V) :
    (∑' y, q.kernel p x y) ≤ q.successProbability p o := by
  by_cases hx : x ∈ vertexOrbit G o
  · exact (q.successProbability_orbit p o x hx).le
  · simpa only [q.kernel_zero_of_start_not_mem p _ _ hx,tsum_zero] using
      q.successProbability_nonneg p o

 
noncomputable def normalizedKernel (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (p : unitInterval) (x y : V) : ℝ :=
  (q.successProbability p o)⁻¹ * q.kernel p x y

 

theorem exists_normalized_operator {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ)
    (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b) (hw : ∀ i, 0 ≤ weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L)
    (p : unitInterval) (hu : 0 < q.successProbability p (root i₀)) :
    ∃ A : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A‖ ∧ ‖A‖ ≤ 1 ∧
      ∀ x y, A (lp.single 2 y (1:ℂ)) x = (q.normalizedKernel (root i₀) p x y : ℂ) := by
  let u := q.successProbability p (root i₀)
  have hu₀ : u ≠ 0 := ne_of_gt hu
  have hn (x y : V) : 0 ≤ q.normalizedKernel (root i₀) p x y :=
    mul_nonneg (inv_nonneg.mpr hu.le) (q.kernel_nonneg p x y)
  have hr (x : V) (S : Finset V) : (∑ y ∈ S, q.normalizedKernel (root i₀) p x y) ≤ 1 := by
    change (∑ y ∈ S, u⁻¹ * q.kernel p x y) ≤ 1
    rw [← Finset.mul_sum]
    calc
      _ ≤ u⁻¹ * (∑' y, q.kernel p x y) := mul_le_mul_of_nonneg_left
        ((q.summable_kernel p x).sum_le_tsum S (fun y _ => q.kernel_nonneg p x y)) (inv_nonneg.mpr hu.le)
      _ ≤ u⁻¹ * u := mul_le_mul_of_nonneg_left
        (q.kernel_row_le_success (root i₀) p x) (inv_nonneg.mpr hu.le)
      _ = 1 := inv_mul_cancel₀ hu₀
  have hc (y : V) (S : Finset V) : (∑ x ∈ S, q.normalizedKernel (root i₀) p x y) ≤ 1 := by
    change (∑ x ∈ S, u⁻¹ * q.kernel p x y) ≤ 1
    rw [← Finset.mul_sum]
    calc
      _ ≤ u⁻¹ * (∑' x, q.kernel p x y) := mul_le_mul_of_nonneg_left
        ((q.summable_kernel_column p y).sum_le_tsum S (fun x _ => q.kernel_nonneg p x y)) (inv_nonneg.mpr hu.le)
      _ ≤ u⁻¹ * u := mul_le_mul_of_nonneg_left
        (q.kernel_column_le_success root weight Γ htr hΓ hw i₀ hw₀ p y) (inv_nonneg.mpr hu.le)
      _ = 1 := inv_mul_cancel₀ hu₀
  obtain ⟨A,hA,hK⟩ := exists_operator_of_row_column_bound (q.normalizedKernel (root i₀) p) 1 (by norm_num) hn hr hc
  refine ⟨A,?_,hA,hK⟩
  apply norm_pos_iff.mpr
  intro ha
  have hz (y : V) : q.kernel p (root i₀) y = 0 := by
    have h := hK (root i₀) y
    rw [ha] at h
    have he : u⁻¹ * q.kernel p (root i₀) y = 0 := Complex.ofReal_eq_zero.mp h.symm
    exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero hu₀)
  have he : u = 0 := by simp only [u,successProbability,hz,tsum_zero]
  exact hu₀ he

end LocalEndpointRule
end EndpointSchur

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
section FiniteLocalIntegral
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def finiteFieldEquiv (Q : Finset E) : FiniteField Q ≃ Set (Q : Set E) where
  toFun ω := Subtype.val ⁻¹' finiteFieldSet Q ω
  invFun η := ⟨η.toFinset.map ⟨Subtype.val,Subtype.val_injective⟩, by
    apply Finset.mem_powerset.mpr
    intro e he
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp he
    exact a.property⟩
  left_inv ω := by
    apply Subtype.ext
    apply Finset.coe_injective
    ext e
    simp only [Finset.coe_map,Set.mem_image,finiteFieldSet,Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨a,ha,rfl⟩
      have ha' : a ∈ (Subtype.val ⁻¹' (ω.val : Set E) : Set (Q : Set E)) := Set.mem_toFinset.mp ha
      exact ha'
    · intro he
      exact ⟨⟨e,Finset.mem_powerset.mp ω.property he⟩,Set.mem_toFinset.mpr he,rfl⟩
  right_inv η := by
    ext e
    simp only [Set.mem_preimage,finiteFieldSet,Finset.coe_map,Set.coe_toFinset,
      Set.mem_image,Function.Embedding.coeFn_mk,Subtype.val_injective.eq_iff,exists_eq_right]

@[simp] theorem finiteFieldEquiv_apply (Q : Finset E) (ω : FiniteField Q) :
    finiteFieldEquiv Q ω = Subtype.val ⁻¹' finiteFieldSet Q ω := rfl

@[simp] theorem finiteFieldEquiv_image (Q : Finset E) (ω : FiniteField Q) :
    Subtype.val '' finiteFieldEquiv Q ω = finiteFieldSet Q ω := by
  rw [finiteFieldEquiv_apply]
  apply Set.image_preimage_eq_of_subset
  intro e he
  exact ⟨⟨e,Finset.mem_powerset.mp ω.property he⟩,rfl⟩

 

theorem finiteFieldWeight_eq_atom (Q : Finset E) (p : unitInterval) (ω : FiniteField Q) :
    finiteFieldWeight Q p ω = (law p : Measure (Set (Q : Set E))).real {finiteFieldEquiv Q ω} := by
  have hn : (finiteFieldEquiv Q ω).ncard = ω.val.card := by
    rw [finiteFieldEquiv_apply,Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
    · exact Set.ncard_coe_finset _
    · intro e he
      exact ⟨⟨e,Finset.mem_powerset.mp ω.property he⟩,rfl⟩
  rw [law,setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ,
    Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ,hn]
  have hc : Fintype.card (Q : Set E) = Q.card := Fintype.card_coe Q
  simp only [finiteFieldWeight,bernoulliWeight,Set.ncard_univ,Nat.card_eq_fintype_card,hc]

 

theorem integral_finite_local (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) :
    (∫ ω, f ω ∂law p) = ∑ η : FiniteField Q, finiteFieldWeight Q p η * f (finiteFieldSet Q η) := by
  let g : Set (Q : Set E) → ℝ := fun η => f (Subtype.val '' η)
  have hmap := integral_map (μ := law p) (measurable_set_restrict (Q : Set E)).aemeasurable
    (measurable_of_finite g).aestronglyMeasurable
  rw [law_map_restrict p (Q : Set E)] at hmap
  have he (ω : Set E) : g (Subtype.val ⁻¹' ω) = f ω := by
    rw [hf ω]
    dsimp [g]
    congr 1
    ext e
    simp [and_comm]
  simp_rw [he] at hmap
  rw [← hmap,integral_fintype Integrable.of_finite]
  rw [← (finiteFieldEquiv Q).sum_comp]
  apply Finset.sum_congr rfl
  intro η _
  rw [← finiteFieldWeight_eq_atom]
  simp only [g,finiteFieldEquiv_image,smul_eq_mul]

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

 

theorem kernel_finite_sum (q : LocalEndpointRule G hloc O M L) (p : unitInterval) (x y : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset
    q.kernel p x y = ∑ η : FiniteField Q, finiteFieldWeight Q p η * q.mass (finiteFieldSet Q η) x y :=
  integral_finite_local _ p (fun ω => q.mass ω x y) (fun ω => q.locality ω x y)

theorem continuous_kernel (q : LocalEndpointRule G hloc O M L) (x y : V) :
    Continuous (fun p : unitInterval => q.kernel p x y) := by
  simp_rw [q.kernel_finite_sum]
  apply continuous_finsetSum
  intro η _
  unfold finiteFieldWeight bernoulliWeight
  fun_prop

theorem continuous_successProbability (q : LocalEndpointRule G hloc O M L) (x : V) :
    Continuous (fun p : unitInterval => q.successProbability p x) := by
  have he (p : unitInterval) : q.successProbability p x =
      ∑ y ∈ (finite_reachBall hloc x M).toFinset, q.kernel p x y := by
    apply tsum_eq_sum
    intro y hy
    exact q.kernel_outside_ball_zero p x y (by simpa only [Set.Finite.mem_toFinset] using hy)
  simp_rw [he]
  exact continuous_finsetSum _ (fun y _ => q.continuous_kernel x y)

end LocalEndpointRule
end FiniteLocalIntegral

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GoodnessCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem internalEdges_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (W : Set V) :
    internalEdges G (a ⁻¹' W) = b ⁻¹' internalEdges G W := by
  ext e
  simp only [internalEdges,Set.mem_ofPred_eq,Set.mem_preimage,hab e,Sym2.mem_map]
  constructor
  · intro h y hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact h z hz
  · intro h z hz
    exact h (a z) ⟨z,hz,rfl⟩

theorem cutExists_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (W : Set V) (e : E) :
    CutExists G (a ⁻¹' W) e ↔ CutExists G W (b e) := by
  constructor
  · rintro ⟨u,v,he,hu,hv⟩
    exact ⟨a u,a v,by rw [hab e,he,Sym2.map_mk],hu,hv⟩
  · rintro ⟨u,v,he,hu,hv⟩
    refine ⟨a.symm u,a.symm v,?_,by simpa using hu,by simpa using hv⟩
    have h := congrArg (Sym2.map a.symm) he
    simpa only [hab e,Sym2.map_map,Equiv.symm_comp_self,id_eq,Sym2.map_id',Sym2.map_mk] using h

theorem contactSet_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (W : Set V) :
    contactSet G (b ⁻¹' ω) (a ⁻¹' W) = b ⁻¹' contactSet G ω W := by
  ext e
  simp only [contactSet,Set.mem_ofPred_eq,Set.mem_preimage,cutExists_aut_preimage G hab]

theorem openMarkedPivotal_pair_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) (e : E) :
    OpenMarkedPivotal G (b ⁻¹' ω) {y} x e ↔
      OpenMarkedPivotal G ω {a y} (a x) (b e) := by
  have he : (b ⁻¹' ω) \ {e} = b ⁻¹' (ω \ {b e}) := by
    ext f
    simp only [Set.mem_sdiff,Set.mem_preimage,Set.mem_singleton_iff,b.injective.eq_iff]
  simp only [OpenMarkedPivotal,MarkedEvent,Set.mem_singleton_iff,exists_eq_left,
    Set.mem_preimage,he,conn_aut_iff G hab]

theorem pivotalDistance_aut_preimage (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) :
    pivotalDistance G (b ⁻¹' ω) x y = pivotalDistance G ω (a x) (a y) := by
  have he : {e | OpenMarkedPivotal G (b ⁻¹' ω) {y} x e} =
      b ⁻¹' {e | OpenMarkedPivotal G ω {a y} (a x) e} := by
    ext e
    exact openMarkedPivotal_pair_aut G hab ω x y e
  rw [pivotalDistance,he,Set.ncard_preimage_of_injective_subset_range b.injective]
  · rfl
  · exact fun e _ => b.surjective e

theorem goodForScale_aut_pullback (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) (L : ℝ)
    (hg : GoodForScale G ω (a x) L) : GoodForScale G (b ⁻¹' ω) x L := by
  intro W hW hconn hpos u hu v hv
  let W' := W.map a.toEmbedding
  have hpre : a ⁻¹' (W' : Set V) = (W : Set V) := by
    ext z
    simp [W']
  have hcfg : b ⁻¹' (ω ∩ internalEdges G (W' : Set V)) =
      (b ⁻¹' ω) ∩ internalEdges G (W : Set V) := by
    rw [Set.preimage_inter,← internalEdges_aut_preimage G hab,hpre]
  have hcontact : (contactSet G (b ⁻¹' ω) (W : Set V)).ncard =
      (contactSet G ω (W' : Set V)).ncard := by
    rw [← hpre,contactSet_aut_preimage G hab,
      Set.ncard_preimage_of_injective_subset_range b.injective]
    exact fun e _ => b.surjective e
  have hW' : (W' : Set V) ⊆ cluster G ω (a x) := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hz
    exact (conn_aut_iff G hab ω x w).mp (hW hw)
  have hc' : ∀ w ∈ W', ∀ z ∈ W', Conn G (ω ∩ internalEdges G (W' : Set V)) w z := by
    intro w hw z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hz
    apply (conn_aut_iff G hab _ u v).mp
    rw [hcfg]
    exact hconn u hu v hv
  have H := hg W' hW' hc' (by rwa [← hcontact]) (a u)
    (Finset.mem_map.mpr ⟨u,hu,rfl⟩) (a v) (Finset.mem_map.mpr ⟨v,hv,rfl⟩)
  rw [← pivotalDistance_aut_preimage G hab,hcfg,← hcontact] at H
  exact H

theorem goodForScale_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) (L : ℝ) :
    GoodForScale G (b ⁻¹' ω) x L ↔ GoodForScale G ω (a x) L := by
  constructor
  · intro h
    have H := goodForScale_aut_pullback G (isAut_symm G hab) (b ⁻¹' ω) (a x) L
      (by simpa only [Equiv.symm_apply_apply] using h)
    simpa only [← Set.preimage_comp,Equiv.self_comp_symm,Set.preimage_id_eq,id_eq] using H
  · exact goodForScale_aut_pullback G hab ω x L

end GoodnessCovariance

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedGoodLocality
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_finite_local (Q : Finset E) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) : Measurable f := by
  let g : Set (Q : Set E) → ℝ := fun η => f (Subtype.val '' η)
  have he : f = g ∘ (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) := by
    funext ω
    rw [hf ω]
    congr 1
    ext e
    simp [and_comm]
  rw [he]
  exact (measurable_of_finite g).comp (measurable_set_restrict (Q : Set E))

theorem integrable_finite_local (Q : Finset E) (p : unitInterval) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) : Integrable f (law p) := by
  let g : Set (Q : Set E) → ℝ := fun η => f (Subtype.val '' η)
  have he : f = g ∘ (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) := by
    funext ω
    rw [hf ω]
    congr 1
    ext e
    simp [and_comm]
  have hi : Integrable g (Measure.map (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (Q : Set E))) (law p)) := by
    rw [law_map_restrict]
    exact Integrable.of_finite
  rw [he]
  exact hi.comp_measurable (measurable_set_restrict (Q : Set E))

def CappedGoodness (G : BondGraph V E) (ω : Set E) (x : V) (M : ℕ) (L : ℝ) : Prop :=
  (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M ∧ GoodForScale G ω x L

theorem cappedGoodness_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (M : ℕ) (L : ℝ) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    CappedGoodness G ω x M L ↔ CappedGoodness G (ω ∩ (Q : Set E)) x M L := by
  have he (η : Set E) : CappedGoodness G η x M L ↔
      ((cluster G η x).Finite ∧ (cluster G η x).ncard ≤ M) ∧ ¬CappedBadGoodness G η x M L := by
    constructor
    · rintro ⟨hf,hM,hg⟩
      exact ⟨⟨hf,hM⟩,fun h => h.2.2 hg⟩
    · rintro ⟨⟨hf,hM⟩,hbad⟩
      refine ⟨hf,hM,?_⟩
      by_contra hn
      exact hbad ⟨hf,hM,hn⟩
  dsimp only
  have hbad := cappedBadGoodness_local G hloc x M L ω
  have hcap := capped_cluster_local G hloc x M ω
  dsimp only at hbad hcap
  rw [he,he,hbad,hcap]

theorem cappedGoodness_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) (M : ℕ) (L : ℝ) :
    CappedGoodness G (b ⁻¹' ω) x M L ↔ CappedGoodness G ω (a x) M L := by
  have hf : (cluster G (b ⁻¹' ω) x).Finite ↔ (cluster G ω (a x)).Finite := by
    rw [← cluster_aut G hab ω x]
    exact (Set.finite_image_iff a.injective.injOn).symm
  have hn : (cluster G (b ⁻¹' ω) x).ncard = (cluster G ω (a x)).ncard := by
    rw [← cluster_aut G hab ω x,Set.ncard_image_of_injective _ a.injective]
  simp only [CappedGoodness,hf,hn,goodForScale_aut_iff G hab]

theorem incidentSupport_ball_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) {r R : ℕ} (h : r ≤ R) :
    incidentSupport G hloc (finite_reachBall hloc x r).toFinset ⊆
      incidentSupport G hloc (finite_reachBall hloc x R).toFinset := by
  apply incidentSupport_mono
  intro z hz
  simp only [Set.Finite.mem_toFinset] at hz ⊢
  exact reachBall_mono_local G x h hz

theorem finite_local_of_subset (Q S : Finset E) (hQS : Q ⊆ S) (f : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (Q : Set E))) (ω : Set E) :
    f ω = f (ω ∩ (S : Set E)) := by
  rw [hf ω,hf (ω ∩ (S : Set E))]
  congr 1
  exact (Set.inter_assoc _ _ _).trans (congrArg (ω ∩ ·) (Set.inter_eq_right.mpr hQS)) |>.symm

end CappedGoodLocality

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CappedLocalLoad
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_prop_local_of_subset (Q S : Finset E) (hQS : Q ⊆ S) (P : Set E → Prop)
    (hf : ∀ ω, P ω ↔ P (ω ∩ (Q : Set E))) (ω : Set E) :
    P ω ↔ P (ω ∩ (S : Set E)) := by
  have he : (ω ∩ (S : Set E)) ∩ (Q : Set E) = ω ∩ (Q : Set E) :=
    (Set.inter_assoc _ _ _).trans (congrArg (ω ∩ ·) (Set.inter_eq_right.mpr hQS))
  exact (hf ω).trans ((he ▸ hf (ω ∩ (S : Set E))).symm)

 

structure CappedLocalLoad (G : BondGraph V E) (hloc : LocallyFinite G) (O : Set V) (M : ℕ) where
  mass : Set E → V → V → ℝ
  radius : ℕ
  nonneg : ∀ ω x y, 0 ≤ mass ω x y
  support : ∀ ω x y, mass ω x y ≠ 0 → x ∈ O ∧ y ∈ O ∧ Conn G ω x y ∧
    (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M
  locality : ∀ ω x y, mass ω x y =
    mass (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x radius).toFinset : Set E)) x y
  covariance : ∀ (a : V ≃ V) (b : E ≃ E), IsAut G a b → ∀ ω x y,
    mass (b ⁻¹' ω) x y = mass ω (a x) (a y)

namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

noncomputable def row (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V) : ℝ :=
  ∑' y, q.mass ω x y

theorem row_nonneg (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V) : 0 ≤ q.row ω x :=
  tsum_nonneg (q.nonneg ω x)

theorem outside_ball_zero (q : CappedLocalLoad G hloc O M) (ω : Set E) (x y : V)
    (hy : y ∉ reachBall G x M) : q.mass ω x y = 0 := by
  by_contra h
  obtain ⟨_,_,hc,hfin,hcap⟩ := q.support ω x y h
  exact hy (finite_cluster_subset_reachBall G ω x hfin M hcap hc)

theorem summable_mass (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V) :
    Summable (q.mass ω x) := by
  apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
  intro y hy
  exact q.outside_ball_zero ω x y (by simpa only [Set.Finite.mem_toFinset] using hy)

theorem mass_le_row (q : CappedLocalLoad G hloc O M) (ω : Set E) (x y : V) :
    q.mass ω x y ≤ q.row ω x := by
  simpa only [Finset.sum_singleton,row] using
    (q.summable_mass ω x).sum_le_tsum {y} (fun z _ => q.nonneg ω x z)

theorem row_locality (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V) :
    q.row ω x = q.row
      (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x q.radius).toFinset : Set E)) x :=
  tsum_congr (q.locality ω x)

theorem row_covariance (q : CappedLocalLoad G hloc O M) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω : Set E) (x : V) : q.row (b ⁻¹' ω) x = q.row ω (a x) := by
  unfold row
  simp_rw [q.covariance a b hab]
  exact a.tsum_eq _

theorem integrable_mass (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x y : V) :
    Integrable (fun ω => q.mass ω x y) (law p) :=
  integrable_finite_local _ p _ (q.locality · x y)

theorem integrable_row (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x : V) :
    Integrable (fun ω => q.row ω x) (law p) :=
  integrable_finite_local _ p _ (q.row_locality · x)

theorem integrable_sq_row (q : CappedLocalLoad G hloc O M) (p : unitInterval) (x : V) :
    Integrable (fun ω => q.row ω x ^ 2) (law p) :=
  integrable_finite_local _ p _ (fun ω => congrArg (· ^ 2) (q.row_locality ω x))

 

noncomputable def truncate (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b) (L : ℝ) :
    LocalEndpointRule G hloc O M L where
  mass ω x y := if q.row ω x ≤ b ∧ CappedGoodness G ω x M L then b⁻¹ * q.mass ω x y else 0
  radius := max q.radius M
  nonneg ω x y := by split_ifs; exact mul_nonneg (inv_nonneg.mpr hb.le) (q.nonneg ω x y); rfl
  row_le_one ω x := by
    by_cases h : q.row ω x ≤ b ∧ CappedGoodness G ω x M L
    · simp only [h,and_self,ite_true,tsum_mul_left]
      exact (mul_le_mul_of_nonneg_left h.1 (inv_nonneg.mpr hb.le)).trans_eq (inv_mul_cancel₀ hb.ne')
    · simp only [h,ite_false,tsum_zero,zero_le_one]
  support ω x y h := by
    split_ifs at h with hkeep
    · have hm : q.mass ω x y ≠ 0 := fun he => h (by rw [he,mul_zero])
      obtain ⟨hx,hy,hc,_,_⟩ := q.support ω x y hm
      exact ⟨hx,hy,hc,hkeep.2⟩
    · exact (h rfl).elim
  locality ω x y := by
    let S := incidentSupport G hloc (finite_reachBall hloc x (max q.radius M)).toFinset
    have hm := finite_local_of_subset _ S
      (incidentSupport_ball_mono G hloc x (le_max_left q.radius M))
      (fun η => q.mass η x y) (q.locality · x y) ω
    have hr := finite_local_of_subset _ S
      (incidentSupport_ball_mono G hloc x (le_max_left q.radius M))
      (fun η => q.row η x) (q.row_locality · x) ω
    have hg := finite_prop_local_of_subset _ S
      (incidentSupport_ball_mono G hloc x (le_max_right q.radius M))
      (fun η => CappedGoodness G η x M L) (fun η => cappedGoodness_local G hloc η x M L) ω
    simp only [hm,hr,hg]
    rfl
  covariance a c hac ω x y := by
    simp only [q.row_covariance a c hac,q.covariance a c hac,cappedGoodness_aut_iff G hac]

end CappedLocalLoad
end CappedLocalLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section TruncationLoss
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CappedLocalLoad
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ}

theorem cap_of_row_ne_zero (q : CappedLocalLoad G hloc O M) (ω : Set E) (x : V)
    (hr : q.row ω x ≠ 0) : (cluster G ω x).Finite ∧ (cluster G ω x).ncard ≤ M := by
  obtain ⟨y,hy⟩ : ∃ y, q.mass ω x y ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hr (by simp only [row,hn,tsum_zero])
  exact (q.support ω x y hy).2.2.2

theorem truncate_scaled_row (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b)
    (L : ℝ) (ω : Set E) (x : V) :
    b * (∑' y, (q.truncate b hb L).mass ω x y) =
      if q.row ω x ≤ b ∧ CappedGoodness G ω x M L then q.row ω x else 0 := by
  by_cases h : q.row ω x ≤ b ∧ CappedGoodness G ω x M L
  · simp only [truncate,ite_eq_left h,tsum_mul_left,← mul_assoc,mul_inv_cancel₀ hb.ne',one_mul]
    rfl
  · simp only [truncate,ite_eq_right h,tsum_zero,mul_zero]

theorem truncate_mass_le (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b)
    (L : ℝ) (ω : Set E) (x y : V) :
    (q.truncate b hb L).mass ω x y ≤ b⁻¹ * q.mass ω x y := by
  change (if _ then _ else _) ≤ _
  split_ifs
  · rfl
  · exact mul_nonneg (inv_nonneg.mpr hb.le) (q.nonneg ω x y)

 

theorem truncate_pointwise_loss (q : CappedLocalLoad G hloc O M) (b : ℝ) (hb : 0 < b)
    (L : ℝ) (ω : Set E) (x : V) :
    q.row ω x ≤ b * (∑' y, (q.truncate b hb L).mass ω x y) + q.row ω x ^ 2 / b +
      b * ({η | CappedBadGoodness G η x M L}.indicator (1 : Set E → ℝ) ω) := by
  rw [q.truncate_scaled_row b hb L]
  have hs : 0 ≤ q.row ω x ^ 2 / b := div_nonneg (sq_nonneg _) hb.le
  have hi : 0 ≤ ({η | CappedBadGoodness G η x M L}.indicator (1 : Set E → ℝ) ω) := by
    apply Set.indicator_nonneg
    intro η _
    norm_num
  by_cases hr : q.row ω x ≤ b
  · by_cases hg : CappedGoodness G ω x M L
    · simp only [hr,hg,and_self,ite_true]
      nlinarith
    · simp only [hg,and_false,ite_false,zero_add]
      by_cases hz : q.row ω x = 0
      · rw [hz]
        positivity
      · have hc := q.cap_of_row_ne_zero ω x hz
        have hbad : CappedBadGoodness G ω x M L := ⟨hc.1,hc.2,fun h => hg ⟨hc.1,hc.2,h⟩⟩
        rw [Set.indicator_of_mem (show ω ∈ {η | CappedBadGoodness G η x M L} from hbad)]
        change q.row ω x ≤ q.row ω x ^ 2 / b + b * 1
        linarith
  · simp only [hr,false_and,ite_false,zero_add]
    have htail : q.row ω x ≤ q.row ω x ^ 2 / b := by
      apply (le_div_iff₀ hb).mpr
      have ht := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hr)) (q.row_nonneg ω x)
      nlinarith
    exact htail.trans (le_add_of_nonneg_right (mul_nonneg hb.le hi))

 

theorem truncate_mean_loss (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ) (x : V) :
    (∫ ω, q.row ω x ∂law p) ≤ b * (q.truncate b hb L).successProbability p x +
      (∫ ω, q.row ω x ^ 2 ∂law p) / b + b * (law p).real {ω | CappedBadGoodness G ω x M L} := by
  let t := q.truncate b hb L
  have ht : Integrable (fun ω => ∑' y, t.mass ω x y) (law p) := by
    apply integrable_finite_local
      (incidentSupport G hloc (finite_reachBall hloc x t.radius).toFinset) p
    intro ω
    exact tsum_congr (t.locality ω x)
  have hbad := measurableSet_cappedBadGoodness G hloc x M L
  have hi : Integrable ({ω | CappedBadGoodness G ω x M L}.indicator (1 : Set E → ℝ)) (law p) :=
    (integrable_const (1:ℝ)).indicator hbad
  have h := integral_mono (q.integrable_row p x)
    (((ht.const_mul b).add ((q.integrable_sq_row p x).div_const b)).add (hi.const_mul b))
    (q.truncate_pointwise_loss b hb L · x)
  dsimp only [Pi.add_apply] at h
  have he₁ := integral_add ((ht.const_mul b).add ((q.integrable_sq_row p x).div_const b)) (hi.const_mul b)
  have he₂ := integral_add (ht.const_mul b) ((q.integrable_sq_row p x).div_const b)
  dsimp only [Pi.add_apply] at he₁ he₂
  rw [he₁,he₂,integral_const_mul,integral_div,integral_const_mul,
    integral_indicator_one hbad] at h
  rw [← t.kernel_row_integral p x] at h
  exact h

theorem truncate_success_lower (q : CappedLocalLoad G hloc O M) (p : unitInterval)
    (b : ℝ) (hb : 0 < b) (L : ℝ) (x : V) (a : ℝ)
    (hmean : a ≤ ∫ ω, q.row ω x ∂law p)
    (hmoment : (∫ ω, q.row ω x ^ 2 ∂law p) / b ≤ a/4)
    (hbad : b * (law p).real {ω | CappedBadGoodness G ω x M L} ≤ a/4) :
    a / (2*b) ≤ (q.truncate b hb L).successProbability p x := by
  have hh := q.truncate_mean_loss p b hb L x
  apply (div_le_iff₀ (mul_pos (by norm_num) hb)).mpr
  nlinarith

end CappedLocalLoad
end TruncationLoss

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CategoricalAmplificationInput
attribute [local instance] Classical.propDecidable Classical.decEq

 

def amplificationVertices (B : Finset V) (k : ℕ) (z : ↥B) (r : Fin k → ↥B) : ℕ → V :=
  fun i => (oldRunVertices k z r i).val

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {O : Set V} {M : ℕ} {L : ℝ}

noncomputable def amplificationWeight (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) : ℝ :=
  oldRunWeight (fun i a b => q.mass (s.2 i) a.val b.val) k z r

theorem amplificationWeight_eq (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) :
    q.amplificationWeight B k z s r = oldPathWeight k q.mass (amplificationVertices B k z r) s.2 := by
  exact (oldPathWeight_oldRunVertices k (fun ω a b => q.mass ω a.val b.val) s.2 z r).symm

theorem amplificationWeight_nonneg (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) (r : Fin k → ↥B) :
    0 ≤ q.amplificationWeight B k z s r :=
  oldRunWeight_nonneg (fun i (a b : ↥B) => q.mass (s.2 i) a.val b.val)
    (fun i a b => q.nonneg (s.2 i) a.val b.val) k z r

theorem amplificationWeight_row (q : LocalEndpointRule G hloc O M L)
    (B : Finset V) (k : ℕ) (z : ↥B) (s : SpliceState E) :
    (∑ r, q.amplificationWeight B k z s r) ≤ 1 := by
  have hr (i : ℕ) (a : ↥B) : (∑ b : ↥B, q.mass (s.2 i) a.val b.val) ≤ 1 := by
    rw [Finset.sum_coe_sort B]
    exact ((q.summable_mass _ _).sum_le_tsum B (fun y _ => q.nonneg _ _ y)).trans (q.row_le_one _ _)
  simpa only [one_pow,amplificationWeight] using sum_oldRunWeight_le
    (fun i (a b : ↥B) => q.mass (s.2 i) a.val b.val)
    (fun _ a b => q.nonneg _ a.val b.val) 1 zero_le_one hr k z

 

noncomputable def amplificationInputs (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) : Finset (SpliceState E) :=
  (finiteSpliceDomain Q (Finset.Icc 1 k)).filter fun s =>
    x ∈ O ∧ z.val ∈ O ∧ n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n ∧
      amplificationVertices B k z r 0 ∈ cluster G s.1 x ∧ q.amplificationWeight B k z s r ≠ 0

theorem mem_amplificationInputs (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E) :
    s ∈ q.amplificationInputs Q B x k n z r ↔
      s ∈ finiteSpliceDomain Q (Finset.Icc 1 k) ∧
      x ∈ O ∧ z.val ∈ O ∧ n ≤ (cluster G s.1 x).ncard ∧ (cluster G s.1 x).ncard < 2*n ∧
      amplificationVertices B k z r 0 ∈ cluster G s.1 x ∧ q.amplificationWeight B k z s r ≠ 0 :=
  Finset.mem_filter

theorem amplificationInputs_subset (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) :
    q.amplificationInputs Q B x k n z r ⊆ finiteSpliceDomain Q (Finset.Icc 1 k) :=
  Finset.filter_subset _ _

theorem amplificationInputs_chain (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E)
    (hs : s ∈ q.amplificationInputs Q B x k n z r) :
    ∀ i, 1 ≤ i → i ≤ k →
      Conn G (s.2 i) (amplificationVertices B k z r i) (amplificationVertices B k z r (i-1)) ∧
      (cluster G (s.2 i) (amplificationVertices B k z r i)).Finite ∧
      (cluster G (s.2 i) (amplificationVertices B k z r i)).ncard ≤ M ∧
      GoodForScale G (s.2 i) (amplificationVertices B k z r i) L := by
  apply oldPathWeight_support G k M L q.mass
  · intro ω a b h
    exact (q.support ω a b h).2.2
  · exact (q.amplificationWeight_eq B k z s r) ▸ ((q.mem_amplificationInputs Q B x k n z r s).mp hs).2.2.2.2.2.2

 

theorem amplificationTrace_support (q : LocalEndpointRule G hloc O M L)
    (Q : Finset E) (B : Finset V) (x : V) (k n : ℕ) (z : ↥B) (r : Fin k → ↥B) (s : SpliceState E)
    (hs : s ∈ q.amplificationInputs Q B x k n z r) (c : List (ℕ × E)) (ωf : Set E)
    (ht : SpliceTrace G x s.2 (amplificationVertices B k z r) k 0 s.1 c ωf) :
    x ∈ O ∧ z.val ∈ O ∧ Conn G ωf x z.val ∧ (cluster G ωf x).Finite ∧
      (cluster G ωf x).ncard ≤ 2*n+k*M := by
  obtain ⟨hdom,hx,hz,_,hbin,_,_⟩ := (q.mem_amplificationInputs Q B x k n z r s).mp hs
  have hc := q.amplificationInputs_chain Q B x k n z r s hs
  have hroot : (cluster G s.1 x).Finite :=
    cluster_finite_of_finite_edges G (Q.finite_toSet.subset
      ((mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) s).mp hdom).1) x
  obtain ⟨hf,hcap⟩ := trajectoryUnion_finite_cap G s.2 (amplificationVertices B k z r) k M
    (fun i hi hik => ⟨(hc i hi hik).2.1,(hc i hi hik).2.2.1⟩)
  have hsub : cluster G ωf x ⊆ cluster G s.1 x ∪ trajectoryUnion G s.2 (amplificationVertices B k z r) k := by
    intro v hv
    by_cases hv' : v ∈ cluster G s.1 x
    · exact Or.inl hv'
    · exact Or.inr (ht.added_subset_trajectory G x s.2 (amplificationVertices B k z r) k 0 s.1 ωf c ⟨hv,hv'⟩)
  refine ⟨hx,hz,?_,(hroot.union hf).subset hsub,?_⟩
  · simpa only [amplificationVertices,oldRunVertices_last,cluster,Set.mem_ofPred_eq] using
      ht.endpoint G x s.2 (amplificationVertices B k z r) k 0 s.1 ωf c
  · exact (Set.ncard_le_ncard hsub (hroot.union hf)).trans
      ((Set.ncard_union_le ..).trans (Nat.add_le_add (by omega) hcap))

end LocalEndpointRule
end CategoricalAmplificationInput

end Percolation

end OAI
