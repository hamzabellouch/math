import OAI.Combinatorics.PlanarL1.Cuts
import OAI.Combinatorics.PlanarL1.Execution

namespace OAI

section

namespace PlanarL1.FiniteL1

open MeasureTheory

variable {I : Type*} [Fintype I] [MeasurableSpace I] [DiscreteMeasurableSpace I]

noncomputable def ofFunction (f : I → ℝ) : Lp ℝ 1 (Measure.count : Measure I) :=
  (MemLp.of_discrete : MemLp f 1 Measure.count).toLp f

lemma norm_ofFunction (f : I → ℝ) : ‖ofFunction f‖ = ∑ i, |f i| := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ i, ‖ofFunction f i‖ ∂Measure.count) = ∫ i, |f i| ∂Measure.count := by
      apply integral_congr_ae
      exact (MemLp.coeFn_toLp (MemLp.of_discrete : MemLp f 1 Measure.count)).mono fun i h => by
        change ‖(MemLp.of_discrete : MemLp f 1 Measure.count).toLp f i‖ = |f i|
        rw [h,Real.norm_eq_abs]
    _ = _ := integral_count _

lemma ofFunction_sub (f g : I → ℝ) :
    ofFunction f - ofFunction g = ofFunction (fun i => f i-g i) := by
  exact (MemLp.toLp_sub (MemLp.of_discrete : MemLp f 1 Measure.count)
    (MemLp.of_discrete : MemLp g 1 Measure.count)).symm

lemma norm_sub (f g : I → ℝ) : ‖ofFunction f-ofFunction g‖ = ∑ i, |f i-g i| := by
  rw [ofFunction_sub,norm_ofFunction]

/-- The final finite cut-coordinate formula, valued in the ACTUAL real L1
space requested by the main theorem, rather than an abstract cut cone. -/
noncomputable def cutMap {V : Type*} (cut : I → Set V) (weight : I → ℝ) (v : V) :
    Lp ℝ 1 (Measure.count : Measure I) := by
  classical
  exact ofFunction (fun i => if v ∈ cut i then weight i else 0)

lemma norm_cutMap {V : Type*} (cut : I → Set V) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (x y : V) :
    ‖cutMap cut weight x-cutMap cut weight y‖ =
      ∑ i, weight i*|((cut i).indicator (fun _ => (1:ℝ)) x)-
        ((cut i).indicator (fun _ => (1:ℝ)) y)| := by
  classical
  rw [cutMap,cutMap,norm_sub]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ cut i <;> by_cases hy : y ∈ cut i <;>
    simp [hx,hy,abs_of_nonneg (hweight i)]

end PlanarL1.FiniteL1



end

section

namespace PlanarL1.FiniteL1
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

variable {V Ω : Type*} [Fintype V] [MeasurableSpace Ω] (μ : Measure Ω)

/-- Binary measurable assignments with integrable pair differences; individual
sets may have infinite measure, exactly as for the paper's label half-lines. -/
structure BinarySystem where
  active : Ω → V → Prop
  measurable : ∀ v, MeasurableSet {ω | active ω v}
  integrable : ∀ x y, Integrable (fun ω =>
    |(if active ω x then (1:ℝ) else 0)-(if active ω y then (1:ℝ) else 0)|) μ

namespace BinarySystem
variable {μ} (B : BinarySystem (V := V) μ)

noncomputable def indicator (v : V) (ω : Ω) : ℝ := if B.active ω v then 1 else 0
noncomputable def fiber (S : Set V) : Set Ω := {ω | ∀ v, B.active ω v ↔ v ∈ S}
noncomputable def fiberValue (S : Set V) (ω : Ω) : ℝ := if ω ∈ B.fiber S then 1 else 0

def Proper (S : Set V) : Prop := S.Nonempty ∧ Sᶜ.Nonempty

noncomputable def contribution (S : Set V) (ω : Ω) : ℝ :=
  if Proper S then B.fiberValue S ω else 0

noncomputable def weight (S : Set V) : ℝ := ∫ ω, B.contribution S ω ∂μ

lemma measurable_fiber (S : Set V) : MeasurableSet (B.fiber S) := by
  have he : B.fiber S = ⋂ v, {ω | B.active ω v ↔ v ∈ S} := by ext ω; simp [fiber]
  rw [he]
  apply MeasurableSet.iInter
  intro v
  by_cases hv : v ∈ S
  · simpa only [hv,iff_true] using B.measurable v
  · simpa only [hv,iff_false,Set.compl_ofPred] using (B.measurable v).compl

lemma measurable_fiberValue (S : Set V) : Measurable (B.fiberValue S) :=
  Measurable.ite (B.measurable_fiber S) measurable_const measurable_const

lemma measurable_contribution (S : Set V) : Measurable (B.contribution S) := by
  unfold contribution
  split_ifs
  · exact B.measurable_fiberValue S
  · exact measurable_const

omit [Fintype V] in
lemma contribution_nonneg (S : Set V) (ω : Ω) : 0 ≤ B.contribution S ω := by
  unfold contribution fiberValue
  split_ifs <;> norm_num

lemma integrable_contribution (S : Set V) : Integrable (B.contribution S) μ := by
  by_cases hp : Proper S
  · obtain ⟨x,hx⟩ := hp.1
    obtain ⟨y,hy⟩ := hp.2
    apply (B.integrable x y).mono' (B.measurable_contribution S).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_of_nonneg (B.contribution_nonneg S ω)]
    by_cases hf : ω ∈ B.fiber S
    · have hfx := (hf x).mpr hx
      have hfy : ¬B.active ω y := fun h => hy ((hf y).mp h)
      simp only [contribution,ite_eq_left hp,fiberValue,ite_eq_left hf,ite_eq_left hfx,ite_eq_right hfy,
        sub_zero,abs_one,le_refl]
    · simp only [contribution,ite_eq_left hp,fiberValue,ite_eq_right hf]
      exact abs_nonneg _
  · have he : B.contribution S = fun _ => 0 := by
      funext ω
      exact ite_eq_right hp
    rw [he]
    exact integrable_zero _ _ _

omit [Fintype V] in
lemma weight_nonneg (S : Set V) : 0 ≤ B.weight S :=
  integral_nonneg (fun ω => B.contribution_nonneg S ω)

noncomputable def cutCost (S : Set V) (x y : V) : ℝ :=
  |(S.indicator (fun _ => (1:ℝ)) x)-(S.indicator (fun _ => (1:ℝ)) y)|

omit [Fintype V] in
lemma cutCost_nonneg (S : Set V) (x y : V) : 0 ≤ cutCost S x y := abs_nonneg _

omit [Fintype V] in
lemma cutCost_eq_zero_of_not_proper {S : Set V} (hS : ¬Proper S) (x y : V) :
    cutCost S x y = 0 := by
  classical
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp [cutCost,hx,hy]
  · exact (hS ⟨⟨x,hx⟩,⟨y,hy⟩⟩).elim
  · exact (hS ⟨⟨y,hy⟩,⟨x,hx⟩⟩).elim
  · simp [cutCost,hx,hy]

lemma sum_contribution (x y : V) (ω : Ω) :
    ∑ S : Set V, B.contribution S ω * cutCost S x y =
      |B.indicator x ω-B.indicator y ω| := by
  classical
  let S₀ : Set V := {v | B.active ω v}
  have hf : ω ∈ B.fiber S₀ := by intro v; rfl
  have ho : ∀ S, S ≠ S₀ → B.contribution S ω = 0 := by
    intro S hS
    have hnf : ω ∉ B.fiber S := by
      intro h
      apply hS
      ext v
      exact (h v).symm
    simp only [contribution,fiberValue,ite_eq_right hnf,ite_self]
  rw [Finset.sum_eq_single S₀ (fun S _ hs => by rw [ho S hs,zero_mul])
    (fun h => (h (Finset.mem_univ _)).elim)]
  have hc : cutCost S₀ x y = |B.indicator x ω-B.indicator y ω| := by
    simp only [cutCost,Set.indicator_apply,indicator,S₀,Set.mem_ofPred_eq]
  by_cases hp : Proper S₀
  · rw [contribution,ite_eq_left hp,fiberValue,ite_eq_left hf,one_mul,hc]
  · rw [contribution,ite_eq_right hp,zero_mul,← hc,cutCost_eq_zero_of_not_proper hp]

/-- Exact cut coefficients, not a finite-dimensional approximation of the label
metric. Empty/full cuts are zero; proper weights are finite by pair integrability. -/
lemma cut_decomposition (x y : V) :
    ∑ S : Set V, B.weight S * cutCost S x y =
      ∫ ω, |B.indicator x ω-B.indicator y ω| ∂μ := by
  classical
  calc
    _ = ∑ S : Set V, ∫ ω, B.contribution S ω*cutCost S x y ∂μ := by
      apply Finset.sum_congr rfl
      intro S _
      rw [integral_mul_const]
      rfl
    _ = ∫ ω, ∑ S : Set V, B.contribution S ω*cutCost S x y ∂μ := by
      symm
      exact integral_finsetSum _ (fun S _ => (B.integrable_contribution S).mul_const _)
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (B.sum_contribution x y))

local instance : MeasurableSpace (Set V) := ⊤

noncomputable def embedding (x : V) : Lp ℝ 1 (Measure.count : Measure (Set V)) :=
  cutMap id B.weight x

lemma distance_embedding (x y : V) :
    ‖B.embedding x-B.embedding y‖ = ∫ ω, |B.indicator x ω-B.indicator y ω| ∂μ := by
  rw [embedding,embedding,norm_cutMap id B.weight B.weight_nonneg]
  exact B.cut_decomposition x y

end BinarySystem
end PlanarL1.FiniteL1


end

section

namespace PlanarL1.FiniteL1
open MeasureTheory

/-- All final metrics, and all adaptive averages of them, use the same finite
cut index type. No finite approximation to the label space is made. -/
structure CutFamily (V : Type*) where
  weight : Set V → ℝ
  nonneg : ∀ S, 0 ≤ weight S

namespace CutFamily
variable {V α ι : Type*} [Fintype V]

noncomputable def distance (C : CutFamily V) (x y : V) : ℝ := by
  classical
  exact ∑ S : Set V, C.weight S * BinarySystem.cutCost S x y

lemma distance_nonneg (C : CutFamily V) (x y : V) : 0 ≤ C.distance x y := by
  classical
  exact Finset.sum_nonneg (fun S _ => mul_nonneg (C.nonneg S) (abs_nonneg _))

noncomputable def ofBinary {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (B : BinarySystem (V := V) μ) : CutFamily V := ⟨B.weight,B.weight_nonneg⟩

lemma distance_ofBinary {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (B : BinarySystem (V := V) μ) (x y : V) :
    (ofBinary B).distance x y=∫ ω, |B.indicator x ω-B.indicator y ω| ∂μ :=
  B.cut_decomposition x y

noncomputable def add (C D : CutFamily V) : CutFamily V where
  weight S := C.weight S+D.weight S
  nonneg S := add_nonneg (C.nonneg S) (D.nonneg S)

lemma distance_add (C D : CutFamily V) (x y : V) :
    (C.add D).distance x y=C.distance x y+D.distance x y := by
  classical
  simp only [distance,add,add_mul,Finset.sum_add_distrib]

noncomputable def sum [Fintype ι] (C : ι → CutFamily V) : CutFamily V where
  weight S := ∑ i, (C i).weight S
  nonneg S := Finset.sum_nonneg (fun i _ => (C i).nonneg S)

lemma distance_sum [Fintype ι] (C : ι → CutFamily V) (x y : V) :
    (sum C).distance x y=∑ i, (C i).distance x y := by
  classical
  simp only [distance,sum,Finset.sum_mul]
  exact Finset.sum_comm

noncomputable def average (E : Execution α) (C : α → CutFamily V) : CutFamily V where
  weight S := E.mean (fun a => (C a).weight S)
  nonneg S := E.mean_nonneg (fun a => (C a).nonneg S)

lemma distance_average (E : Execution α) (C : α → CutFamily V) (x y : V) :
    (average E C).distance x y=E.mean (fun a => (C a).distance x y) := by
  classical
  simp only [distance,average,Execution.mean_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [mul_comm,← Execution.mean_smul]
  congr 1
  funext a
  exact mul_comm _ _

noncomputable def scale (c : ℝ) (hc : 0 ≤ c) (C : CutFamily V) : CutFamily V where
  weight S := c*C.weight S
  nonneg S := mul_nonneg hc (C.nonneg S)

lemma distance_scale (c : ℝ) (hc : 0 ≤ c) (C : CutFamily V) (x y : V) :
    (scale c hc C).distance x y=c*C.distance x y := by
  classical
  simp only [distance,scale,Finset.mul_sum,mul_assoc]

local instance : MeasurableSpace (Set V) := ⊤

noncomputable def embedding (C : CutFamily V) (x : V) : Lp ℝ 1 (Measure.count : Measure (Set V)) :=
  cutMap id C.weight x

lemma norm_embedding (C : CutFamily V) (x y : V) :
    ‖C.embedding x-C.embedding y‖=C.distance x y := by
  classical
  exact norm_cutMap id C.weight C.nonneg x y

/-- The last rescaling step in the manuscript, using actual real Lp1. The
geometric lower bound is a prerequisite proved by the random construction. -/
theorem embedding_of_bounds (C : CutFamily V) (d : V → V → ℝ) {a b : ℝ}
    (ha : 0 < a) (hl : ∀ x y, a*d x y ≤ C.distance x y)
    (hu : ∀ x y, C.distance x y ≤ b*d x y) :
    ∃ f : V → Lp ℝ 1 (Measure.count : Measure (Set V)),
      ∀ x y, d x y ≤ ‖f x-f y‖ ∧ ‖f x-f y‖ ≤ (b/a)*d x y := by
  refine ⟨(scale a⁻¹ (inv_nonneg.mpr ha.le) C).embedding,?_⟩
  intro x y
  rw [norm_embedding,distance_scale]
  constructor
  · have h := mul_le_mul_of_nonneg_left (hl x y) (inv_nonneg.mpr ha.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul] using h
  · have h := mul_le_mul_of_nonneg_left (hu x y) (inv_nonneg.mpr ha.le)
    simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

end CutFamily
end PlanarL1.FiniteL1



end

end OAI
