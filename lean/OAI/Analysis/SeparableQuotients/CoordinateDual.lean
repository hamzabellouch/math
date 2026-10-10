import OAI.Analysis.SeparableQuotients.NormCompletion

namespace OAI

noncomputable section

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

lemma includeFinite_injective : Function.Injective K.includeFinite := by
  intro x y h
  exact K.finiteMap_injective (congrArg Subtype.val h)

lemma generator_independent : LinearIndependent ℝ K.generator := by
  change LinearIndependent ℝ (fun a : Γ => K.includeFinite (Finsupp.single a 1))
  exact (Finsupp.linearIndependent_single_one (R := ℝ) (ι := Γ)).map_injOn
      K.includeFinite K.includeFinite_injective.injOn

lemma infiniteDimensional [Infinite Γ] : ¬ Module.Finite ℝ K.Space := by
  intro h
  let := h
  exact Module.Finite.not_linearIndependent_of_infinite K.generator K.generator_independent

@[reducible] local instance dualNormedGroup : NormedAddCommGroup (StrongDual ℝ K.Space) := inferInstance
@[reducible] local instance dualNormedSpace : NormedSpace ℝ (StrongDual ℝ K.Space) := inferInstance

/-- The coordinate predual. -/
def predual : Submodule ℝ (StrongDual ℝ K.Space) :=
  (Submodule.span ℝ (Set.range K.coordinate)).topologicalClosure

instance predual_isClosed : IsClosed (K.predual : Set (StrongDual ℝ K.Space)) :=
  Submodule.isClosed_topologicalClosure _

lemma coordinate_mem_predual (a : Γ) : K.coordinate a ∈ K.predual :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, rfl⟩)

lemma functional_mem_predual (f : K.carrier) : K.functional f ∈ K.predual := by
  rw [K.functional_eq_sum]
  exact Submodule.sum_mem _ (fun a _ =>
    Submodule.smul_mem _ _ (K.coordinate_mem_predual a))

@[reducible] local instance predualDualNormedGroup :
    NormedAddCommGroup (StrongDual ℝ K.predual) := inferInstance
@[reducible] local instance predualDualNormedSpace :
    NormedSpace ℝ (StrongDual ℝ K.predual) := inferInstance

/-- Canonical evaluation into the dual of the coordinate span. -/
def evaluation : K.Space →L[ℝ] StrongDual ℝ K.predual :=
  (ContinuousLinearMap.precomp ℝ K.predual.subtypeL).comp
    (NormedSpace.inclusionInDoubleDual ℝ K.Space)

@[simp] lemma evaluation_apply (x : K.Space) (g : K.predual) :
    K.evaluation x g = g.val x := rfl

lemma norm_evaluation (x : K.Space) : ‖K.evaluation x‖ = ‖x‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
    intro g
    exact (g.val.le_opNorm x).trans_eq (mul_comm _ _)
  · change ‖x.val‖ ≤ ‖K.evaluation x‖
    apply lp.norm_le_of_forall_le (f := x.val) (norm_nonneg (K.evaluation x))
    intro f
    let g : K.predual := ⟨K.functional f, K.functional_mem_predual f⟩
    calc
      |K.functional f x| = ‖K.evaluation x g‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖K.evaluation x‖ * ‖g‖ := (K.evaluation x).le_opNorm g
      _ ≤ ‖K.evaluation x‖ * 1 :=
        mul_le_mul_of_nonneg_left (K.norm_functional_le f) (norm_nonneg (K.evaluation x))
      _ = _ := mul_one _

def evaluationIsometry : K.Space →ₗᵢ[ℝ] StrongDual ℝ K.predual where
  toLinearMap := K.evaluation.toLinearMap
  norm_map' := K.norm_evaluation

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology Classical
open Filter
universe u
variable {Γ : Type u} (K : NormingSet Γ)

lemma projection_norm_apply_le (A : Set Γ) (hA : K.CropStable A) (x : K.Space) :
    ‖K.projection A hA x‖ ≤ ‖x‖ :=
  ((K.projection A hA).le_opNorm x).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (K.norm_projection_le A hA) (norm_nonneg x))

/-- Strong convergence of uniformly contractive coordinate crops whose sets eventually contain every coordinate. -/
lemma tendsto_projection {ι : Type*} {l : Filter ι} (A : ι → Set Γ)
    (hA : ∀ i, K.CropStable (A i)) (hcover : ∀ a, ∀ᶠ i in l, a ∈ A i) (x : K.Space) :
    Tendsto (fun i => K.projection (A i) (hA i) x) l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v, hv⟩ := K.denseRange_includeFinite.exists_dist_lt x (by positivity : (0 : ℝ) < ε/3)
  have hevent : ∀ᶠ i in l, ∀ a ∈ v.support, a ∈ A i :=
    (v.support.eventually_all).mpr (fun a _ => hcover a)
  filter_upwards [hevent] with i hi
  have hvfix : K.projection (A i) (hA i) (K.includeFinite v) = K.includeFinite v := by
    rw [K.projection_includeFinite]
    congr 1
    ext a
    by_cases ha : a ∈ A i
    · simp [ha]
    · have hz : v a = 0 := by
        by_contra hn
        exact ha (hi a (Finsupp.mem_support_iff.mpr hn))
      simp [ha, hz]
  rw [dist_eq_norm] at hv ⊢
  calc
    ‖K.projection (A i) (hA i) x - x‖ =
        ‖K.projection (A i) (hA i) (x - K.includeFinite v) + (K.includeFinite v - x)‖ := by
      rw [(K.projection (A i) (hA i)).map_sub, hvfix]
      abel_nf
    _ ≤ ‖K.projection (A i) (hA i) (x - K.includeFinite v)‖ + ‖K.includeFinite v - x‖ :=
      norm_add_le _ _
    _ ≤ ‖x - K.includeFinite v‖ + ‖K.includeFinite v - x‖ := by
      gcongr
      exact K.projection_norm_apply_le _ _ _
    _ < ε := by rw [norm_sub_rev (K.includeFinite v) x]; linarith

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)
@[reducible] local instance dualNormedGroup' : NormedAddCommGroup (StrongDual ℝ K.Space) := inferInstance
@[reducible] local instance dualNormedSpace' : NormedSpace ℝ (StrongDual ℝ K.Space) := inferInstance

/-- The coordinate functional regarded as an element of the actual predual. -/
def predualCoordinate (a : Γ) : K.predual := ⟨K.coordinate a, K.coordinate_mem_predual a⟩

def rationalPredual : (Γ →₀ ℚ) →ₗ[ℚ] K.predual :=
  Finsupp.linearCombination ℚ K.predualCoordinate

lemma rationalPredual_val (f : Γ →₀ ℚ) :
    (K.rationalPredual f).val = ∑ a ∈ f.support, (f a : ℝ) • K.coordinate a := by
  simp only [rationalPredual, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [show (∑ a ∈ f.support, f a • K.predualCoordinate a).val =
      ∑ a ∈ f.support, (f a • K.predualCoordinate a).val from
    Submodule.coe_sum _ _ _]
  congr 1

lemma rationalPredual_eq_functional (f : K.carrier) :
    (K.rationalPredual f.val).val = K.functional f := by
  rw [K.rationalPredual_val, K.functional_eq_sum]

lemma norm_rationalPredual_le (f : Γ →₀ ℚ) (hf : f ∈ K.carrier) :
    ‖K.rationalPredual f‖ ≤ 1 := by
  change ‖(K.rationalPredual f).val‖ ≤ 1
  rw [K.rationalPredual_eq_functional ⟨f, hf⟩]
  exact K.norm_functional_le ⟨f, hf⟩

@[simp] lemma rationalPredual_single (a : Γ) (q : ℚ) :
    K.rationalPredual (Finsupp.single a q) = q • K.predualCoordinate a :=
  Finsupp.linearCombination_single _ _ _

lemma rationalPredual_apply (f : Γ →₀ ℚ) (x : K.Space) :
    (K.rationalPredual f).val x = ∑ a ∈ f.support, (f a : ℝ) * K.coordinate a x := by
  rw [K.rationalPredual_val]
  simp only [sum_apply, smul_apply, smul_eq_mul]

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction
open scoped Classical
universe u

lemma absConvex_abs_le {V : Type u} [AddCommGroup V] [Module ℚ V]
    (L : V →ₗ[ℚ] ℝ) (r : ℝ) (hr : 0 ≤ r) : AbsConvex ℚ {x | |L x| ≤ r} := by
  constructor
  · intro a ha
    rintro _ ⟨x, hx, rfl⟩
    change |L (a • x)| ≤ r
    rw [L.map_smul, Rat.smul_def, abs_mul, ← Real.norm_eq_abs (a : ℝ), Rat.norm_cast_real]
    calc
      _ ≤ ‖a‖ * r := mul_le_mul_of_nonneg_left hx (norm_nonneg a)
      _ ≤ r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha hr
  · intro x hx y hy a b ha hb hab
    change |L (a • x + b • y)| ≤ r
    have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
    have hab' : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
    calc
      _ = |(a : ℝ) * L x + (b : ℝ) * L y| := by
        simp only [L.map_add, L.map_smul, Rat.smul_def]
      _ ≤ |(a : ℝ) * L x| + |(b : ℝ) * L y| := abs_add_le _ _
      _ = (a : ℝ) * |L x| + (b : ℝ) * |L y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha', abs_of_nonneg hb']
      _ ≤ (a : ℝ) * r + (b : ℝ) * r := add_le_add
        (mul_le_mul_of_nonneg_left hx ha') (mul_le_mul_of_nonneg_left hy hb')
      _ = r := by rw [← add_mul, hab', one_mul]

end SeparableQuotient.NormConstruction

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)
@[reducible] local instance dualNormedGroup'' : NormedAddCommGroup (StrongDual ℝ K.Space) := inferInstance
@[reducible] local instance dualNormedSpace'' : NormedSpace ℝ (StrongDual ℝ K.Space) := inferInstance

/-- Evaluation of any rational array, not only chosen normers. -/
def evaluateArray (x : K.Space) : (Γ →₀ ℚ) →ₗ[ℚ] ℝ where
  toFun := fun f => (K.rationalPredual f).val x
  map_add' := by intro f g; simp
  map_smul' := by intro q f; simp

lemma evaluateArray_eq (x : K.Space) (f : Γ →₀ ℚ) :
    K.evaluateArray x f = ∑ a ∈ f.support, (f a : ℝ) * K.coordinate a x :=
  K.rationalPredual_apply f x

lemma evaluateArray_eq_functional (x : K.Space) (f : K.carrier) :
    K.evaluateArray x f.val = K.functional f x := by
  change (K.rationalPredual f).val x = _
  rw [K.rationalPredual_eq_functional f]

lemma norm_le_of_evaluateArray (x : K.Space) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ f ∈ K.carrier, |K.evaluateArray x f| ≤ r) : ‖x‖ ≤ r := by
  change ‖x.val‖ ≤ r
  apply lp.norm_le_of_forall_le hr
  intro f
  change ‖K.functional f x‖ ≤ r
  simpa only [K.evaluateArray_eq_functional x f, Real.norm_eq_abs] using h f.val f.property

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

lemma evaluateArray_filter_of_zero (x : K.Space) (A : Set Γ)
    (hx : ∀ a ∉ A, K.coordinate a x = 0) (f : Γ →₀ ℚ) :
    K.evaluateArray x (f.filter (· ∈ A)) = K.evaluateArray x f := by
  rw [K.evaluateArray_eq, K.evaluateArray_eq]
  simp only [Finsupp.support_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ A
  · simp [ha]
  · simp [ha, hx a ha]

lemma evaluateArray_projection (x : K.Space) (A : Set Γ) (hA : K.CropStable A)
    (f : Γ →₀ ℚ) :
    K.evaluateArray (K.projection A hA x) f = K.evaluateArray x (f.filter (· ∈ A)) := by
  rw [K.evaluateArray_eq, K.evaluateArray_eq]
  simp only [Finsupp.support_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  rw [K.coordinate_projection]
  by_cases ha : a ∈ A <;> simp [ha]

end SeparableQuotient.NormConstruction.NormingSet

end

end OAI
