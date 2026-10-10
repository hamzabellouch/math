import OAI.Analysis.SeparableQuotients.ColorDecomposition

namespace OAI

noncomputable section

/- The completion of c₀₀ under a bounded rational norming set. -/
namespace SeparableQuotient.NormConstruction
open scoped Topology ENNReal
open Filter
universe u
variable {Γ : Type u}

structure NormingSet (Γ : Type u) where
  carrier : Set (Γ →₀ ℚ)
  coordinate_mem : ∀ a, Finsupp.single a 1 ∈ carrier
  coefficient_bound : ∀ f ∈ carrier, ∀ a, |(f a : ℝ)| ≤ 1

namespace NormingSet
variable (K : NormingSet Γ)
abbrev BoundedSpace := lp (fun _ : K.carrier => ℝ) ⊤

def coordinateVector (a : Γ) : K.BoundedSpace :=
  ⟨fun f => (f.val a : ℝ), memℓp_infty ⟨1, by
    rintro _ ⟨f, rfl⟩
    exact K.coefficient_bound f.val f.property a⟩⟩

@[simp] lemma coordinateVector_apply (a : Γ) (f : K.carrier) :
    K.coordinateVector a f = (f.val a : ℝ) := rfl

lemma norm_coordinateVector_le (a : Γ) : ‖K.coordinateVector a‖ ≤ 1 :=
  lp.norm_le_of_forall_le (by norm_num) fun f => K.coefficient_bound _ f.property a

lemma norm_coordinateVector (a : Γ) : ‖K.coordinateVector a‖ = 1 := by
  apply le_antisymm (K.norm_coordinateVector_le a)
  simpa [coordinateVector] using lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0)
    (K.coordinateVector a) ⟨Finsupp.single a 1, K.coordinate_mem a⟩

/-- Algebraic inclusion of the prescribed finitely supported vectors. -/
def finiteMap : (Γ →₀ ℝ) →ₗ[ℝ] K.BoundedSpace :=
  Finsupp.linearCombination ℝ K.coordinateVector

@[simp] lemma finiteMap_single (a : Γ) (t : ℝ) :
    K.finiteMap (Finsupp.single a t) = t • K.coordinateVector a :=
  Finsupp.linearCombination_single _ _ _

lemma finiteMap_apply (x : Γ →₀ ℝ) (f : K.carrier) :
    K.finiteMap x f = x.sum (fun a t => t * (f.val a : ℝ)) := by
  change (lp.evalₗ (𝕜 := ℝ) (fun _ : K.carrier => ℝ) ⊤ f) (K.finiteMap x) = _
  simp only [finiteMap, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    map_smul, lp.evalₗ_apply, K.coordinateVector_apply, smul_eq_mul]

@[simp] lemma finiteMap_coordinate (x : Γ →₀ ℝ) (a : Γ) :
    K.finiteMap x ⟨Finsupp.single a 1, K.coordinate_mem a⟩ = x a := by
  classical
  rw [K.finiteMap_apply]
  simp [Finsupp.sum, Finsupp.single_apply, apply_ite, eq_comm]

lemma finiteMap_injective : Function.Injective K.finiteMap := by
  intro x y h
  ext a
  simpa only [K.finiteMap_coordinate] using
    congrArg (fun z : K.BoundedSpace => z ⟨Finsupp.single a 1, K.coordinate_mem a⟩) h

lemma norm_finiteMap_le_l1 (x : Γ →₀ ℝ) :
    ‖K.finiteMap x‖ ≤ x.sum (fun _ t => |t|) := by
  classical
  calc
    ‖K.finiteMap x‖ = ‖∑ a ∈ x.support, x a • K.coordinateVector a‖ := rfl
    _ ≤ ∑ a ∈ x.support, ‖x a • K.coordinateVector a‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul, K.norm_coordinateVector, mul_one, Real.norm_eq_abs,
      Finsupp.sum]

/-- The concrete Banach completion. Its norm is literally the supremum of
absolute evaluations over K. -/
def closedSpan : Submodule ℝ K.BoundedSpace := K.finiteMap.range.topologicalClosure
abbrev Space := K.closedSpan

instance : CompleteSpace K.Space := by
  let : IsClosed (K.closedSpan : Set K.BoundedSpace) :=
    Submodule.isClosed_topologicalClosure _
  exact IsClosed.completeSpace_coe

def includeFinite : (Γ →₀ ℝ) →ₗ[ℝ] K.Space :=
  K.finiteMap.codRestrict K.closedSpan (fun x =>
    Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

@[simp] lemma includeFinite_val (x : Γ →₀ ℝ) :
    (K.includeFinite x).val = K.finiteMap x := rfl

lemma denseRange_includeFinite : DenseRange K.includeFinite := by
  have hd : DenseRange (Set.inclusion (show (K.finiteMap.range : Set K.BoundedSpace) ⊆
      K.closedSpan from Submodule.le_topologicalClosure _)) :=
    (denseRange_inclusion_iff _).mpr (by intro x hx; exact hx)
  exact hd.comp (show Function.Surjective K.finiteMap.rangeRestrict from fun ⟨y, x, hx⟩ =>
      ⟨x, Subtype.ext hx⟩).denseRange
    (continuous_inclusion _)

def functional (f : K.carrier) : K.Space →L[ℝ] ℝ :=
  (lp.evalCLM ℝ (fun _ : K.carrier => ℝ) ⊤ f).comp K.closedSpan.subtypeL

def coordinate (a : Γ) : K.Space →L[ℝ] ℝ :=
  K.functional ⟨Finsupp.single a 1, K.coordinate_mem a⟩

@[simp] lemma functional_includeFinite (f : K.carrier) (x : Γ →₀ ℝ) :
    K.functional f (K.includeFinite x) = x.sum (fun a t => t * (f.val a : ℝ)) :=
  K.finiteMap_apply x f

@[simp] lemma coordinate_includeFinite (a : Γ) (x : Γ →₀ ℝ) :
    K.coordinate a (K.includeFinite x) = x a := K.finiteMap_coordinate x a

def generator (a : Γ) : K.Space := K.includeFinite (Finsupp.single a 1)

@[simp] lemma norm_generator (a : Γ) : ‖K.generator a‖ = 1 := by
  change ‖K.finiteMap (Finsupp.single a 1)‖ = 1
  simp [K.norm_coordinateVector]

lemma functional_bound (f : K.carrier) (x : K.Space) : |K.functional f x| ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) x.val f

lemma norm_functional_le (f : K.carrier) : ‖K.functional f‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa [Real.norm_eq_abs] using K.functional_bound f x

lemma coordinate_bound (a : Γ) (x : K.Space) : |K.coordinate a x| ≤ ‖x‖ :=
  K.functional_bound _ x

lemma norm_eq_sup (x : K.Space) : ‖x‖ = ⨆ f : K.carrier, |K.functional f x| :=
  lp.norm_eq_ciSup x.val

lemma approximating_sequence (x : K.Space) :
    ∃ v : ℕ → Γ →₀ ℝ, Tendsto (fun n => K.includeFinite (v n)) atTop (𝓝 x) := by
  have hx := K.denseRange_includeFinite x
  obtain ⟨v, hv, ht⟩ := mem_closure_iff_seq_limit.mp hx
  choose w hw using hv
  exact ⟨w, by simpa only [hw] using ht⟩

/-- Every completed vector has countable coordinate support. -/
lemma support_countable (x : K.Space) : Set.Countable {a | K.coordinate a x ≠ 0} := by
  obtain ⟨v, hv⟩ := K.approximating_sequence x
  have hc : Set.Countable (⋃ n, ((v n).support : Set Γ)) :=
    Set.countable_iUnion (fun n => (v n).support.countable_toSet)
  apply hc.mono
  intro a ha
  by_contra h
  have hz : ∀ n, v n a = 0 := by
    intro n
    by_contra hn
    exact h (Set.mem_iUnion.mpr ⟨n, Finsupp.mem_support_iff.mpr hn⟩)
  have ht := (K.coordinate a).continuous.tendsto x |>.comp hv
  have ht0 : Tendsto (fun n => K.coordinate a (K.includeFinite (v n))) atTop (𝓝 0) := by
    simpa only [K.coordinate_includeFinite, hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact ha (tendsto_nhds_unique ht ht0)

/-- Every norming functional is its finite coordinate combination even after
completion; hence no nonzero completed vector can vanish at every coordinate. -/
lemma functional_eq_sum (f : K.carrier) :
    K.functional f = ∑ a ∈ f.val.support, (f.val a : ℝ) • K.coordinate a := by
  classical
  let g : K.Space →L[ℝ] ℝ := ∑ a ∈ f.val.support, (f.val a : ℝ) • K.coordinate a
  have hlin : (K.functional f).toLinearMap.comp K.includeFinite =
      g.toLinearMap.comp K.includeFinite := by
    apply Finsupp.lhom_ext
    intro a t
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      K.functional_includeFinite, Finsupp.sum_single_index, zero_mul]
    change t * (f.val a : ℝ) = (∑ b ∈ f.val.support,
      (f.val b : ℝ) • K.coordinate b) (K.includeFinite (Finsupp.single a t))
    simp only [sum_apply, smul_apply,
      K.coordinate_includeFinite, Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · simp [mul_comm]
    · intro b _ hab
      simp [Ne.symm hab]
    · intro ha
      have hz : f.val a = 0 := by simpa using (not_congr Finsupp.mem_support_iff).mp ha
      simp [hz]
  apply DFunLike.coe_injective
  apply K.denseRange_includeFinite.equalizer (K.functional f).continuous g.continuous
  funext x
  exact LinearMap.congr_fun hlin x

lemma coordinates_separate (x : K.Space) (h : ∀ a, K.coordinate a x = 0) : x = 0 := by
  apply Subtype.ext
  apply lp.ext
  funext f
  change K.functional f x = 0
  rw [K.functional_eq_sum]
  simp [h]

lemma coordinate_ext {x y : K.Space} (h : ∀ a, K.coordinate a x = K.coordinate a y) : x = y := by
  apply sub_eq_zero.mp
  apply K.coordinates_separate
  intro a
  rw [(K.coordinate a).map_sub x y, h a, sub_self]

end NormingSet
end SeparableQuotient.NormConstruction

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology ENNReal Classical
open Filter
universe u
variable {Γ : Type u} (K : NormingSet Γ)

/-- Stability of a norming set under the specified coordinate crop. -/
def CropStable (A : Set Γ) : Prop := ∀ f ∈ K.carrier, f.filter (· ∈ A) ∈ K.carrier

variable (A : Set Γ) (hA : K.CropStable A)

def cropNormer (f : K.carrier) : K.carrier := ⟨f.val.filter (· ∈ A), hA _ f.property⟩

def cropAmbient : K.BoundedSpace →L[ℝ] K.BoundedSpace :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun f => x (K.cropNormer A hA f), memℓp_infty ⟨‖x‖, by
        rintro _ ⟨f, rfl⟩
        exact lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) x _⟩⟩
      map_add' := fun x y => by apply lp.ext; rfl
      map_smul' := fun c x => by apply lp.ext; rfl }
    1 (fun x => by
      simpa only [one_mul] using lp.norm_le_of_forall_le (norm_nonneg x)
        (fun f => lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) x
          (K.cropNormer A hA f)))

@[simp] lemma cropAmbient_apply (x : K.BoundedSpace) (f : K.carrier) :
    K.cropAmbient A hA x f = x (K.cropNormer A hA f) := rfl

lemma cropAmbient_finiteMap (x : Γ →₀ ℝ) :
    K.cropAmbient A hA (K.finiteMap x) = K.finiteMap (x.filter (· ∈ A)) := by
  apply lp.ext
  funext f
  rw [K.cropAmbient_apply, K.finiteMap_apply, K.finiteMap_apply]
  simp only [cropNormer, Finsupp.filter_apply, apply_ite, Rat.cast_zero,
    mul_zero]
  rw [Finsupp.sum_filter_index]
  simp only [Finsupp.sum, Finsupp.support_filter, Finset.sum_filter]

lemma cropAmbient_mem (x : K.Space) : K.cropAmbient A hA x.val ∈ K.closedSpan := by
  have hi : K.finiteMap.range ∈ Module.End.invtSubmodule (K.cropAmbient A hA) := by
    rw [Module.End.mem_invtSubmodule_iff_map_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v.filter (· ∈ A), (K.cropAmbient_finiteMap A hA v).symm⟩
  have hc := Submodule.topologicalClosure_mem_invtSubmodule hi
  rw [Module.End.mem_invtSubmodule_iff_map_le] at hc
  exact hc ⟨x.val, x.property, rfl⟩

/-- Contractive interval/rectangle projection on the actual Banach completion. -/
def projection : K.Space →L[ℝ] K.Space :=
  ((K.cropAmbient A hA).comp K.closedSpan.subtypeL).codRestrict K.closedSpan
    (K.cropAmbient_mem A hA)

lemma norm_projection_le : ‖K.projection A hA‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖K.cropAmbient A hA x.val‖ ≤ 1 * ‖x.val‖
  rw [one_mul]
  exact lp.norm_le_of_forall_le (norm_nonneg x.val)
    (fun f => lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) x.val
      (K.cropNormer A hA f))

@[simp] lemma projection_includeFinite (x : Γ →₀ ℝ) :
    K.projection A hA (K.includeFinite x) = K.includeFinite (x.filter (· ∈ A)) :=
  Subtype.ext (K.cropAmbient_finiteMap A hA x)

lemma coordinate_projection (a : Γ) (x : K.Space) :
    K.coordinate a (K.projection A hA x) = if a ∈ A then K.coordinate a x else 0 := by
  have h : (K.coordinate a).comp (K.projection A hA) =
      if a ∈ A then K.coordinate a else 0 := by
    apply DFunLike.coe_injective
    apply K.denseRange_includeFinite.equalizer
      ((K.coordinate a).comp (K.projection A hA)).continuous
      (if a ∈ A then K.coordinate a else (0 : K.Space →L[ℝ] ℝ)).continuous
    funext v
    by_cases ha : a ∈ A <;> simp [ha]
  by_cases ha : a ∈ A <;> simpa [ha] using DFunLike.congr_fun h x

lemma projection_idempotent (x : K.Space) :
    K.projection A hA (K.projection A hA x) = K.projection A hA x := by
  apply K.coordinate_ext
  intro a
  simp only [K.coordinate_projection]
  split_ifs <;> rfl

end SeparableQuotient.NormConstruction.NormingSet

end

end OAI
