import Mathlib
import OAI.Analysis.HardSphere.Kernels.FiniteKernelPi
import OAI.Analysis.HardSphere.Geometry.LocalCheck

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
open ProbabilityTheory

section AuxiliaryMarginals
variable {ι : Type*} [DecidableEq ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  {C : Type*} [Fintype C]
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

def auxiliaryChecks (x : ∀ i, X i) (c : C) : LocalCheck Z where
  support := (checks c).support
  nonempty := (checks c).nonempty
  arity := (checks c).arity
  pass := fun z ↦ (checks c).pass (fun i ↦ (x i, z i))
  measurable_pass := (by fun_prop : Measurable (fun z : ∀ i, Z i ↦ fun i ↦ (x i,z i)))
    (checks c).measurable_pass
  depends := by
    intro z w h
    apply (checks c).depends
    intro i hi
    exact Prod.ext rfl (h i hi)

omit [DecidableEq ι] [Fintype C] in
lemma auxiliary_checkWeight (s : Finset ι) (x : ∀ i, X i) (z : ∀ i, Z i) :
    checkWeight (auxiliaryChecks checks x) s z =
      checkWeight checks s (fun i ↦ (x i,z i)) := rfl

def auxiliaryDensity (s : Finset ι) (x : ∀ i, X i) (z : ∀ i, Z i) : ℝ≥0∞ :=
  checkNormalizer (auxiliaryChecks checks x) (fun i ↦ κ i (x i)) s z

lemma auxiliaryDensity_delete_le {s t : Finset ι} (hst : Disjoint s t)
    (x : ∀ i, X i) (z : ∀ i, Z i) :
    auxiliaryDensity checks κ (s ∪ t) x z ≤
      auxiliaryDensity checks κ s x z * ∏ i ∈ t, κ i (x i) Set.univ :=
  checkNormalizer_delete_le (auxiliaryChecks checks x) hst z

omit [Fintype C] [∀ i, IsFiniteKernel (κ i)] in
lemma auxiliaryDensity_depends (s : Finset ι) (z : ∀ i, Z i) :
    DependsOn (fun x ↦ auxiliaryDensity checks κ s x z) (s : Set ι) := by
  intro x y hxy
  have hμ : (fun i : s ↦ κ i (x i)) = (fun i : s ↦ κ i (y i)) := by
    funext i
    rw [hxy i i.property]
  change (∫⁻ u, checkWeight (auxiliaryChecks checks x) s
    (Function.updateFinset z s u) ∂Measure.pi (fun i : s ↦ κ i (x i))) = _
  rw [hμ]
  apply lintegral_congr
  intro u
  simp only [auxiliary_checkWeight]
  apply checkWeight_depends
  intro i hi
  exact Prod.ext (hxy i hi) rfl

lemma measurable_auxiliaryDensity (s : Finset ι) (z : ∀ i, Z i) :
    Measurable (fun x ↦ auxiliaryDensity checks κ s x z) := by
  let κ' (i : s) : Kernel (∀ j, X j) (Z i) :=
    (κ i).comap (fun x ↦ x i) (measurable_pi_apply (i : ι))
  let η := finiteKernelPi κ'
  have hm : Measurable (fun p : (∀ i, X i) × (∀ i : s, Z i) ↦
      checkWeight checks s (fun i ↦ (p.1 i, Function.updateFinset z s p.2 i))) := by
    apply (measurable_checkWeight checks s).comp
    exact Measurable.of_eval fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp ((measurable_updateFinset (x := z) (s := s)).comp
          measurable_snd))
  have h := hm.lintegral_kernel_prod_right' (κ := η)
  simpa only [η, finiteKernelPi_apply, κ', Kernel.comap_apply,
    auxiliaryDensity, checkNormalizer, lmarginal, auxiliary_checkWeight] using h

lemma auxiliaryDensity_integral (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)]
    (s : Finset ι) (x : ∀ i, X i) (z : ∀ i, Z i) :
    lmarginal μ s (fun y ↦ auxiliaryDensity checks κ s y z) x =
      checkNormalizer checks (fun i ↦ (μ i).compProd (κ i)) s (fun i ↦ (x i,z i)) := by
  let f (p : ∀ i : s, X i × Z i) :=
    checkWeight checks s (Function.updateFinset (fun i ↦ (x i,z i)) s p)
  have hf : Measurable f := (measurable_checkWeight checks s).comp measurable_updateFinset
  have hh := lintegral_pi_compProd (fun i : s ↦ κ i) (fun i : s ↦ μ i) hf
  change (∫⁻ y, auxiliaryDensity checks κ s (Function.updateFinset x s y) z
    ∂Measure.pi (fun i : s ↦ μ i)) = (∫⁻ p, f p ∂Measure.pi (fun i : s ↦ (μ i).compProd (κ i)))
  rw [hh]
  apply lintegral_congr
  intro y
  change (∫⁻ u, checkWeight (auxiliaryChecks checks (Function.updateFinset x s y)) s
    (Function.updateFinset z s u)
    ∂Measure.pi (fun i : s ↦ κ i (Function.updateFinset x s y i))) = _
  have hμ : (fun i : s ↦ κ i (Function.updateFinset x s y i)) = (fun i : s ↦ κ i (y i)) := by
    funext i
    simp [Function.updateFinset, i.property]
  rw [hμ]
  apply lintegral_congr
  intro u
  rw [auxiliary_checkWeight]
  apply checkWeight_depends
  intro i hi
  simp [Function.updateFinset, hi]

end AuxiliaryMarginals

section OverlapProducts
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]

def densityProduct (s : Finset ι) (g : ∀ i, X i → ℝ≥0∞) (x : ∀ i, X i) : ℝ≥0∞ :=
  ∏ i ∈ s, g i (x i)

omit [DecidableEq ι] in
lemma measurable_densityProduct (s : Finset ι) (g : ∀ i, X i → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) : Measurable (densityProduct s g) :=
  Finset.measurable_prod s fun i _ ↦ (hg i).comp (measurable_pi_apply i)

omit [DecidableEq ι] [∀ i, MeasurableSpace (X i)] in
lemma densityProduct_depends (s : Finset ι) (g : ∀ i, X i → ℝ≥0∞) :
    DependsOn (densityProduct s g) (s : Set ι) := by
  intro x y hxy
  exact Finset.prod_congr rfl fun i hi ↦ congrArg (g i) (hxy i hi)

omit [∀ i, MeasurableSpace (X i)] in
lemma densityProduct_union (s t : Finset ι) (g h : ∀ i, X i → ℝ≥0∞)
    (x : ∀ i, X i) :
    densityProduct s g x * densityProduct t h x =
      ∏ i ∈ s ∪ t, (if i ∈ s then g i (x i) else 1) *
        (if i ∈ t then h i (x i) else 1) := by
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
    simp only [Finset.filter_mem_eq_inter, Finset.union_inter_cancel_left, densityProduct]
  · rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
    simp only [Finset.filter_mem_eq_inter, Finset.union_inter_cancel_right, densityProduct]

lemma lmarginal_overlap_products {μ : ∀ i, Measure (X i)}
    [∀ i, IsProbabilityMeasure (μ i)] (s t : Finset ι)
    (g h : ∀ i, X i → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (hh : ∀ i, Measurable (h i)) {G : ℝ≥0∞}
    (hgb : ∀ i x, g i x ≤ G)
    (hgm : ∀ i, ∫⁻ x, g i x ∂μ i = 1)
    (hhm : ∀ i, ∫⁻ x, h i x ∂μ i = 1) (x : ∀ i, X i) :
    lmarginal μ (s ∪ t) (fun y ↦ densityProduct s g y * densityProduct t h y) x ≤
      G ^ (s ∩ t).card := by
  let f (i : ι) (y : X i) :=
    (if i ∈ s then g i y else 1) * (if i ∈ t then h i y else 1)
  have hf : ∀ i, Measurable (f i) := by
    intro i
    dsimp [f]
    split_ifs <;> fun_prop
  rw [show (fun y ↦ densityProduct s g y * densityProduct t h y) =
      (fun y ↦ ∏ i ∈ s ∪ t, f i (y i)) from funext (densityProduct_union s t g h)]
  rw [lmarginal_prod_coordinates f hf]
  have hi (i : ι) : (∫⁻ y, f i y ∂μ i) ≤ if i ∈ s ∩ t then G else 1 := by
    by_cases his : i ∈ s <;> by_cases hit : i ∈ t
    · simp only [f, his, hit, ite_true, Finset.mem_inter, and_self]
      calc
        (∫⁻ y, g i y * h i y ∂μ i) ≤ ∫⁻ y, G * h i y ∂μ i :=
          lintegral_mono fun y ↦ mul_le_mul_left (hgb i y) _
        _ = G := by rw [lintegral_const_mul _ (hh i), hhm, mul_one]
    all_goals simp [f, his, hit, hgm, hhm]
  calc
    (∏ i ∈ s ∪ t, ∫⁻ y, f i y ∂μ i) ≤
        ∏ i ∈ s ∪ t, if i ∈ s ∩ t then G else 1 :=
      Finset.prod_le_prod fun i _ ↦ hi i
    _ = G ^ (s ∩ t).card := by
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
      have heq : (s ∪ t).filter (fun i ↦ i ∈ s ∩ t) = s ∩ t := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
        tauto
      rw [heq, Finset.prod_const]

omit [∀ i, MeasurableSpace (X i)] in
lemma dependsOn_mul_union {s t : Finset ι} {f g : (∀ i, X i) → ℝ≥0∞}
    (hf : DependsOn f (s : Set ι)) (hg : DependsOn g (t : Set ι)) :
    DependsOn (fun x ↦ f x * g x) ((s ∪ t : Finset ι) : Set ι) := by
  intro x y hxy
  change f x * g x = f y * g y
  rw [hf (fun i hi ↦ hxy i (Finset.mem_union_left t hi)),
    hg (fun i hi ↦ hxy i (Finset.mem_union_right s hi))]

end OverlapProducts

section KernelOverlap
variable {ι : Type*} [DecidableEq ι] {X Z W : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  [∀ i, MeasurableSpace (W i)]
  {C D : Type*} [Fintype C] [Fintype D]
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (other : D → LocalCheck (fun i ↦ X i × W i))
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]
  (η : ∀ i, Kernel (X i) (W i)) [∀ i, IsFiniteKernel (η i)]

lemma auxiliaryDensity_overlap_bound
    {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    (fs ft cs ct : Finset ι)
    (hff : Disjoint fs ft) (hfn : Disjoint (fs ∪ ft) (cs ∪ ct))
    {G : ℝ≥0∞}
    (hκb : ∀ i x, κ i x Set.univ ≤ G)
    (hκm : ∀ i, ∫⁻ x, κ i x Set.univ ∂μ i = 1)
    (hηm : ∀ i, ∫⁻ x, η i x Set.univ ∂μ i = 1)
    (x : ∀ i, X i) (z : ∀ i, Z i) (w : ∀ i, W i) :
    lmarginal μ ((fs ∪ ft) ∪ (cs ∪ ct))
      (fun y ↦ auxiliaryDensity checks κ (fs ∪ cs) y z *
        auxiliaryDensity other η (ft ∪ ct) y w) x ≤
      (checkNormalizer checks (fun i ↦ (μ i).compProd (κ i)) fs (fun i ↦ (x i,z i)) *
       checkNormalizer other (fun i ↦ (μ i).compProd (η i)) ft (fun i ↦ (x i,w i))) *
       G ^ (cs ∩ ct).card := by
  let g (i : ι) (y : X i) := κ i y Set.univ
  let h (i : ι) (y : X i) := η i y Set.univ
  have hg : ∀ i, Measurable (g i) := fun i ↦ (κ i).measurable_coe MeasurableSet.univ
  have hh : ∀ i, Measurable (h i) := fun i ↦ (η i).measurable_coe MeasurableSet.univ
  have hfs : Disjoint fs cs := hfn.mono Finset.subset_union_left Finset.subset_union_left
  have hft : Disjoint ft ct := hfn.mono Finset.subset_union_right Finset.subset_union_right
  let F (y : ∀ i, X i) := auxiliaryDensity checks κ fs y z
  let H (y : ∀ i, X i) := auxiliaryDensity other η ft y w
  let P (y : ∀ i, X i) := densityProduct cs g y * densityProduct ct h y
  have hF : Measurable F := measurable_auxiliaryDensity checks κ fs z
  have hH : Measurable H := measurable_auxiliaryDensity other η ft w
  have hP : Measurable P := (measurable_densityProduct cs g hg).mul
    (measurable_densityProduct ct h hh)
  have hFd : DependsOn F (fs : Set ι) := auxiliaryDensity_depends checks κ fs z
  have hHd : DependsOn H (ft : Set ι) := auxiliaryDensity_depends other η ft w
  have hPd : DependsOn P ((cs ∪ ct : Finset ι) : Set ι) :=
    dependsOn_mul_union (densityProduct_depends cs g) (densityProduct_depends ct h)
  calc
    _ ≤ lmarginal μ ((fs ∪ ft) ∪ (cs ∪ ct)) (fun y ↦ (F y * H y) * P y) x := by
      apply lmarginal_mono _ x
      intro y
      calc
        _ ≤ (F y * densityProduct cs g y) * (H y * densityProduct ct h y) :=
          mul_le_mul' (auxiliaryDensity_delete_le checks κ hfs y z)
            (auxiliaryDensity_delete_le other η hft y w)
        _ = _ := by dsimp [P]; ac_rfl
    _ = (lmarginal μ fs F x * lmarginal μ ft H x) * lmarginal μ (cs ∪ ct) P x := by
      rw [lmarginal_mul_disjoint (f := fun y ↦ F y * H y) (g := P) hfn
        (hF.mul hH) hP (dependsOn_mul_union hFd hHd) hPd,
        lmarginal_mul_disjoint (f := F) (g := H) hff hF hH hFd hHd]
    _ ≤ (lmarginal μ fs F x * lmarginal μ ft H x) * G ^ (cs ∩ ct).card :=
      mul_le_mul_right (lmarginal_overlap_products cs ct g h hg hh hκb hκm hηm x) _
    _ = _ := by rw [auxiliaryDensity_integral, auxiliaryDensity_integral]

end KernelOverlap

section ConditionalNormalizers
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] {C : Type*} [Fintype C]
  (checks : C → LocalCheck X)

def UniformInsertionOn (μ : ∀ i, Measure (X i)) (a : ℝ≥0∞) (r : Finset ι) : Prop :=
  ∀ i ∈ r, ∀ (s : Finset ι), i ∉ s → ∀ x : ∀ j, X j,
    a ≤ ∫⁻ y, (insertionEvent checks s i).indicator (fun _ ↦ (1 : ℝ≥0∞))
      (Function.update x i y) ∂μ i

omit [Fintype C] in
lemma insertion_integral_lower_on {μ : ∀ i, Measure (X i)} {a : ℝ≥0∞}
    {r : Finset ι} (hcompat : UniformInsertionOn checks μ a r)
    {s : Finset ι} {i : ι} (hir : i ∈ r) (hi : i ∉ s) (x : ∀ i, X i) :
    a * checkWeight checks s x ≤
      ∫⁻ y, checkWeight checks (insert i s) (Function.update x i y) ∂μ i := by
  classical
  by_cases hx : x ∈ retainedEvent checks s
  · have heq : (fun y ↦ checkWeight checks (insert i s) (Function.update x i y)) =
        fun y ↦ (insertionEvent checks s i).indicator (fun _ ↦ (1 : ℝ≥0∞))
          (Function.update x i y) := by
      funext y
      have hu := (retainedEvent_update checks hi x y).2 hx
      simp [checkWeight, retainedEvent_insert, Set.indicator_apply, hu]
    rw [heq]
    simpa [checkWeight, hx] using hcompat i hir s hi x
  · simp [checkWeight, hx]

def partialNormalizer (μ : ∀ i, Measure (X i)) (s o : Finset ι)
    (x : ∀ i, X i) : ℝ≥0∞ := lmarginal μ s (checkWeight checks (s ∪ o)) x

lemma partialNormalizer_insert_lower {μ : ∀ i, Measure (X i)}
    [∀ i, SigmaFinite (μ i)] {a : ℝ≥0∞} {r : Finset ι}
    (hcompat : UniformInsertionOn checks μ a r) {s o : Finset ι} {i : ι}
    (hir : i ∈ r) (hi : i ∉ s ∪ o) (x : ∀ i, X i) :
    a * partialNormalizer checks μ s o x ≤
      partialNormalizer checks μ (insert i s) o x := by
  have his : i ∉ s := fun h ↦ hi (Finset.mem_union_left o h)
  rw [partialNormalizer, partialNormalizer, Finset.insert_union,
    lmarginal_insert' _ (measurable_checkWeight checks _) his]
  calc
    a * lmarginal μ s (checkWeight checks (s ∪ o)) x =
        lmarginal μ s (fun x ↦ a * checkWeight checks (s ∪ o) x) x := by
      dsimp [lmarginal]
      exact (lintegral_const_mul a ((measurable_checkWeight checks (s ∪ o)).comp
        (measurable_updateFinset (x := x) (s := s)))).symm
    _ ≤ _ := lmarginal_mono (insertion_integral_lower_on checks hcompat hir hi) x

lemma partialNormalizer_union_lower {μ : ∀ i, Measure (X i)}
    [∀ i, SigmaFinite (μ i)] {a : ℝ≥0∞} {r : Finset ι}
    (hcompat : UniformInsertionOn checks μ a r)
    (s t o : Finset ι) (htr : t ⊆ r) (hto : Disjoint (s ∪ o) t)
    (x : ∀ i, X i) :
    a ^ t.card * partialNormalizer checks μ s o x ≤
      partialNormalizer checks μ (s ∪ t) o x := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hit ih =>
    have hino : i ∉ s ∪ o := (Finset.disjoint_insert_right.mp hto).1
    have hto' := (Finset.disjoint_insert_right.mp hto).2
    have hiu : i ∉ (s ∪ t) ∪ o := by
      simp only [Finset.mem_union, not_or] at hino ⊢
      exact ⟨⟨hino.1, hit⟩, hino.2⟩
    calc
      a ^ (insert i t).card * partialNormalizer checks μ s o x =
          a * (a ^ t.card * partialNormalizer checks μ s o x) := by
        rw [Finset.card_insert_of_notMem hit, pow_succ]
        ac_rfl
      _ ≤ a * partialNormalizer checks μ (s ∪ t) o x :=
        mul_le_mul_right (ih ((Finset.subset_insert _ _).trans htr) hto') a
      _ ≤ partialNormalizer checks μ (insert i (s ∪ t)) o x :=
        partialNormalizer_insert_lower checks hcompat (htr (Finset.mem_insert_self _ _)) hiu x
      _ = _ := by rw [Finset.union_insert]

lemma partialNormalizer_pos {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} (ha : 0 < a) {s o : Finset ι}
    (hcompat : UniformInsertionOn checks μ a s) (hso : Disjoint s o)
    (x : ∀ i, X i) (hx : x ∈ retainedEvent checks o) :
    0 < partialNormalizer checks μ s o x := by
  have h := partialNormalizer_union_lower checks hcompat ∅ s o (Finset.Subset.refl s)
    (by simpa using hso.symm) x
  simp only [partialNormalizer, Finset.empty_union, lmarginal_empty, checkWeight,
    Set.indicator_of_mem hx, mul_one] at h
  exact lt_of_lt_of_le (by positivity) h

lemma partialNormalizer_far_eq {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {s o : Finset ι} (hso : Disjoint s o) (hsep : SeparatedChecks checks s o)
    (x : ∀ i, X i) :
    partialNormalizer checks μ s o x = checkNormalizer checks μ s x * checkWeight checks o x := by
  rw [partialNormalizer]
  have heq : checkWeight checks (s ∪ o) = fun y ↦ checkWeight checks s y * checkWeight checks o y :=
    funext (checkWeight_union checks hsep)
  rw [heq]
  change (∫⁻ y, checkWeight checks s (Function.updateFinset x s y) *
    checkWeight checks o (Function.updateFinset x s y) ∂Measure.pi (fun i : s ↦ μ i)) = _
  have hu : ∀ y : ∀ i : s, X i,
      checkWeight checks o (Function.updateFinset x s y) = checkWeight checks o x := by
    intro y
    apply checkWeight_depends
    intro i hi
    have his : i ∉ s := Finset.disjoint_right.mp hso hi
    simp [Function.updateFinset, his]
  simp_rw [hu]
  exact lintegral_mul_const _ ((measurable_checkWeight checks s).comp
    (measurable_updateFinset (x := x) (s := s)))

lemma partialNormalizer_le_far {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    {s t o : Finset ι} (hst : Disjoint s t) (x : ∀ i, X i) :
    partialNormalizer checks μ (s ∪ t) o x ≤ checkNormalizer checks μ s x := by
  calc
    _ ≤ lmarginal μ (s ∪ t) (checkWeight checks s) x :=
      lmarginal_mono (checkWeight_antitone checks
        (Finset.subset_union_left.trans Finset.subset_union_left)) x
    _ = _ := by
      rw [lmarginal_union' μ _ (measurable_checkWeight checks s) hst]
      change (∫⁻ y, checkNormalizer checks μ s (Function.updateFinset x t y)
        ∂Measure.pi (fun i : t ↦ μ i)) = _
      simp_rw [checkNormalizer_const checks s _ x]
      simp

end ConditionalNormalizers

variable {ι : Type*} [DecidableEq ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  {C : Type*} [Fintype C]
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

def conditionalDensity (s o : Finset ι) (x : ∀ i, X i) (z : ∀ i, Z i) : ℝ≥0∞ :=
  lmarginal (fun i ↦ κ i (x i)) s
    (fun v ↦ checkWeight checks (s ∪ o) (fun i ↦ (x i,v i))) z

omit [Fintype C] [∀ i, IsFiniteKernel (κ i)] in
lemma conditionalDensity_le_auxiliaryDensity (s o : Finset ι)
    (x : ∀ i, X i) (z : ∀ i, Z i) :
    conditionalDensity checks κ s o x z ≤ auxiliaryDensity checks κ s x z :=
  lmarginal_mono (fun v ↦ checkWeight_antitone checks Finset.subset_union_left
    (fun i ↦ (x i,v i))) z

lemma measurable_conditionalDensity (s o : Finset ι) (z : ∀ i, Z i) :
    Measurable (fun x ↦ conditionalDensity checks κ s o x z) := by
  let κ' (i : s) : Kernel (∀ j, X j) (Z i) :=
    (κ i).comap (fun x ↦ x i) (measurable_pi_apply (i : ι))
  let η := finiteKernelPi κ'
  have hm : Measurable (fun p : (∀ i, X i) × (∀ i : s, Z i) ↦
      checkWeight checks (s ∪ o) (fun i ↦ (p.1 i, Function.updateFinset z s p.2 i))) := by
    apply (measurable_checkWeight checks (s ∪ o)).comp
    exact Measurable.of_eval fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp ((measurable_updateFinset (x := z) (s := s)).comp
          measurable_snd))
  have h := hm.lintegral_kernel_prod_right' (κ := η)
  simpa only [η, finiteKernelPi_apply, κ', Kernel.comap_apply,
    conditionalDensity, lmarginal] using h

lemma conditionalDensity_integral (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)]
    (s o : Finset ι) (x : ∀ i, X i) (z : ∀ i, Z i) :
    lmarginal μ s (fun y ↦ conditionalDensity checks κ s o y z) x =
      partialNormalizer checks (fun i ↦ (μ i).compProd (κ i)) s o (fun i ↦ (x i,z i)) := by
  let f (p : ∀ i : s, X i × Z i) :=
    checkWeight checks (s ∪ o) (Function.updateFinset (fun i ↦ (x i,z i)) s p)
  have hf : Measurable f := (measurable_checkWeight checks (s ∪ o)).comp measurable_updateFinset
  have hh := lintegral_pi_compProd (fun i : s ↦ κ i) (fun i : s ↦ μ i) hf
  change (∫⁻ y, conditionalDensity checks κ s o (Function.updateFinset x s y) z
    ∂Measure.pi (fun i : s ↦ μ i)) = (∫⁻ p, f p ∂Measure.pi (fun i : s ↦ (μ i).compProd (κ i)))
  rw [hh]
  apply lintegral_congr
  intro y
  change (∫⁻ u, checkWeight checks (s ∪ o)
    (fun i ↦ (Function.updateFinset x s y i, Function.updateFinset z s u i))
    ∂Measure.pi (fun i : s ↦ κ i (Function.updateFinset x s y i))) = _
  have hμ : (fun i : s ↦ κ i (Function.updateFinset x s y i)) = (fun i : s ↦ κ i (y i)) := by
    funext i
    simp [Function.updateFinset, i.property]
  rw [hμ]
  apply lintegral_congr
  intro u
  apply congrArg (checkWeight checks (s ∪ o))
  funext i
  by_cases hi : i ∈ s <;> simp [Function.updateFinset, hi]

end HardSphere.Comparison
end

end OAI
