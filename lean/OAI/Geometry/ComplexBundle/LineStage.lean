import OAI.Geometry.ComplexBundle.Maps
import OAI.Geometry.ComplexBundle.SmoothLine
import OAI.Geometry.ComplexBundle.Tuples

namespace OAI

noncomputable section

/-! Doubling stages of line bundles and their Hilbert direct sums. -/

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

section Continuity
variable {B U V : Type*} [TopologicalSpace B]
    [NormedAddCommGroup U] [NormedAddCommGroup V] [NormedSpace ℂ V]
    {E F : B → Type*}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace U E)] [TopologicalSpace (TotalSpace V F)]
    [FiberBundle U E]
    [FiberBundle V F] [VectorBundle ℂ V F]

theorem continuous_twoScaled (T₀ T₁ : ∀ x, E x →ₗ[ℂ] F x)
    (h₀ : Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj (T₀ z.proj z.2)))
    (h₁ : Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj (T₁ z.proj z.2)))
    (c : ℂ) (i : Fin 24) :
    Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj
      (twoOfTwentyFour (c • T₀ z.proj) (c • T₁ z.proj) i z.2)) := by
  have hs (d : ℂ) (T : ∀ x, E x →ₗ[ℂ] F x)
      (hT : Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj (T z.proj z.2))) :
      Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj (d • T z.proj z.2)) :=
    continuousOn_univ.mp (continuousOn_bundle_smul_over (fun z : TotalSpace U E => z.proj)
      (FiberBundle.continuous_proj U E).continuousOn (fun _ => d)
      (fun z => T z.proj z.2) continuousOn_const hT.continuousOn)
  by_cases h : i=0
  · simpa [twoOfTwentyFour,h] using hs c T₀ h₀
  · by_cases h' : i=1
    · simpa [twoOfTwentyFour,h,h'] using hs c T₁ h₁
    · simpa [twoOfTwentyFour,h,h'] using hs 0 T₀ h₀
end Continuity

def lineSumDoublingStep {ι S : Type*} [Fintype ι] [Fintype S]
    (K : ι → ℕ) (label : S → Option ι) :
    ContinuousNormalizedStep (EuclideanSpace ℂ S) (EuclideanSpace ℂ (S⊕S))
      (SmoothLineSumBundle K label) (SmoothLineSumBundle K (Sum.elim label label)) := by
  let L := fun u : S⊕S => productLineCore K (Sum.elim label label u)
  exact
    { tuple := fun x => doublingTuple (lineSumInl L x) (lineSumInr L x)
        (lineSumFst L x) (lineSumSnd L x)
        (lineSumFst_inner L x) (lineSumSnd_inner L x)
        (lineSumFst_comp_inl L x) (lineSumSnd_comp_inr L x) (lineSum_inl_fst_add_inr_snd L x)
      continuous_forward := continuous_twoScaled (lineSumInl L) (lineSumInr L)
        (continuous_lineSumInl L) (continuous_lineSumInr L) doublingScale
      continuous_reverse := continuous_twoScaled (lineSumFst L) (lineSumSnd L)
        (continuous_lineSumFst L) (continuous_lineSumSnd L) doublingScale }

/-- A finite list of actual projective-product line bundles. -/
structure LineStage {ι : Type*} (K : ι → ℕ) where
  Slot : Type
  finiteSlot : Fintype Slot
  label : Slot → Option ι

attribute [instance] LineStage.finiteSlot

namespace LineStage
variable {ι : Type*} [Fintype ι] {K : ι → ℕ}

abbrev Model (a : LineStage K) := EuclideanSpace ℂ a.Slot
abbrev Fiber (a : LineStage K) := SmoothLineSumBundle K a.label

abbrev Step (a b : LineStage K) := ContinuousNormalizedStep a.Model b.Model a.Fiber b.Fiber

def double (a : LineStage K) : LineStage K :=
  ⟨a.Slot⊕a.Slot,inferInstance,Sum.elim a.label a.label⟩

def doublingStep (a : LineStage K) : a.Step a.double := lineSumDoublingStep K a.label

def tail (a : LineStage K) : ℕ → LineStage K
  | 0 => a
  | n+1 => (tail a n).double

def tailStep (a : LineStage K) (n : ℕ) : (a.tail n).Step (a.tail (n+1)) :=
  (a.tail n).doublingStep

omit [Fintype ι] in
theorem double_card (a : LineStage K) : Fintype.card a.double.Slot = 2*Fintype.card a.Slot := by
  change Fintype.card (a.Slot⊕a.Slot)=_
  rw [Fintype.card_sum]
  omega

omit [Fintype ι] in
theorem tail_card (a : LineStage K) (n : ℕ) : Fintype.card (a.tail n).Slot = 2^n*Fintype.card a.Slot := by
  induction n with
  | zero =>
    change Fintype.card a.Slot = 2 ^ 0 * Fintype.card a.Slot
    simp only [pow_zero, one_mul]
  | succ n ih =>
    rw [tail,double_card,ih,pow_succ]
    ring

end LineStage
end Kaplansky

end

namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} [Fintype ι] {K : ι → ℕ}

/-- The actual stage fibers have their finite-dimensional Hilbert-space
instances directly from the finite orthogonal sum model. -/
instance lineStage_finite (a : LineStage K) (y : ProjectiveProduct K) :
    FiniteDimensional ℂ (a.Fiber y) :=
  inferInstanceAs (FiniteDimensional ℂ (EuclideanSpace ℂ a.Slot))
instance lineStage_complete (a : LineStage K) (y : ProjectiveProduct K) :
    CompleteSpace (a.Fiber y) :=
  inferInstanceAs (CompleteSpace (EuclideanSpace ℂ a.Slot))

end Kaplansky

section
open Bundle Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Kaplansky
open ComplexGrassmann
namespace LineStage
variable {ι : Type*} {J : Type} [Fintype J] {K : ι → ℕ}

def sum (a : J → LineStage K) : LineStage K :=
  ⟨Σ j : J, (a j).Slot, inferInstance, fun (s : Σ j : J, (a j).Slot) => (a s.1).label s.2⟩

def sumProj (a : J → LineStage K) (j : J) (y : ProjectiveProduct K) :
    (sum a).Fiber y →ₗ[ℂ] (a j).Fiber y where
  toFun v := WithLp.toLp 2 (fun s => (show (sum a).Model from v) ⟨j,s⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem continuous_sumProj (a : J → LineStage K) (j : J) :
    Continuous (fun z : TotalSpace (sum a).Model (sum a).Fiber =>
      TotalSpace.mk' (a j).Model z.proj (sumProj a j z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  exact ⟨FiberBundle.continuous_proj _ _, fun s => continuous_finiteLineSumComponent (fun (t : Σ j : J, (a j).Slot) => productLineCore K ((a t.1).label t.2)) ⟨j,s⟩⟩

def sumInj (a : J → LineStage K) (j : J) (y : ProjectiveProduct K) :
    (a j).Fiber y →ₗ[ℂ] (sum a).Fiber y where
  toFun v := WithLp.toLp 2 (fun s => if h : s.1 = j then
    (show (a j).Model from v) (h ▸ s.2) else 0)
  map_add' v w := by
    apply (EuclideanSpace.equiv _ ℂ).injective
    funext s
    change (if h : s.1=j then (show (a j).Model from v) (h ▸ s.2) +
      (show (a j).Model from w) (h ▸ s.2) else 0) =
      (if h : s.1=j then (show (a j).Model from v) (h ▸ s.2) else 0) +
      (if h : s.1=j then (show (a j).Model from w) (h ▸ s.2) else 0)
    by_cases h : s.1=j <;> simp [h]
  map_smul' c v := by
    apply (EuclideanSpace.equiv _ ℂ).injective
    funext s
    change (if h : s.1=j then c • (show (a j).Model from v) (h ▸ s.2) else 0) =
      c • (if h : s.1=j then (show (a j).Model from v) (h ▸ s.2) else 0)
    by_cases h : s.1=j <;> simp [h]

theorem continuous_sumInj (a : J → LineStage K) (j : J) :
    Continuous (fun z : TotalSpace (a j).Model (a j).Fiber =>
      TotalSpace.mk' (sum a).Model z.proj (sumInj a j z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  refine ⟨FiberBundle.continuous_proj _ _, ?_⟩
  rintro ⟨k,s⟩
  by_cases h : k=j
  · subst k
    have hc : Continuous (fun z : TotalSpace (a j).Model (a j).Fiber =>
        TotalSpace.mk' ℂ (E := (productLineCore K ((a j).label s)).Fiber)
          z.proj ((show (a j).Model from z.2) s)) :=
      continuous_finiteLineSumComponent (fun t => productLineCore K ((a j).label t)) s
    apply hc.congr
    intro z
    apply congrArg (TotalSpace.mk' ℂ z.proj)
    let v : (a j).Model := z.2
    change @Eq ℂ (v s) (if h : j = j then v (h ▸ s) else 0)
    symm
    exact dite_eq_left rfl
  · have hc : Continuous (fun z : TotalSpace (a j).Model (a j).Fiber =>
        TotalSpace.mk' ℂ (E := (productLineCore K ((a k).label s)).Fiber) z.proj 0) :=
      (Trivialization.continuous_zeroSection ℂ (F := ℂ) (E := (productLineCore K ((a k).label s)).Fiber)).comp
        (FiberBundle.continuous_proj _ _)
    apply hc.congr
    intro z
    apply congrArg (TotalSpace.mk' ℂ z.proj)
    let v : (a j).Model := z.2
    change @Eq ℂ 0 (if h : k = j then v (h ▸ s) else 0)
    symm
    exact dite_eq_right h

@[simp] theorem sumProj_sumInj_same (a : J → LineStage K) (j : J)
    (y : ProjectiveProduct K) (v : (a j).Fiber y) :
    sumProj a j y (sumInj a j y v) = v := by
  apply (EuclideanSpace.equiv _ ℂ).injective
  funext s
  change (if h : j = j then (show (a j).Model from v) (h ▸ s) else 0) =
    (show (a j).Model from v) s
  exact dite_eq_left rfl

@[simp] theorem sumProj_sumInj_ne (a : J → LineStage K) {j k : J} (h : k≠j)
    (y : ProjectiveProduct K) (v : (a j).Fiber y) :
    sumProj a k y (sumInj a j y v) = 0 := by
  apply (EuclideanSpace.equiv _ ℂ).injective
  funext s
  change (if h : k = j then (show (a j).Model from v) (h ▸ s) else 0) = 0
  exact dite_eq_right h

theorem sumProj_ext (a : J → LineStage K) (y : ProjectiveProduct K)
    {v w : (sum a).Fiber y} (h : ∀ j, sumProj a j y v = sumProj a j y w) : v=w := by
  apply (EuclideanSpace.equiv _ ℂ).injective
  funext ⟨j,s⟩
  exact congrArg (fun v : (a j).Model => v s) (h j)

end LineStage
end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} [Fintype ι] {K : ι → ℕ}

omit [Fintype ι] in
/-- The actual Hermitian metric is continuous when evaluated on two bundle
vectors over the same varying base, including vectors in the total space. -/
theorem continuous_lineStage_inner_over (a : LineStage K) {X : Type*} [TopologicalSpace X]
    (b : X → ProjectiveProduct K) (hb : Continuous b)
    (v w : ∀ x, a.Fiber (b x))
    (hv : Continuous (fun x => TotalSpace.mk' a.Model (b x) (v x)))
    (hw : Continuous (fun x => TotalSpace.mk' a.Model (b x) (w x))) :
    Continuous (fun x => inner ℂ (v x) (w x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let C := fun s => productLineCore K (a.label s)
  let chart := (smoothLineSumCore K a.label).indexAt (b x)
  have hcv := (FiberBundle.continuousAt_totalSpace a.Model _ (x₀ := x)).mp hv.continuousAt |>.2
  have hcw := (FiberBundle.continuousAt_totalSpace a.Model _ (x₀ := x)).mp hw.continuousAt |>.2
  apply (hcv.inner hcw).congr_of_eventuallyEq
  · have hn := (hb.continuousAt (x := x)) ((isOpen_lineSumBaseSet C chart).mem_nhds
      ((smoothLineSumCore K a.label).mem_baseSet_at (b x)))
    filter_upwards [hn] with z hz
    exact (finiteLineSum_chart_inner C (fun s => productLineCore_unitary K (a.label s))
      chart (b z) hz (v z) (w z)).symm

end Kaplansky

end

open scoped BigOperators
namespace Kaplansky.LineStage
open ComplexGrassmann
variable {ι : Type*} {J : Type} [Fintype J] {K : ι → ℕ}

theorem sum_inner (a : J → LineStage K) (y : ProjectiveProduct K)
    (v w : (sum a).Fiber y) :
    inner ℂ v w = ∑ j, inner ℂ (sumProj a j y v) (sumProj a j y w) := by
  change (∑ s : Σ j : J, (a j).Slot,
    inner ℂ ((show (sum a).Model from v) s) ((show (sum a).Model from w) s)) =
    ∑ j : J, ∑ s : (a j).Slot,
      inner ℂ ((show (sum a).Model from v) ⟨j,s⟩) ((show (sum a).Model from w) ⟨j,s⟩)
  exact Fintype.sum_sigma _

end Kaplansky.LineStage

end

end OAI
