import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Topology.UrysohnsLemma

namespace OAI

/-! Compact dimension contents, their finite measures, and positive support. -/

section

noncomputable section
open Set TopologicalSpace
namespace Kaplansky

/-- The elementary dimension properties used to construct a compact content.
This is an auxiliary interface, not a quasitrace or a linearity assumption. -/
structure PositiveDimensionFunctional (X : Type*) [TopologicalSpace X] where
  toFun : C(X, ℝ) → ℝ
  nonneg : ∀ f, 0 ≤ f → 0 ≤ toFun f
  mono : ∀ f g, 0 ≤ f → f ≤ g → toFun f ≤ toFun g
  subadd : ∀ f g, 0 ≤ f → 0 ≤ g → toFun (f+g) ≤ toFun f + toFun g
  orthogonal : ∀ f g, 0 ≤ f → 0 ≤ g → f*g=0 → toFun (f+g) = toFun f + toFun g

namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] (D : PositiveDimensionFunctional X)

/-- Continuous nonnegative functions majorizing one on the compact set. -/
def majorants (K : Compacts X) : Set C(X, ℝ) := {f | 0 ≤ f ∧ ∀ x ∈ K, 1 ≤ f x}

def compactValue (K : Compacts X) : ℝ := sInf (D.toFun '' majorants K)

theorem majorants_nonempty (K : Compacts X) : (majorants K).Nonempty :=
  ⟨1, zero_le_one, fun _ _ => le_rfl⟩

theorem majorant_values_bddBelow (K : Compacts X) : BddBelow (D.toFun '' majorants K) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact D.nonneg f hf.1

theorem compactValue_nonneg (K : Compacts X) : 0 ≤ D.compactValue K := by
  apply le_csInf ((majorants_nonempty K).image D.toFun)
  rintro _ ⟨f, hf, rfl⟩
  exact D.nonneg f hf.1

theorem compactValue_le (K : Compacts X) {f : C(X, ℝ)} (hf : f ∈ majorants K) :
    D.compactValue K ≤ D.toFun f := csInf_le (D.majorant_values_bddBelow K) ⟨f, hf, rfl⟩

theorem le_compactValue (K : Compacts X) {r : ℝ}
    (h : ∀ f ∈ majorants K, r ≤ D.toFun f) : r ≤ D.compactValue K := by
  apply le_csInf ((majorants_nonempty K).image D.toFun)
  rintro _ ⟨f, hf, rfl⟩
  exact h f hf

theorem compactValue_le_one (K : Compacts X) : D.compactValue K ≤ D.toFun 1 :=
  D.compactValue_le K ⟨zero_le_one, fun _ _ => le_rfl⟩

theorem compactValue_mono (K L : Compacts X) (h : (K : Set X) ⊆ L) :
    D.compactValue K ≤ D.compactValue L := by
  apply D.le_compactValue
  intro f hf
  exact D.compactValue_le K ⟨hf.1, fun x hx => hf.2 x (h hx)⟩

theorem compactValue_sup_le (K L : Compacts X) :
    D.compactValue (K ⊔ L) ≤ D.compactValue K + D.compactValue L := by
  apply (sub_le_iff_le_add).mp
  apply D.le_compactValue K
  intro f hf
  suffices h : D.compactValue (K ⊔ L) - D.toFun f ≤ D.compactValue L by linarith
  apply D.le_compactValue L
  intro g hg
  have hfg : f+g ∈ majorants (K ⊔ L) := by
    refine ⟨add_nonneg hf.1 hg.1, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · exact (hf.2 x hx).trans (le_add_of_nonneg_right (hg.1 x))
    · exact (hg.2 x hx).trans (le_add_of_nonneg_left (hf.1 x))
  have h := (D.compactValue_le (K ⊔ L) hfg).trans (D.subadd f g hf.1 hg.1)
  linarith

end PositiveDimensionFunctional
end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace
namespace Kaplansky

/-- Disjoint closed sets admit nonnegative continuous cutoffs with disjoint
supports and sum at most one. -/
theorem exists_disjoint_compact_cutoffs {X : Type*} [TopologicalSpace X] [NormalSpace X]
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (hKL : Disjoint K L) :
    ∃ u v : C(X, ℝ), 0 ≤ u ∧ 0 ≤ v ∧ u+v ≤ 1 ∧ u*v=0 ∧
      (∀ x ∈ K, u x=1) ∧ (∀ x ∈ L, v x=1) := by
  obtain ⟨f, hfK, hfL, hf⟩ := exists_continuous_zero_one_of_isClosed hK hL hKL
  let u : C(X, ℝ) := ⟨fun x => max (1-3*f x) 0, by fun_prop⟩
  let v : C(X, ℝ) := ⟨fun x => max (3*f x-2) 0, by fun_prop⟩
  refine ⟨u, v, (fun x => le_max_right _ _), (fun x => le_max_right _ _), ?_, ?_, ?_, ?_⟩
  · intro x
    change max (1-3*f x) 0 + max (3*f x-2) 0 ≤ 1
    have hx := hf x
    rcases le_total (1-3*f x) 0 with h | h <;>
      rcases le_total (3*f x-2) 0 with h' | h'
    · rw [max_eq_right h, max_eq_right h']; norm_num
    · rw [max_eq_right h, max_eq_left h']; linarith [hx.2]
    · rw [max_eq_left h, max_eq_right h']; linarith [hx.1]
    · linarith
  · ext x
    change max (1-3*f x) 0 * max (3*f x-2) 0 = 0
    by_cases h : 1-3*f x ≤ 0
    · rw [max_eq_right h, zero_mul]
    · rw [max_eq_right (by linarith : 3*f x-2 ≤ 0), mul_zero]
  · intro x hx
    change max (1-3*f x) 0 = 1
    rw [hfK hx]
    norm_num
  · intro x hx
    change max (3*f x-2) 0 = 1
    rw [hfL hx]
    norm_num

end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace
open scoped NNReal ENNReal
namespace Kaplansky
namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] [NormalSpace X] (D : PositiveDimensionFunctional X)

theorem compactValue_sup_disjoint (K L : Compacts X)
    (hKL : Disjoint (K : Set X) L) (hK : IsClosed (K : Set X)) (hL : IsClosed (L : Set X)) :
    D.compactValue (K ⊔ L) = D.compactValue K + D.compactValue L := by
  apply le_antisymm (D.compactValue_sup_le K L)
  apply D.le_compactValue
  intro f hf
  obtain ⟨u, v, hu, hv, huv, hzero, huK, hvL⟩ :=
    exists_disjoint_compact_cutoffs (K : Set X) L hK hL hKL
  have huf : u*f ∈ majorants K := by
    refine ⟨fun x => mul_nonneg (hu x) (hf.1 x), ?_⟩
    intro x hx
    change 1 ≤ u x*f x
    rw [huK x hx, one_mul]
    exact hf.2 x (Or.inl hx)
  have hvf : v*f ∈ majorants L := by
    refine ⟨fun x => mul_nonneg (hv x) (hf.1 x), ?_⟩
    intro x hx
    change 1 ≤ v x*f x
    rw [hvL x hx, one_mul]
    exact hf.2 x (Or.inr hx)
  have hm : u*f+v*f ≤ f := by
    intro x
    change u x*f x+v x*f x ≤ f x
    have h := mul_le_mul_of_nonneg_right (huv x) (hf.1 x)
    change (u x+v x)*f x ≤ 1*f x at h
    simpa only [add_mul, one_mul] using h
  have hz : (u*f)*(v*f)=0 := by
    calc
      (u*f)*(v*f) = (u*v)*(f*f) := by ring
      _ = 0 := by rw [hzero, zero_mul]
  calc
    _ ≤ D.toFun (u*f)+D.toFun (v*f) := add_le_add (D.compactValue_le K huf) (D.compactValue_le L hvf)
    _ = D.toFun (u*f+v*f) := (D.orthogonal _ _ huf.1 hvf.1 hz).symm
    _ ≤ D.toFun f := D.mono _ _ (add_nonneg huf.1 hvf.1) hm

/-- An actual compact content obtained by infima of positive dimension values. -/
def content : MeasureTheory.Content X where
  toFun K := ⟨D.compactValue K, D.compactValue_nonneg K⟩
  mono' K L h := D.compactValue_mono K L h
  sup_le' K L := D.compactValue_sup_le K L
  sup_disjoint' K L h hK hL := NNReal.eq (D.compactValue_sup_disjoint K L h hK hL)

@[simp] theorem content_toReal (K : Compacts X) : (D.content K).toReal = D.compactValue K := by
  exact ENNReal.coe_toReal _

end PositiveDimensionFunctional
end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal
namespace Kaplansky
namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] [NormalSpace X] [R1Space X]
    [MeasurableSpace X] [BorelSpace X] (D : PositiveDimensionFunctional X)

/-- The Borel measure furnished by the proved compact content. -/
def measure : Measure X := D.content.measure

theorem measure_open (U : Opens X) :
    D.measure (U : Set X) = D.content.innerContent U := by
  rw [measure, Content.measure_apply _ U.isOpen.measurableSet, Content.outerMeasure_opens]

theorem measure_open_eq_sup (U : Opens X) :
    D.measure (U : Set X) = ⨆ (K : Compacts X) (_ : (K : Set X) ⊆ U), D.content K :=
  D.measure_open U

omit [R1Space X] [MeasurableSpace X] [BorelSpace X] in
theorem content_le_one (K : Compacts X) : D.content K ≤ ENNReal.ofReal (D.toFun 1) := by
  rw [← ENNReal.ofReal_toReal (show D.content K ≠ ∞ from ENNReal.coe_ne_top)]
  rw [D.content_toReal K]
  exact ENNReal.ofReal_le_ofReal (D.compactValue_le_one K)

theorem measure_univ_le : D.measure Set.univ ≤ ENNReal.ofReal (D.toFun 1) := by
  change D.measure ((⊤ : Opens X) : Set X) ≤ _
  rw [D.measure_open_eq_sup]
  exact iSup₂_le fun K _ => D.content_le_one K

instance measure_isFiniteMeasure : IsFiniteMeasure D.measure :=
  ⟨D.measure_univ_le.trans_lt ENNReal.ofReal_lt_top⟩

end PositiveDimensionFunctional
end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace
namespace Kaplansky
namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] (D : PositiveDimensionFunctional X)

theorem zero_value : D.toFun 0 = 0 := by
  have h := D.orthogonal 0 0 le_rfl le_rfl (mul_zero _)
  rw [add_zero] at h
  linarith

theorem compactValue_empty : D.compactValue ⊥ = 0 := by
  apply le_antisymm _ (D.compactValue_nonneg _)
  rw [← D.zero_value]
  exact D.compactValue_le _ ⟨le_rfl, fun _ hx => False.elim hx⟩

/-- Positive scalar invariance is a dimension property, not spectral homogeneity. -/
def ScaleInvariant : Prop := ∀ (f : C(X, ℝ)), 0 ≤ f → ∀ r : ℝ, 0 < r →
  D.toFun (r • f) = D.toFun f

theorem compactValue_le_of_pos (hscale : D.ScaleInvariant) (K : Compacts X)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (hK : ∀ x ∈ K, 0 < f x) :
    D.compactValue K ≤ D.toFun f := by
  by_cases hne : (K : Set X).Nonempty
  · obtain ⟨x, hx, hmin⟩ := K.isCompact.exists_isMinOn hne f.continuous.continuousOn
    have hp := hK x hx
    rw [← hscale f hf ((f x)⁻¹) (inv_pos.mpr hp)]
    apply D.compactValue_le
    refine ⟨fun y => mul_nonneg (inv_nonneg.mpr hp.le) (hf y), ?_⟩
    intro y hy
    change 1 ≤ (f x)⁻¹ * f y
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hp).mpr (by simpa using hmin hy)
  · have h : K = ⊥ := by
      ext x
      change (x ∈ K) ↔ False
      exact ⟨fun hx => hne ⟨x, hx⟩, False.elim⟩
    rw [h, D.compactValue_empty]
    exact D.nonneg f hf

variable [CompactSpace X]

/-- A function vanishing off K has dimension at most the compact content of K. -/
theorem value_le_compactValue_of_support (hscale : D.ScaleInvariant) (K : Compacts X)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (hs : ∀ x, x ∉ K → f x=0) :
    D.toFun f ≤ D.compactValue K := by
  apply D.le_compactValue
  intro g hg
  have hp : 0 < ‖f‖+1 := by linarith [norm_nonneg f]
  have hle : f ≤ (‖f‖+1) • g := by
    intro x
    change f x ≤ (‖f‖+1)*g x
    by_cases hx : x ∈ K
    · have hb : f x ≤ ‖f‖+1 := (f.apply_le_norm x).trans (by linarith)
      exact hb.trans (le_mul_of_one_le_right hp.le (hg.2 x hx))
    · rw [hs x hx]
      exact mul_nonneg hp.le (hg.1 x)
  calc
    D.toFun f ≤ D.toFun ((‖f‖+1) • g) := D.mono _ _ hf hle
    _ = D.toFun g := hscale g hg.1 _ hp

end PositiveDimensionFunctional
end Kaplansky

end
end

section

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal Topology
namespace Kaplansky

/-- Continuous scalar cutoff, used only for uniform approximation of functions. -/
def continuousDimensionCutoff {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (t : ℝ) : C(X, ℝ) :=
  ⟨fun x => max (f x-t) 0, by fun_prop⟩

theorem continuousDimensionCutoff_nonneg {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (t : ℝ) :
    0 ≤ continuousDimensionCutoff f t := fun _ => le_max_right _ _

theorem continuousDimensionCutoff_zero {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) (hf : 0 ≤ f) :
    continuousDimensionCutoff f 0 = f := by
  ext x
  change max (f x-0) 0 = f x
  rw [sub_zero, max_eq_left (show 0 ≤ f x from hf x)]

namespace PositiveDimensionFunctional
variable {X : Type*} [TopologicalSpace X] (D : PositiveDimensionFunctional X)

/-- Lower semicontinuity is required only on the nonnegative cone. -/
def ConeLowerSemicontinuous : Prop :=
  LowerSemicontinuous (fun f : {f : C(X, ℝ) // 0 ≤ f} => D.toFun f.val)

theorem exists_positive_cutoff (hsc : D.ConeLowerSemicontinuous)
    (f : C(X, ℝ)) (hf : 0 ≤ f) {r : ℝ} (hr : r < D.toFun f) :
    ∃ t : ℝ, 0 < t ∧ r < D.toFun (continuousDimensionCutoff f t) := by
  let g : ℝ → {f : C(X, ℝ) // 0 ≤ f} :=
    fun t => ⟨continuousDimensionCutoff f t, continuousDimensionCutoff_nonneg f t⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × X => max (f p.2-p.1) 0)
    fun_prop
  have h0 : r < D.toFun (g 0).val := by
    simpa only [g, continuousDimensionCutoff_zero f hf] using hr
  have he := (hsc.comp hg) 0 r h0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ/2, half_pos hδ, hball ?_⟩
  change dist (δ/2) (0 : ℝ) < δ
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
  linarith

variable [CompactSpace X] [NormalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]

/-- The finite measure represents dimension on every positive support.
The proof uses genuine compact contents and lower semicontinuity, not an
assumed measure representation or finite-spectrum approximation. -/
theorem measure_positive_support (hscale : D.ScaleInvariant) (hsc : D.ConeLowerSemicontinuous)
    (f : C(X, ℝ)) (hf : 0 ≤ f) :
    D.measure {x | 0 < f x} = ENNReal.ofReal (D.toFun f) := by
  let U : Opens X := ⟨{x | 0 < f x}, isOpen_lt continuous_const f.continuous⟩
  change D.measure (U : Set X) = _
  apply le_antisymm
  · rw [D.measure_open_eq_sup]
    refine iSup₂_le fun K hK => ?_
    rw [← ENNReal.ofReal_toReal (show D.content K ≠ ∞ from ENNReal.coe_ne_top), D.content_toReal]
    exact ENNReal.ofReal_le_ofReal (D.compactValue_le_of_pos hscale K f hf (fun x hx => hK hx))
  · have hl : D.toFun f ≤ (D.measure (U : Set X)).toReal := by
      apply le_of_forall_lt
      intro r hr
      obtain ⟨t, ht, hrt⟩ := D.exists_positive_cutoff hsc f hf hr
      let K : Compacts X := ⟨{x | t ≤ f x}, (isClosed_le continuous_const f.continuous).isCompact⟩
      have hKU : (K : Set X) ⊆ U := fun x hx => ht.trans_le hx
      have hs : ∀ x, x ∉ K → continuousDimensionCutoff f t x = 0 := by
        intro x hx
        change max (f x-t) 0=0
        apply max_eq_right
        have hx' : ¬t ≤ f x := hx
        linarith
      have hle := D.value_le_compactValue_of_support hscale K
        (continuousDimensionCutoff f t) (continuousDimensionCutoff_nonneg f t) hs
      have hm : D.compactValue K ≤ (D.measure (U : Set X)).toReal := by
        rw [← D.content_toReal K, D.measure_open]
        apply ENNReal.toReal_mono
        · rw [← D.measure_open]
          exact measure_ne_top _ _
        · exact D.content.le_innerContent K U hKU
      exact hrt.trans_le (hle.trans hm)
    calc
      ENNReal.ofReal (D.toFun f) ≤ ENNReal.ofReal (D.measure (U : Set X)).toReal :=
        ENNReal.ofReal_le_ofReal hl
      _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)

end PositiveDimensionFunctional
end Kaplansky

end
end

end OAI
