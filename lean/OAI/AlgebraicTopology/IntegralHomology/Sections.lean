import OAI.Geometry.ComplexBundle.Sections
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Compact

namespace OAI

noncomputable section

namespace Kaplansky

/-! Section classes in one-point compactifications and their naturality. -/

section
open Bundle Topology Filter Set OnePoint

/-- A continuous real-valued measurement tending to infinity forces escape
from every closed compact set. Properness of the measurement is not needed. -/
theorem tendsto_onePoint_of_measure {X Z : Type*} [TopologicalSpace Z]
    {l : Filter X} {f : X → Z} (q : Z → ℝ) (hq : Continuous q)
    (h : Tendsto (fun x => q (f x)) l atTop) :
    Tendsto (fun x => (f x : OnePoint Z)) l (𝓝 ∞) := by
  apply OnePoint.tendsto_coe_infty.comp
  apply hasBasis_coclosedCompact.tendsto_right_iff.mpr
  intro S hS
  obtain ⟨r, hr⟩ := hS.2.bddAbove_image hq.continuousOn
  filter_upwards [h.eventually_gt_atTop r] with x hx
  exact fun hmem => (not_lt_of_ge (hr (mem_image_of_mem q hmem))) hx

variable {B V : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : B → Type*} [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℂ (E b)]
  [TopologicalSpace (TotalSpace V E)] [FiberBundle V E] [VectorBundle ℂ V E]

/-- Push a nowhere-zero section out along each fiber, ending at infinity. -/
def sectionToInfinity (s : ∀ b, E b) (z : unitInterval × B) :
    OnePoint (TotalSpace V E) :=
  if z.1 = 1 then ∞ else
    (TotalSpace.mk' V z.2 ((((1 - z.1.val)⁻¹ : ℝ) : ℂ) • s z.2) : OnePoint (TotalSpace V E))

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [FiberBundle V E] [VectorBundle ℂ V E] in
theorem sectionToInfinity_continuousAt_end (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (hnorm : Continuous (fun z : TotalSpace V E => ‖z.2‖))
    (hne : ∀ b, s b ≠ 0) (b : B) :
    ContinuousAt (sectionToInfinity (V := V) s) (1, b) := by
  classical
  have hsmall : Tendsto (fun z : unitInterval × B => 1 - z.1.val)
      (𝓝[{z | z.1 ≠ 1}] (1, b)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa [ContinuousWithinAt] using (show Continuous (fun z : unitInterval × B => 1 - z.1.val) from continuous_const.sub (continuous_subtype_val.comp continuous_fst)).continuousAt (x := (1,b)) |>.continuousWithinAt (s := {z : unitInterval × B | z.1 ≠ 1})
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hlt : z.1.val < 1 := lt_of_le_of_ne z.1.property.2 (fun h => hz (Subtype.ext h))
      exact sub_pos.mpr hlt
  have hnorms : Tendsto (fun z : unitInterval × B => ‖s z.2‖)
      (𝓝[{z | z.1 ≠ 1}] (1, b)) (𝓝 ‖s b‖) :=
    ((hnorm.comp hs).comp continuous_snd).continuousAt.continuousWithinAt
  have hlarge := (tendsto_inv_nhdsGT_zero.comp hsmall).atTop_mul_pos
    (norm_pos_iff.mpr (hne b)) hnorms
  have hescape : Tendsto (fun z : unitInterval × B =>
      (TotalSpace.mk' V z.2 ((((1 - z.1.val)⁻¹ : ℝ) : ℂ) • s z.2) : OnePoint (TotalSpace V E)))
      (𝓝[{z | z.1 ≠ 1}] (1, b)) (𝓝 ∞) := by
    apply tendsto_onePoint_of_measure (fun z : TotalSpace V E => ‖z.2‖) hnorm
    convert hlarge using 1
    ext z
    simp only [Function.comp_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (sub_nonneg.mpr z.1.property.2))]
  rw [ContinuousAt, show sectionToInfinity (V := V) s (1,b) = ∞ by simp [sectionToInfinity]]
  rw [← nhdsWithin_univ]
  apply Filter.Tendsto.piecewise_nhdsWithin (t := {z : unitInterval × B | z.1 = 1})
  · exact tendsto_const_nhds
  · rw [univ_inter, show {z : unitInterval × B | z.1 = 1}ᶜ = {z | z.1 ≠ 1} from rfl]
    exact hescape

theorem continuous_sectionToInfinity (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (hnorm : Continuous (fun z : TotalSpace V E => ‖z.2‖))
    (hne : ∀ b, s b ≠ 0) : Continuous (sectionToInfinity (V := V) s) := by
  classical
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t,b⟩
  by_cases ht : t = 1
  · subst t
    exact sectionToInfinity_continuousAt_end s hs hnorm hne b
  · have hscalar : ContinuousAt (fun z : unitInterval × B => (((1 - z.1.val)⁻¹ : ℝ) : ℂ)) (t,b) := by
      apply Complex.continuous_ofReal.continuousAt.comp
      apply ContinuousAt.inv₀
      · exact continuous_const.continuousAt.sub (continuous_subtype_val.comp continuous_fst).continuousAt
      · exact sub_ne_zero.mpr (fun h => ht (Subtype.ext h.symm))
    have hv : ContinuousAt (fun z : unitInterval × B =>
        TotalSpace.mk' V z.2 ((((1 - z.1.val)⁻¹ : ℝ) : ℂ) • s z.2)) (t,b) := by
      rw [FiberBundle.continuousAt_totalSpace]
      refine ⟨continuous_snd.continuousAt, ?_⟩
      have hc := (FiberBundle.continuousAt_totalSpace V _ (x₀ := (t,b))).mp
        (hs.comp continuous_snd).continuousAt |>.2
      apply (hscalar.smul hc).congr_of_eventuallyEq
      let e := trivializationAt V E b
      have hn := continuous_snd.continuousAt (x := (t,b)) (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt V E b))
      filter_upwards [hn] with z hz
      exact (e.linear ℂ hz).map_smul _ _
    apply (OnePoint.continuous_coe.continuousAt.comp hv).congr_of_eventuallyEq
    have hn : ∀ᶠ z : unitInterval × B in 𝓝 (t,b), z.1 ≠ 1 :=
      continuous_fst.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds ht)
    filter_upwards [hn] with z hz
    exact ite_eq_right hz

/-- A nowhere-zero section is null-homotopic in the one-point total space.
Continuity at infinity is proved from the actual continuous fiber norm. -/
def compactifiedSectionNullHomotopy (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (hnorm : Continuous (fun z : TotalSpace V E => ‖z.2‖))
    (hne : ∀ b, s b ≠ 0) :
    ContinuousMap.Homotopy (compactifiedSection s hs) (ContinuousMap.const B ∞) where
  toFun := sectionToInfinity s
  continuous_toFun := continuous_sectionToInfinity s hs hnorm hne
  map_zero_left b := by simp [sectionToInfinity, compactifiedSection]
  map_one_left b := by simp [sectionToInfinity]

end

section
open Bundle Topology CategoryTheory AlgebraicTopology OnePoint

/-- Ordinary singular homology with integer coefficients. -/
def integralSingularHomology (n : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} ℤ :=
  (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)

theorem integralSingularHomology_homotopy {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (n : ℕ) :
    (integralSingularHomology n).map f = (integralSingularHomology n).map g :=
  H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) n

/-- A constant map induces zero in every positive homological degree. -/
theorem integralSingularHomology_const {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) {n : ℕ} (hn : n ≠ 0) :
    (integralSingularHomology n).map (TopCat.ofHom (ContinuousMap.const X y)) = 0 := by
  let f : TopCat.of X ⟶ TopCat.of PUnit := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let g : TopCat.of PUnit ⟶ TopCat.of Y := TopCat.ofHom (ContinuousMap.const PUnit y)
  have he : TopCat.ofHom (ContinuousMap.const X y) = f ≫ g := rfl
  rw [he, Functor.map_comp]
  have hz := isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) hn
  have hf : (integralSingularHomology n).map f = 0 := hz.eq_of_tgt _ _
  rw [hf, Limits.zero_comp]

variable {B V : Type} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : B → Type} [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℂ (E b)]
  [TopologicalSpace (TotalSpace V E)] [FiberBundle V E] [VectorBundle ℂ V E]

/-- The section-induced map into the homology of the one-point total space.
This is an actual singular homology morphism, not a postulated characteristic class. -/
def sectionHomologyMap (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b))) (n : ℕ) :
    (integralSingularHomology n).obj (TopCat.of B) ⟶
      (integralSingularHomology n).obj (TopCat.of (OnePoint (TotalSpace V E))) :=
  (integralSingularHomology n).map (TopCat.ofHom (compactifiedSection s hs))

/-- Every pair of continuous sections induces the same integral homology map,
even if their zero sets have different dimensions or contain degenerate zeros. -/
theorem sectionHomologyMap_eq (s t : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (ht : Continuous (fun b => TotalSpace.mk' V b (t b))) (n : ℕ) :
    sectionHomologyMap s hs n = sectionHomologyMap t ht n :=
  integralSingularHomology_homotopy (compactifiedSectionHomotopy s t hs ht) n

/-- A nowhere-zero section makes its actual section-induced map vanish in
positive degree. This does not assert that the canonical map is nonzero. -/
theorem sectionHomologyMap_eq_zero (s : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (hnorm : Continuous (fun z : TotalSpace V E => ‖z.2‖))
    (hne : ∀ b, s b ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    sectionHomologyMap s hs n = 0 := by
  exact (integralSingularHomology_homotopy
    (compactifiedSectionNullHomotopy s hs hnorm hne) n).trans
      (integralSingularHomology_const ∞ hn)

/-- If any nowhere-zero section exists, all section-induced maps vanish in
positive degree. All geometric hypotheses are explicit. -/
theorem sectionHomologyMap_eq_zero_of_nonvanishing (s t : ∀ b, E b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (ht : Continuous (fun b => TotalSpace.mk' V b (t b)))
    (hnorm : Continuous (fun z : TotalSpace V E => ‖z.2‖))
    (hne : ∀ b, t b ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    sectionHomologyMap s hs n = 0 :=
  (sectionHomologyMap_eq s t hs ht n).trans (sectionHomologyMap_eq_zero t ht hnorm hne hn)

end

open Bundle Topology CategoryTheory OnePoint
section

/-- A genuine homeomorphism of total spaces gives an isomorphism on the
integral homology of their one-point compactifications. -/
def compactificationHomologyIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) :
    (integralSingularHomology n).obj (TopCat.of (OnePoint X)) ≅
      (integralSingularHomology n).obj (TopCat.of (OnePoint Y)) :=
  (integralSingularHomology n).mapIso (TopCat.isoOfHomeo e.onePointCongr)

variable {B V W : Type} [TopologicalSpace B]
  {E F : B → Type}
  [TopologicalSpace (TotalSpace V E)] [TopologicalSpace (TotalSpace W F)]

/-- Naturality under an actual homeomorphism carrying one section to another.
The equality concerns constructed singular homology morphisms. -/
theorem sectionHomologyMap_naturality (e : TotalSpace V E ≃ₜ TotalSpace W F)
    (s : ∀ b, E b) (t : ∀ b, F b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (ht : Continuous (fun b => TotalSpace.mk' W b (t b)))
    (he : ∀ b, e (TotalSpace.mk' V b (s b)) = TotalSpace.mk' W b (t b)) (n : ℕ) :
    sectionHomologyMap s hs n ≫ (compactificationHomologyIso e n).hom =
      sectionHomologyMap t ht n := by
  change (integralSingularHomology n).map _ ≫ (integralSingularHomology n).map _ = _
  rw [← Functor.map_comp]
  apply congrArg ((integralSingularHomology n).map)
  ext b
  exact congrArg (fun z : TotalSpace W F => (z : OnePoint (TotalSpace W F))) (he b)

/-- Vanishing is preserved and reflected by genuine bundle isomorphisms
that carry the chosen sections to one another. -/
theorem sectionHomologyMap_naturality_zero_iff (e : TotalSpace V E ≃ₜ TotalSpace W F)
    (s : ∀ b, E b) (t : ∀ b, F b)
    (hs : Continuous (fun b => TotalSpace.mk' V b (s b)))
    (ht : Continuous (fun b => TotalSpace.mk' W b (t b)))
    (he : ∀ b, e (TotalSpace.mk' V b (s b)) = TotalSpace.mk' W b (t b)) (n : ℕ) :
    sectionHomologyMap s hs n = 0 ↔ sectionHomologyMap t ht n = 0 := by
  have h := sectionHomologyMap_naturality e s t hs ht he n
  constructor
  · intro hz
    rw [← h, hz, Limits.zero_comp]
  · intro hz
    have hc := congrArg (fun f => f ≫ (compactificationHomologyIso e n).inv) h
    simpa [Category.assoc, hz] using hc

end

end Kaplansky

end

end OAI
