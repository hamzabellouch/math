import Mathlib
import OAI.GroupTheory.FiniteType.PresentationGeometry
import OAI.GroupTheory.FiniteType.PresentationVanKampen

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
namespace PresentationGeometry
namespace Adjunction

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {A : Set Y} (f : C(A, X))

def descend (g : X → Z) (h : Y → Z) (he : ∀ a : A, h a.1 = g (f a)) :
    Space f → Z := by
  classical
  refine Quotient.lift (Sum.elim g h) ?_
  have hn : ∀ a, Sum.elim g h (normalize f a) = Sum.elim g h a := by
    intro a
    cases a with
    | inl x => rfl
    | inr y =>
      by_cases hy : y ∈ A
      · simpa only [normalize_inr_mem f ⟨y, hy⟩, Sum.elim_inl, Sum.elim_inr] using
          (he ⟨y, hy⟩).symm
      · rw [normalize_inr_notMem f y hy]
  intro a b hab
  exact (hn a).symm.trans ((congrArg (Sum.elim g h) hab).trans (hn b))

omit [TopologicalSpace Z] in
@[simp] theorem descend_old (g : X → Z) (h : Y → Z)
    (he : ∀ a : A, h a.1 = g (f a)) (x : X) :
    descend f g h he (old f x) = g x := rfl

omit [TopologicalSpace Z] in
@[simp] theorem descend_disk (g : X → Z) (h : Y → Z)
    (he : ∀ a : A, h a.1 = g (f a)) (y : Y) :
    descend f g h he (disk f y) = h y := rfl

theorem continuous_descend (g : C(X, Z)) (h : C(Y, Z))
    (he : ∀ a : A, h a.1 = g (f a)) : Continuous (descend f g h he) :=
  (g.continuous.sumElim h.continuous).quotient_lift _

end Adjunction
namespace Cells

open Metric

def innerClosed {X : Type*} [TopologicalSpace X] {k d : ℕ}
    (f : C(boundary k d, X)) : Set (Space f) :=
  Adjunction.disk f '' {p : Fin k × Disk d | ‖p.2.1‖ ≤ (1 / 2 : ℝ)}

def collar {X : Type*} [TopologicalSpace X] {k d : ℕ}
    (f : C(boundary k d, X)) : Set (Space f) := (innerClosed f)ᶜ

def cellInterior {X : Type*} [TopologicalSpace X] {k d : ℕ}
    (f : C(boundary k d, X)) (i : Fin k) : Set (Space f) :=
  range ((OpenDisk d).domRestrict (characteristic f i))

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ} (f : C(boundary k d, X))

theorem collar_isOpen : IsOpen (collar f) := by
  have hc : IsClosed (innerClosed f) := ((isClosed_le (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const).isCompact.image (Adjunction.continuous_disk f)).isClosed
  exact hc.isOpen_compl

omit [T2Space X] [CompactSpace X] in
theorem cellInterior_isOpen (i : Fin k) : IsOpen (cellInterior f i) :=
  (characteristic_isOpenEmbedding f i).isOpen_range

omit [T2Space X] [CompactSpace X] in
theorem mem_collar_old (x : X) : Adjunction.old f x ∈ collar f := by
  rintro ⟨p, hp, he⟩
  have hpn : p ∉ boundary k d := by
    intro hh
    have hh' : ‖p.2.1‖ = 1 := by simpa only [boundary, mem_ofPred_eq, mem_sphere_zero_iff_norm] using hh
    change ‖p.2.1‖ ≤ (1 / 2 : ℝ) at hp
    linarith
  exact Adjunction.old_ne_disk_of_notMem f x hpn he.symm

omit [T2Space X] [CompactSpace X] in
theorem mem_collar_disk_iff (i : Fin k) (v : Disk d) :
    Adjunction.disk f (i, v) ∈ collar f ↔ (1 / 2 : ℝ) < ‖v.1‖ := by
  change (¬ ∃ p, ‖p.2.1‖ ≤ (1 / 2 : ℝ) ∧ Adjunction.disk f p = _) ↔ _
  constructor
  · intro h
    by_contra hn
    exact h ⟨(i, v), le_of_not_gt hn, rfl⟩
  · intro hv ⟨p, hp, he⟩
    have hpn : p ∉ boundary k d := by
      intro hh
      have hh' : ‖p.2.1‖ = 1 := by
        simpa only [boundary, mem_ofPred_eq, mem_sphere_zero_iff_norm] using hh
      linarith
    have he' := (Adjunction.disk_eq_disk_of_notMem f hpn).mp he
    cases he'
    exact (not_le.mpr hv) hp

omit [T2Space X] [CompactSpace X] in
theorem characteristic_on_openDisk (i : Fin k) (v : OpenDisk d) :
    characteristic f i v.1 = Adjunction.disk f (i, interiorInDisk v) :=
  characteristic_on_disk f i (interiorInDisk v)

omit [T2Space X] [CompactSpace X] in
theorem cellInterior_pairwiseDisjoint : Pairwise (Disjoint on cellInterior f) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨u, rfl⟩ ⟨v, hv⟩
  change characteristic f j v.1 = characteristic f i u.1 at hv
  rw [characteristic_on_openDisk f i u, characteristic_on_openDisk f j v] at hv
  have he : (j, interiorInDisk v) = (i, interiorInDisk u) :=
    (Adjunction.disk_eq_disk_of_notMem f (interiorInFamily j v).property).mp hv
  exact hij (congrArg Prod.fst he).symm

omit [T2Space X] [CompactSpace X] in
theorem collar_union_interiors : collar f ∪ ⋃ i, cellInterior f i = univ := by
  apply eq_univ_of_forall
  intro z
  by_cases hz : z ∈ collar f
  · exact Or.inl hz
  · have hz' : z ∈ innerClosed f := not_not.mp hz
    obtain ⟨⟨i, v⟩, hv, rfl⟩ := hz'
    right
    apply mem_iUnion.mpr
    refine ⟨i, ⟨⟨v.1, ?_⟩, ?_⟩⟩
    · rw [mem_ball_zero_iff]
      change ‖v.1‖ ≤ (1 / 2 : ℝ) at hv
      linarith
    · exact characteristic_on_disk f i v

omit [T2Space X] [CompactSpace X] in
theorem cellInterior_contractible (i : Fin k) : ContractibleSpace (cellInterior f i) := by
  let : ContractibleSpace (OpenDisk d) :=
    (convex_ball (0 : Fin d → ℝ) 1).contractibleSpace ⟨0, by simp⟩
  exact (characteristic_isOpenEmbedding f i).isEmbedding.toHomeomorph.symm.contractibleSpace

theorem annulus_pathConnected (hd : 1 < d) :
    IsPathConnected {v : Fin d → ℝ | (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 1} := by
  let A : Set (Fin d → ℝ) := {v | (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 1}
  have hs : IsPathConnected (sphere (0 : Fin d → ℝ) 1) :=
    isPathConnected_sphere (by simpa using hd) 0 (by norm_num)
  have ht : IsPathConnected (Ioo (1 / 2 : ℝ) 1) :=
    (convex_Ioo (1 / 2 : ℝ) 1).isPathConnected ⟨3 / 4, by norm_num⟩
  have he : (fun p : (Fin d → ℝ) × ℝ => p.2 • p.1) ''
      (sphere (0 : Fin d → ℝ) 1 ×ˢ Ioo (1 / 2 : ℝ) 1) = A := by
    ext v
    constructor
    · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
      have hu' : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
      change (1 / 2 : ℝ) < ‖t • u‖ ∧ ‖t • u‖ < 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1]), hu', mul_one]
      exact ht
    · intro hv
      have hv' : (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 1 := hv
      have hn : ‖v‖ ≠ 0 := by linarith [hv'.1]
      refine ⟨(‖v‖⁻¹ • v, ‖v‖), ⟨?_, hv'⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      · change ‖v‖ • (‖v‖⁻¹ • v) = v
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  change IsPathConnected A
  rw [← he]
  exact (hs.prod ht).image (continuous_snd.smul continuous_fst)

omit [T2Space X] [CompactSpace X] in
theorem collar_inter_interior (i : Fin k) :
    collar f ∩ cellInterior f i =
      characteristic f i '' {v : Fin d → ℝ | (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 1} := by
  ext z
  constructor
  · rintro ⟨hz, ⟨v, rfl⟩⟩
    refine ⟨v.1, ⟨?_, mem_ball_zero_iff.mp v.2⟩, rfl⟩
    change characteristic f i v.1 ∈ collar f at hz
    rw [characteristic_on_openDisk f i v] at hz
    exact (mem_collar_disk_iff f i (interiorInDisk v)).mp hz
  · rintro ⟨v, hv, rfl⟩
    let u : OpenDisk d := ⟨v, mem_ball_zero_iff.mpr hv.2⟩
    refine ⟨?_, ⟨u, rfl⟩⟩
    rw [show v = (interiorInDisk u).1 from rfl, characteristic_on_disk]
    exact (mem_collar_disk_iff f i (interiorInDisk u)).mpr hv.1

omit [T2Space X] [CompactSpace X] in
theorem collar_inter_interior_pathConnected (hd : 1 < d) (i : Fin k) :
    IsPathConnected (collar f ∩ cellInterior f i) := by
  rw [collar_inter_interior]
  apply (annulus_pathConnected hd).image'
  apply (characteristic_continuousOn f i).mono
  intro v hv
  exact mem_closedBall_zero_iff.mpr (le_of_lt hv.2)

theorem collar_fundamentalGroupMap_surjective (hd : 1 < d) (b : collar f) :
    Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(collar f, Space f)) b) := by
  apply PresentationVanKampen.fundamentalGroupMap_surjective_of_disjoint_open_cover
    (collar f) (cellInterior f) (collar_isOpen f) (cellInterior_isOpen f)
    (collar_union_interiors f) (cellInterior_pairwiseDisjoint f)
    (collar_inter_interior_pathConnected f hd)
  intro i
  let := cellInterior_contractible f i
  infer_instance

end Cells
end PresentationGeometry

namespace PresentationGeometry.Cells
section

open Metric

abbrev Shell (d : ℕ) := {v : Fin d → ℝ | (1 / 2 : ℝ) ≤ ‖v‖ ∧ ‖v‖ ≤ 1}

instance shell_compactSpace (d : ℕ) : CompactSpace (Shell d) := by
  apply isCompact_iff_compactSpace.mp
  exact (isCompact_closedBall (0 : Fin d → ℝ) 1).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    (fun v hv => mem_closedBall_zero_iff.mpr hv.2)

def shellInDisk {d : ℕ} (v : Shell d) : Disk d :=
  ⟨v.1, mem_closedBall_zero_iff.mpr v.2.2⟩

@[fun_prop] theorem shellInDisk_continuous {dimension : ℕ} :
    Continuous (shellInDisk (d := dimension)) :=
  continuous_subtype_val.subtype_mk _

def shellBoundary (k d : ℕ) : Set (Fin k × Shell d) := {p | ‖p.2.1‖ = 1}

theorem shellBoundary_closed (k d : ℕ) : IsClosed (shellBoundary k d) :=
  isClosed_eq (continuous_norm.comp (continuous_subtype_val.comp continuous_snd)) continuous_const

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ} (f : C(boundary k d, X))

def shellAttach : C(shellBoundary k d, X) where
  toFun p := f ⟨(p.1.1, shellInDisk p.1.2), mem_sphere_zero_iff_norm.mpr p.2⟩
  continuous_toFun := f.continuous.comp (by fun_prop)

abbrev ClosedCollarSpace := Adjunction.Space (shellAttach f)

instance : T2Space (ClosedCollarSpace f) :=
  Adjunction.t2Space (shellBoundary_closed k d) (shellAttach f)

def shellInclude : ClosedCollarSpace f → Space f :=
  Adjunction.descend (shellAttach f) (Adjunction.old f)
    (fun p => Adjunction.disk f (p.1, shellInDisk p.2))
    (fun p => Adjunction.disk_boundary f
      ⟨(p.1.1, shellInDisk p.1.2), mem_sphere_zero_iff_norm.mpr p.2⟩)

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellInclude_old (x : X) :
    shellInclude f (Adjunction.old (shellAttach f) x) = Adjunction.old f x := rfl

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellInclude_disk (p : Fin k × Shell d) :
    shellInclude f (Adjunction.disk (shellAttach f) p) =
      Adjunction.disk f (p.1, shellInDisk p.2) := rfl

omit [T2Space X] [CompactSpace X] in
theorem shellInclude_continuous : Continuous (shellInclude f) := by
  apply Adjunction.continuous_descend (shellAttach f)
    ⟨_, Adjunction.continuous_old f⟩
    ⟨_, (Adjunction.continuous_disk f).comp (by fun_prop)⟩

omit [T2Space X] [CompactSpace X] in
theorem shellInclude_injective : Injective (shellInclude f) := by
  let m : X ⊕ (Fin k × Shell d) → X ⊕ (Fin k × Disk d) :=
    Sum.map id (fun p => (p.1, shellInDisk p.2))
  have hm : Injective m := by
    apply Function.Injective.sumMap (fun _ _ h => h)
    intro a b h
    apply Prod.ext
    · exact congrArg (fun p : Fin k × Disk d => p.1) h
    · apply Subtype.ext
      exact congrArg (fun p => p.2.1) h
  have hn : ∀ a, Adjunction.normalize f (m a) = m (Adjunction.normalize (shellAttach f) a) := by
    intro a
    cases a with
    | inl x => rfl
    | inr p =>
      by_cases hp : p ∈ shellBoundary k d
      · have hp' : (p.1, shellInDisk p.2) ∈ boundary k d :=
          mem_sphere_zero_iff_norm.mpr hp
        change Adjunction.normalize f (Sum.inr (p.1, shellInDisk p.2)) = _
        rw [Adjunction.normalize_inr_mem f ⟨_, hp'⟩,
          Adjunction.normalize_inr_mem (shellAttach f) ⟨p, hp⟩]
        rfl
      · have hp' : (p.1, shellInDisk p.2) ∉ boundary k d := by
          intro hh
          apply hp
          exact mem_sphere_zero_iff_norm.mp hh
        change Adjunction.normalize f (Sum.inr (p.1, shellInDisk p.2)) = _
        rw [Adjunction.normalize_inr_notMem f _ hp',
          Adjunction.normalize_inr_notMem (shellAttach f) p hp]
        rfl
  intro a b hab
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      apply Quotient.sound
      apply hm
      rw [← hn a, ← hn b]
      have hq : ∀ z, shellInclude f (Quotient.mk (Adjunction.relation (shellAttach f)) z) =
          Quotient.mk (Adjunction.relation f) (m z) := by
        intro z; cases z <;> rfl
      rw [hq, hq] at hab
      exact Quotient.exact hab

theorem shellInclude_isClosedEmbedding : IsClosedEmbedding (shellInclude f) :=
  (shellInclude_continuous f).isClosedEmbedding (shellInclude_injective f)

omit [T2Space X] [CompactSpace X] in
theorem collar_subset_range_shellInclude : collar f ⊆ range (shellInclude f) := by
  intro z hz
  obtain ⟨x | p, rfl⟩ := Quotient.mk_surjective z
  · exact ⟨Adjunction.old (shellAttach f) x, rfl⟩
  · have hp : (1 / 2 : ℝ) < ‖p.2.1‖ := (mem_collar_disk_iff f p.1 p.2).mp hz
    refine ⟨Adjunction.disk (shellAttach f)
      (p.1, ⟨p.2.1, hp.le, mem_closedBall_zero_iff.mp p.2.2⟩), ?_⟩
    rfl

def collarToShell : C(collar f, ClosedCollarSpace f) where
  toFun z := (shellInclude_isClosedEmbedding f).isEmbedding.toHomeomorph.symm
    ⟨z.1, collar_subset_range_shellInclude f z.2⟩
  continuous_toFun :=
    (shellInclude_isClosedEmbedding f).isEmbedding.toHomeomorph.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)

@[simp] theorem shellInclude_collarToShell (z : collar f) :
    shellInclude f (collarToShell f z) = z.1 :=
  congrArg Subtype.val ((shellInclude_isClosedEmbedding f).isEmbedding.toHomeomorph.apply_symm_apply _)

end

open Metric
open scoped unitInterval

variable {k d : ℕ}

theorem shell_norm_pos (v : Shell d) : 0 < ‖v.1‖ := by
  linarith [v.2.1]

def shellUnit (p : Fin k × Shell d) : boundary k d := by
  have hn : ‖p.2.1‖ ≠ 0 := (shell_norm_pos p.2).ne'
  have hunit : ‖‖p.2.1‖⁻¹ • p.2.1‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  exact ⟨(p.1, ⟨‖p.2.1‖⁻¹ • p.2.1, mem_closedBall_zero_iff.mpr hunit.le⟩),
    mem_sphere_zero_iff_norm.mpr hunit⟩

theorem shellUnit_continuous : Continuous (shellUnit (k := k) (d := d)) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk continuous_fst
  apply Continuous.subtype_mk
  exact ((continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).inv₀
    (fun p => (shell_norm_pos p.2).ne')).smul (continuous_subtype_val.comp continuous_snd)

theorem shellUnit_boundary (p : shellBoundary k d) :
    shellUnit p.1 = ⟨(p.1.1, shellInDisk p.1.2), mem_sphere_zero_iff_norm.mpr p.2⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change ‖p.1.2.1‖⁻¹ • p.1.2.1 = p.1.2.1
    rw [show ‖p.1.2.1‖ = 1 from p.2, inv_one, one_smul]

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable (f : C(boundary k d, X))

def shellRetraction : C(ClosedCollarSpace f, X) where
  toFun := Adjunction.descend (shellAttach f) id (f ∘ shellUnit)
    (fun p => congrArg f (shellUnit_boundary p))
  continuous_toFun := Adjunction.continuous_descend (shellAttach f)
    (ContinuousMap.id X) ⟨f ∘ shellUnit, f.continuous.comp shellUnit_continuous⟩ _

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellRetraction_old (x : X) :
    shellRetraction f (Adjunction.old (shellAttach f) x) = x := rfl

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellRetraction_disk (p : Fin k × Shell d) :
    shellRetraction f (Adjunction.disk (shellAttach f) p) = f (shellUnit p) := rfl

def radialVector (t : I) (v : Shell d) : Fin d → ℝ :=
  ((1 - (t : ℝ)) + (t : ℝ) * ‖v.1‖⁻¹) • v.1

theorem norm_radialVector (t : I) (v : Shell d) :
    ‖radialVector t v‖ = (1 - (t : ℝ)) * ‖v.1‖ + (t : ℝ) := by
  have hn : ‖v.1‖ ≠ 0 := (shell_norm_pos v).ne'
  have hc : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * ‖v.1‖⁻¹ :=
    add_nonneg (sub_nonneg.mpr t.2.2) (mul_nonneg t.2.1 (inv_nonneg.mpr (norm_nonneg _)))
  rw [radialVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, add_mul,
    mul_assoc, inv_mul_cancel₀ hn, mul_one]

def radialDisk (t : I) (v : Shell d) : Disk d :=
  ⟨radialVector t v, mem_closedBall_zero_iff.mpr (by
    rw [norm_radialVector]
    nlinarith [v.2.2, mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr v.2.2)])⟩

theorem radialDisk_continuous : Continuous (fun p : I × Shell d => radialDisk p.1 p.2) := by
  apply Continuous.subtype_mk
  have ht : Continuous (fun p : I × Shell d => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun p : I × Shell d => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_const.sub ht).add (ht.mul (hv.norm.inv₀
    (fun p => (shell_norm_pos p.2).ne')))).smul hv

@[simp] theorem radialDisk_zero (v : Shell d) : radialDisk 0 v = shellInDisk v := by
  apply Subtype.ext
  simp [radialDisk, radialVector, shellInDisk]

@[simp] theorem radialDisk_boundary (t : I) (p : shellBoundary k d) :
    radialDisk t p.1.2 = shellInDisk p.1.2 := by
  apply Subtype.ext
  change ((1 - (t : ℝ)) + (t : ℝ) * ‖p.1.2.1‖⁻¹) • p.1.2.1 = p.1.2.1
  rw [show ‖p.1.2.1‖ = 1 from p.2, inv_one, mul_one, sub_add_cancel, one_smul]

def shellSlide (t : I) : ClosedCollarSpace f → Space f :=
  Adjunction.descend (shellAttach f) (Adjunction.old f)
    (fun p => Adjunction.disk f (p.1, radialDisk t p.2)) (fun p => by
      rw [radialDisk_boundary t p]
      exact Adjunction.disk_boundary f
        ⟨(p.1.1, shellInDisk p.1.2), mem_sphere_zero_iff_norm.mpr p.2⟩)

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellSlide_old (t : I) (x : X) :
    shellSlide f t (Adjunction.old (shellAttach f) x) = Adjunction.old f x := rfl

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellSlide_disk (t : I) (p : Fin k × Shell d) :
    shellSlide f t (Adjunction.disk (shellAttach f) p) =
      Adjunction.disk f (p.1, radialDisk t p.2) := rfl

omit [T2Space X] [CompactSpace X] in
theorem shellSlide_continuous : Continuous (fun p : I × ClosedCollarSpace f => shellSlide f p.1 p.2) := by
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
  have h₁ : Continuous (fun p : I × X => Adjunction.old f p.2) :=
    (Adjunction.continuous_old f).comp continuous_snd
  have h₂ : Continuous (fun p : I × (Fin k × Shell d) =>
      Adjunction.disk f (p.2.1, radialDisk p.1 p.2.2)) :=
    (Adjunction.continuous_disk f).comp
      ((continuous_fst.comp continuous_snd).prodMk
        (radialDisk_continuous.comp (continuous_fst.prodMk
          (continuous_snd.comp continuous_snd))))
  convert (h₁.sumElim h₂).comp Homeomorph.prodSumDistrib.continuous using 1
  funext p
  rcases p with ⟨t, x | y⟩ <;> rfl

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellSlide_zero (z : ClosedCollarSpace f) :
    shellSlide f 0 z = shellInclude f z := by
  induction z using Quotient.inductionOn with | h z =>
    cases z with
    | inl x => rfl
    | inr p => exact congrArg (fun v => Adjunction.disk f (p.1, v)) (radialDisk_zero p.2)

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellSlide_one (z : ClosedCollarSpace f) :
    shellSlide f 1 z = Adjunction.old f (shellRetraction f z) := by
  induction z using Quotient.inductionOn with | h z =>
    cases z with
    | inl x => rfl
    | inr p =>
      change Adjunction.disk f (p.1, radialDisk 1 p.2) = Adjunction.old f (f (shellUnit p))
      have hv : (p.1, radialDisk 1 p.2) = (shellUnit p).1 := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [radialDisk, radialVector, shellUnit]
      rw [hv]
      exact Adjunction.disk_boundary f (shellUnit p)

@[simp] theorem collarToShell_old (x : X) :
    collarToShell f ⟨Adjunction.old f x, mem_collar_old f x⟩ =
      Adjunction.old (shellAttach f) x := by
  apply shellInclude_injective f
  rw [shellInclude_collarToShell, shellInclude_old]

end PresentationGeometry.Cells

end

end OAI
