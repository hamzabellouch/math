import Mathlib
import OAI.Geometry.PrescribedPotential.LocalizedCompact
import OAI.Geometry.PrescribedPotential.ParametrixAtlas

namespace OAI

/-! Global Sobolev. -/

section

 

noncomputable section
open Set Filter Topology MeasureTheory Manifold IsManifold
open scoped ContDiff SchwartzMap BoundedContinuousFunction Classical

namespace GlobalElliptic
open Anticanonical EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] (A : ComplexAtlas d X)

 
def smoothSpace : Submodule ℝ (X → ℂ) where
  carrier := {f | ∀ i, ContDiffOn ℝ ∞ (f ∘ (A.euclideanChart i).symm)
    (A.euclideanChart i).target}
  zero_mem' := by intro i; exact contDiffOn_const
  add_mem' := by intro f h hf hh i; exact (hf i).add (hh i)
  smul_mem' := by intro c f hf i; exact contDiffOn_const.smul (hf i)

abbrev Smooth := ↥(smoothSpace A)

instance : FunLike (Smooth A) X ℂ where
  coe := Subtype.val
  coe_injective := Subtype.val_injective

namespace Smooth
variable {A}

@[simp] lemma add_apply (f h : Smooth A) (x : X) : (f + h) x = f x + h x := rfl
@[simp] lemma smul_apply (c : ℝ) (f : Smooth A) (x : X) : (c • f) x = c • f x := rfl
@[simp] lemma zero_apply (x : X) : (0 : Smooth A) x = 0 := rfl

lemma smooth (f : Smooth A) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (f ∘ (A.euclideanChart i).symm) (A.euclideanChart i).target := f.property i

lemma continuous (f : Smooth A) : Continuous (f : X → ℂ) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨i, hi⟩ := A.covers x
  let e := A.euclideanChart i
  have hx : x ∈ e.source := by simpa [e] using hi
  have he := e.continuousAt hx
  have hf := ((f.smooth i).continuousOn.continuousAt (e.open_target.mem_nhds (e.mapsTo hx))).comp he
  apply hf.congr
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  exact congrArg f (e.left_inv hy)

@[ext] lemma ext {f h : Smooth A} (H : ∀ x, f x = h x) : f = h := Subtype.ext (funext H)

def const (c : ℂ) : Smooth A := ⟨fun _ => c, fun _ => contDiffOn_const⟩

 
def mul (f h : Smooth A) : Smooth A := ⟨fun x => f x * h x, fun i => (f.smooth i).mul (h.smooth i)⟩

end Smooth

 
def localizeFun (i : Fin A.count) (ρ f : Smooth A) (y : EC d) : ℂ :=
  if y ∈ (A.euclideanChart i).target then
    ρ ((A.euclideanChart i).symm y) * f ((A.euclideanChart i).symm y) else 0

lemma localizeFun_apply {i : Fin A.count} (ρ f : Smooth A) {y : EC d}
    (hy : y ∈ (A.euclideanChart i).target) :
    localizeFun A i ρ f y = ρ ((A.euclideanChart i).symm y) *
      f ((A.euclideanChart i).symm y) := ite_eq_left hy

lemma localizeFun_support (i : Fin A.count) (ρ f : Smooth A) :
    Function.support (localizeFun A i ρ f) ⊆ (A.euclideanChart i) '' tsupport (ρ : X → ℂ) := by
  intro y hy
  have hn : localizeFun A i ρ f y ≠ 0 := hy
  by_cases ht : y ∈ (A.euclideanChart i).target
  · rw [localizeFun_apply A ρ f ht] at hn
    exact ⟨(A.euclideanChart i).symm y,
      subset_tsupport _ (left_ne_zero_of_mul hn), (A.euclideanChart i).right_inv ht⟩
  · exact (hn (ite_eq_right ht)).elim

lemma localizeFun_smooth_compact [T2Space X] [CompactSpace X]
    (i : Fin A.count) (ρ f : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) :
    ContDiff ℝ ∞ (localizeFun A i ρ f) ∧ HasCompactSupport (localizeFun A i ρ f) := by
  let e := A.euclideanChart i
  let K := e '' tsupport (ρ : X → ℂ)
  have hK : IsCompact K := (isClosed_tsupport _).isCompact.image_of_continuousOn
    (e.continuousOn.mono hρ)
  have hs : Function.support (localizeFun A i ρ f) ⊆ K := localizeFun_support A i ρ f
  constructor
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ e.target
    · have hc := ((ρ.smooth i).mul (f.smooth i)).contDiffAt (e.open_target.mem_nhds hy)
      apply hc.congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      exact localizeFun_apply A ρ f hz
    · have hyK : y ∉ K := by
        rintro ⟨x, hx, rfl⟩
        exact hy (e.mapsTo (hρ hx))
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hyK] with z hz
      exact Function.notMem_support.mp (fun h => hz (hs h))
  · exact HasCompactSupport.of_support_subset_isCompact hK hs

 
def localize [T2Space X] [CompactSpace X] (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) (f : Smooth A) : 𝓢(EC d, ℂ) :=
  (localizeFun_smooth_compact A i ρ f hρ).2.toSchwartzMap
    (localizeFun_smooth_compact A i ρ f hρ).1

@[simp] lemma localize_apply [T2Space X] [CompactSpace X] (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) (f : Smooth A) (y : EC d) :
    localize A i ρ hρ f y = localizeFun A i ρ f y := rfl

 
def localizeLinear [T2Space X] [CompactSpace X] (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) : Smooth A →ₗ[ℝ] 𝓢(EC d, ℂ) where
  toFun := localize A i ρ hρ
  map_add' f h := by
    ext y
    simp only [localize_apply, localizeFun, add_apply]
    split_ifs <;> simp [mul_add]
  map_smul' c f := by
    ext y
    simp only [localize_apply, localizeFun, smul_apply]
    split_ifs <;> simp [mul_left_comm]

end GlobalElliptic

end
end

end OAI
