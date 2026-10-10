import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.RestrictionB
import OAI.Combinatorics.Chromatic.Shuffle.EulerForm

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def componentB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) : B a μ d →ₗ[ℚ] B a μ d :=
  (destabilizingSpace a μ d).mapQ (destabilizingSpace a μ d) (componentS d k)
    (fun f hf=>componentS_destabilizing_mem a μ d k f hf)

@[simp] lemma componentB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (f : S d) :
    componentB a μ d k ((destabilizingSpace a μ d).mkQ f) =
      (destabilizingSpace a μ d).mkQ (componentS d k f) := rfl

omit [Fintype I] [DecidableEq I] in
lemma componentS_componentS (d : I → ℕ) (k l : ℤ) (f : S d) :
    componentS d k (componentS d l f) = if k=l then componentS d l f else 0 :=
  componentS_of_homogeneous _ _ (componentS_homogeneous _ _ _) _

lemma componentB_componentB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k l : ℤ) (f : B a μ d) :
    componentB a μ d k (componentB a μ d l f) =
      if k=l then componentB a μ d l f else 0 := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change (destabilizingSpace a μ d).mkQ (componentS d k (componentS d l f)) =
      if k=l then (destabilizingSpace a μ d).mkQ (componentS d l f) else 0
    rw [componentS_componentS]
    split_ifs <;> simp

@[simp] lemma componentB_idempotent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (f : B a μ d) :
    componentB a μ d k (componentB a μ d k f) = componentB a μ d k f := by
  rw [componentB_componentB,ite_eq_left rfl]

lemma componentB_negative (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (hk : k<0) (f : B a μ d) : componentB a μ d k f = 0 := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change (destabilizingSpace a μ d).mkQ (componentS d k f) = 0
    have hs : componentS d k f=0 := Subtype.ext
      (homogeneous_negative_eq_zero _ (componentS_homogeneous d k f) hk)
    rw [hs,map_zero]

theorem componentB_finite_decomposition (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (f : B a μ d) :
    ∃ s : Finset ℤ, (∀ k∉s,componentB a μ d k f=0) ∧
      (∑ k ∈ s,componentB a μ d k f)=f := by
  classical
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    refine ⟨degreeSet f.val,?_,?_⟩
    · intro k hk
      change (destabilizingSpace a μ d).mkQ (componentS d k f) = 0
      have hs : componentS d k f=0 := by
        apply Subtype.ext
        apply weightedHomogeneousComponent_eq_zero'
        intro x hx
        exact fun h=>hk (Finset.mem_image.mpr ⟨x,hx,h⟩)
      rw [hs,map_zero]
    · change (∑ k ∈ degreeSet f.val,(destabilizingSpace a μ d).mkQ (componentS d k f)) =
        (destabilizingSpace a μ d).mkQ f
      rw [← map_sum,sum_componentS]

noncomputable def gradeB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) : Submodule ℚ (B a μ d) := LinearMap.range (componentB a μ d k)

lemma mem_gradeB_iff (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (f : B a μ d) :
    f ∈ gradeB a μ d k ↔ componentB a μ d k f=f := by
  constructor
  · rintro ⟨g,rfl⟩
    exact componentB_idempotent a μ d k g
  · intro h
    exact ⟨f,h⟩

lemma componentB_on_grade (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k l : ℤ) (f : B a μ d) (hf : f∈gradeB a μ d l) :
    componentB a μ d k f = if k=l then f else 0 := by
  obtain ⟨g,rfl⟩ := hf
  exact componentB_componentB a μ d k l g

theorem gradeB_finite_independent (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (s : Finset ℤ) (f : ℤ → B a μ d)
    (hf : ∀ k∈s,f k∈gradeB a μ d k) (hz : ∑ k ∈ s,f k=0) :
    ∀ k∈s,f k=0 := by
  classical
  intro k hk
  have h := congrArg (componentB a μ d k) hz
  rw [map_sum,map_zero] at h
  have heq : ∑ l ∈ s,componentB a μ d k (f l) = f k := by
    rw [Finset.sum_eq_single k]
    · exact (mem_gradeB_iff a μ d k _).mp (hf k hk)
    · intro l hl hlk
      rw [componentB_on_grade a μ d k l _ (hf l hl),ite_eq_right (Ne.symm hlk)]
    · exact fun hn=>(hn hk).elim
  rwa [heq] at h

end ElementaryPositivity.RawShuffle
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
@[simp] lemma dimensionCast_trans {d e b : I → ℕ} (h : d=e) (j : e=b) (f : S d) :
    dimensionCast j (dimensionCast h f) = dimensionCast (h.trans j) f := by
  subst e; subst b; rfl

lemma shuffle_assoc_cast (a : I → I → ℕ) {d e b : I → ℕ}
    (f : S d) (g : S e) (h : S b) :
    dimensionCast (add_assoc d e b) (shufflePolynomial a (shufflePolynomial a f g) h) =
      shufflePolynomial a f (shufflePolynomial a g h) := by
  rw [dimensionCast_eq_castS]
  exact shufflePolynomial_assoc a f g h

lemma shuffle_assoc_cast_symm (a : I → I → ℕ) {d e b : I → ℕ}
    (f : S d) (g : S e) (h : S b) :
    shufflePolynomial a (shufflePolynomial a f g) h =
      dimensionCast (add_assoc d e b).symm (shufflePolynomial a f (shufflePolynomial a g h)) := by
  rw [← shuffle_assoc_cast,dimensionCast_trans]
  rfl

@[simp] lemma shufflePolynomial_zero_left (a : I → I → ℕ) (d e : I → ℕ) (g : S e) :
    shufflePolynomial a (0 : S d) g = 0 := by
  exact LinearMap.congr_fun (map_zero (shuffleLinear a d e)) g
@[simp] lemma shufflePolynomial_zero_right (a : I → I → ℕ) (d e : I → ℕ) (f : S d) :
    shufflePolynomial a f (0 : S e) = 0 := (shuffleLinear a d e f).map_zero

lemma destabilizing_shuffle_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : slope c η d = slope c η e) {f : S d}
    (hf : f ∈ destabilizingSpace a (slope c η) d) (g : S e) :
    shufflePolynomial a f g ∈ destabilizingSpace a (slope c η) (d+e) := by
  induction hf using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨u,v,h,f₁,g',hu,hv,hμ,rfl⟩ := hF
    subst d
    refine Submodule.subset_span ⟨u,v+e,(add_assoc u v e).symm,f₁,
      shufflePolynomial a g' g,hu,add_ne_zero_left v e hv,?_,?_⟩
    · rw [slope_add_same c η hc hs]
      exact hμ
    · exact shuffle_assoc_cast_symm a f₁ g' g
  | zero => simp
  | add f f' hf hf' ih ih' =>
    simpa only [shufflePolynomial_add_left] using
      (destabilizingSpace a (slope c η) (d+e)).add_mem ih ih'
  | smul r f hf ih =>
    simpa only [shufflePolynomial_smul_left] using
      (destabilizingSpace a (slope c η) (d+e)).smul_mem r ih

lemma destabilizing_shuffle_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : slope c η d = slope c η e) (f : S d)
    {g : S e} (hg : g ∈ destabilizingSpace a (slope c η) e) :
    shufflePolynomial a f g ∈ destabilizingSpace a (slope c η) (d+e) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨u,v,h,g',h',hu,hv,hμ,rfl⟩ := hg
    subst e
    refine Submodule.subset_span ⟨d+u,v,add_assoc d u v,
      shufflePolynomial a f g',h',add_ne_zero_right d u hu,hv,?_,?_⟩
    · rw [slope_add_same c η hc hs]
      apply slope_add_gt c η hc hu (mass_eq c η hc d)
      rwa [hs]
    · exact (shuffle_assoc_cast a f g' h').symm
  | zero => simp
  | add g g' hg hg' ih ih' =>
    simpa only [shufflePolynomial_add_right] using
      (destabilizingSpace a (slope c η) (d+e)).add_mem ih ih'
  | smul r g hg ih =>
    simpa only [shufflePolynomial_smul_right] using
      (destabilizingSpace a (slope c η) (d+e)).smul_mem r ih

noncomputable def shuffleB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : slope c η d = slope c η e) :
    B a (slope c η) d →ₗ[ℚ] B a (slope c η) e →ₗ[ℚ] B a (slope c η) (d+e) := by
  let J := destabilizingSpace a (slope c η) (d+e)
  let L : S d →ₗ[ℚ] B a (slope c η) e →ₗ[ℚ] B a (slope c η) (d+e) :=
    { toFun := fun f => (destabilizingSpace a (slope c η) e).mapQ J
        (shuffleLinear a d e f) (by
          intro g hg
          exact destabilizing_shuffle_right a c η hc hs f hg)
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on with
        | H x => exact congrArg J.mkQ (shufflePolynomial_add_left a f g x)
      map_smul' := by
        intro r f
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on with
        | H x => exact congrArg J.mkQ (shufflePolynomial_smul_left a r f x) }
  exact (destabilizingSpace a (slope c η) d).liftQ L (by
    intro f hf
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro g
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (destabilizing_shuffle_left a c η hc hs hf g))

@[simp] lemma shuffleB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : slope c η d = slope c η e) (f : S d) (g : S e) :
    shuffleB a c η hc d e hs ((destabilizingSpace a (slope c η) d).mkQ f)
      ((destabilizingSpace a (slope c η) e).mkQ g) =
    (destabilizingSpace a (slope c η) (d+e)).mkQ (shufflePolynomial a f g) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
