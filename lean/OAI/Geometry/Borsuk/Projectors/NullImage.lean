import Mathlib

namespace OAI

namespace BorsukNine
open Set MeasureTheory
open scoped Topology

section NullImage
variable {D T : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

lemma differentiable_image_null_of_projection (μ : Measure T) [μ.IsAddHaarMeasure]
    (p : T →L[ℝ] D) (hp : Function.Surjective p) (hpn : ¬ Function.Injective p)
    {f : D → T} {S : Set D} (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) : μ (f '' S) = 0 := by
  let g : T → T := fun x => f (p x)
  let g' : T → T →L[ℝ] T := fun x => (fderiv ℝ f (p x)).comp p
  have hd : ∀ x ∈ p ⁻¹' S, HasFDerivWithinAt g (g' x) (p ⁻¹' S) x := by
    intro x hx
    exact ((hf (p x) hx).hasFDerivAt.comp x p.hasFDerivAt).hasFDerivWithinAt
  have hdet : ∀ x ∈ p ⁻¹' S, (g' x).det = 0 := by
    intro x _
    change ((g' x).toLinearMap).det = 0
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    apply mt LinearMap.ker_eq_bot.mp
    intro hinj
    exact hpn (fun u v huv => hinj (by change fderiv ℝ f (p x) (p u) = fderiv ℝ f (p x) (p v); rw [huv]))
  have he : g '' (p ⁻¹' S) = f '' S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨p x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨z,rfl⟩ := hp x
      exact ⟨z,hx,rfl⟩
  rw [← he]
  exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ hd hdet

end NullImage

noncomputable def initialProjection (n m : ℕ) (h : n ≤ m) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x (Fin.castLE h i))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

lemma initialProjection_apply (n m : ℕ) (h : n ≤ m) (x : EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    initialProjection n m h x i = x (Fin.castLE h i) := rfl

lemma initialProjection_surjective (n m : ℕ) (h : n ≤ m) :
    Function.Surjective (initialProjection n m h) := by
  intro x
  refine ⟨WithLp.toLp 2 (fun j : Fin m => if h : j.val < n then x ⟨j.val,h⟩ else 0),?_⟩
  apply PiLp.ext
  intro i
  change (if hj : i.val < n then x ⟨i.val,hj⟩ else 0) = x i
  simp only [dite_eq_left i.isLt]

lemma initialProjection_not_injective (n m : ℕ) (h : n < m) :
    ¬ Function.Injective (initialProjection n m h.le) := by
  intro hh
  have hl := LinearMap.finrank_le_finrank_of_injective
    (f := (initialProjection n m h.le).toLinearMap) hh
  simp only [finrank_euclideanSpace_fin] at hl
  omega

lemma differentiable_image_null_of_dim_lt (n m : ℕ) (h : n < m)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    volume (f '' S) = 0 :=
  differentiable_image_null_of_projection volume (initialProjection n m h.le)
    (initialProjection_surjective n m h.le) (initialProjection_not_injective n m h) hf

lemma open_exists_not_mem_differentiable_image (n m : ℕ) (h : n < m)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y ∈ U, y ∉ f '' S := by
  by_contra hn
  push Not at hn
  have hl : volume U ≤ volume (f '' S) := measure_mono hn
  rw [differentiable_image_null_of_dim_lt n m h hf] at hl
  exact (hU.measure_ne_zero volume hne) (le_antisymm hl (zero_le))

end BorsukNine

end OAI
