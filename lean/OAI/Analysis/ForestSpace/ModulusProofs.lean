import OAI.Analysis.ForestSpace.Moduli
import OAI.Analysis.ForestSpace.Projections

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section ModulusDefinitions

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E}

 theorem cofinite_nontrivial (hI : ¬FiniteDimensional ℝ E) (F : Cofinite E) :
    Nontrivial F.val := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hss
  let := hss
  let : FiniteDimensional ℝ F.val := Module.Finite.of_injective
    (0 : F.val →ₗ[ℝ] ℝ) (fun _ _ _ => Subsingleton.elim _ _)
  let : FiniteDimensional ℝ (E ⧸ F.val) := F.property.2
  exact hI (Module.Finite.of_submodule_quotient F.val)

 theorem cofinite_exists_unit (hI : ¬FiniteDimensional ℝ E) (F : Cofinite E) :
    ∃ y : E, y ∈ F.val ∧ ‖y‖ = 1 := by
  let := cofinite_nontrivial hI F
  obtain ⟨y,hy⟩ := exists_norm_eq F.val zero_le_one
  exact ⟨y,y.property,hy⟩

 theorem cofiniteKernel {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] (f : E →L[ℝ] G) :
    IsClosed (f.toLinearMap.ker : Set E) ∧ FiniteDimensional ℝ (E ⧸ f.toLinearMap.ker) := by
  exact ⟨f.isClosed_ker, Module.Finite.equiv f.toLinearMap.quotKerEquivRange.symm⟩

 theorem averageValues_nonempty (hI : ¬FiniteDimensional ℝ E)
    (t : ℝ) (x : E) (F : Cofinite E) : (averageValues E norm t x F).Nonempty := by
  obtain ⟨y,hy,hyn⟩ := cofinite_exists_unit hI F
  exact ⟨_,y,hy,hyn,rfl⟩

 theorem averageValues_bddBelow (t : ℝ) (x : E) (F : Cofinite E) :
    BddBelow (averageValues E norm t x F) := by
  refine ⟨-1, ?_⟩
  rintro a ⟨y,hy,hyn,rfl⟩
  linarith [norm_nonneg (x+t•y),norm_nonneg (x-t•y)]

 theorem averageInner_le (hI : ¬FiniteDimensional ℝ E)
    {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : ‖x‖ = 1) (F : Cofinite E) :
    averageInner E norm t x F ≤ t := by
  obtain ⟨y,hy,hyn⟩ := cofinite_exists_unit hI F
  have hp := norm_add_le x (t•y)
  have hm := norm_sub_le x (t•y)
  rw [hx,norm_smul,Real.norm_of_nonneg ht,hyn,mul_one] at hp hm
  have hh : averageInner E norm t x F ≤ (‖x+t•y‖+‖x-t•y‖)/2-1 :=
    csInf_le (averageValues_bddBelow t x F) ⟨y,hy,hyn,rfl⟩
  linarith

 theorem averageCenter_bddAbove (hI : ¬FiniteDimensional ℝ E)
    {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : ‖x‖ = 1) :
    BddAbove (Set.range (averageInner E norm t x)) := by
  exact ⟨t, fun a ⟨F,hF⟩ => hF ▸ averageInner_le hI ht hx F⟩

/-- A quantitative subspace formulation implies the literal inf-sup-inf bound.
The nonempty-inner-sphere and bounded-supremum details are explicit. -/
 theorem averageModulus_lower_of_subspaces (hI : ¬FiniteDimensional ℝ E)
    {t L : ℝ} (ht : 0 ≤ t)
    (h : ∀ x : E, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε → ∃ F : Cofinite E,
      ∀ y : E, y ∈ F.val → ‖y‖ = 1 → L-ε ≤ (‖x+t•y‖+‖x-t•y‖)/2-1) :
    L ≤ averageModulus E norm t := by
  have hunit : ∃ x : E, ‖x‖ = 1 := by
    obtain ⟨x,hx,hxn⟩ := cofinite_exists_unit hI (cofiniteTop E)
    exact ⟨x,hxn⟩
  apply le_csInf
  · obtain ⟨x,hx⟩ := hunit
    exact ⟨_,x,hx,rfl⟩
  · rintro a ⟨x,hx,rfl⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨F,hF⟩ := h x hx ε hε
    have hb : L-ε ≤ averageInner E norm t x F := by
      apply le_csInf (averageValues_nonempty hI t x F)
      rintro b ⟨y,hy,hyn,rfl⟩
      exact hF y hy hyn
    have hs : averageInner E norm t x F ≤ averageCenter E norm t x :=
      le_csSup (averageCenter_bddAbove hI ht hx) ⟨F,rfl⟩
    linarith

end ModulusDefinitions

section ForestModulus
variable {V : Type} [PartialOrder V]

 theorem sqrt_perturbation {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (h1 : 1 ≤ a+δ) : Real.sqrt (1+b) ≤ Real.sqrt (a^2+b)+δ := by
  have hs := Real.sq_sqrt (show 0 ≤ a^2+b by positivity)
  have has : a ≤ Real.sqrt (a^2+b) := (Real.le_sqrt ha (show 0 ≤ a^2+b by positivity)).mpr (by linarith)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [mul_nonneg hδ (sub_nonneg.mpr has), sq_nonneg (a+δ-1)]

theorem pair_perturbation {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x a y : E) (b : ℝ) (hb : 0 ≤ b) (hx : ‖x‖ = 1)
    (hpair : Real.sqrt (‖a‖^2+b) ≤ (‖a+y‖+‖a-y‖)/2) :
    Real.sqrt (1+b) ≤ (‖x+y‖+‖x-y‖)/2+2*‖x-a‖ := by
  let δ : ℝ := ‖x-a‖
  have hc : 1 ≤ ‖a‖+δ := by
    have hh := norm_add_le a (x-a)
    have he : a+(x-a) = x := by abel
    rw [he, hx] at hh
    exact hh
  have hroot := sqrt_perturbation (norm_nonneg a) hb (norm_nonneg (x-a)) hc
  have hp : ‖a+y‖ ≤ ‖x+y‖+δ := by
    have hh := norm_sub_le (x+y) (x-a)
    have he : x+y-(x-a) = a+y := by abel
    rwa [he] at hh
  have hm : ‖a-y‖ ≤ ‖x-y‖+δ := by
    have hh := norm_sub_le (x-y) (x-a)
    have he : x-y-(x-a) = a-y := by abel
    rwa [he] at hh
  change Real.sqrt (1+b) ≤ (‖x+y‖+‖x-y‖)/2+2*δ
  linarith

 theorem forest_average_head (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Finset V) (hH : IsLowerSet (H : Set V)) (x y : X V)
    (hx : ‖x‖ = 1) (hy : y ∈ (finiteCoordinates H).toLinearMap.ker)
    (hyn : ‖y‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (1+t^2/12) ≤ (‖x+t•y‖+‖x-t•y‖)/2+2*‖x-PX H hH x‖ := by
  have hy' := annihilates_of_mem_ker_coordinates H hH hy
  have hpair := paired_estimate hF hAnc (H : Set V) hH
    (P (H : Set V) hH x) (t • (y : FullDual V))
    (annihilates_P (H : Set V) hH x) (hy'.smul t)
  have hyn' : ‖(y : FullDual V)‖ = 1 := hyn
  rw [norm_smul, Real.norm_of_nonneg ht, hyn', mul_one] at hpair
  have hh := pair_perturbation (x : FullDual V) (P (H : Set V) hH x)
    (t • (y : FullDual V)) (t^2/12) (by positivity) hx hpair
  exact hh

/-- The midpoint bound for every coordinate-completion forest,
using the averaged signed excess rather than its maximum. -/
 theorem forest_average_modulus [Infinite V]
    (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (t : ℝ) (ht : 0 < t) :
    Real.sqrt (1+t^2/12)-1 ≤ averageModulus (X V) norm t := by
  apply averageModulus_lower_of_subspaces (E := X V) (not_finiteDimensional_X (V := V)) ht.le
  intro x hx ε hε
  obtain ⟨H,hH,hclose⟩ := exists_head_approx hAnc x (ε/4) (by positivity)
  let F : Cofinite (X V) := ⟨(finiteCoordinates H).toLinearMap.ker,
    (finiteCoordinates H).isClosed_ker, finiteCoordinates_kernel_finite H⟩
  refine ⟨F, ?_⟩
  intro y hy hyn
  have hh := forest_average_head hF hAnc H hH x y hx hy hyn t ht.le
  linarith

end ForestModulus

end

end ForestSpace

end OAI
