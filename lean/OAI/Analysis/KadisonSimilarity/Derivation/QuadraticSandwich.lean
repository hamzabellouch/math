import OAI.Analysis.KadisonSimilarity.Derivation.BoundedHomRow
import OAI.Analysis.Naimark.States
import Mathlib.Analysis.Convex.Cone.Extension

namespace OAI

/-! The separation step in Haagerup's cyclic-similarity argument. Equal
finite square sums with comparable orbit norms give a positive functional
between the corresponding quadratic forms. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def listSquareSum (L : List A) : selfAdjoint A :=
  (L.map fun a => (⟨star a * a, (star_mul_self_nonneg a).isSelfAdjoint⟩ : selfAdjoint A)).sum

def listOrbitSum (π : BoundedUnitalHom A H) (ξ : H) (L : List A) : ℝ :=
  (L.map fun a => ‖π.1 a ξ‖ ^ 2).sum

@[simp] theorem listSquareSum_nil : listSquareSum ([] : List A) = 0 := rfl
@[simp] theorem listSquareSum_singleton_coe (a : A) :
    (listSquareSum [a] : A) = star a * a := by simp [listSquareSum]
omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
@[simp] theorem listOrbitSum_nil (π : BoundedUnitalHom A H) (ξ : H) :
    listOrbitSum π ξ [] = 0 := rfl

@[simp] theorem listSquareSum_append (L K : List A) :
    listSquareSum (L ++ K) = listSquareSum L + listSquareSum K := by
  simp [listSquareSum]

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
@[simp] theorem listOrbitSum_append (π : BoundedUnitalHom A H) (ξ : H) (L K : List A) :
    listOrbitSum π ξ (L ++ K) = listOrbitSum π ξ L + listOrbitSum π ξ K := by
  simp [listOrbitSum]

theorem listSquareSum_scale (r : ℝ) (hr : 0 ≤ r) (L : List A) :
    listSquareSum (L.map fun a => Real.sqrt r • a) = r • listSquareSum L := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, listSquareSum, List.sum_cons] at ih ⊢
    rw [ih, smul_add]
    congr 1
    apply Subtype.ext
    change star (Real.sqrt r • a) * (Real.sqrt r • a) = r • (star a * a)
    rw [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, Real.mul_self_sqrt hr]

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
theorem listOrbitSum_scale (π : BoundedUnitalHom A H) (ξ : H)
    (r : ℝ) (hr : 0 ≤ r) (L : List A) :
    listOrbitSum π ξ (L.map fun a => Real.sqrt r • a) = r * listOrbitSum π ξ L := by
  have he (a : A) : ‖π.1 (Real.sqrt r • a) ξ‖ ^ 2 = r * ‖π.1 a ξ‖ ^ 2 := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, smul_apply,
      norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg r), mul_pow,
      Real.sq_sqrt hr]
  simp only [listOrbitSum, List.map_map, Function.comp_def, he]
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

def orbitSandwichCone (π : BoundedUnitalHom A H) (ξ : H) (K : ℝ) :
    PointedCone ℝ (selfAdjoint A × ℝ) where
  carrier := {z | ∃ a b : List A,
    z.1 = listSquareSum a - listSquareSum b ∧
      z.2 ≤ listOrbitSum π ξ a - K * listOrbitSum π ξ b}
  zero_mem' := ⟨[], [], by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, hx, hr⟩ ⟨c, d, hy, hs⟩
    refine ⟨a ++ c, b ++ d, ?_, ?_⟩
    · simp only [Prod.fst_add, listSquareSum_append, hx, hy]; abel
    · simp only [Prod.snd_add, listOrbitSum_append]
      linarith
  smul_mem' := by
    rintro ⟨r, hr⟩ x ⟨a, b, hx, hs⟩
    refine ⟨a.map (fun c => Real.sqrt r • c), b.map (fun c => Real.sqrt r • c), ?_, ?_⟩
    · simp only [Prod.smul_fst, Nonneg.mk_smul, listSquareSum_scale r hr, hx, smul_sub]
    · simp only [Prod.smul_snd, Nonneg.mk_smul, smul_eq_mul, listOrbitSum_scale π ξ r hr]
      nlinarith [mul_le_mul_of_nonneg_left hs hr]

omit [CompleteSpace H] in
/-- The only hypothesis is the finite quadratic comparison. -/
theorem exists_positive_orbit_sandwich (π : BoundedUnitalHom A H) (ξ : H) (K : ℝ)
    (hcompare : ∀ a b : List A, listSquareSum a = listSquareSum b →
      listOrbitSum π ξ a ≤ K * listOrbitSum π ξ b) :
    ∃ ω : A →ₚ[ℂ] ℂ, ∀ a : A,
      ‖π.1 a ξ‖ ^ 2 ≤ (ω (star a * a)).re ∧
        (ω (star a * a)).re ≤ K * ‖π.1 a ξ‖ ^ 2 := by
  let E := selfAdjoint A
  let P : Submodule ℝ (E × ℝ) := (LinearMap.inr ℝ E ℝ).range
  let f : (E × ℝ) →ₗ.[ℝ] ℝ := (-LinearMap.snd ℝ E ℝ).toPMap P
  let C := orbitSandwichCone π ξ K
  have hnonneg (x : f.domain) (hx : (x : E × ℝ) ∈ C) : 0 ≤ f x := by
    obtain ⟨r, hr⟩ := x.property
    obtain ⟨a, b, hab, hs⟩ := hx
    have hx0 : ((x : E × ℝ)).1 = 0 := by rw [← hr]; rfl
    have he : listSquareSum a = listSquareSum b := sub_eq_zero.mp (hab.symm.trans hx0)
    have hc := hcompare a b he
    change 0 ≤ -((x : E × ℝ)).2
    linarith
  have hdense (y : E × ℝ) : ∃ x : f.domain, (x : E × ℝ) + y ∈ C := by
    let a := CFC.sqrt (y.1 : A)⁺
    let b := CFC.sqrt (y.1 : A)⁻
    have ha : (star a * a) = (y.1 : A)⁺ := by
      rw [(CFC.sqrt_nonneg _).star_eq, CFC.sqrt_mul_sqrt_self _ (CFC.posPart_nonneg _)]
    have hb : (star b * b) = (y.1 : A)⁻ := by
      rw [(CFC.sqrt_nonneg _).star_eq, CFC.sqrt_mul_sqrt_self _ (CFC.negPart_nonneg _)]
    let r := listOrbitSum π ξ [a] - K * listOrbitSum π ξ [b] - y.2
    refine ⟨⟨(0, r), ⟨r, rfl⟩⟩, [a], [b], ?_, ?_⟩
    · apply Subtype.ext
      simp only [Prod.fst_add, zero_add, AddSubgroupClass.coe_sub,
        listSquareSum_singleton_coe]
      rw [ha, hb, CFC.posPart_sub_negPart _ y.1.property]
    · change r + y.2 ≤ _
      dsimp [r]
      linarith
  obtain ⟨g, hg, hgpos⟩ := riesz_extension C f hnonneg hdense
  have hvertical (r : ℝ) : g (0, r) = -r := hg ⟨(0, r), ⟨r, rfl⟩⟩
  let φ : E →ₗ[ℝ] ℝ := g.comp (LinearMap.inl ℝ E ℝ)
  have hgformula (x : E) (r : ℝ) : g (x, r) = φ x - r := by
    have he : (x, r) = (x, (0 : ℝ)) + (0, r) := by simp
    rw [he, map_add, hvertical]
    rfl
  have hbounds (a : A) : ‖π.1 a ξ‖ ^ 2 ≤ φ (listSquareSum [a]) ∧
      φ (listSquareSum [a]) ≤ K * ‖π.1 a ξ‖ ^ 2 := by
    have hlo := hgpos (listSquareSum [a], ‖π.1 a ξ‖ ^ 2)
      ⟨[a], [], by simp [listOrbitSum]⟩
    have hhi := hgpos (-listSquareSum [a], -K * ‖π.1 a ξ‖ ^ 2)
      ⟨[], [a], by simp [listOrbitSum]⟩
    rw [hgformula] at hlo hhi
    simp only [map_neg] at hhi
    constructor <;> linarith
  have hφpos (x : A) (hx : 0 ≤ x) : 0 ≤ φ ⟨x, hx.isSelfAdjoint⟩ := by
    have he : listSquareSum [CFC.sqrt x] = ⟨x, hx.isSelfAdjoint⟩ := by
      apply Subtype.ext
      simp only [listSquareSum_singleton_coe]
      rw [(CFC.sqrt_nonneg _).star_eq, CFC.sqrt_mul_sqrt_self _ hx]
    exact (sq_nonneg _).trans (he ▸ (hbounds (CFC.sqrt x)).1)
  let ω : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ (NaimarkZFC.selfAdjointComplexify φ)
    (fun x hx => by
      rw [show x = (⟨x, hx.isSelfAdjoint⟩ : selfAdjoint A) from rfl,
        NaimarkZFC.selfAdjointComplexify_coe]
      exact ⟨hφpos x hx, by simp⟩)
  refine ⟨ω, fun a => ?_⟩
  change _ ≤ (NaimarkZFC.selfAdjointComplexify φ (star a * a)).re ∧ _
  have he : (star a * a) = (listSquareSum [a] : A) := (listSquareSum_singleton_coe a).symm
  change _ ≤ (NaimarkZFC.selfAdjointComplexify φ (star a * a)).re ∧
    (NaimarkZFC.selfAdjointComplexify φ (star a * a)).re ≤ _
  rw [he, NaimarkZFC.selfAdjointComplexify_coe]
  exact hbounds a

end KadisonSimilarity

end

end OAI
