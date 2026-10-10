import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Chains.NormalizedTuples
import OAI.CategoryTheory.Thomason.Gray.CylinderAssembly
import OAI.CategoryTheory.Thomason.Simplicial.RealizedSimplexWeakEquivalences
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import OAI.CategoryTheory.Thomason.Transfer.WeakFactorizationRecognition
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

namespace OAI

section

/-!
# The interval specialization of the Alexander--Whitney diagonal

Only the last two cuts of the classical diagonal survive after mapping the
right factor to the normalized interval complex. We give this map explicitly.
Its chain identity and naturality are the precise specialization of
Goerss--Jardine, IV.2, Remark 2.5, retained as published inputs in this phase.
Positivity, the right counit and both endpoints are proved from the formula.
-/

namespace Thomason.Construction.SimplexComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

/-- The last vertex of a basis simplex decides its endpoint summand. -/
noncomputable def awEnd {m : ℕ} (θ : Fin (m + 1) →o Fin 2) (a : Fin 2) (p : ℕ) :
    Chains m p →ₗ[ℤ] Chains m p :=
  Finsupp.linearCombination ℤ (fun s =>
    if θ (s (Fin.last p)) = a then Finsupp.single s 1 else 0)

/-- The penultimate cut contributes an edge precisely when its interval
vertices are 0 and 1. -/
noncomputable def awEdge {m : ℕ} (θ : Fin (m + 1) →o Fin 2) (p : ℕ) :
    Chains m (p + 1) →ₗ[ℤ] Chains m p :=
  Finsupp.linearCombination ℤ (fun s =>
    if θ (s (Fin.last p).castSucc) = 0 ∧ θ (s (Fin.last (p + 1))) = 1 then
      Finsupp.single (deleteVertex s (Fin.last (p + 1))) 1 else 0)

noncomputable def awApp (h : NormalizedSimplexIdentities) {m : ℕ}
    (θ : Fin (m + 1) →o Fin 2) :
    (p : ℕ) → Chains m p →+ (rightCylinder (directedComplex m (h.squared m))).group p
  | 0 => (awEnd θ 0 0).toAddMonoidHom.prod (awEnd θ 1 0).toAddMonoidHom
  | p + 1 => (awEnd θ 0 (p + 1)).toAddMonoidHom.prod
      ((awEnd θ 1 (p + 1)).toAddMonoidHom.prod (awEdge θ p).toAddMonoidHom)

@[simp]
theorem awEnd_single {m p : ℕ} (θ : Fin (m + 1) →o Fin 2) (a : Fin 2)
    (s : Basis m p) (z : ℤ) :
    awEnd θ a p (Finsupp.single s z) = if θ (s (Fin.last p)) = a then
      Finsupp.single s z else 0 := by
  classical
  simp only [awEnd, Finsupp.linearCombination_single]
  split <;> simp_all

@[simp]
theorem awEdge_single {m p : ℕ} (θ : Fin (m + 1) →o Fin 2)
    (s : Basis m (p + 1)) (z : ℤ) :
    awEdge θ p (Finsupp.single s z) =
      if θ (s (Fin.last p).castSucc) = 0 ∧ θ (s (Fin.last (p + 1))) = 1 then
        Finsupp.single (deleteVertex s (Fin.last (p + 1))) z else 0 := by
  classical
  simp only [awEdge, Finsupp.linearCombination_single]
  split <;> simp_all

theorem awEnd_positive {m p : ℕ} (θ : Fin (m + 1) →o Fin 2) (a : Fin 2)
    {x : Chains m p} (hx : x ∈ positive m p) : awEnd θ a p x ∈ positive m p := by
  classical
  intro t
  simp only [awEnd, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg (hx s)
  split <;> simp only [Finsupp.single_apply, Finsupp.zero_apply] <;> (try split_ifs) <;> norm_num

theorem awEdge_positive {m p : ℕ} (θ : Fin (m + 1) →o Fin 2)
    {x : Chains m (p + 1)} (hx : x ∈ positive m (p + 1)) :
    awEdge θ p x ∈ positive m p := by
  classical
  intro t
  simp only [awEdge, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg (hx s)
  split <;> simp only [Finsupp.single_apply, Finsupp.zero_apply] <;> (try split_ifs) <;> norm_num

theorem awEnd_sum {m p : ℕ} (θ : Fin (m + 1) →o Fin 2) (x : Chains m p) :
    awEnd θ 0 p x + awEnd θ 1 p x = x := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add s z x _ _ ih =>
    have hv : θ (s (Fin.last p)) = 0 ∨ θ (s (Fin.last p)) = 1 := by omega
    have hs : awEnd θ 0 p (Finsupp.single s z) +
        awEnd θ 1 p (Finsupp.single s z) = Finsupp.single s z := by
      rcases hv with hv | hv <;> simp [hv]
    rw [map_add, map_add]
    calc
      _ = (awEnd θ 0 p (Finsupp.single s z) + awEnd θ 1 p (Finsupp.single s z)) +
          (awEnd θ 0 p x + awEnd θ 1 p x) := by abel
      _ = _ := congrArg₂ (· + ·) hs ih

theorem awEnd_const {m p : ℕ} (a b : Fin 2) (x : Chains m p) :
    awEnd (OrderHom.const _ a) b p x = if a = b then x else 0 := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add s z x _ _ ih =>
    simp only [map_add, awEnd_single, ih]
    change (if a = b then Finsupp.single s z else 0) + (if a = b then x else 0) = _
    split_ifs <;> simp

theorem awEdge_const {m p : ℕ} (a : Fin 2) (x : Chains m (p + 1)) :
    awEdge (OrderHom.const _ a) p x = 0 := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add s z x _ _ ih =>
    have ha : ¬ (a = 0 ∧ a = 1) := by omega
    simp [ha, ih]

/-- Only the classical chain identity and its ordinal naturality are left
as hypotheses. All objects and maps here have their explicit formulas. -/
structure AlexanderWhitneyInput (h : NormalizedSimplexIdentities) : Prop where
  differential {m : ℕ} (θ : Fin (m + 1) →o Fin 2) (p : ℕ) (x : Chains m (p + 1)) :
    awApp h θ p (SimplexComplex.differential m p x) =
      (rightCylinder (directedComplex m (h.squared m))).differential p (awApp h θ (p + 1) x)
  naturality {l m : ℕ} (a : Fin (l + 1) →o Fin (m + 1)) (θ : Fin (m + 1) →o Fin 2)
      (p : ℕ) (x : Chains l p) :
    (RightCylinder.map (directedMap (h.squared l) (h.squared m) a (h.naturality a))).app p
      (awApp h (θ.comp a) p x) = awApp h θ p (mapChains a p x)

namespace AlexanderWhitneyInput

variable {h : NormalizedSimplexIdentities} (aw : AlexanderWhitneyInput h)

/-- The positive augmented chain map obtained from the explicit AW formula. -/
noncomputable def chainMap {m : ℕ} (θ : Fin (m + 1) →o Fin 2) :
    Hom (directedComplex m (h.squared m)) (rightCylinder (directedComplex m (h.squared m))) where
  app := awApp h θ
  differential := aw.differential θ
  augmentation x := by
    change augmentation m (awEnd θ 0 0 x) + augmentation m (awEnd θ 1 0 x) = augmentation m x
    rw [← map_add, awEnd_sum]
  positive p x hx := by
    cases p with
    | zero => exact ⟨awEnd_positive θ 0 hx, awEnd_positive θ 1 hx⟩
    | succ p => exact ⟨awEnd_positive θ 0 hx, awEnd_positive θ 1 hx, awEdge_positive θ hx⟩

theorem projection_chainMap {m : ℕ} (θ : Fin (m + 1) →o Fin 2) (p : ℕ) (x : Chains m p) :
    (RightCylinder.projection (directedComplex m (h.squared m))).app p
      ((aw.chainMap θ).app p x) = x := by
  cases p <;> exact awEnd_sum θ x

theorem chainMap_const {m : ℕ} (a : Bool) (p : ℕ) (x : Chains m p) :
    (aw.chainMap (OrderHom.const _ (if a then 1 else 0))).app p x =
      (RightCylinder.endpoint (directedComplex m (h.squared m)) a).app p x := by
  cases p <;> cases a <;>
    simp [chainMap, awApp, RightCylinder.endpoint, RightCylinder.endpointMap,
      awEnd_const, awEdge_const]

end AlexanderWhitneyInput
end Thomason.Construction.SimplexComplex

end

section

/-! # The boundary identity for the explicit interval diagonal

Splitting the alternating boundary into its last face and the other faces
computes the defect of the endpoint projections. Their defect is exactly the
edge term. The edge identity then follows from square-zero.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators
open _root_.OAI.Thomason.Construction.DirectedComplex

/-- Deleting a vertex other than the last preserves the last vertex. -/
theorem deleteVertex_last_castSucc {m p : ℕ} (s : Basis m (p + 1)) (i : Fin (p + 1)) :
    deleteVertex s i.castSucc (Fin.last p) = s (Fin.last (p + 1)) := by
  change s (i.castSucc.succAbove (Fin.last p)) = _
  rw [Fin.succAbove_castSucc_of_le _ _ (Fin.le_last i)]
  rfl

/-- Deleting the last vertex exposes the penultimate vertex. -/
theorem deleteVertex_last_last {m p : ℕ} (s : Basis m (p + 1)) :
    deleteVertex s (Fin.last (p + 1)) (Fin.last p) = s (Fin.last p).castSucc := by
  change s ((Fin.last (p + 1)).succAbove (Fin.last p)) = _
  rw [Fin.succAbove_last_apply]

/-- Boundary projection is determined by the two final vertex labels. -/
theorem awEnd_boundary_expansion {m p : ℕ} (θ : Fin (m + 1) →o Fin 2)
    (a : Fin 2) (s : Basis m (p + 1)) :
    awEnd θ a p (differentialBasis m p s) =
      (∑ i : Fin (p + 1), if θ (s (Fin.last (p + 1))) = a then
        Finsupp.single (deleteVertex s i.castSucc) ((-1 : ℤ) ^ i.val) else 0) +
      (if θ (s (Fin.last p).castSucc) = a then
        Finsupp.single (deleteVertex s (Fin.last (p + 1))) ((-1 : ℤ) ^ (p + 1)) else 0) := by
  classical
  rw [differentialBasis, map_sum, Fin.sum_univ_castSucc]
  simp only [awEnd_single, deleteVertex_last_castSucc, deleteVertex_last_last,
    Fin.val_castSucc, Fin.val_last]

/-- The final endpoint's boundary defect is the signed interval-edge term. -/
theorem awEnd_one_differential_basis {m p : ℕ} (θ : Fin (m + 1) →o Fin 2)
    (s : Basis m (p + 1)) :
    awEnd θ 1 p (differentialBasis m p s) =
      differential m p (awEnd θ 1 (p + 1) (Finsupp.single s 1)) +
        ((-1 : ℤ) ^ p) • awEdge θ p (Finsupp.single s 1) := by
  classical
  have hle : θ (s (Fin.last p).castSucc) ≤ θ (s (Fin.last (p + 1))) :=
    θ.monotone (s.monotone (by exact Fin.le_last _))
  have hlast : θ (s (Fin.last (p + 1))) = 0 ∨ θ (s (Fin.last (p + 1))) = 1 := by omega
  have hprev : θ (s (Fin.last p).castSucc) = 0 ∨ θ (s (Fin.last p).castSucc) = 1 := by omega
  rw [awEnd_boundary_expansion, awEnd_single, awEdge_single]
  rcases hlast with hl | hl <;> rcases hprev with hp | hp
  · simp [hl, hp]
  · omega
  · simp only [hl, hp, zero_ne_one, and_self, ↓reduceIte,
      differential_single, one_smul]
    conv_rhs => rw [differentialBasis, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Finsupp.smul_single, smul_eq_mul,
      mul_one, pow_succ, mul_neg_one, Finsupp.single_neg]
    abel
  · simp only [hl, hp, one_ne_zero, and_true,
      ↓reduceIte, smul_zero, add_zero, differential_single, one_smul]
    conv_rhs => rw [differentialBasis, Fin.sum_univ_castSucc]
    rfl

/-- The endpoint defect formula extends to all normalized chains by linearity. -/
theorem awEnd_one_differential {m p : ℕ} (θ : Fin (m + 1) →o Fin 2)
    (x : Chains m (p + 1)) :
    awEnd θ 1 p (differential m p x) =
      differential m p (awEnd θ 1 (p + 1) x) + ((-1 : ℤ) ^ p) • awEdge θ p x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]; abel
  | single s z =>
    have hsz : (Finsupp.single s z : Chains m (p + 1)) = z • Finsupp.single s 1 := by
      simp
    rw [hsz]
    simp only [map_smul, differential_single, one_smul]
    rw [awEnd_one_differential_basis, smul_add, smul_comm z]

/-- The initial endpoint has the opposite boundary defect. -/
theorem awEnd_zero_differential {m p : ℕ} (θ : Fin (m + 1) →o Fin 2)
    (x : Chains m (p + 1)) :
    awEnd θ 0 p (differential m p x) =
      differential m p (awEnd θ 0 (p + 1) x) - ((-1 : ℤ) ^ p) • awEdge θ p x := by
  have h := awEnd_one_differential θ x
  have hsource := congrArg (differential m p) (awEnd_sum θ x)
  rw [map_add] at hsource
  apply eq_sub_iff_add_eq.mpr
  apply add_right_cancel (b := differential m p (awEnd θ 1 (p + 1) x))
  calc
    _ = awEnd θ 0 p (differential m p x) +
        (differential m p (awEnd θ 1 (p + 1) x) +
          ((-1 : ℤ) ^ p) • awEdge θ p x) := by abel
    _ = awEnd θ 0 p (differential m p x) + awEnd θ 1 p (differential m p x) := by rw [← h]
    _ = differential m p x := awEnd_sum θ _
    _ = _ := hsource.symm

/-- The interval-edge operator commutes with the normalized differential. -/
theorem awEdge_differential {m p : ℕ} (θ : Fin (m + 1) →o Fin 2)
    (x : Chains m (p + 2)) :
    awEdge θ p (differential m (p + 1) x) =
      differential m p (awEdge θ (p + 1) x) := by
  have h0 := awEnd_one_differential θ (differential m (p + 1) x)
  rw [boundarySquared m p x, map_zero] at h0
  have h1 := congrArg (differential m p) (awEnd_one_differential θ x)
  simp only [map_add, map_smul] at h1
  rw [boundarySquared m p (awEnd θ 1 (p + 1 + 1) x), zero_add] at h1
  rw [h1, pow_succ, mul_neg_one, neg_smul] at h0
  have he : ((-1 : ℤ) ^ p) • awEdge θ p (differential m (p + 1) x) =
      ((-1 : ℤ) ^ p) • differential m p (awEdge θ (p + 1) x) := by
    calc
      _ = ((-1 : ℤ) ^ p) • differential m p (awEdge θ (p + 1) x) +
          (-(((-1 : ℤ) ^ p) • differential m p (awEdge θ (p + 1) x)) +
            ((-1 : ℤ) ^ p) • awEdge θ p (differential m (p + 1) x)) := by abel
      _ = _ := by rw [← h0, add_zero]
  have hsq : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← mul_pow]
    norm_num
  have := congrArg (fun y => ((-1 : ℤ) ^ p) • y) he
  simpa only [smul_smul, hsq, one_smul] using this

/-- The explicit AW interval formula is a chain map, without a published input. -/
theorem awApp_differential (h : NormalizedSimplexIdentities) {m : ℕ}
    (θ : Fin (m + 1) →o Fin 2) (p : ℕ) (x : Chains m (p + 1)) :
    awApp h θ p (differential m p x) =
      (rightCylinder (directedComplex m (h.squared m))).differential p
        (awApp h θ (p + 1) x) := by
  cases p with
  | zero =>
    apply Prod.ext
    · simpa [awApp, RightCylinder.differential, directedComplex, rightCylinder] using
        awEnd_zero_differential θ x
    · simpa [awApp, RightCylinder.differential, directedComplex, rightCylinder] using
        awEnd_one_differential θ x
  | succ p =>
    exact Prod.ext (awEnd_zero_differential θ x)
      (Prod.ext (awEnd_one_differential θ x) (awEdge_differential θ x))

end Thomason.Construction.SimplexComplex

end

section

/-! # Naturality of the explicit interval diagonal

The endpoint terms depend only on the image's last vertex. For the edge term,
a collapse at the final two vertices is incompatible with crossing the
interval; every other collapse remains after the last vertex is deleted.
-/

namespace Thomason.Construction.SimplexComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

/-- The final label of a normalized image is the label of its final vertex. -/
theorem awEnd_mapBasis {l m p : ℕ} (a : Fin (l + 1) →o Fin (m + 1))
    (θ : Fin (m + 1) →o Fin 2) (e : Fin 2) (s : Basis l p) :
    awEnd θ e p (mapBasis a p s) =
      if θ (a (s (Fin.last p))) = e then mapBasis a p s else 0 := by
  classical
  by_cases ha : StrictMono (fun i => a (s i))
  · simp only [mapBasis, dite_eq_left ha, awEnd_single]
    rfl
  · simp only [mapBasis, dite_eq_right ha, map_zero, ite_self]

/-- Endpoint projection commutes with every normalized ordinal map. -/
theorem awEnd_naturality {l m p : ℕ} (a : Fin (l + 1) →o Fin (m + 1))
    (θ : Fin (m + 1) →o Fin 2) (e : Fin 2) (x : Chains l p) :
    mapChains a p (awEnd (θ.comp a) e p x) = awEnd θ e p (mapChains a p x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single s z =>
    simp only [awEnd_single, mapChains_single, map_smul, awEnd_mapBasis]
    change mapChains a p (if θ (a (s (Fin.last p))) = e then Finsupp.single s z else 0) = _
    split_ifs <;> simp_all

/-- A strict prefix and a strict last step give a strict full vertex map. -/
theorem strictMono_of_prefix {p m : ℕ} (g : Fin (p + 2) → Fin (m + 1))
    (hp : StrictMono (fun i : Fin (p + 1) => g i.castSucc))
    (hl : g (Fin.last p).castSucc < g (Fin.last (p + 1))) : StrictMono g := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hl
  · simpa only [Fin.succ_castSucc] using hp j.castSucc_lt_succ

/-- Crossing the interval prevents a final-vertex collapse from being the only collapse. -/
theorem mapBasis_prefix_vanish {l m p : ℕ} (a : Fin (l + 1) →o Fin (m + 1))
    (θ : Fin (m + 1) →o Fin 2) (s : Basis l (p + 1))
    (ha : ¬StrictMono (fun i => a (s i)))
    (hc : θ (a (s (Fin.last p).castSucc)) = 0 ∧
      θ (a (s (Fin.last (p + 1)))) = 1) :
    mapBasis a p (deleteVertex s (Fin.last (p + 1))) = 0 := by
  have hn : ¬StrictMono (fun i => a (deleteVertex s (Fin.last (p + 1)) i)) := by
    intro hp
    apply ha
    apply strictMono_of_prefix (fun i => a (s i))
    · have hfun : (fun i => a (deleteVertex s (Fin.last (p + 1)) i)) =
          (fun i => a (s i.castSucc)) := by
        funext i
        change a (s ((Fin.last (p + 1)).succAbove i)) = a (s i.castSucc)
        rw [Fin.succAbove_last_apply]
      rwa [hfun] at hp
    · apply lt_of_not_ge
      intro he
      have h := θ.monotone he
      rw [hc.1, hc.2] at h
      exact (by decide : ¬ (1 : Fin 2) ≤ 0) h
  exact dite_eq_right hn

/-- The edge component commutes with ordinal maps on each source simplex. -/
theorem awEdge_mapBasis {l m p : ℕ} (a : Fin (l + 1) →o Fin (m + 1))
    (θ : Fin (m + 1) →o Fin 2) (s : Basis l (p + 1)) :
    mapChains a p (awEdge (θ.comp a) p (Finsupp.single s 1)) =
      awEdge θ p (mapBasis a (p + 1) s) := by
  classical
  by_cases ha : StrictMono (fun i => a (s i))
  · rw [mapBasis, dite_eq_left ha, awEdge_single, awEdge_single]
    change mapChains a p
      (if θ (a (s (Fin.last p).castSucc)) = 0 ∧ θ (a (s (Fin.last (p + 1)))) = 1 then
        Finsupp.single (deleteVertex s (Fin.last (p + 1))) 1 else 0) =
      (if θ (a (s (Fin.last p).castSucc)) = 0 ∧ θ (a (s (Fin.last (p + 1)))) = 1 then
        Finsupp.single (deleteVertex (OrderEmbedding.ofStrictMono _ ha) (Fin.last (p + 1))) 1
        else 0)
    split_ifs <;> simp only [map_zero, mapChains_single, one_smul,
      mapBasis_delete_strict a s ha]
  · rw [mapBasis, dite_eq_right ha, map_zero, awEdge_single]
    change mapChains a p
      (if θ (a (s (Fin.last p).castSucc)) = 0 ∧ θ (a (s (Fin.last (p + 1)))) = 1 then
        Finsupp.single (deleteVertex s (Fin.last (p + 1))) 1 else 0) = 0
    split_ifs with hc
    · simpa only [mapChains_single, one_smul] using mapBasis_prefix_vanish a θ s ha hc
    · exact map_zero _

/-- Edge projection commutes with every normalized ordinal map. -/
theorem awEdge_naturality {l m p : ℕ} (a : Fin (l + 1) →o Fin (m + 1))
    (θ : Fin (m + 1) →o Fin 2) (x : Chains l (p + 1)) :
    mapChains a p (awEdge (θ.comp a) p x) = awEdge θ p (mapChains a (p + 1) x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single s z =>
    have hs : (Finsupp.single s z : Chains l (p + 1)) = z • Finsupp.single s 1 := by simp
    rw [hs]
    simp only [map_smul, mapChains_single, one_smul, awEdge_mapBasis]

/-- The concrete interval diagonal is natural, without a published input. -/
theorem awApp_naturality (h : NormalizedSimplexIdentities) {l m : ℕ}
    (a : Fin (l + 1) →o Fin (m + 1)) (θ : Fin (m + 1) →o Fin 2)
    (p : ℕ) (x : Chains l p) :
    (RightCylinder.map (directedMap (h.squared l) (h.squared m) a (h.naturality a))).app p
      (awApp h (θ.comp a) p x) = awApp h θ p (mapChains a p x) := by
  cases p with
  | zero => exact Prod.ext (awEnd_naturality a θ 0 x) (awEnd_naturality a θ 1 x)
  | succ p =>
    exact Prod.ext (awEnd_naturality a θ 0 x)
      (Prod.ext (awEnd_naturality a θ 1 x) (awEdge_naturality a θ x))

/-- Both classical identities for the explicit interval diagonal are proved. -/
theorem alexanderWhitneyInput (h : NormalizedSimplexIdentities) : AlexanderWhitneyInput h where
  differential := awApp_differential h
  naturality := awApp_naturality h

end Thomason.Construction.SimplexComplex

end

section

/-! # Constructing the principal simplex cells

Cone a positive globular table to a new final vertex using the explicitly
proved prism chain map. Iterating gives a cell with the top simplex as its
top chain and the expected endpoint vertices, without an atom-existence
hypothesis. The signed-part formula and composition-generation assertion
remain separate published facts.
-/

namespace Thomason.Construction.SimplexComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

/-- Include the old vertices before a new final vertex. -/
def coneInclusion (m : ℕ) : Fin (m + 1) →o Fin (m + 2) :=
  Fin.castSuccOrderEmb.toOrderHom

/-- The constant map to the new final vertex. -/
def coneVertex (m : ℕ) : Fin (m + 1) →o Fin (m + 2) :=
  OrderHom.const _ (Fin.last (m + 1))

theorem cone_le (m : ℕ) (i : Fin (m + 1)) : coneInclusion m i ≤ coneVertex m i :=
  Fin.le_last _

/-- The concrete positive prism from the old simplex to the new vertex. -/
noncomputable def coneChainMap (h : NormalizedSimplexIdentities) (m : ℕ) :
    Hom (rightCylinder (directedComplex m (h.squared m)))
      (directedComplex (m + 1) (h.squared (m + 1))) :=
  prismChainMap h (A := ∅) (by intro a b hab hb; exact hb.elim)
    (coneInclusion m) (coneVertex m) (cone_le m)
    (by intro x hx; exact hx.elim) (by intro x hx y hy; rfl)

/-- Cone a cell by applying the positive prism to its explicit interval table. -/
noncomputable def coneCell (h : NormalizedSimplexIdentities) {m : ℕ} (x : h.object m) :
    h.object (m + 1) :=
  Cell.map (coneChainMap h m) (RightCylinder.intervalCell x)

/-- Evaluation of the cone map in a fixed positive degree. -/
theorem coneChainMap_succ_app (h : NormalizedSimplexIdentities) (m p : ℕ)
    (z : (rightCylinder (directedComplex m (h.squared m))).group (p + 1)) :
    (coneChainMap h m).app (p + 1) z =
      mapChains (coneInclusion m) (p + 1) z.1 +
      mapChains (coneVertex m) (p + 1) z.2.1 +
      prism (coneInclusion m) (coneVertex m) (cone_le m) p z.2.2 := rfl

/-- Evaluation of the cone table, retaining explicit directed-complex types. -/
theorem coneCell_table (h : NormalizedSimplexIdentities) {m : ℕ}
    (x : h.object m) (a : Bool) (n : ℕ) :
    (coneCell h x).table a n = (coneChainMap h m).app n
      (RightCylinder.intervalCellTable (K := directedComplex m (h.squared m)) x a n) := rfl

/-- The upper chain of the coned cell is the cone of its old upper chain. -/
theorem coneCell_top (h : NormalizedSimplexIdentities) {m : ℕ}
    (x : h.object m) (a : Bool) :
    (coneCell h x).table a (m + 1) =
      prism (coneInclusion m) (coneVertex m) (cone_le m) m (x.table a m) := by
  have hz : x.table a (m + 1) = 0 :=
    NormalizedSimplexIdentities.chains_eq_zero_above (by omega) _
  change prismApp h (coneInclusion m) (coneVertex m) (cone_le m) (m + 1)
    (RightCylinder.intervalCellTable x a (m + 1)) = _
  by_cases he : Even m <;> cases a <;>
    simp [RightCylinder.intervalCellTable, prismApp, he, hz]

/-- The prism on a top simplex appends exactly the new final vertex. -/
theorem prismBasis_cone_top (m : ℕ) :
    prismBasis (coneInclusion m) (coneVertex m) (cone_le m) m (topBasis m) =
      Finsupp.single (topBasis (m + 1)) 1 := by
  have he : append ((coneInclusion m).comp (topBasis m).toOrderHom)
      ((coneVertex m) (topBasis m (Fin.last m))) (cone_le m _) = OrderHom.id := by
    apply DFunLike.ext
    intro i
    induction i using Fin.lastCases with
    | last => exact append_last _ _ _
    | cast i => exact append_castSucc _ _ _ i
  calc
    _ = tuple (append ((coneInclusion m).comp (topBasis m).toOrderHom)
        ((coneVertex m) (topBasis m (Fin.last m))) (cone_le m _)) := rfl
    _ = tuple OrderHom.id := congrArg tuple he
    _ = _ := by
      simp only [tuple, mapBasis_id]
      rfl

/-- The source of the cone is the inclusion of the old source. -/
theorem coneCell_source (h : NormalizedSimplexIdentities) {m : ℕ} (x : h.object m) :
    (h.object (m + 1)).source 0 (coneCell h x) =
      (h.map (coneInclusion m)).toFun ((h.object m).source 0 x) := by
  let x' : Cell (directedComplex m (h.squared m)) := x
  have he := RightCylinder.intervalCell_source x'
  calc
    _ = Cell.map (coneChainMap h m) ((RightCylinder.intervalCell x').face false 0) :=
      (Cell.map_face (coneChainMap h m) (RightCylinder.intervalCell x') false 0).symm
    _ = Cell.map (coneChainMap h m)
        (Cell.map (RightCylinder.endpoint (directedComplex m (h.squared m)) false)
          (x'.face false 0)) := congrArg (Cell.map (coneChainMap h m)) he
    _ = _ := by
      apply Cell.ext
      funext b p
      exact prismChainMap_endpoint h (A := ∅) (by intro a b hab hb; exact hb.elim)
        (coneInclusion m) (coneVertex m) (cone_le m)
        (by intro x hx; exact hx.elim) (by intro x hx y hy; rfl)
        false p ((x'.face false 0).table b p)

/-- The target of the cone is the constant image of the old target. -/
theorem coneCell_target (h : NormalizedSimplexIdentities) {m : ℕ} (x : h.object m) :
    (h.object (m + 1)).target 0 (coneCell h x) =
      (h.map (coneVertex m)).toFun ((h.object m).target 0 x) := by
  let x' : Cell (directedComplex m (h.squared m)) := x
  have he := RightCylinder.intervalCell_target x'
  calc
    _ = Cell.map (coneChainMap h m) ((RightCylinder.intervalCell x').face true 0) :=
      (Cell.map_face (coneChainMap h m) (RightCylinder.intervalCell x') true 0).symm
    _ = Cell.map (coneChainMap h m)
        (Cell.map (RightCylinder.endpoint (directedComplex m (h.squared m)) true)
          (x'.face true 0)) := congrArg (Cell.map (coneChainMap h m)) he
    _ = _ := by
      apply Cell.ext
      funext b p
      exact prismChainMap_endpoint h (A := ∅) (by intro a b hab hb; exact hb.elim)
        (coneInclusion m) (coneVertex m) (cone_le m)
        (by intro x hx; exact hx.elim) (by intro x hx y hy; rfl)
        true p ((x'.face true 0).table b p)

/-- The principal cell, built recursively rather than postulated. -/
noncomputable def principalCell (h : NormalizedSimplexIdentities) : (m : ℕ) → h.object m
  | 0 => vertex h 0
  | m + 1 => coneCell h (principalCell h m)

/-- The constructed cell contains exactly the principal top simplex. -/
theorem principalCell_top (h : NormalizedSimplexIdentities) (m : ℕ) (a : Bool) :
    (principalCell h m).table a m = Finsupp.single (topBasis m) 1 := by
  induction m with
  | zero =>
    change Finsupp.single (vertexBasis (0 : Fin 1)) 1 = Finsupp.single (topBasis 0) 1
    congr 1
    apply DFunLike.ext
    intro i
    fin_cases i
    rfl
  | succ m ih =>
    rw [principalCell, coneCell_top, ih, prism_single, one_smul, prismBasis_cone_top]

/-- The initial vertex of the constructed principal cell is zero. -/
theorem principalCell_source (h : NormalizedSimplexIdentities) (m : ℕ) :
    (h.object m).source 0 (principalCell h m) = vertex h 0 := by
  induction m with
  | zero => exact (vertex_dimensionLE h 0).1
  | succ m ih =>
    rw [principalCell, coneCell_source, ih, map_vertex]
    rfl

/-- The final vertex of the constructed principal cell is the last vertex. -/
theorem principalCell_target (h : NormalizedSimplexIdentities) (m : ℕ) :
    (h.object m).target 0 (principalCell h m) = vertex h (Fin.last m) := by
  induction m with
  | zero => exact (vertex_dimensionLE h 0).2
  | succ m ih =>
    rw [principalCell, coneCell_target, ih, map_vertex]
    rfl

end Thomason.Construction.SimplexComplex

end

section

/-! # Positive splitting from disjoint simplex boundaries

This proves the binary decomposition step on the actual normalized chains.
No atom-generation hypothesis is used. Disjoint negative/positive boundary
supports make the shared chain positive by its two equal expressions.
-/

namespace Thomason.Construction.SimplexComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

/-- Two expressions for a middle chain prove its positivity coefficientwise. -/
theorem positive_middle_of_disjoint {m p : ℕ} (x y ap am bp bm : Chains m p)
    (hx : x ∈ positive m p) (hy : y ∈ positive m p)
    (hap : ap ∈ positive m p) (hbm : bm ∈ positive m p)
    (he : x + ap - am = y + bm - bp)
    (hd : ∀ b, am b = 0 ∨ bp b = 0) :
    x + ap - am ∈ positive m p := by
  intro b
  have hx' := hx b
  have hy' := hy b
  have ha' := hap b
  have hb' := hbm b
  have he' := congrArg (fun z : Chains m p => z b) he
  simp only [Finsupp.add_apply, Finsupp.sub_apply] at he' ⊢
  rcases hd b with h | h <;> omega

/-- Ordered, disjoint r-boundaries produce an actual strict binary composite. -/
theorem split_of_disjoint_boundaries (h : NormalizedSimplexIdentities) {m : ℕ}
    (X A B : h.object m) (r : ℕ)
    (he : ∀ n, r < n → ∀ side, X.table side n = A.table side n + B.table side n)
    (hd : ∀ b, A.table false r b = 0 ∨ B.table true r b = 0) :
    ∃ (Y Z : h.object m) (hyz : (h.object m).target r Y = (h.object m).source r Z),
      (h.object m).comp r Y Z hyz = X ∧
      (∀ n, r < n → ∀ side, Y.table side n = A.table side n) ∧
      (∀ n, r < n → ∀ side, Z.table side n = B.table side n) := by
  apply DirectedComplex.Cell.exists_comp_of_positive_middle X
    (Cell.PositiveTable.ofCell A) (Cell.PositiveTable.ofCell B) r he
  exact positive_middle_of_disjoint
    (X.table false r) (X.table true r)
    (A.table true r) (A.table false r) (B.table true r) (B.table false r)
    (X.positive false r) (X.positive true r) (A.positive true r) (B.positive false r)
    (DirectedComplex.Cell.replacement_middle_eq X
      (Cell.PositiveTable.ofCell A) (Cell.PositiveTable.ofCell B) r
      (he (r+1) (Nat.lt_succ_self r) false)) hd

/-- The same splitting allows either upper summand to be a finite sum of
atoms: its augmentation need not be one. -/
theorem split_of_disjoint_positiveTables (h : NormalizedSimplexIdentities) {m : ℕ}
    (X : h.object m)
    (A B : Cell.PositiveTable (directedComplex m (h.squared m))) (r : ℕ)
    (he : ∀ n, r < n → ∀ side, X.table side n = A.table side n + B.table side n)
    (hd : ∀ b, A.table false r b = 0 ∨ B.table true r b = 0) :
    ∃ (Y Z : h.object m) (hyz : (h.object m).target r Y = (h.object m).source r Z),
      (h.object m).comp r Y Z hyz = X ∧
      (∀ n, r < n → ∀ side, Y.table side n = A.table side n) ∧
      (∀ n, r < n → ∀ side, Z.table side n = B.table side n) := by
  apply Cell.exists_comp_of_positive_middle X A B r he
  exact positive_middle_of_disjoint
    (X.table false r) (X.table true r)
    (A.table true r) (A.table false r) (B.table true r) (B.table false r)
    (X.positive false r) (X.positive true r) (A.positive true r) (B.positive false r)
    (Cell.replacement_middle_eq X A B r (he (r+1) (Nat.lt_succ_self r) false)) hd

end Thomason.Construction.SimplexComplex

end

section

/-! # The algebraic factorization part of Kan–Quillen

The boundary and horn small-object factorizations do not require any
hypothesis about geometric-realization weak equivalences. We construct
these two systems first, leaving the semantic identifications of
Goerss–Jardine (1999), Theorems I.11.3–I.11.4 and Corollary II.8.6, explicit.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.MorphismProperty
open SSet.modelCategoryQuillen
open scoped Simplicial

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

/-- Finite boundaries permit the ordinary countable small-object argument. -/
instance boundarySmallObjectCardinal :
    I.{0}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{0} where
  isSmall := isSmall_ofHoms _
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{0} A := by
      obtain ⟨n⟩ := hi
      infer_instance
    infer_instance

instance boundarySmallObjectArgument : I.{0}.HasSmallObjectArgument.{0} :=
  ⟨Cardinal.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- The left boundary lifting class is exactly the monomorphisms. -/
theorem boundary_left_class : I.{0}.rlp.llp = monomorphisms SSet.{0} := by
  apply le_antisymm
  · rw [llp_rlp_of_hasSmallObjectArgument]
    rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact I_le_monomorphisms
  · intro X Y f hf
    have : Mono f := hf
    exact transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp.{0} I ℕ f
      ⟨(SSet.relativeCellComplexOfMono f).transfiniteCompositionOfShape' (fun _ => ⟨_⟩)⟩

/-- Actual boundary factorization, independent of the weak-equivalence definition. -/
theorem boundary_weakFactorizationSystem :
    IsWeakFactorizationSystem (monomorphisms SSet.{0}) I.rlp := by
  have hw : IsWeakFactorizationSystem I.rlp.llp I.rlp :=
    IsWeakFactorizationSystem.mk' _ _ (fun _ _ hi hp => hi _ hp)
  rwa [boundary_left_class] at hw

/-- Actual horn factorization, independent of the weak-equivalence definition. -/
theorem horn_weakFactorizationSystem :
    IsWeakFactorizationSystem SSet.anodyneExtensions.{0} J.rlp := by
  change IsWeakFactorizationSystem J.rlp.llp J.rlp
  exact IsWeakFactorizationSystem.mk' _ _ (fun _ _ hi hp => hi _ hp)

/-- Only the semantic identifications remain when supplying the classical
Kan–Quillen input: both factorization constructions are already proved. -/
theorem kanQuillenInput_of_semantic_classes
    (h2 : realizationWeakEquivalences.{0}.HasTwoOutOfThreeProperty)
    (hb : I.rlp = J.rlp ⊓ realizationWeakEquivalences.{0})
    (hh : SSet.anodyneExtensions.{0} = monomorphisms SSet.{0} ⊓ realizationWeakEquivalences) :
    KanQuillenPublishedInput.{0} where
  twoOutOfThree := h2
  cofibrationFactorization := by rw [← hb]; exact boundary_weakFactorizationSystem
  fibrationFactorization := by rw [← hh]; exact horn_weakFactorizationSystem

end Thomason.Construction

end

section

/-! # The span shape used in simplicial gluing

This small diagram category is restricted to the one pushout shape needed
by the Thomason proof. Its maps retain the actual comparison on pushouts.
-/

namespace Thomason.Construction.SimplicialSpan

open CategoryTheory CategoryTheory.Limits

structure Diagram where
  A : SSet.{0}
  B : SSet.{0}
  C : SSet.{0}
  left : A ⟶ B
  right : A ⟶ C

@[ext] structure Hom (X Y : Diagram) where
  a : X.A ⟶ Y.A
  b : X.B ⟶ Y.B
  c : X.C ⟶ Y.C
  left_w : X.left ≫ b = a ≫ Y.left
  right_w : X.right ≫ c = a ≫ Y.right

namespace Hom

def id (X : Diagram) : Hom X X where
  a := 𝟙 _
  b := 𝟙 _
  c := 𝟙 _
  left_w := by simp
  right_w := by simp

def comp {X Y Z : Diagram} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  a := f.a ≫ g.a
  b := f.b ≫ g.b
  c := f.c ≫ g.c
  left_w := by rw [← Category.assoc, f.left_w, Category.assoc, g.left_w, ← Category.assoc]
  right_w := by rw [← Category.assoc, f.right_w, Category.assoc, g.right_w, ← Category.assoc]

end Hom

instance : Category Diagram where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext <;> simp [Hom.comp, Hom.id]
  comp_id f := by ext <;> simp [Hom.comp, Hom.id]
  assoc f g h := by ext <;> simp [Hom.comp]

@[simp] theorem comp_a {X Y Z : Diagram} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).a = f.a ≫ g.a := rfl
@[simp] theorem comp_b {X Y Z : Diagram} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).b = f.b ≫ g.b := rfl
@[simp] theorem comp_c {X Y Z : Diagram} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).c = f.c ≫ g.c := rfl

noncomputable abbrev pushout (X : Diagram) : SSet.{0} := Limits.pushout X.left X.right

noncomputable def pushoutMap {X Y : Diagram} (f : X ⟶ Y) : pushout X ⟶ pushout Y :=
  Limits.pushout.desc (f.b ≫ Limits.pushout.inl Y.left Y.right)
    (f.c ≫ Limits.pushout.inr Y.left Y.right) (by
      rw [← Category.assoc, f.left_w, Category.assoc, Limits.pushout.condition,
        ← Category.assoc, ← f.right_w, Category.assoc])

@[reassoc (attr := simp)] theorem inl_pushoutMap {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout.inl X.left X.right ≫ pushoutMap f =
      f.b ≫ Limits.pushout.inl Y.left Y.right := Limits.pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem inr_pushoutMap {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout.inr X.left X.right ≫ pushoutMap f =
      f.c ≫ Limits.pushout.inr Y.left Y.right := Limits.pushout.inr_desc _ _ _

noncomputable def pushoutFunctor : Diagram ⥤ SSet.{0} where
  obj := pushout
  map := pushoutMap
  map_id X := by
    change pushoutMap (Hom.id X) = 𝟙 _
    apply Limits.pushout.hom_ext <;> simp [Hom.id]
  map_comp f g := by
    change pushoutMap (Hom.comp f g) = pushoutMap f ≫ pushoutMap g
    apply Limits.pushout.hom_ext <;> simp [Hom.comp]

/-- The comparison is the supplied fourth map of the actual pushout squares. -/
theorem pushoutMap_fac {X Y : Diagram} {P Q : SSet.{0}}
    {b : X.B ⟶ P} {c : X.C ⟶ P} {b' : Y.B ⟶ Q} {c' : Y.C ⟶ Q}
    (hp : IsPushout X.left X.right b c) (hq : IsPushout Y.left Y.right b' c')
    (f : X ⟶ Y) (g : P ⟶ Q) (hb : b ≫ g = f.b ≫ b') (hc : c ≫ g = f.c ≫ c') :
    hp.isoPushout.hom ≫ pushoutMap f ≫ hq.isoPushout.inv = g := by
  apply hp.hom_ext <;> simp [hb, hc]

end Thomason.Construction.SimplicialSpan

end

section

/-! # A factorization of the span shape from the actual Kan–Quillen WFS -/

namespace Thomason.Construction.SimplicialSpan

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

/-- The relative map at the covariant end of a span. -/
noncomputable def relativeB {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout X.left f.a ⟶ Y.B := Limits.pushout.desc f.b Y.left f.left_w

@[reassoc (attr := simp)] theorem inl_relativeB {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout.inl X.left f.a ≫ relativeB f = f.b :=
  Limits.pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem inr_relativeB {X Y : Diagram} (f : X ⟶ Y) :
    Limits.pushout.inr X.left f.a ≫ relativeB f = Y.left :=
  Limits.pushout.inr_desc _ _ _

structure Prefix {X Y : Diagram} (f : X ⟶ Y) where
  A : SSet.{0}
  C : SSet.{0}
  right : A ⟶ C
  iA : X.A ⟶ A
  iC : X.C ⟶ C
  pA : A ⟶ Y.A
  pC : C ⟶ Y.C
  i_right : X.right ≫ iC = iA ≫ right
  p_right : right ≫ pC = pA ≫ Y.right
  facA : iA ≫ pA = f.a
  facC : iC ≫ pC = f.c
  hiA : Mono iA
  hiC : Mono iC
  hpA : (J.rlp ⊓ realizationWeakEquivalences) pA
  hpC : (J.rlp ⊓ realizationWeakEquivalences) pC

/-- Factor first at C and then at the matching object over C. -/
noncomputable def factorPrefix {X Y : Diagram} (f : X ⟶ Y) (kq : KanQuillenPublishedInput.{0}) :
    Prefix f := by
  let T := J.rlp ⊓ realizationWeakEquivalences
  have := kq.cofibrationFactorization
  have hT : T = (MorphismProperty.monomorphisms SSet.{0}).rlp :=
    (MorphismProperty.rlp_eq_of_wfs _ _).symm
  have : T.IsStableUnderBaseChange := by rw [hT]; infer_instance
  have : T.IsStableUnderComposition := by rw [hT]; infer_instance
  let c := MorphismProperty.factorizationData (MorphismProperty.monomorphisms SSet.{0}) T f.c
  let u : X.A ⟶ pullback Y.right c.p := pullback.lift f.a (X.right ≫ c.i) (by
    rw [Category.assoc, c.fac]
    exact f.right_w.symm)
  let a := MorphismProperty.factorizationData (MorphismProperty.monomorphisms SSet.{0}) T u
  refine
    { A := a.Z
      C := c.Z
      right := a.p ≫ pullback.snd Y.right c.p
      iA := a.i
      iC := c.i
      pA := a.p ≫ pullback.fst Y.right c.p
      pC := c.p
      i_right := ?_
      p_right := ?_
      facA := ?_
      facC := c.fac
      hiA := a.hi
      hiC := c.hi
      hpA := ?_
      hpC := c.hp }
  · rw [← Category.assoc, a.fac]
    exact (pullback.lift_snd _ _ _).symm
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  · rw [← Category.assoc, a.fac]
    exact pullback.lift_fst _ _ _
  · exact T.comp_mem _ _ a.hp (T.pullback_fst Y.right c.p c.hp)

/-- The specialized cofibration conditions for this span orientation. -/
structure Cofibration {X Y : Diagram} (f : X ⟶ Y) : Prop where
  monoA : Mono f.a
  monoC : Mono f.c
  monoRelative : Mono (relativeB f)

structure Factorization {X Y : Diagram} (f : X ⟶ Y) where
  Z : Diagram
  i : X ⟶ Z
  p : Z ⟶ Y
  fac : i ≫ p = f
  hi : Cofibration i
  hpA : (J.rlp ⊓ realizationWeakEquivalences) p.a
  hpB : (J.rlp ⊓ realizationWeakEquivalences) p.b
  hpC : (J.rlp ⊓ realizationWeakEquivalences) p.c

/-- The final factorization at B is relative to the already constructed A.
No diagram model structure or gluing theorem is assumed. -/
noncomputable def factorization {X Y : Diagram} (f : X ⟶ Y)
    (kq : KanQuillenPublishedInput.{0}) : Factorization f := by
  have := kq.cofibrationFactorization
  let q := factorPrefix f kq
  let u : Limits.pushout X.left q.iA ⟶ Y.B :=
    Limits.pushout.desc f.b (q.pA ≫ Y.left) (by
      rw [← Category.assoc, q.facA, f.left_w])
  let b := MorphismProperty.factorizationData
    (MorphismProperty.monomorphisms SSet.{0})
    (J.rlp ⊓ realizationWeakEquivalences) u
  let Z : Diagram := ⟨q.A, b.Z, q.C,
    Limits.pushout.inr X.left q.iA ≫ b.i, q.right⟩
  let i : X ⟶ Z :=
    ⟨q.iA, Limits.pushout.inl X.left q.iA ≫ b.i, q.iC,
      by dsimp [Z]; rw [← Category.assoc, Limits.pushout.condition, Category.assoc],
      q.i_right⟩
  let p : Z ⟶ Y :=
    ⟨q.pA, b.p, q.pC,
      by dsimp [Z]; rw [Category.assoc, b.fac]; exact Limits.pushout.inr_desc _ _ _,
      q.p_right⟩
  refine ⟨Z, i, p, ?_, ⟨q.hiA, q.hiC, ?_⟩, q.hpA, b.hp, q.hpC⟩
  · apply Hom.ext
    · exact q.facA
    · change (Limits.pushout.inl X.left q.iA ≫ b.i) ≫ b.p = f.b
      rw [Category.assoc, b.fac]
      exact Limits.pushout.inl_desc _ _ _
    · exact q.facC
  · have he : relativeB i = b.i := by
      apply Limits.pushout.hom_ext
      · exact Limits.pushout.inl_desc _ _ _
      · exact Limits.pushout.inr_desc _ _ _
    rw [he]
    exact b.hi

end Thomason.Construction.SimplicialSpan

end

end OAI
