import OAI.Analysis.Nonexpansive.WeakSelfMap
import OAI.Analysis.Nonexpansive.PointwiseWeakApproximation
import Mathlib.Topology.Algebra.Semigroup
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-!
# Compact semigroups of nonexpansive selfmaps

Convexity converts pointwise weak closure into finite simultaneous norm
approximation.  This justifies composition of limits without asserting weak
continuity of an arbitrary nonlinear map.  Fixed right translations are
continuous and the compact semigroup theorem then gives an idempotent.
-/

noncomputable section

open Set
open scoped Topology

namespace ReflexiveFixedPoints

universe u v

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {K : Set X}

namespace WeakSelfMap

/-- Convexity of an actual map family is measured in its ambient function
vector space.  The subtype of points of `K` need not be a vector space. -/
def ConvexFamily (B : Set (WeakSelfMap K)) : Prop :=
  Convex ℝ (weakAmbient '' B)

/-- One actual member approximates at all the chosen arguments. -/
theorem exists_finite_norm_approx {B : Set (WeakSelfMap K)}
    (hB : ConvexFamily B) {h : WeakSelfMap K} (hh : h ∈ closure B)
    {ι : Type v} [Fintype ι] (a : ι → K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ B, ∀ i, dist (toNorm g (a i)) (toNorm h (a i)) < ε := by
  have hw : weakAmbient h ∈ closure (weakAmbient '' B) :=
    mem_closure_image continuous_weakAmbient.continuousAt hh
  obtain ⟨_, ⟨g, hg, rfl⟩, hnear⟩ :=
    exists_mem_norm_approx_of_mem_pointwiseWeak_closure hB hw a hε
  refine ⟨g, hg, fun i => ?_⟩
  change dist ((toNorm g (a i) : K) : X) ((toNorm h (a i) : K) : X) < ε
  rw [dist_eq_norm]
  exact hnear i

theorem exists_finset_norm_approx {B : Set (WeakSelfMap K)}
    (hB : ConvexFamily B) {h : WeakSelfMap K} (hh : h ∈ closure B)
    (s : Finset K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ B, ∀ a ∈ s, dist (toNorm g a) (toNorm h a) < ε := by
  classical
  obtain ⟨g, hg, hnear⟩ := exists_finite_norm_approx hB hh
    (fun a : s => (a : K)) hε
  exact ⟨g, hg, fun a ha => hnear ⟨a, ha⟩⟩

/-- Nonexpansiveness passes to pointwise weak closure of a convex family. -/
theorem nonexpansive_of_mem_closure {B : Set (WeakSelfMap K)}
    (hB : ConvexFamily B)
    (hLip : ∀ g ∈ B, LipschitzWith 1 (toNorm g))
    {h : WeakSelfMap K} (hh : h ∈ closure B) :
    LipschitzWith 1 (toNorm h) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul]
  by_contra hab
  have hgap : 0 < dist (toNorm h a) (toNorm h b) - dist a b :=
    sub_pos.mpr (lt_of_not_ge hab)
  let ε := (dist (toNorm h a) (toNorm h b) - dist a b) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨g, hg, hnear⟩ := exists_finset_norm_approx hB hh {a, b} hε
  have ha := hnear a (by simp)
  have hb := hnear b (by simp)
  have hgl : dist (toNorm g a) (toNorm g b) ≤ dist a b := by
    simpa using (hLip g hg).dist_le_mul a b
  have htri := dist_triangle4 (toNorm h a) (toNorm g a)
    (toNorm g b) (toNorm h b)
  rw [dist_comm (toNorm h a) (toNorm g a)] at htri
  dsimp [ε] at ha hb
  linarith

/-- Finite norm approximations suffice for membership in weak closure. -/
theorem mem_closure_of_finite_norm_approx {B : Set (WeakSelfMap K)}
    {h : WeakSelfMap K}
    (happrox : ∀ (s : Finset K) (ε : ℝ), 0 < ε →
      ∃ g ∈ B, ∀ a ∈ s, dist (toNorm g a) (toNorm h a) < ε) :
    h ∈ closure B := by
  have hn : toNorm h ∈ closure (toNorm '' B) := by
    apply mem_closure_of_finite_dist_approx
    intro s ε hε
    obtain ⟨g, hg, hnear⟩ := happrox s ε hε
    exact ⟨toNorm g, ⟨g, hg, rfl⟩, hnear⟩
  have hw := mem_closure_image continuous_ofNorm.continuousAt hn
  have hs : ofNorm '' (toNorm '' B) ⊆ B := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    simpa only [ofNorm_toNorm] using hg
  exact closure_mono hs (by simpa only [ofNorm_toNorm] using hw)

/-- The closure is composition-closed using two finite simultaneous
approximations, both evaluated at arguments fixed before approximation. -/
theorem comp_mem_closure {B : Set (WeakSelfMap K)}
    (hB : ConvexFamily B)
    (hLip : ∀ g ∈ B, LipschitzWith 1 (toNorm g))
    (hcomp : ∀ f ∈ B, ∀ g ∈ B, comp f g ∈ B)
    {h k : WeakSelfMap K} (hh : h ∈ closure B) (hk : k ∈ closure B) :
    comp h k ∈ closure B := by
  classical
  apply mem_closure_of_finite_norm_approx
  intro s ε hε
  obtain ⟨kg, hkg, hknear⟩ := exists_finset_norm_approx hB hk s
    (show 0 < ε / 3 by linarith)
  obtain ⟨hg, hhg, hhnear⟩ := exists_finite_norm_approx hB hh
    (fun a : s => toNorm k a) (show 0 < ε / 3 by linarith)
  refine ⟨comp hg kg, hcomp hg hhg kg hkg, ?_⟩
  intro a ha
  have hfirst : dist (toNorm hg (toNorm kg a)) (toNorm hg (toNorm k a)) ≤
      dist (toNorm kg a) (toNorm k a) := by
    simpa using (hLip hg hhg).dist_le_mul (toNorm kg a) (toNorm k a)
  have hsecond := hhnear ⟨a, ha⟩
  have hkfirst := hknear a ha
  change dist (toNorm hg (toNorm kg a)) (toNorm h (toNorm k a)) < ε
  have htri := dist_triangle (toNorm hg (toNorm kg a))
    (toNorm hg (toNorm k a)) (toNorm h (toNorm k a))
  linarith

/-- A decreasing family of nonempty convex composition-closed families
of nonexpansive maps has an idempotent in the intersection of its
pointwise weak closures. -/
theorem exists_idempotent_in_iInter_closure
    [CompactSpace (WeakCarrier K)] [T2Space (WeakCarrier K)]
    (B : ℕ → Set (WeakSelfMap K))
    (hBn : ∀ n, (B n).Nonempty) (hBanti : Antitone B)
    (hBconv : ∀ n, ConvexFamily (B n))
    (hBLip : ∀ n g, g ∈ B n → LipschitzWith 1 (toNorm g))
    (hBcomp : ∀ n f, f ∈ B n → ∀ g, g ∈ B n → comp f g ∈ B n) :
    ∃ P ∈ ⋂ n, closure (B n), comp P P = P ∧ LipschitzWith 1 (toNorm P) := by
  let A : Set (WeakSelfMap K) := ⋂ n, closure (B n)
  have hClosureAnti : Antitone (fun n => closure (B n)) := by
    intro i j hij
    exact closure_mono (hBanti hij)
  have hAn : A.Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun n => closure (B n))
      hClosureAnti.directed_ge
      (fun n => (hBn n).mono subset_closure)
      (fun _ => isClosed_closure.isCompact) (fun _ => isClosed_closure)
  have hAc : IsCompact A := (isClosed_iInter fun _ => isClosed_closure).isCompact
  have hAcomp : ∀ f ∈ A, ∀ g ∈ A, comp f g ∈ A := by
    intro f hf g hg
    apply mem_iInter.mpr
    intro n
    exact comp_mem_closure (hBconv n) (hBLip n) (hBcomp n)
      (mem_iInter.mp hf n) (mem_iInter.mp hg n)
  let : Semigroup (WeakSelfMap K) :=
    { mul := comp
      mul_assoc := comp_assoc }
  obtain ⟨P, hP, hPP⟩ := exists_idempotent_in_compact_subsemigroup
    (fun g : WeakSelfMap K => continuous_comp_right g) A hAn hAc hAcomp
  refine ⟨P, hP, hPP, ?_⟩
  exact nonexpansive_of_mem_closure (hBconv 0) (hBLip 0) (mem_iInter.mp hP 0)

end WeakSelfMap

end ReflexiveFixedPoints

end

end OAI
