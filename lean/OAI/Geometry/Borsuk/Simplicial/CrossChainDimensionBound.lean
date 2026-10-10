import Mathlib
import OAI.Geometry.Borsuk.Simplicial.SignedVertex

namespace OAI

namespace BorsukNine.SimplicialChains

lemma cross_chain_dimension_bound (n m : ℕ)
    (T : Chain (cross n) →ₗ[F₂] Chain (cross m))
    (hd : (boundary (cross m)).comp T = T.comp (boundary (cross n)))
    (hN : (normMap (cross m) flip).comp T = T.comp (normMap (cross n) flip))
    (ha : (augmentation (cross m)).comp T = augmentation (cross n))
    (hgrade : ∀ d, degreeChains (cross n) d ≤ (degreeChains (cross m) d).comap T) :
    n ≤ m := by
  by_contra hnm
  have hmn : m < n := Nat.lt_of_not_ge hnm
  let c : ℕ → Chain (cross m) := fun i => T (crossTower n i)
  have hstep : ∀ i < m, boundary (cross m) (c (i+1)) =
      normMap (cross m) flip (c i) := by
    intro i hi
    change boundary (cross m) (T (crossTower n (i+1))) =
      normMap (cross m) flip (T (crossTower n i))
    rw [← LinearMap.comp_apply, hd, LinearMap.comp_apply,
      crossTower_boundary n i (by omega), ← LinearMap.comp_apply, ← hN,
      LinearMap.comp_apply]
  have htop : c m = 0 := by
    have hg := hgrade (m+1) (crossTower_degree n m)
    change c m ∈ degreeChains (cross m) (m+1) at hg
    rw [degreeChains_eq_bot_of_card_bound (cross m) (m+1)
      (fun s hs => Nat.lt_succ_of_le (cross_card m s hs)), Submodule.mem_bot] at hg
    exact hg
  have hh := antipodal_tower_augmentation_zero (cross m) flip (cross_flip m)
    flip_involutive (cross_free m) m c hstep (by rw [htop, map_zero])
  change augmentation (cross m) (T (crossTower n 0)) = 0 at hh
  rw [← LinearMap.comp_apply, ha, crossTower_augmentation n (by omega)] at hh
  exact one_ne_zero hh

end BorsukNine.SimplicialChains

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def barycenter (s : Finset E) : E := (s.card : ℝ)⁻¹ • ∑ x ∈ s, x

lemma barycenter_eq_centerMass (s : Finset E) :
    barycenter s = s.centerMass (fun _ => (1 : ℝ)) id := by
  simp [barycenter, Finset.centerMass]

lemma barycenter_mem_convex {A : Set E} (hA : Convex ℝ A) {s : Finset E}
    (hs : s.Nonempty) (hsA : (s : Set E) ⊆ A) : barycenter s ∈ A := by
  rw [barycenter_eq_centerMass]
  apply hA.centerMass_mem
  · intro x hx; exact zero_le_one
  · simpa using (Nat.cast_pos.mpr hs.card_pos : (0 : ℝ) < s.card)
  · intro x hx; exact hsA hx

lemma barycenter_norm_le {s : Finset E} (hs : s.Nonempty) {D : ℝ}
    (hD : ∀ x ∈ s, ‖x‖ ≤ D) : ‖barycenter s‖ ≤ D := by
  have h := barycenter_mem_convex (convex_closedBall (0 : E) D) hs (A := Metric.closedBall 0 D)
    (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using hD x hx)
  simpa only [Metric.mem_closedBall, dist_zero_right] using h

lemma barycenter_inner {s : Finset E} (hs : s.Nonempty) (w : E)
    (hw : ∀ x ∈ s, ⟪w,x⟫ = 1) : ⟪w,barycenter s⟫ = 1 := by
  rw [barycenter, real_inner_smul_right, inner_sum]
  simp only [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero)

def hemisphereComplex (R : ℝ) : PreAbstractSimplicialComplex E where
  faces := {s | s.Nonempty ∧ ∃ w : E, ‖w‖ ≤ R ∧ ∀ x ∈ s, ‖x‖ ≤ 1 ∧ ⟪w,x⟫ = 1}
  isRelLowerSet_faces := by
    rintro s ⟨hs, w, hw, hs'⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    exact ⟨ht, w, hw, fun x hx => hs' x (hts hx)⟩

lemma hemisphere_vertex_nonzero {R : ℝ} {s : Finset E} (hs : s ∈ hemisphereComplex R)
    {x : E} (hx : x ∈ s) : x ≠ 0 := by
  obtain ⟨_, w, _, hw⟩ := hs
  intro he
  have h := (hw x hx).2
  simp [he] at h

lemma hemisphere_barycenter {R : ℝ} {s : Finset E} (hs : s ∈ hemisphereComplex R)
    {t : Finset E} (ht : t.Nonempty) (hts : t ⊆ s) :
    ∃ w : E, ‖w‖ ≤ R ∧ ‖barycenter t‖ ≤ 1 ∧ ⟪w,barycenter t⟫ = 1 := by
  obtain ⟨_, w, hw, hws⟩ := hs
  exact ⟨w, hw, barycenter_norm_le ht (fun x hx => (hws x (hts hx)).1),
    barycenter_inner ht w (fun x hx => (hws x (hts hx)).2)⟩

lemma barycenter_sub_eq {s : Finset E} (hs : s.Nonempty) (x : E) :
    barycenter s - x = (s.card : ℝ)⁻¹ • ∑ y ∈ s, (y-x) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_sub, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hs.card_ne_zero), one_smul]
  rfl

lemma barycenter_dist_vertex [DecidableEq E] {s : Finset E} {x : E} (hx : x ∈ s)
    {D : ℝ} (hD : ∀ y ∈ s, ∀ z ∈ s, dist y z ≤ D) :
    dist (barycenter s) x ≤ ((s.card : ℝ)-1) / s.card * D := by
  have hs : s.Nonempty := ⟨x,hx⟩
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [dist_eq_norm, barycenter_sub_eq hs x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))]
  have hh : (∑ y ∈ s, (y-x)) = ∑ y ∈ s.erase x, (y-x) := by
    rw [← Finset.sum_erase_add _ _ hx]
    simp
  rw [hh]
  calc
    (s.card : ℝ)⁻¹ * ‖∑ y ∈ s.erase x, (y-x)‖ ≤
        (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, ‖y-x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (le_of_lt hc))
    _ ≤ (s.card : ℝ)⁻¹ * ∑ y ∈ s.erase x, D := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hc))
      apply Finset.sum_le_sum
      intro y hy
      simpa only [dist_eq_norm] using hD y (Finset.mem_of_mem_erase hy) x hx
    _ = ((s.card : ℝ)-1) / s.card * D := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hx,
        Nat.cast_sub hs.card_pos, Nat.cast_one]
      ring

lemma barycenter_dist_carrier [DecidableEq E] {s t : Finset E} (ht : t.Nonempty)
    (hts : t ⊆ s) {D : ℝ} (hD : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D) :
    dist (barycenter s) (barycenter t) ≤ ((s.card : ℝ)-1) / s.card * D := by
  have h := barycenter_mem_convex
    (convex_closedBall (barycenter s) (((s.card : ℝ)-1) / s.card * D)) ht
    (fun x hx => (Metric.mem_closedBall').mpr (barycenter_dist_vertex (hts hx) hD))
  exact (Metric.mem_closedBall').mp h

lemma barycenter_mesh_factor {a n : ℕ} (ha : 0 < a) (han : a ≤ n) :
    ((a : ℝ)-1) / a ≤ ((n : ℝ)-1) / n := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le ha han
  apply (div_le_div_iff₀ ha' hn').mpr
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han
  nlinarith

end BorsukNine.SimplicialChains

end OAI
