import OAI.Analysis.LiebThirring.CubeFlags

namespace OAI

universe u39

noncomputable section
open Finset


namespace SharpLiebThirring.CubeFlags

/-- Coordinate reflection as an isometric linear equivalence in the sup norm. -/
def Signs.linearIsometry {n : ℕ} (s : Signs n) :
    (Fin n → ℝ) ≃ₗᵢ[ℝ] (Fin n → ℝ) where
  toFun x i := if s.val i then -x i else x i
  invFun x i := if s.val i then -x i else x i
  left_inv x := by
    funext i
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs]
  right_inv x := by
    funext i
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs]
  map_add' x y := by
    funext i
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs, add_comm]
  map_smul' a x := by
    funext i
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs]
  norm_map' x := by
    simp only [Pi.norm_def]
    congr 1
    apply Finset.sup_congr rfl
    intro i _
    change ‖(if s.val i then -x i else x i)‖₊ = ‖x i‖₊
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs]

instance {n : ℕ} : MulAction (Signs n) (Fin n → ℝ) where
  smul s x := s.linearIsometry x
  one_smul x := by
    ext i
    change (if (1 : Signs n).val i then -x i else x i) = x i
    simp
  mul_smul s t x := by
    ext i
    change (if (s * t).val i then -x i else x i) =
      if s.val i then -(if t.val i then -x i else x i) else (if t.val i then -x i else x i)
    simp only [Signs.mul_val]
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;>
      rcases Bool.eq_false_or_eq_true (t.val i) with ht | ht <;> simp [hs, ht]

lemma Signs.smul_real {n : ℕ} (s : Signs n) (x : Fin n → ℝ) (i : Fin n) :
    (s • x) i = if s.val i then -x i else x i := rfl

instance {n : ℕ} : IsIsometricSMul (Signs n) (Fin n → ℝ) where
  isometry_smul s := s.linearIsometry.isometry

instance {n : ℕ} : MulAction (Signs n) (Fin n → ℤ) where
  smul s x i := if s.val i then -x i else x i
  one_smul x := by
    ext i
    change (if (1 : Signs n).val i then -x i else x i) = x i
    simp
  mul_smul s t x := by
    ext i
    change (if (s * t).val i then -x i else x i) =
      if s.val i then -(if t.val i then -x i else x i) else (if t.val i then -x i else x i)
    simp only [Signs.mul_val]
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;>
      rcases Bool.eq_false_or_eq_true (t.val i) with ht | ht <;> simp [hs, ht]

lemma Signs.smul_int {n : ℕ} (s : Signs n) (x : Fin n → ℤ) (i : Fin n) :
    (s • x) i = if s.val i then -x i else x i := rfl

lemma Flag.point_smul {n : ℕ} (s : Signs n) (F : Flag n) (k : Fin (n + 1)) :
    (s • F).point k = s • F.point k := by
  ext i
  exact F.reflect_point s.val k i

lemma Flag.vertex_smul {n : ℕ} (s : Signs n) (F : Flag n) (k : Fin (n + 1)) :
    (s • F).vertex k = s • F.vertex k := by
  ext i
  exact F.reflect_vertex s.val k i

/-- The common final vertex is the cube center. -/
def Flag.center {n : ℕ} (F : Flag n) : Fin n → ℝ := F.point (Fin.last n)

@[simp] lemma Flag.center_apply {n : ℕ} (F : Flag n) (i : Fin n) :
    F.center i = (F.base i : ℝ) + 1 / 2 := by
  simp only [center, point, vertex, Fin.val_last, (F.order.symm i).isLt, ↓reduceIte]
  push_cast
  ring

lemma Flag.center_smul {n : ℕ} (s : Signs n) (F : Flag n) :
    (s • F).center = s • F.center := F.point_smul s _

lemma Flag.dist_point_center {n : ℕ} (F : Flag n) (k : Fin (n + 1)) :
    dist (F.point k) F.center ≤ 1 / 2 := by
  rw [dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  intro i
  rw [Real.dist_eq, abs_le, F.center_apply]
  have hb := F.point_bounds k i
  constructor <;> linarith

lemma Flag.dist_combination_center {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    dist (∑ k, w k • F.point k) F.center ≤ 1 / 2 := by
  rw [dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  intro i
  rw [Real.dist_eq, abs_le, F.center_apply]
  have hb := F.combination_bounds w hw hs i
  constructor <;> linarith

lemma Flag.neighbor_center_dist {n : ℕ} [NeZero n] (F : Flag n) (j : Fin (n + 1)) :
    dist (F.neighbor j).center F.center ≤ 1 := by
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), k ≠ j := by
    by_cases hj : j.val = 0
    · exact ⟨⟨n, by omega⟩, by intro h; have hh := congrArg Fin.val h; simp at hh; omega⟩
    · exact ⟨0, by intro h; have hh := congrArg Fin.val h; simp at hh; omega⟩
  have he : (F.neighbor j).point k = F.point k := by
    ext i
    simp only [point, congrFun (F.neighbor_vertex j k hk) i]
  calc
    _ ≤ dist (F.neighbor j).center (F.point k) + dist (F.point k) F.center := dist_triangle _ _ _
    _ ≤ 1 / 2 + 1 / 2 := by
      apply add_le_add
      · rw [dist_comm, ← he]
        exact (F.neighbor j).dist_point_center k
      · exact F.dist_point_center k
    _ = 1 := by norm_num

lemma Flag.dist_combination_point {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (k : Fin (n + 1)) :
    dist (∑ l, w l • F.point l) (F.point k) ≤ 1 := by
  calc
    _ ≤ dist (∑ l, w l • F.point l) F.center + dist F.center (F.point k) := dist_triangle _ _ _
    _ ≤ 1 / 2 + 1 / 2 := add_le_add (F.dist_combination_center w hw hs)
      (by rw [dist_comm]; exact F.dist_point_center k)
    _ = 1 := by norm_num

lemma dist_scale {E : Type u39} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (hh : 0 ≤ h) (x y : E) : dist (h • x) (h • y) = h * dist x y := by
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]

lemma Flag.dist_scaled_point_center {n : ℕ} (F : Flag n) (h : ℝ) (hh : 0 ≤ h)
    (k : Fin (n + 1)) : dist (h • F.point k) (h • F.center) ≤ h / 2 := by
  rw [dist_scale h hh]
  nlinarith [F.dist_point_center k]

lemma Flag.finite_base_bounds {n : ℕ} (L U : ℤ) :
    Set.Finite {F : Flag n | ∀ i, L ≤ F.base i ∧ F.base i ≤ U} := by
  let e : {F : Flag n // ∀ i, L ≤ F.base i ∧ F.base i ≤ U} →
      ((Fin n → ↥(Finset.Icc L U)) × (Fin n → Bool) × Equiv.Perm (Fin n)) :=
    fun F ↦ (fun i ↦ ⟨F.val.base i, by simpa only [Finset.mem_Icc] using F.prop i⟩,
      F.val.corner, F.val.order)
  have he : Function.Injective e := by
    intro F G h
    apply Subtype.ext
    apply Flag.ext
    · funext i
      exact congrArg Subtype.val (congrFun (congrArg Prod.fst h) i)
    · exact congrArg (fun z ↦ z.2.1) h
    · exact congrArg (fun z ↦ z.2.2) h
  exact Set.finite_def.mpr ⟨Fintype.ofInjective e he⟩

/-- Cubes whose centers are close to a compact set form a finite collection. -/
lemma Flag.finite_near_centers {n : ℕ} {K : Set (Fin n → ℝ)} (hK : Bornology.IsBounded K)
    (h r : ℝ) (hh : 0 < h) :
    Set.Finite {F : Flag n | ∃ x ∈ K, dist (h • F.center) x < r} := by
  obtain ⟨B, hB⟩ := hK.exists_norm_le
  obtain ⟨U, hU⟩ := exists_int_gt ((B + r) / h + 1)
  apply (Flag.finite_base_bounds (-U) U).subset
  rintro F ⟨x, hx, hd⟩ i
  have hc : ‖h • F.center‖ < B + r := by
    have ht := norm_add_le (h • F.center - x) x
    rw [sub_add_cancel, ← dist_eq_norm] at ht
    linarith [hB x hx]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh] at hc
  have hc' : ‖F.center‖ < (B + r) / h := (lt_div_iff₀ hh).mpr (by nlinarith)
  have hi : |F.center i| ≤ ‖F.center‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm F.center i
  rw [F.center_apply] at hi
  have hl : -(U : ℝ) ≤ F.base i := by
    have := (abs_le.mp hi).1
    linarith
  have hu : (F.base i : ℝ) ≤ U := by
    have := (abs_le.mp hi).2
    linarith
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

/-- The spatially truncated cylinder of cubical flags used in continuation. -/
def nearCylinder {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ) (t : Fin n) (m : ℕ) : Set (Flag n) :=
  {F | (∃ x ∈ K, dist (h • F.center) x < r) ∧ 0 ≤ F.base t ∧ F.base t < (m : ℤ)}

lemma finite_nearCylinder {n : ℕ} {K : Set (Fin n → ℝ)} (hK : Bornology.IsBounded K)
    (h r : ℝ) (hh : 0 < h) (t : Fin n) (m : ℕ) : (nearCylinder K h r t m).Finite :=
  (Flag.finite_near_centers hK h r hh).subset (fun _ hF ↦ hF.1)

lemma nearCylinder_smul {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ) (t : Fin n) (m : ℕ)
    (s : Signs n) (ht : s.val t = false) (hK : ∀ x ∈ K, s • x ∈ K)
    {F : Flag n} (hF : F ∈ nearCylinder K h r t m) : s • F ∈ nearCylinder K h r t m := by
  obtain ⟨⟨x, hx, hd⟩, hlo, hhi⟩ := hF
  refine ⟨⟨s • x, hK x hx, ?_⟩, ?_, ?_⟩
  · rw [F.center_smul]
    have he : h • (s • F.center) = s • (h • F.center) := by
      ext i
      simp only [Pi.smul_apply, Signs.smul_real, smul_eq_mul]
      rcases Bool.eq_false_or_eq_true (s.val i) with hi | hi <;> simp [hi]
      ring
    rw [he, dist_smul]
    exact hd
  · simpa only [Flag.smul_def, Flag.reflect, ht, Bool.false_eq_true, ↓reduceIte] using hlo
  · simpa only [Flag.smul_def, Flag.reflect, ht, Bool.false_eq_true, ↓reduceIte] using hhi

lemma nearCylinder_point_cthickening {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ)
    (hh : 0 ≤ h) (t : Fin n) (m : ℕ) {F : Flag n} (hF : F ∈ nearCylinder K h r t m)
    (k : Fin (n + 1)) : h • F.point k ∈ Metric.cthickening (r + h / 2) K := by
  obtain ⟨x, hx, hd⟩ := hF.1
  apply Metric.mem_cthickening_of_dist_le _ x _ K hx
  calc
    _ ≤ dist (h • F.point k) (h • F.center) + dist (h • F.center) x := dist_triangle _ _ _
    _ ≤ h / 2 + r := add_le_add (F.dist_scaled_point_center h hh k) hd.le
    _ = r + h / 2 := add_comm _ _


lemma Flag.neighbor_base_of_ne_last {n : ℕ} [NeZero n] (F : Flag n) (j : Fin (n + 1))
    (hj : j ≠ Fin.last n) : (F.neighbor j).base = F.base := by
  have hn : j.val ≠ n := fun h ↦ hj (Fin.ext h)
  by_cases hz : j.val = 0
  · simp only [neighbor, dite_eq_left hz, flip_base]
  · simp only [neighbor, dite_eq_right hz, dite_eq_right hn, swap]

/-- A time-boundary facet is exactly the last facet of a flag expanding time last. -/
lemma Flag.neighbor_outside_time {n : ℕ} [NeZero n] (F : Flag n) (j : Fin (n + 1))
    (t : Fin n) (m : ℤ) (hlo : 0 ≤ F.base t) (hhi : F.base t < m)
    (hout : ¬ (0 ≤ (F.neighbor j).base t ∧ (F.neighbor j).base t < m)) :
    j = Fin.last n ∧ (F.order.symm t).val = n - 1 ∧
      ((F.base t = 0 ∧ F.corner t = false) ∨ (F.base t = m - 1 ∧ F.corner t = true)) := by
  have hj : j = Fin.last n := by
    by_contra hj
    rw [F.neighbor_base_of_ne_last j hj] at hout
    exact hout ⟨hlo, hhi⟩
  have hp : 0 < n := NeZero.pos n
  have hc : F.neighbor j = F.cross (F.order ⟨n - 1, by omega⟩) := by
    subst j
    simp only [neighbor, Fin.val_last, ne_of_gt hp, ↓reduceDIte]
  rw [hc] at hout
  have ht : t = F.order ⟨n - 1, by omega⟩ := by
    by_contra ht
    simp only [cross, Function.update_of_ne ht] at hout
    exact hout ⟨hlo, hhi⟩
  refine ⟨hj, ?_, ?_⟩
  · rw [ht, Equiv.symm_apply_apply]
  · have hh : (F.cross (F.order ⟨n - 1, by omega⟩)).base t =
        F.base t + if F.corner t then 1 else -1 := by
      simp only [cross, ← ht, Function.update_self]
    simp only [hh] at hout
    rcases Bool.eq_false_or_eq_true (F.corner t) with htrue | hfalse
    · simp only [htrue, ↓reduceIte] at hout
      exact Or.inr ⟨by omega, htrue⟩
    · simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at hout
      exact Or.inl ⟨by omega, hfalse⟩

lemma Flag.point_time_boundary {n : ℕ} [NeZero n] (F : Flag n) (t : Fin n)
    (ht : (F.order.symm t).val = n - 1) (k : Fin (n + 1)) (hk : k ≠ Fin.last n) :
    F.point k t = (F.base t : ℝ) + if F.corner t then 1 else 0 := by
  have hp : 0 < n := NeZero.pos n
  have hk' : k.val < n := by
    have hh : k.val ≠ n := fun h ↦ hk (Fin.ext h)
    omega
  simp only [point, vertex, ht, show ¬ n - 1 < k.val by omega, ↓reduceIte]
  rcases Bool.eq_false_or_eq_true (F.corner t) with hc | hc <;> simp [hc]
  ring

lemma nearCylinder_point_time {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ)
    (hh : 0 ≤ h) (t : Fin n) (m : ℕ) (hm : h * m = 1)
    {F : Flag n} (hF : F ∈ nearCylinder K h r t m) (k : Fin (n + 1)) :
    (h • F.point k) t ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hl, hu⟩ := F.point_bounds k t
  have hb : (0 : ℝ) ≤ F.base t := by exact_mod_cast hF.2.1
  have hc : (F.base t : ℝ) + 1 ≤ m := by
    have hh := hF.2.2
    exact_mod_cast (show F.base t + 1 ≤ (m : ℤ) by omega)
  change 0 ≤ h * F.point k t ∧ h * F.point k t ≤ 1
  constructor
  · exact mul_nonneg hh (by linarith)
  · nlinarith

lemma nearCylinder_combination_time {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ)
    (hh : 0 ≤ h) (t : Fin n) (m : ℕ) (hm : h * m = 1)
    {F : Flag n} (hF : F ∈ nearCylinder K h r t m)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    (h • (∑ k, w k • F.point k)) t ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hl, hu⟩ := F.combination_bounds w hw hs t
  have hb : (0 : ℝ) ≤ F.base t := by exact_mod_cast hF.2.1
  have hc : (F.base t : ℝ) + 1 ≤ m := by
    have hh := hF.2.2
    exact_mod_cast (show F.base t + 1 ≤ (m : ℤ) by omega)
  change 0 ≤ h * (∑ k, w k • F.point k) t ∧ h * (∑ k, w k • F.point k) t ≤ 1
  constructor
  · exact mul_nonneg hh (by linarith)
  · nlinarith

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags

/-- Embed the twice-barycenter lattice at mesh size `h`. -/
def gridPoint {n : ℕ} (h : ℝ) (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i ↦ h * (z i : ℝ) / 2

lemma gridPoint_vertex {n : ℕ} (h : ℝ) (F : Flag n) (k : Fin (n + 1)) :
    gridPoint h (F.vertex k) = h • F.point k := by
  ext i
  simp only [gridPoint, Pi.smul_apply, smul_eq_mul, Flag.point]
  ring

lemma gridPoint_smul {n : ℕ} (h : ℝ) (s : Signs n) (z : Fin n → ℤ) :
    gridPoint h (s • z) = s • gridPoint h z := by
  ext i
  simp only [gridPoint, Signs.smul_real, Signs.smul_int]
  rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs]
  ring

lemma gridPoint_injective {n : ℕ} {h : ℝ} (hh : h ≠ 0) :
    Function.Injective (gridPoint (n := n) h) := by
  intro z w he
  ext i
  have hx : h * (z i : ℝ) / 2 = h * (w i : ℝ) / 2 := congrFun he i
  have hi : (z i : ℝ) = (w i : ℝ) := mul_left_cancel₀ hh ((div_left_inj' (by norm_num : (2 : ℝ) ≠ 0)).mp hx)
  exact_mod_cast hi

section VertexComplex
variable {n : ℕ} (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))

/-- All vertices of a group-invariant collection of cubical flags. -/
def vertices : SubMulAction H (Fin n → ℤ) where
  carrier := {z | ∃ F : D, ∃ k, F.val.vertex k = z}
  smul_mem' s z hz := by
    obtain ⟨F, k, rfl⟩ := hz
    refine ⟨s • F, k, ?_⟩
    exact F.val.vertex_smul s.val k

instance verticesFintype [Fintype D] : Fintype (vertices H D) := by
  have hfin : Set.Finite (vertices H D : Set (Fin n → ℤ)) := by
    have he : (vertices H D : Set (Fin n → ℤ)) = Set.range
        (fun p : D × Fin (n + 1) ↦ p.1.val.vertex p.2) := by
      ext z
      constructor
      · rintro ⟨F, k, rfl⟩
        exact ⟨(F, k), rfl⟩
      · rintro ⟨⟨F, k⟩, rfl⟩
        exact ⟨F, k, rfl⟩
    rw [he]
    exact Set.finite_range _
  exact hfin.fintype

def flagVertex (F : D) (k : Fin (n + 1)) : vertices H D := ⟨F.val.vertex k, F, k, rfl⟩

lemma flagVertex_smul (s : H) (F : D) (k : Fin (n + 1)) :
    flagVertex H D (s • F) k = s • flagVertex H D F k :=
  Subtype.ext (F.val.vertex_smul s.val k)

lemma flagVertex_orbits_injective (F : D) :
    Function.Injective (fun k ↦ (Quotient.mk'' (flagVertex H D F k) :
      Quotient (MulAction.orbitRel H (vertices H D)))) := by
  intro j k he
  have hr := Quotient.exact' he
  obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hr)
  have hh : F.val.vertex j = s.val • F.val.vertex k := (congrArg Subtype.val hs).symm
  apply F.val.vertex_orbits_distinct j k s.val
  intro i
  exact congrFun hh i

/-- Freeness of the real vertex positions induces freeness on the finite
vertex set. It is supplied by the compact free-locus tube, not presumed. -/
theorem verticesIsCancel (h : ℝ)
    (hfree : ∀ z : vertices H D, ∀ s : H, s • gridPoint h z.val = gridPoint h z.val → s = 1) :
    IsCancelSMul H (vertices H D) where
  right_cancel' s t z he := by
    have he' : s • z.val = t • z.val := congrArg Subtype.val he
    have he'' : (t⁻¹ * s) • z.val = z.val := by
      rw [mul_smul, he', inv_smul_smul]
    have hp : (t⁻¹ * s) • gridPoint h z.val = gridPoint h z.val := by
      calc
        _ = gridPoint h ((t⁻¹ * s) • z.val) := (gridPoint_smul h (t⁻¹ * s).val z.val).symm
        _ = _ := congrArg (gridPoint h) he''
    exact (inv_mul_eq_one.mp (hfree z _ hp)).symm

end VertexComplex
end SharpLiebThirring.CubeFlags

end

end OAI
