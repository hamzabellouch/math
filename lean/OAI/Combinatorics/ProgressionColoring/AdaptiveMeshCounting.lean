import OAI.Combinatorics.ProgressionColoring.AdaptiveMesh
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval

namespace OAI

/-! Actual lifted mesh endpoints and finite spacing bounds.  Endpoint sets
are constructed from the exponential mesh, not supplied as count hypotheses. -/

namespace QuantitativeVanDerWaerden

/-- The elementary one-dimensional packing inequality, with both end points
included.  This formulation has no rounding loss in subsequent estimates. -/
theorem finite_spacing_bound (s : Finset ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ u v : ℝ, u ≤ v →
    (∀ x ∈ s, u ≤ x ∧ x ≤ v) →
    (∀ x ∈ s, ∀ y ∈ s, x < y → δ ≤ y - x) →
    (s.card : ℝ) * δ ≤ v - u + δ := by
  classical
  induction s using Finset.induction_on_min with
  | empty => intro u v huv _ _; simp; linarith
  | @insert a s hmin ih =>
    intro u v huv hmem hsep
    have ha := hmem a (Finset.mem_insert_self _ _)
    have hnot : a ∉ s := by intro h; exact (lt_irrefl a) (hmin a h)
    rw [Finset.card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one, add_mul]
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst s
      simp
      linarith
    · obtain ⟨b, hb⟩ := hs
      have hgap := hsep a (Finset.mem_insert_self _ _) b
        (Finset.mem_insert_of_mem hb) (hmin b hb)
      have hbv := (hmem b (Finset.mem_insert_of_mem hb)).2
      have hsmall := ih (a + δ) v (by linarith)
        (by
          intro x hx
          have hxv := (hmem x (Finset.mem_insert_of_mem hx)).2
          have hxgap := hsep a (Finset.mem_insert_self _ _) x
            (Finset.mem_insert_of_mem hx) (hmin x hx)
          exact ⟨by linarith, hxv⟩)
        (fun x hx y hy hxy => hsep x (Finset.mem_insert_of_mem hx)
          y (Finset.mem_insert_of_mem hy) hxy)
      linarith

noncomputable def integerTranslatesBetween (r u v : ℝ) : Finset ℝ := by
  classical
  exact (Finset.Icc (⌈u - r⌉ : ℤ) ⌊v - r⌋).image (fun z : ℤ => r + z)

theorem mem_integerTranslatesBetween (r u v x : ℝ) :
    x ∈ integerTranslatesBetween r u v ↔
      u ≤ x ∧ x ≤ v ∧ ∃ z : ℤ, x = r + z := by
  classical
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have h := Finset.mem_Icc.mp hz
    have hl := Int.ceil_le.mp h.1
    have hu := Int.le_floor.mp h.2
    exact ⟨by linarith, by linarith, z, rfl⟩
  · rintro ⟨hlo, hhi, z, rfl⟩
    exact Finset.mem_image.mpr ⟨z, Finset.mem_Icc.mpr
      ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩, rfl⟩

theorem integerTranslatesBetween_card (r u v : ℝ) (huv : u ≤ v)
    (hlen : v - u < 1) : (integerTranslatesBetween r u v).card ≤ 1 := by
  classical
  have hp := finite_spacing_bound (integerTranslatesBetween r u v) 1 (by norm_num)
    u v huv
    (by
      intro x hx
      have h := (mem_integerTranslatesBetween r u v x).mp hx
      exact ⟨h.1, h.2.1⟩)
    (by
      intro x hx y hy hxy
      obtain ⟨_, _, z, rfl⟩ := (mem_integerTranslatesBetween r u v x).mp hx
      obtain ⟨_, _, w, rfl⟩ := (mem_integerTranslatesBetween r u v y).mp hy
      have hzw : (z : ℝ) < w := by linarith
      have hzw' : z < w := by exact_mod_cast hzw
      have hgap : (1 : ℝ) ≤ (w : ℝ) - z := by
        exact_mod_cast (show (1 : ℤ) ≤ w - z by omega)
      linarith)
  have hcard : ((integerTranslatesBetween r u v).card : ℝ) < 2 := by
    simpa only [mul_one] using lt_of_le_of_lt hp (by linarith)
  have hn : (integerTranslatesBetween r u v).card < 2 := by exact_mod_cast hcard
  omega

namespace AdaptiveMesh

variable (A : AdaptiveMesh)

theorem left_lt_half (i : A.Label) : A.left i < 1 / 2 := by
  have hw := A.width_pos i
  have hr := A.right_le_half i
  dsimp [width] at hw
  linarith

theorem contains_left (i : A.Label) : A.Contains i (A.left i) :=
  ⟨le_refl _, sub_pos.mp (A.width_pos i)⟩

theorem centered_of_lift_mem (i : A.Label) (z : ℤ) {x : ℝ}
    (hx : A.Contains i (x - z)) : centered x = x - z := by
  have hl := (A.left_ge_neg_half i).trans hx.1
  have hu := hx.2.trans_le (A.right_le_half i)
  have hc := centered_add_int (x - z) z
  rw [centered_eq_of_mem hl hu] at hc
  simpa only [sub_add_cancel] using hc

theorem label_of_lift_mem (i : A.Label) (z : ℤ) {x : ℝ}
    (hx : A.Contains i (x - z)) : A.meshLabel x = i := by
  apply (A.meshLabel_eq_iff x i).mpr
  rw [A.centered_of_lift_mem i z hx]
  exact hx

theorem lifted_unique (i j : A.Label) (z w : ℤ) {x : ℝ}
    (hi : A.Contains i (x - z)) (hj : A.Contains j (x - w)) :
    i = j ∧ z = w := by
  refine ⟨(A.label_of_lift_mem i z hi).symm.trans (A.label_of_lift_mem j w hj), ?_⟩
  have hzi := A.centered_of_lift_mem i z hi
  have hwj := A.centered_of_lift_mem j w hj
  have he : (z : ℝ) = w := by linarith
  exact_mod_cast he

/-- Every real lift belongs to an actual half-open lifted mesh cell. -/
theorem exists_lift_mem (x : ℝ) :
    ∃ (i : A.Label) (z : ℤ), A.Contains i (x - z) := by
  refine ⟨A.meshLabel x, ⌊x + 1 / 2⌋, ?_⟩
  exact A.meshLabel_contains x

theorem lifted_endpoint_gap (i j : A.Label) (z w : ℤ)
    (h : A.left i + z < A.left j + w) :
    A.right i + z ≤ A.left j + w := by
  by_contra hnot
  have hi : A.Contains i (A.left j + w - z) := ⟨by linarith, by linarith⟩
  have hj : A.Contains j (A.left j + w - w) := by
    simpa only [add_sub_cancel_right] using A.contains_left j
  obtain ⟨hij, hzw⟩ := A.lifted_unique i j z w hi hj
  subst j
  subst w
  exact (lt_irrefl _) h

theorem right_is_lifted_endpoint (i : A.Label) (z : ℤ) :
    ∃ (j : A.Label) (w : ℤ), A.right i + z = A.left j + w := by
  obtain ⟨j, w, hj⟩ := A.exists_lift_mem (A.right i + z)
  have hjlo : A.left j + w ≤ A.right i + z := by linarith [hj.1]
  have hjhi : A.right i + z < A.right j + w := by linarith [hj.2]
  by_contra hnot
  have hstrict : A.left j + w < A.right i + z := by
    apply lt_of_le_of_ne hjlo
    intro he
    exact hnot ⟨j, w, he.symm⟩
  have hipos : A.left i + z < A.right i + z := by
    have hw := A.width_pos i
    dsimp [width] at hw
    linarith
  let p := (max (A.left i + z) (A.left j + w) + (A.right i + z)) / 2
  have hmax : max (A.left i + z) (A.left j + w) < A.right i + z :=
    max_lt hipos hstrict
  have hpi : A.Contains i (p - z) := by
    have hm := le_max_left (A.left i + z) (A.left j + w)
    dsimp [Contains, p]
    constructor <;> linarith
  have hpj : A.Contains j (p - w) := by
    have hm := le_max_right (A.left i + z) (A.left j + w)
    dsimp [Contains, p]
    constructor <;> linarith
  obtain ⟨hij, hzw⟩ := A.lifted_unique i j z w hpi hpj
  subst j
  subst w
  exact (lt_irrefl _) hjhi

noncomputable def endpointsBetween (u v : ℝ) : Finset ℝ := by
  classical
  exact ((Finset.univ.product
    (Finset.Icc (⌈u - 1 / 2⌉ : ℤ) ⌊v + 1 / 2⌋)).image
      (fun p : A.Label × ℤ => A.left p.1 + p.2)).filter
        (fun x => u ≤ x ∧ x ≤ v)

theorem mem_endpointsBetween (u v x : ℝ) :
    x ∈ A.endpointsBetween u v ↔
      u ≤ x ∧ x ≤ v ∧ ∃ (i : A.Label) (z : ℤ), x = A.left i + z := by
  classical
  constructor
  · intro hx
    obtain ⟨himg, hlu, huv⟩ := Finset.mem_filter.mp hx
    obtain ⟨⟨i, z⟩, _, rfl⟩ := Finset.mem_image.mp himg
    exact ⟨hlu, huv, i, z, rfl⟩
  · rintro ⟨hux, hxv, i, z, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hux, hxv⟩
    apply Finset.mem_image.mpr
    refine ⟨(i, z), Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.ceil_le.mpr
      linarith [A.left_lt_half i]
    · apply Int.le_floor.mpr
      linarith [A.left_ge_neg_half i]

/-- The anchor's closed circle neighborhood, realized by one real interval.
An integer translate leaves every label and every width unchanged. -/
noncomputable def neighborhoodEndpoints (i : A.Label) (z : ℤ) : Finset ℝ :=
  A.endpointsBetween (A.left i + z - A.width i) (A.right i + z + A.width i)

theorem neighborhoodEndpoints_card (i : A.Label) (z : ℤ) :
    (A.neighborhoodEndpoints i z).card ≤ 49 := by
  classical
  let u := A.left i + z - A.width i
  let v := A.right i + z + A.width i
  have hw := A.width_pos i
  have huv : u ≤ v := by dsimp [u, v, width] at *; linarith
  have hpack := finite_spacing_bound (A.neighborhoodEndpoints i z)
    (A.width i / 16) (by positivity) u v huv
    (by
      intro x hx
      have h := (A.mem_endpointsBetween u v x).mp hx
      exact ⟨h.1, h.2.1⟩)
    (by
      intro x hx y hy hxy
      obtain ⟨hxlo, hxhi, j, w, rfl⟩ := (A.mem_endpointsBetween u v x).mp hx
      obtain ⟨_, _, k, t, rfl⟩ := (A.mem_endpointsBetween u v y).mp hy
      have hgap := A.lifted_endpoint_gap j k w t hxy
      have hjw := A.neighbor_width i j (le_refl _) (sub_pos.mp hw).le
        (le_refl _) (sub_pos.mp (A.width_pos j)).le
        ⟨z - w, by
          push_cast
          apply abs_le.mpr
          dsimp [u, v] at hxlo hxhi
          dsimp [width] at *
          constructor <;> linarith⟩
      dsimp [width] at hjw ⊢
      linarith)
  have hlen : v - u = 3 * A.width i := by dsimp [u, v, width]; ring
  rw [hlen] at hpack
  have hcard : ((A.neighborhoodEndpoints i z).card : ℝ) ≤ 49 := by
    nlinarith
  exact_mod_cast hcard

noncomputable def activeEndpoints (η u v : ℝ) : Finset ℝ := by
  classical
  exact (A.endpointsBetween u v).filter (fun x => η ≤ rho x)

/-- Active endpoints are separated globally, including across the circle cut:
the complete cell starting at the first endpoint lies before the second. -/
theorem activeEndpoints_spacing (η u v : ℝ) {x y : ℝ}
    (hx : x ∈ A.activeEndpoints η u v) (hy : y ∈ A.activeEndpoints η u v)
    (hxy : x < y) : A.H * η / 4 ≤ y - x := by
  classical
  obtain ⟨hxe, hxa⟩ := Finset.mem_filter.mp hx
  obtain ⟨hye, _⟩ := Finset.mem_filter.mp hy
  obtain ⟨_, _, i, z, rfl⟩ := (A.mem_endpointsBetween u v x).mp hxe
  obtain ⟨_, _, j, w, rfl⟩ := (A.mem_endpointsBetween u v y).mp hye
  rw [rho_add_int] at hxa
  have hw := A.width_bounds_of_closed_mem i (le_refl _)
    (sub_pos.mp (A.width_pos i)).le
  have hgap := A.lifted_endpoint_gap i j z w hxy
  have hH := A.H_pos
  have hmul := mul_le_mul_of_nonneg_left hxa (by positivity : 0 ≤ A.H / 4)
  have hap := mul_nonneg (by positivity : 0 ≤ A.H / 4) A.alpha_pos.le
  dsimp [width] at hw
  nlinarith [hw.1]

theorem activeEndpoints_card_bound (η u v : ℝ) (hη : 0 < η)
    (huv : u ≤ v) (hlen : v - u ≤ 4 * A.H) :
    ((A.activeEndpoints η u v).card : ℝ) ≤ 16 / η + 1 := by
  classical
  have hH := A.H_pos
  have hpack := finite_spacing_bound (A.activeEndpoints η u v)
    (A.H * η / 4) (by positivity) u v huv
    (by
      intro x hx
      have h := (A.mem_endpointsBetween u v x).mp (Finset.mem_filter.mp hx).1
      exact ⟨h.1, h.2.1⟩)
    (fun _ hx _ hy hxy => A.activeEndpoints_spacing η u v hx hy hxy)
  have hd : 0 < A.H * η / 4 := by positivity
  have he : (16 / η + 1) * (A.H * η / 4) = 4 * A.H + A.H * η / 4 := by
    field_simp
    ring
  apply (mul_le_mul_iff_left₀ hd).mp
  rw [he]
  linarith

/-- The only additional discontinuities of the truncated label are the two
threshold points in each period. Equality at either threshold is retained. -/
noncomputable def thresholdPoints (η u v : ℝ) : Finset ℝ :=
  integerTranslatesBetween (η - 1 / 2) u v ∪
    integerTranslatesBetween (1 / 2 - η) u v

noncomputable def truncatedBreakpoints (η u v : ℝ) : Finset ℝ :=
  A.activeEndpoints η u v ∪ thresholdPoints η u v

theorem thresholdPoints_card (η u v : ℝ) (huv : u ≤ v) (hlen : v - u < 1) :
    (thresholdPoints η u v).card ≤ 2 := by
  classical
  exact (Finset.card_union_le _ _).trans (by
    have hl := integerTranslatesBetween_card (η - 1 / 2) u v huv hlen
    have hr := integerTranslatesBetween_card (1 / 2 - η) u v huv hlen
    omega)

theorem truncatedBreakpoints_card_bound (η u v : ℝ) (hη : 0 < η)
    (huv : u ≤ v) (hlen : v - u ≤ 4 * A.H) :
    ((A.truncatedBreakpoints η u v).card : ℝ) ≤ 16 / η + 3 := by
  classical
  have hshort : v - u < 1 := by linarith [A.H_le]
  have he := A.activeEndpoints_card_bound η u v hη huv hlen
  have ht := thresholdPoints_card η u v huv hshort
  have hu := Finset.card_union_le (A.activeEndpoints η u v) (thresholdPoints η u v)
  have htr : ((thresholdPoints η u v).card : ℝ) ≤ 2 := by exact_mod_cast ht
  have hur : ((A.truncatedBreakpoints η u v).card : ℝ) ≤
      (A.activeEndpoints η u v).card + (thresholdPoints η u v).card := by
    exact_mod_cast hu
  linarith

theorem truncatedBreakpoints_card (D : ℕ) (hD : 0 < D) (u v : ℝ)
    (huv : u ≤ v) (hlen : v - u ≤ 4 * A.H) :
    (A.truncatedBreakpoints (1 / (1000 * (D : ℝ))) u v).card ≤ 16004 * D := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hc := A.truncatedBreakpoints_card_bound (1 / (1000 * (D : ℝ))) u v
    (by positivity) huv hlen
  have he : (16 : ℝ) / (1 / (1000 * (D : ℝ))) = 16000 * D := by
    field_simp
    ring
  rw [he] at hc
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hb : ((A.truncatedBreakpoints (1 / (1000 * (D : ℝ))) u v).card : ℝ) ≤
      16004 * D := by linarith
  exact_mod_cast hb

end AdaptiveMesh
end QuantitativeVanDerWaerden

end OAI
