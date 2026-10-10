import OAI.Geometry.HeilbronnTriangle.LatticeResidues

namespace OAI


namespace Problem355.SpecialNormals

variable {ι : Type*} [DecidableEq ι]

theorem outside_coordinate_zero {R : Type*} [CommRing R]
    (v : ι → R) (i j k : ι) (hki : k ≠ i) (hkj : k ≠ j)
    (hv : v ∈ Submodule.span R {Pi.single i (1 : R) - Pi.single j 1}) :
    v k = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
  have hk := congrFun ha k
  simpa [hki, hkj, Ne.symm hki, Ne.symm hkj] using hk.symm

theorem outside_coordinate_dvd (q : ℕ) (x : ι → ℤ)
    (i j k : ι) (hki : k ≠ i) (hkj : k ≠ j)
    (hx : (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}) :
    (q : ℤ) ∣ x k := by
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x k) q).mp
    (outside_coordinate_zero _ i j k hki hkj hx)

theorem modulus_le_outside_natAbs (q : ℕ) (x : ι → ℤ)
    (i j k : ι) (hki : k ≠ i) (hkj : k ≠ j) (hxk : x k ≠ 0)
    (hx : (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}) :
    q ≤ (x k).natAbs := by
  simpa using Int.natAbs_le_of_dvd_ne_zero
    (outside_coordinate_dvd q x i j k hki hkj hx) hxk

theorem half_modulus_lt_shell (q : ℕ) (x : ι → ℤ)
    (i j k : ι) (hki : k ≠ i) (hkj : k ≠ j) (hxk : x k ≠ 0)
    (hx : (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
    (R : ℝ) (hR : ((x k).natAbs : ℝ) < 2 * R) :
    (q : ℝ) / 2 < R := by
  have hq : (q : ℝ) ≤ (x k).natAbs := by
    exact_mod_cast modulus_le_outside_natAbs q x i j k hki hkj hxk hx
  linarith

theorem card_difference_line {q : ℕ} [Fact q.Prime]
    {i j : ι} (hij : i ≠ j) :
    Nat.card (Submodule.span (ZMod q)
      {(Pi.single i (1 : ZMod q) - Pi.single j 1 : ι → ZMod q)}) = q := by
  have hd : (Pi.single i (1 : ZMod q) - Pi.single j 1 : ι → ZMod q) ≠ 0 := by
    intro hz
    have hi := congrFun hz i
    simp [hij] at hi
  rw [← Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton (ZMod q)
    (ι → ZMod q) _ hd).toEquiv, Nat.card_eq_fintype_card, ZMod.card]

theorem card_le_modulus_mul_fiber_bound [Fintype ι]
    {q : ℕ} [Fact q.Prime] {i j : ι} (hij : i ≠ j)
    (S : Finset (ι → ℤ)) (M : ℕ)
    (hS : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
    (hbound : ∀ y : ι → ZMod q,
      (S.filter fun x => (fun t => (x t : ZMod q)) = y).card ≤ M) :
    S.card ≤ q * M := by
  classical
  let L : Set (ι → ZMod q) :=
    ↑(Submodule.span (ZMod q)
      {(Pi.single i (1 : ZMod q) - Pi.single j 1 : ι → ZMod q)})
  have hcard : L.toFinset.card = q := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact card_difference_line hij
  by_contra hn
  have hlt : L.toFinset.card * M < S.card := by
    rw [hcard]
    exact lt_of_not_ge hn
  obtain ⟨y, hy, hlarge⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := S) (t := L.toFinset) (f := fun x => fun t => (x t : ZMod q))
      (fun x hx => Set.mem_toFinset.mpr (hS x hx)) hlt
  exact (not_lt_of_ge (hbound y)) hlarge

theorem card_exceptional_normals_mul_sq_le
    (S : Finset (Fin 3 → ℤ)) (R q : ℕ) (hq : 0 < q)
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hbox : ∀ x ∈ S, ∀ t, -(R : ℤ) ≤ x t ∧ x t ≤ (R : ℤ))
    (hnonzero : ∀ x ∈ S, x k ≠ 0)
    (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}) :
    S.card * q ^ 2 ≤ (4 * R) ^ 3 := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨x, hx⟩
  · simp [hS]
  have hheight : (x k).natAbs ≤ R := by
    have h := abs_le.mpr (hbox x hx k)
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hqR : q ≤ R :=
    (modulus_le_outside_natAbs q x i j k hki hkj (hnonzero x hx) (hline x hx)).trans hheight
  apply LatticeResidues.card_modular_line_mul_sq_le S R q hq hqR
    (Pi.single i 1 - Pi.single j 1) hbox
  intro y hy
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hline y hy)
  refine ⟨a, fun t => ?_⟩
  simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun ha t).symm

theorem card_exceptional_normals_le
    (S : Finset (Fin 3 → ℤ)) (R q : ℕ) (hq : 0 < q)
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hbox : ∀ x ∈ S, ∀ t, -(R : ℤ) ≤ x t ∧ x t ≤ (R : ℤ))
    (hnonzero : ∀ x ∈ S, x k ≠ 0)
    (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}) :
    (S.card : ℝ) ≤ 64 * (R : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  apply (le_div_iff₀ (sq_pos_of_pos hqpos)).mpr
  have h := card_exceptional_normals_mul_sq_le S R q hq i j k hki hkj hbox hnonzero hline
  have hreal : (S.card : ℝ) * (q : ℝ) ^ 2 ≤ (4 * (R : ℝ)) ^ 3 := by
    exact_mod_cast h
  nlinarith

end Problem355.SpecialNormals

end OAI
