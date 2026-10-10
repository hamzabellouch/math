import OAI.Analysis.OInfinity.RowCompletionBuffer

namespace OAI

/-! # Connected comparison using two forward shrinks

The two shrinks have the same final projection. Their literal base product
is the compression of the prescribed connected completion cocycles. Thus
the path used here never requires an ambient-to-relative connectedness
inference, and its final unitary has no leftover complementary block.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma compressed_binary_word (a : Fin 2 → E) (p : E) (hpp : p * p = p)
    (hp : ∀ j, Commute (a j) p) (k : ℕ) :
    (a 0 * p) ^ k * (a 1 * p) = (a 0 ^ k * a 1) * p := by
  induction k with
  | zero => simp only [pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, pow_succ']
    have hpk : Commute p (a 0 ^ k * a 1) :=
      ((hp 0).symm.pow_right k).mul_right (hp 1).symm
    calc
      (a 0 * p) * ((a 0 ^ k * a 1) * p) =
          a 0 * (p * (a 0 ^ k * a 1)) * p := by noncomm_ring
      _ = a 0 * ((a 0 ^ k * a 1) * p) * p := by rw [hpk.eq]
      _ = (a 0 * a 0 ^ k * a 1) * p := by
        calc
          _ = (a 0 * (a 0 ^ k * a 1)) * (p * p) := by noncomm_ring
          _ = _ := by rw [hpp]; noncomm_ring

lemma compressed_binary_gram (a : Fin 2 → E) (p : E)
    (hp : star p = p) (hpp : p * p = p)
    (ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0) :
    ∀ i j, star (a i * p) * (a j * p) = if i = j then p else 0 := by
  intro i j
  rw [star_mul, hp]
  calc
    _ = p * (star (a i) * a j) * p := by noncomm_ring
    _ = _ := by rw [ha]; split_ifs <;> simp only [mul_one, mul_zero, zero_mul, hpp]

lemma compressed_binary_sum (a : Fin 2 → E) (p : E)
    (hp : star p = p) (hpp : p * p = p)
    (ha : (∑ i, a i * star (a i)) = 1)
    (hac : ∀ i, Commute (a i) p) :
    (∑ i, (a i * p) * star (a i * p)) = p := by
  calc
    _ = ∑ i, (a i * star (a i)) * p := by
      apply Finset.sum_congr rfl
      intro i _
      rw [star_mul, hp]
      have hsp : Commute p (star (a i)) := by
        simpa only [hp] using (hac i).star_star.symm
      calc
        _ = a i * (p * p) * star (a i) := by noncomm_ring
        _ = a i * p * star (a i) := by rw [hpp]
        _ = _ := by rw [mul_assoc, hsp.eq]; noncomm_ring
    _ = p := by rw [← Finset.sum_mul, ha, one_mul]

lemma unitary_commutes_projection_of_fixed_complement (p : E) (u : unitary E)
    (h : (u : E) * (1 - p) = 1 - p ∧ (1 - p) * (u : E) = 1 - p) :
    Commute (u : E) p := by
  change (u : E) * p = p * (u : E)
  have h₁ := h.1
  have h₂ := h.2
  rw [mul_sub, mul_one] at h₁
  rw [sub_mul, one_mul] at h₂
  exact sub_right_injective (h₁.trans h₂.symm)

lemma unitary_inverse_comparison (u : unitary E) (x y : E) :
    ‖star (u : E) * x * (u : E) - y‖ =
      ‖x - (u : E) * y * star (u : E)‖ := by
  have he : star (u : E) * x * (u : E) - y =
      star (u : E) * (x - (u : E) * y * star (u : E)) * (u : E) := by
    rw [mul_sub, sub_mul]
    have hc : star (u : E) * ((u : E) * y * star (u : E)) * (u : E) = y := by
      calc
        _ = (star (u : E) * (u : E)) * y * (star (u : E) * (u : E)) := by noncomm_ring
        _ = y := by rw [u.property.1, one_mul, mul_one]
    rw [hc]
  rw [he, CStarRing.norm_mul_coe_unitary]
  change ‖((star u : unitary E) : E) * (x - (u : E) * y * star (u : E))‖ = _
  rw [CStarRing.norm_coe_unitary_mul]

/-- This is the quantitative two-shrink assembly, with the base connectedness
supplied by the actual completion formula. All coefficients at the endpoint
are genuine unitaries; there is no polar correction or residual corner. -/
lemma exists_connected_forward_shrink_comparison [Nontrivial E]
    (r b a c d : Fin 2 → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (hb : ∀ i j, star (b i) * b j = if i = j then 1 else 0)
    (hbs : (∑ i, b i * star (b i)) = 1)
    (ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0)
    (has : (∑ i, a i * star (a i)) = 1)
    (hc : ∀ i j, star (c i) * c j = if i = j then 1 else 0)
    (hcs : (∑ i, c i * star (c i)) = 1)
    (har : bergRowsCommute a r) (hcr : bergRowsCommute c r)
    (u v : unitary E) (hu : Joined (1 : unitary E) u) (hv : Joined (1 : unitary E) v)
    (hua : ∀ j, (u : E) * a j = b j) (hvc : ∀ j, (v : E) * c j = b j)
    (hp0 : 1 - r 0 * star (r 0) ≠ 0)
    (hd : ∀ i j, star (d i) * d j = if i = j then 1 - r 0 * star (r 0) else 0)
    (hds : (∑ i, d i * star (d i)) = 1 - r 0 * star (r 0))
    (had : bergRowsCommute a d) (hcd : bergRowsCommute c d)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ w : unitary E, Joined (1 : unitary E) w ∧
      ∀ i ≤ m, ‖(w : E) * (a 0 ^ i * a 1) * star (w : E) -
        (c 0 ^ i * c 1)‖ < ε := by
  let p := 1 - r 0 * star (r 0)
  have hr₀ : star (r 0) * r 0 = 1 := by simpa only [ite_true] using hr 0 0
  have hp : star p = p := by simp only [p, star_sub, star_one, star_mul, star_star]
  have hpp : p * p = p := by
    have he : (r 0 * star (r 0)) * (r 0 * star (r 0)) = r 0 * star (r 0) := by
      rw [mul_assoc, ← mul_assoc (star (r 0)), hr₀, one_mul]
    dsimp only [p]
    noncomm_ring [he]
  have hap (j : Fin 2) : Commute (a j) p :=
    (Commute.one_right _).sub_right ((har j 0).1.mul_right (har j 0).2)
  have hcp (j : Fin 2) : Commute (c j) p :=
    (Commute.one_right _).sub_right ((hcr j 0).1.mul_right (hcr j 0).2)
  let A : Fin 2 → E := fun j => a j * p
  let C : Fin 2 → E := fun j => c j * p
  have hAd : bergRowsCommute A d := by
    intro i j
    have hpd : Commute p (d j) := by
      change p * d j = d j * p
      rw [finiteRow_left_support p d hp hpp hd hds j, finiteRow_right_support p d hp hpp hd j]
    refine ⟨(had i j).1.mul_left hpd, ?_⟩
    exact (had i j).2.mul_left (by simpa only [hp] using hpd.star_star)
  have hCd : bergRowsCommute C d := by
    intro i j
    have hpd : Commute p (d j) := by
      change p * d j = d j * p
      rw [finiteRow_left_support p d hp hpp hd hds j, finiteRow_right_support p d hp hpp hd j]
    refine ⟨(hcd i j).1.mul_left hpd, ?_⟩
    exact (hcd i j).2.mul_left (by simpa only [hp] using hpd.star_star)
  let δ := ε / 6
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨X, hX, hX0, hXg, hXe⟩ := exists_binary_shrink_path r a hr ha has har m δ hδ
  obtain ⟨Y, hY, hY0, hYg, hYe⟩ := exists_binary_shrink_path r c hr hc hcs hcr m δ hδ
  obtain ⟨V, hV, hV0, hVp, hVe⟩ := exists_relative_binary_power_path p hp hpp hp0 A d
    (compressed_binary_gram a p hp hpp ha) hd (compressed_binary_sum a p hp hpp has hap)
    hds hAd m δ hδ
  obtain ⟨Z, hZ, hZ0, hZp, hZe⟩ := exists_relative_binary_power_path p hp hpp hp0 C d
    (compressed_binary_gram c p hp hpp hc) hd (compressed_binary_sum c p hp hpp hcs hcp)
    hds hCd m δ hδ
  let M : unitInterval → unitary E := fun t => star (Z t) * V t
  have hM : Continuous M := (continuous_star.comp hZ).mul hV
  have hMp (t : unitInterval) : Commute (M t : E) p := by
    have hz : Commute (star (Z t : E)) p := by
      simpa only [hp] using
        (unitary_commutes_projection_of_fixed_complement p (Z t) (hZp t)).star_star
    exact hz.mul_left (unitary_commutes_projection_of_fixed_complement p (V t) (hVp t))
  let W : unitInterval → E := fun t => star (Y t) * (M t : E) * X t
  have hWg (t : unitInterval) : star (W t) * W t = 1 ∧ W t * star (W t) = 1 := by
    have h := commonCornerTransfer_products 1 1 p (X t) (Y t) (M t)
      (hXg t).1 (hXg t).2 (mul_one _) (hYg t).1 (hYg t).2 (mul_one _) (hMp t)
    exact ⟨h.1, h.2.1⟩
  let U : unitInterval → unitary E := fun t => ⟨W t, hWg t⟩
  have hU : Continuous U := Continuous.subtype_mk
    (((continuous_star.comp hY).mul (continuous_subtype_val.comp hM)).mul hX) _
  have hrowA : a = fun j => star (u : E) * b j := by
    funext j
    rw [← hua j, ← mul_assoc, u.property.1, one_mul]
  have hrowC : c = fun j => star (v : E) * b j := by
    funext j
    rw [← hvc j, ← mul_assoc, v.property.1, one_mul]
  obtain ⟨K, hK, hKe⟩ := binaryShrinkValue_reference_cross_joined r b hr hb hbs u v hu hv
  have hU0 : U 0 = K := by
    apply Subtype.ext
    change star (Y 0) * (star (Z 0 : E) * (V 0 : E)) * X 0 = (K : E)
    rw [hV0, hZ0, OneMemClass.coe_one, star_one, one_mul, mul_one, hX0, hY0,
      hrowA, hrowC, hKe]
  have hJoined : Joined (U 0) (U 1) :=
    ⟨{ toFun := U, continuous_toFun := hU, source' := rfl, target' := rfl }⟩
  refine ⟨U 1, (hU0 ▸ hK).trans hJoined, fun i hi => ?_⟩
  have hmid : ‖(M 1 : E) * ((a 0 ^ i * a 1) * p) * star (M 1 : E) -
      (c 0 ^ i * c 1) * p‖ < 2 * δ := by
    have h₁ := hVe i hi
    have h₂ := hZe i hi
    rw [compressed_binary_word a p hpp hap i] at h₁
    rw [compressed_binary_word c p hpp hcp i] at h₂
    change ‖(V 1 : E) * ((a 0 ^ i * a 1) * p) * star (V 1 : E) - (d 0 ^ i * d 1)‖ < δ at h₁
    change ‖(Z 1 : E) * ((c 0 ^ i * c 1) * p) * star (Z 1 : E) - (d 0 ^ i * d 1)‖ < δ at h₂
    have hh : ‖(V 1 : E) * ((a 0 ^ i * a 1) * p) * star (V 1 : E) -
        (Z 1 : E) * ((c 0 ^ i * c 1) * p) * star (Z 1 : E)‖ < 2 * δ := by
      calc
        _ ≤ ‖(V 1 : E) * ((a 0 ^ i * a 1) * p) * star (V 1 : E) - (d 0 ^ i * d 1)‖ +
            ‖(d 0 ^ i * d 1) - (Z 1 : E) * ((c 0 ^ i * c 1) * p) * star (Z 1 : E)‖ :=
          by
            simpa only [dist_eq_norm] using
              (dist_triangle ((V 1 : E) * ((a 0 ^ i * a 1) * p) * star (V 1 : E))
                (d 0 ^ i * d 1) ((Z 1 : E) * ((c 0 ^ i * c 1) * p) * star (Z 1 : E)))
        _ < δ + δ := add_lt_add h₁ (by rwa [norm_sub_rev])
        _ = _ := by ring
    have hn := unitary_inverse_comparison (Z 1)
      ((V 1 : E) * ((a 0 ^ i * a 1) * p) * star (V 1 : E)) ((c 0 ^ i * c 1) * p)
    have hid : (M 1 : E) * ((a 0 ^ i * a 1) * p) * star (M 1 : E) =
        star (Z 1 : E) * ((V 1 : E) * ((a 0 ^ i * a 1) * p) * star (V 1 : E)) * (Z 1 : E) := by
      change (star (Z 1 : E) * (V 1 : E)) * _ * star (star (Z 1 : E) * (V 1 : E)) = _
      simp only [star_mul, star_star]
      noncomm_ring
    rw [hid, hn]
    exact hh
  have hYn : ‖Y 1‖ ≤ 1 := by
    have hh := congrArg norm (hYg 1).1
    rw [CStarRing.norm_star_mul_self, norm_one] at hh
    nlinarith [norm_nonneg (Y 1)]
  have hh := commonCornerTransfer_error 1 (X 1) (Y 1) (a 0 ^ i * a 1) (c 0 ^ i * c 1)
    ((a 0 ^ i * a 1) * p) ((c 0 ^ i * c 1) * p) (M 1)
    (hYg 1).1 (one_mul _) (mul_one _) hYn (2 * δ)
    ((hXe i hi).trans (by linarith)) ((hYe i hi).trans (by linarith)) hmid
  change ‖W 1 * (a 0 ^ i * a 1) * star (W 1) - (c 0 ^ i * c 1)‖ < ε
  exact hh.trans_eq (by dsimp only [δ]; ring)

end WeakPureInfiniteness

end

end OAI
