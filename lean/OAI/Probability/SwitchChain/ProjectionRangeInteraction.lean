import OAI.Probability.SwitchChain.RankOneInteraction

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.ProjectionRangeInteraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem interaction_of_decomposition
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hR : ∀ z, R (Q z - P (Q z)) = Q z - P (Q z))
    (hS : ∀ z, S (P z - Q (P z)) = P z - Q (P z))
    (f p q j : E) (hf : f = P p + Q q + j)
    (hPj : P j = 0) (hQj : Q j = 0) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * ⟪f - P f, f - Q f⟫ := by
  let a := Q q - P (Q q)
  let b := P p - Q (P p)
  have hPa : P a = 0 := by simp only [a, map_sub, hPi, sub_self]
  have hQb : Q b = 0 := by simp only [b, map_sub, hQi, sub_self]
  have hja : ⟪j, a⟫ = 0 := by
    simp only [a, inner_sub_right]
    rw [← hQs, ← hPs, hQj, hPj, inner_zero_left, inner_zero_left, sub_self]
  have hjb : ⟪j, b⟫ = 0 := by
    simp only [b, inner_sub_right]
    rw [← hPs, ← hQs, hPj, hQj, inner_zero_left, inner_zero_left, sub_self]
  have ha : f - P f = j + a := by
    rw [hf]
    simp only [map_add, hPi, hPj]
    dsimp [a]
    module
  have hb : f - Q f = j + b := by
    rw [hf]
    simp only [map_add, hQi, hQj]
    dsimp [b]
    module
  have hfa : ⟪f, a⟫ = ⟪a, a⟫ := by
    have hz : ⟪P f, a⟫ = 0 := by rw [hPs, hPa, inner_zero_right]
    have ht : ⟪f - P f, a⟫ = ⟪a, a⟫ := by
      rw [ha, inner_add_left, hja, zero_add]
    simpa only [inner_sub_left, hz, sub_zero] using ht
  have hfb : ⟪f, b⟫ = ⟪b, b⟫ := by
    have hz : ⟪Q f, b⟫ = 0 := by rw [hQs, hQb, inner_zero_right]
    have ht : ⟪f - Q f, b⟫ = ⟪b, b⟫ := by
      rw [hb, inner_add_left, hjb, zero_add]
    simpa only [inner_sub_left, hz, sub_zero] using ht
  have hRa : R a = a := hR q
  have hSb : S b = b := hS p
  have hra := RankOneInteraction.error_norm_sq_le R hRs f a hRa hfa
  have hsb := RankOneInteraction.error_norm_sq_le S hSs f b hSb hfb
  have hGf : G f = G j := by rw [hf, map_add, map_add, hGP, hGQ, zero_add, zero_add]
  have hg : ‖G f‖ ^ 2 ≤ ‖j‖ ^ 2 := by
    rw [hGf]
    exact RankOneInteraction.projection_norm_sq_le G hGs hGi j
  have hid : ⟪f - P f, f - Q f⟫ = ‖j‖ ^ 2 + ⟪a, b⟫ := by
    rw [ha, hb, inner_add_left, inner_add_right, inner_add_right,
      hjb, show ⟪a, j⟫ = 0 by rw [real_inner_comm, hja],
      real_inner_self_eq_norm_sq]
    ring
  have hlow := RankOneInteraction.interaction_lower_bound a b j (f - P f) (f - Q f) hid
  linarith

theorem exists_range_decomposition [FiniteDimensional ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (f : E) :
    ∃ p q j : E, f = P p + Q q + j ∧ P j = 0 ∧ Q j = 0 := by
  let K : Submodule ℝ E := P.range ⊔ Q.range
  let w := K.starProjection f
  let j := f - w
  have hw : w ∈ K := K.starProjection_apply_mem f
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hw
  obtain ⟨p₀, rfl⟩ := hp
  obtain ⟨q₀, rfl⟩ := hq
  have hj : j ∈ Kᗮ := K.sub_starProjection_mem_orthogonal f
  have hPj : P j = 0 := by
    have hm : P j ∈ K := (show P.range ≤ K from le_sup_left) (show P j ∈ P.range from ⟨j, rfl⟩)
    have hz : ⟪j, P j⟫ = 0 := (K.mem_orthogonal' j).mp hj (P j) hm
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hPs, hPi, hz]
  have hQj : Q j = 0 := by
    have hm : Q j ∈ K := (show Q.range ≤ K from le_sup_right) (show Q j ∈ Q.range from ⟨j, rfl⟩)
    have hz : ⟪j, Q j⟫ = 0 := (K.mem_orthogonal' j).mp hj (Q j) hm
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hQs, hQi, hz]
  refine ⟨p₀, q₀, j, ?_, hPj, hQj⟩
  rw [hpq]
  dsimp [j]
  module

theorem exists_correlated_range_decomposition [FiniteDimensional ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (p : E) :
    ∃ x u : E, P p = P (Q x) + u ∧ P u = u ∧ Q u = 0 := by
  let K := (P.comp Q).range
  let w := K.starProjection (P p)
  let u := P p - w
  have hw : w ∈ K := K.starProjection_apply_mem (P p)
  obtain ⟨x, hx⟩ := hw
  change P (Q x) = w at hx
  have hPw : P w = w := by rw [← hx, hPi]
  have hPu : P u = u := by simp only [u, map_sub, hPi, hPw]
  have hu : u ∈ Kᗮ := K.sub_starProjection_mem_orthogonal (P p)
  have hQu : Q u = 0 := by
    have hm : P (Q u) ∈ K := ⟨u, rfl⟩
    have hz : ⟪u, P (Q u)⟫ = 0 := (K.mem_orthogonal' u).mp hu _ hm
    rw [← hPs, hPu] at hz
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hQs, hQi, hz]
  refine ⟨x, u, ?_, hPu, hQu⟩
  rw [hx]
  dsimp [u]
  module

theorem exists_two_projection_decomposition [FiniteDimensional ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (f : E) :
    ∃ p q j u v : E,
      f = P (Q p) + Q (P q) + j + u + v ∧
      P j = 0 ∧ Q j = 0 ∧ P u = u ∧ Q u = 0 ∧ P v = 0 ∧ Q v = v := by
  obtain ⟨p₀,q₀,j,hf,hPj,hQj⟩ := exists_range_decomposition P Q hPs hQs hPi hQi f
  obtain ⟨p,u,hp,hPu,hQu⟩ := exists_correlated_range_decomposition P Q hPs hQs hPi hQi p₀
  obtain ⟨q,v,hq,hQv,hPv⟩ := exists_correlated_range_decomposition Q P hQs hPs hQi hPi q₀
  refine ⟨p,q,j,u,v,?_,hPj,hQj,hPu,hQu,hPv,hQv⟩
  rw [hf,hp,hq]
  module

theorem interaction_of_correlated_error_ranges [FiniteDimensional ℝ E]
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hR : ∀ z, R (Q (P z) - P (Q (P z))) = Q (P z) - P (Q (P z)))
    (hS : ∀ z, S (P (Q z) - Q (P (Q z))) = P (Q z) - Q (P (Q z)))
    (f : E) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * ⟪f - P f, f - Q f⟫ := by
  obtain ⟨p,q,j,u,v,hf,hPj,hQj,hPu,hQu,hPv,hQv⟩ :=
    exists_two_projection_decomposition P Q hPs hQs hPi hQi f
  let a := Q (P q) - P (Q (P q))
  let b := P (Q p) - Q (P (Q p))
  have hPa : P a = 0 := by simp only [a, map_sub, hPi, sub_self]
  have hQb : Q b = 0 := by simp only [b, map_sub, hQi, sub_self]
  have hja : ⟪j, a⟫ = 0 := by
    simp only [a, inner_sub_right]
    rw [← hQs j (P q), hQj, inner_zero_left,
      ← hPs j (Q (P q)), hPj, inner_zero_left, sub_self]
  have hjb : ⟪j, b⟫ = 0 := by
    simp only [b, inner_sub_right]
    rw [← hPs j (Q p), hPj, inner_zero_left,
      ← hQs j (P (Q p)), hQj, inner_zero_left, sub_self]
  have hju : ⟪j, u⟫ = 0 := by rw [← hPu, ← hPs, hPj, inner_zero_left]
  have hjv : ⟪j, v⟫ = 0 := by rw [← hQv, ← hQs, hQj, inner_zero_left]
  have hua : ⟪u, a⟫ = 0 := by rw [← hPu, hPs, hPa, inner_zero_right]
  have hvb : ⟪v, b⟫ = 0 := by rw [← hQv, hQs, hQb, inner_zero_right]
  have huv : ⟪u, v⟫ = 0 := by rw [← hPu, hPs, hPv, inner_zero_right]
  have hva : ⟪v, a⟫ = 0 := by
    simp only [a, inner_sub_right]
    rw [← hQs, hQv, ← hPs, hPv, inner_zero_left,
      ← hPs, hPv, inner_zero_left, sub_self]
  have hub : ⟪u, b⟫ = 0 := by
    simp only [b, inner_sub_right]
    rw [← hPs, hPu, ← hQs, hQu, inner_zero_left,
      ← hQs, hQu, inner_zero_left, sub_self]
  have ha : f - P f = j + a + v := by
    rw [hf]
    simp only [map_add, hPi, hPj, hPu, hPv]
    dsimp [a]
    module
  have hb : f - Q f = j + b + u := by
    rw [hf]
    simp only [map_add, hQi, hQj, hQu, hQv]
    dsimp [b]
    module
  have hfa : ⟪f, a⟫ = ⟪a, a⟫ := by
    have hz : ⟪P f, a⟫ = 0 := by rw [hPs, hPa, inner_zero_right]
    have ht : ⟪f - P f, a⟫ = ⟪a, a⟫ := by
      rw [ha, inner_add_left, inner_add_left, hja, hva, zero_add, add_zero]
    simpa only [inner_sub_left, hz, sub_zero] using ht
  have hfb : ⟪f, b⟫ = ⟪b, b⟫ := by
    have hz : ⟪Q f, b⟫ = 0 := by rw [hQs, hQb, inner_zero_right]
    have ht : ⟪f - Q f, b⟫ = ⟪b, b⟫ := by
      rw [hb, inner_add_left, inner_add_left, hjb, hub, zero_add, add_zero]
    simpa only [inner_sub_left, hz, sub_zero] using ht
  have hra := RankOneInteraction.error_norm_sq_le R hRs f a (hR q) hfa
  have hsb := RankOneInteraction.error_norm_sq_le S hSs f b (hS p) hfb
  have hGu : G u = 0 := by rw [← hPu, hGP]
  have hGv : G v = 0 := by rw [← hQv, hGQ]
  have hGf : G f = G j := by
    rw [hf]
    simp only [map_add, hGP, hGQ, hGu, hGv, zero_add, add_zero]
  have hg : ‖G f‖ ^ 2 ≤ ‖j‖ ^ 2 := by
    rw [hGf]
    exact RankOneInteraction.projection_norm_sq_le G hGs hGi j
  have hid : ⟪f - P f, f - Q f⟫ = ‖j‖ ^ 2 + ⟪a, b⟫ := by
    rw [ha, hb]
    simp only [inner_add_left, inner_add_right, hjb, hju, hvb,
      show ⟪a, j⟫ = 0 by rw [real_inner_comm, hja],
      show ⟪a, u⟫ = 0 by rw [real_inner_comm, hua],
      show ⟪v, j⟫ = 0 by rw [real_inner_comm, hjv],
      show ⟪v, u⟫ = 0 by rw [real_inner_comm, huv],
      real_inner_self_eq_norm_sq, zero_add, add_zero]
  have hlow := RankOneInteraction.interaction_lower_bound a b j (f - P f) (f - Q f) hid
  linarith

end Problem315.ProjectionRangeInteraction

end

end OAI
