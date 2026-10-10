import OAI.Analysis.HenonEmden.UniformEnergy

namespace OAI

section Main

namespace HenonLaneEmden

theorem main_nonexistence (n : ℕ) (hn : 2 ≤ n) (p q A B : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hsub : Subcritical n p q A B) :
    ¬ ∃ u v : Space n → ℝ, IsSolution n p q A B u v := by
  rintro ⟨u,v,h⟩
  have hn3 := h.dimension_ge_three hn
  obtain ⟨C,_hC,hbound⟩ := uniform_unit_energy hn3 hp hq hsub
  obtain ⟨R,hR,hRC⟩ := h.scaled_energy_unbounded hn hp hq hsub C
  have hscale := h.dilate (h.product_gt_one hn hp hq) (show 0 < R by linarith)
  exact not_lt_of_ge (hbound _ _ hscale) hRC

theorem lane_emden_nonexistence (n : ℕ) (hn : 3 ≤ n) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hsub : 1 / (p + 1) + 1 / (q + 1) > ((n : ℝ) - 2) / (n : ℝ)) :
    ¬ ∃ u v : Space n → ℝ,
      ContDiff ℝ 2 u ∧ ContDiff ℝ 2 v ∧
      (∀ x, 0 < u x) ∧ (∀ x, 0 < v x) ∧
      (∀ x, -(Laplacian.laplacian u) x = Real.rpow (v x) p) ∧
      (∀ x, -(Laplacian.laplacian v) x = Real.rpow (u x) q) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : Subcritical n p q 0 0 := by
    have hh := (div_lt_iff₀ hn0).mp hsub
    unfold Subcritical
    simp only [add_zero,div_eq_mul_inv,one_mul] at hh ⊢
    nlinarith [hh]
  rintro ⟨u,v,hu,hv,hup,hvp,heu,hev⟩
  apply main_nonexistence n (by omega) p q 0 0 hp hq hs
  refine ⟨u,v,hu.continuous,hv.continuous,hu.contDiffOn,hv.contDiffOn,hup,hvp,?_,?_⟩
  · intro x _hx
    simpa only [Real.rpow_eq_pow,Real.rpow_zero,one_mul] using heu x
  · intro x _hx
    simpa only [Real.rpow_eq_pow,Real.rpow_zero,one_mul] using hev x

end HenonLaneEmden

end Main

end OAI
