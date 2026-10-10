import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialGrowth

namespace OAI

/-! Polynomial bounds on every vertical strip after removing the single
radial pole. Bounds for the meromorphic function follow away from it. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaSelectedRadialRegularized_polynomial_strip (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (a b : ℝ) :
    ∃ (C : ℝ) (N : ℕ),0 ≤ C ∧ ∀ s : ℂ,s.re∈Icc a b →
      ‖cubicThetaSelectedRadialRegularized g hc s‖ ≤ C*(1+|s.im|)^N := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1/2-a)
  let m := n+2
  let L : ℝ := 1/2-(m:ℝ)
  let R : ℝ := max (max a b) 2
  have hm : 2  ≤  m := by dsimp [m]; omega
  have hmR : (2:ℝ)  ≤  m := by exact_mod_cast hm
  have hLa : L<a := by dsimp [L,m]; push_cast; linarith
  have haR : a ≤ R := (le_max_left a b).trans (le_max_left _ _)
  have hbR : b ≤ R := (le_max_right a b).trans (le_max_left _ _)
  have hR2 : 2 ≤ R := le_max_right _ _
  have hLR : L<R := by dsimp [L]; linarith
  obtain ⟨C₀,hC₀,hleft⟩ := cubicThetaSelectedRadialDirichlet_left_bound g hc hm
  let C₁ := 81*cubicThetaDirichletNormMass (2*R-1)
  have hC₁ : 0 ≤ C₁ := mul_nonneg (by norm_num) (cubicThetaDirichletNormMass_nonneg _)
  let C := C₀+C₁
  have hC : 0 ≤ C := add_nonneg hC₀ hC₁
  let D := 2+|L|+|R|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hboundary (σ : ℝ) (hσ : σ=L ∨ σ=R) :
      ∀ s : ℂ,s.re=σ →
      ‖cubicThetaSelectedRadialRegularized g hc s‖ ≤ (D*C)*(1+|s.im|)^(4*m+1) := by
    intro s hs
    have hstrip : s.re∈Icc L R := by rcases hσ with h | h <;> simp [hs,h,hLR.le]
    have hsp : s≠(5/6:ℂ) := by
      intro he
      have hre := congrArg Complex.re he
      norm_num at hre
      rcases hσ with h | h
      · have : s.re=L := hs.trans h
        dsimp [L] at this
        linarith
      · have : s.re=R := hs.trans h
        linarith
    have hline : ‖cubicThetaSelectedRadialDirichlet g hc s‖ ≤ C*(1+|s.im|)^(4*m) := by
      rcases hσ with h | h
      · exact (hleft s (hs.trans h)).trans (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right hC₁) (by positivity))
      · have H := cubicThetaSelectedRadialDirichlet_right_bound g hc
          (σ:=R) (by linarith) s (hs.trans h)
        calc
          _  ≤  C₁ := H
          _  ≤  C := le_add_of_nonneg_left hC₀
          _  ≤  _ := le_mul_of_one_le_right hC (one_le_pow₀ (by linarith [abs_nonneg s.im]))
    rw [cubicThetaSelectedRadialRegularized_eq g hc hsp,norm_mul]
    calc
      _  ≤  (D*(1+|s.im|))*(C*(1+|s.im|)^(4*m)) :=
        mul_le_mul (cubicTheta_radial_affine_bound L R s hstrip) hline
          (_root_.norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add,pow_one]; ring
  have H := polynomial_strip_of_finite_order hLR
    (cubicThetaSelectedRadialRegularized_differentiable g hc)
    (cubicThetaSelectedRadialRegularized_finiteOrder g hc L R)
    (mul_nonneg hD hC) (4*m+1) (hboundary L (Or.inl rfl)) (hboundary R (Or.inr rfl))
  refine ⟨(D*C)*2^(4*m+1)*(R-L+1)^(4*m+1),4*m+1,by positivity,?_⟩
  intro s hs
  exact H s ⟨hLa.le.trans hs.1,hs.2.trans hbR⟩

theorem cubicThetaSelectedRadialDirichlet_large_height (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (a b : ℝ) :
    ∃ (C : ℝ) (N : ℕ),0 ≤ C ∧ ∀ s : ℂ,s.re∈Icc a b → 1 ≤ |s.im| →
      ‖cubicThetaSelectedRadialDirichlet g hc s‖ ≤ C*(1+|s.im|)^N := by
  obtain ⟨C,N,hC,hbound⟩ := cubicThetaSelectedRadialRegularized_polynomial_strip g hc a b
  refine ⟨C,N,hC,?_⟩
  intro s hs ht
  have hlow : 1 ≤ ‖s-(5/6:ℂ)‖ := by
    exact ht.trans (by simpa using Complex.abs_im_le_norm (s-(5/6:ℂ)))
  have hsp : s≠(5/6:ℂ) := by
    intro h
    norm_num [h] at hlow
  have H := hbound s hs
  rw [cubicThetaSelectedRadialRegularized_eq g hc hsp,norm_mul] at H
  exact (le_mul_of_one_le_left (_root_.norm_nonneg _) hlow).trans H

end CubicFirstMoment

end

end OAI
