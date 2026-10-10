import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearMeshBalance

namespace OAI

/-! Fourth-order cubature and the uncut orbital tail at the physical mesh
R^-10. Constants are independent of the slab width and the site positions. -/

noncomputable section
namespace ContinuumCoulomb

theorem nuclear_quadrature_physical_scale {R S a b c q m : ℝ}
    (hR : 1 ≤ R) (hS : S ≤ 2*R^5) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (_hq : 0 ≤ q) (hm : 0 ≤ m) :
    (a*m*S*R^3+b*R^6+c*R^3)*(1/R^10)^4+q*(1/R^10)^2/R^12 ≤
      (2*a*m+b+c+q)/R^32 := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hs : a*m*S*R^3 ≤ 2*a*m*R^8 := by
    calc
      _ ≤ a*m*(2*R^5)*R^3 := by gcongr
      _ = _ := by ring
  have he : (a*m*S*R^3+b*R^6+c*R^3)*(1/R^10)^4+q*(1/R^10)^2/R^12 =
      (a*m*S*R^3+b*R^6+c*R^3)/R^40+q/R^32 := by
    field_simp [ne_of_gt hR0]
  rw [he]
  calc
    _ ≤ (2*a*m*R^8+b*R^6+c*R^3)/R^40+q/R^32 := by gcongr
    _ = 2*a*m/R^32+b/R^34+c/R^37+q/R^32 := by
      field_simp [ne_of_gt hR0]
    _ ≤ 2*a*m/R^32+b/R^32+c/R^32+q/R^32 := by
      gcongr <;> norm_num
    _ = _ := by ring

theorem manufactured_orbital_quadrature_physical_scale
    {rho A B C L R S : ℝ} (hrho : 0 ≤ rho) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hR : 1 ≤ R) (hS : S ≤ 2*R^5) (m : ℕ) :
    rho*(24*((2*Real.pi+1)*(64*A*R^3))*(max 1 L)^4*(216*m*S+13824*R^3)+
        2048*Real.pi*B*(64*A*R^3))*(1/R^10)^4+C*(1/R^10)^2/R^12 ≤
    (2*(rho*24*(2*Real.pi+1)*64*A*(max 1 L)^4*216)+
       rho*24*(2*Real.pi+1)*64*A*(max 1 L)^4*13824+
       rho*2048*Real.pi*B*64*A+C)*((m:ℝ)+1)/R^32 := by
  let a := rho*24*(2*Real.pi+1)*64*A*(max 1 L)^4*216
  let b := rho*24*(2*Real.pi+1)*64*A*(max 1 L)^4*13824
  let c := rho*2048*Real.pi*B*64*A
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he := nuclear_quadrature_physical_scale hR hS ha hb hc hC (Nat.cast_nonneg m)
  have hnum : 2*a*(m:ℝ)+b+c+C ≤ (2*a+b+c+C)*((m:ℝ)+1) := by
    nlinarith [mul_nonneg hb (Nat.cast_nonneg m),mul_nonneg hc (Nat.cast_nonneg m),
      mul_nonneg hC (Nat.cast_nonneg m)]
  apply le_trans _ (div_le_div_of_nonneg_right hnum (by positivity))
  convert he using 1
  dsimp [a,b,c]
  ring

end ContinuumCoulomb

end

end OAI
