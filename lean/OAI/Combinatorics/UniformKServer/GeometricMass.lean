import Mathlib
import OAI.Combinatorics.UniformKServer.PilotScales

namespace OAI

                                    
section

/-! The actual geometric scales and the posterior ball masses at a request.
The shift comparison is proved from metric ball inclusion, rather than assumed
as an abstract scalar inequality. The scale count is independent of aspect. -/
noncomputable section
namespace UniformKServer.GeometricMass
open Finset
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]

def radius (R q : ℝ) (j : ℕ) : ℝ := R*q^(j+1)
def mass (μ : X → ℝ) (x : X) (a : ℝ) : ℝ := ∑ y, if dist x y ≤ a then μ y else 0

theorem radius_pos (R q : ℝ) (hR : 0< R) (hq : 0< q) (j : ℕ) : 0< radius R q j := by
  unfold radius; positivity

theorem mass_nonneg (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (a : ℝ) : 0 ≤ mass μ x a := by
  apply sum_nonneg
  intro y _
  split_ifs <;> [exact hμ y; exact le_rfl]

theorem mass_mono (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) {a b : ℝ} (hab : a ≤ b) :
    mass μ x a ≤ mass μ x b := by
  apply sum_le_sum
  intro y _
  by_cases hy : dist x y ≤ a
  · simp only [ite_eq_left hy,ite_eq_left (hy.trans hab),le_refl]
  · simp only [ite_eq_right hy]
    split_ifs <;> [exact hμ y; exact le_rfl]

theorem mass_total (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (a : ℝ) :
    mass μ x a ≤ ∑ y, μ y := by
  apply sum_le_sum
  intro y _
  split_ifs <;> [exact le_rfl; exact hμ y]

theorem mass_center (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (a : ℝ) (ha : 0 ≤ a) :
    μ x ≤ mass μ x a := by
  have hs := single_le_sum (s:=univ) (f:=fun y => if dist x y ≤ a then μ y else 0)
    (fun y _ => by split_ifs <;> [exact hμ y; exact le_rfl]) (mem_univ x)
  simpa only [mass,dist_self,ite_eq_left ha] using hs

theorem radius_shift (R q : ℝ) (j p : ℕ) (hp : p ≤ j) :
    radius R q j=radius R q (j-p)*q^p := by
  unfold radius
  rw [mul_assoc,←pow_add]
  congr 2
  omega

theorem mass_shift (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (R q γ D : ℝ)
    (hR : 0< R) (hq : 0< q) (p j : ℕ) (hp : p ≤ j) (hs : D*q^p ≤ γ) :
    mass μ x (D*radius R q j) ≤ mass μ x (γ*radius R q (j-p)) := by
  apply mass_mono μ hμ x
  rw [radius_shift R q j p hp]
  have h := mul_le_mul_of_nonneg_right hs (radius_pos R q hR hq (j-p)).le
  nlinarith only [h]

def logarithm (μ : X → ℝ) (x : X) (R q γ D : ℝ) (j : ℕ) : ℝ :=
  Real.log (mass μ x (D*radius R q j)/mass μ x (γ*radius R q j))

theorem logarithm_nonneg (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (hx : 1 ≤ μ x)
    (R q γ D : ℝ) (hR : 0< R) (hq : 0< q) (hγ : 0 ≤ γ) (hD : γ ≤ D) (j : ℕ) :
    0 ≤ logarithm μ x R q γ D j := by
  have hr := radius_pos R q hR hq j
  have ha := hx.trans (mass_center μ hμ x _ (mul_nonneg hγ hr.le))
  apply Real.log_nonneg
  apply (le_div_iff₀ (by linarith : 0< mass μ x (γ*radius R q j))).mpr
  simpa only [one_mul] using mass_mono μ hμ x (mul_le_mul_of_nonneg_right hD hr.le)

theorem log_sum (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (hx : 1 ≤ μ x)
    (k R q γ D : ℝ) (hk : ∑ y, μ y ≤ k) (hR : 0< R) (hq : 0< q) (hγ : 0 ≤ γ)
    (hD : γ ≤ D) (p J : ℕ) (hs : D*q^p ≤ γ) :
    (∑ j∈range J, logarithm μ x R q γ D j) ≤ (p:ℝ)*Real.log k := by
  have hk1 : 1 ≤ k := hx.trans ((single_le_sum (fun y _ => hμ y) (mem_univ x)).trans hk)
  have ha (j : ℕ) : 1 ≤ mass μ x (γ*radius R q j) :=
    hx.trans (mass_center μ hμ x _ (mul_nonneg hγ (radius_pos R q hR hq j).le))
  have hb (j : ℕ) : mass μ x (γ*radius R q j) ≤ mass μ x (D*radius R q j) :=
    mass_mono μ hμ x (mul_le_mul_of_nonneg_right hD (radius_pos R q hR hq j).le)
  have ht (j : ℕ) : mass μ x (D*radius R q j) ≤ if j< p then k else mass μ x (γ*radius R q (j-p)) := by
    split_ifs with hj
    · exact (mass_total μ hμ x _).trans hk
    · exact mass_shift μ hμ x R q γ D hR hq p j (by omega) hs
  simpa only [div_one,logarithm] using PilotScales.scale_logarithms
    (fun j => mass μ x (γ*radius R q j)) (fun j => mass μ x (D*radius R q j)) J p 1 k
    (by norm_num) hk1 (fun j _ => ha j) (fun j _ => hb j) (fun j _ => ht j)

def nonheavy (μ : X → ℝ) (x : X) (R q γ D δ : ℝ) (j : ℕ) : Prop :=
  (1+δ)*mass μ x (γ*radius R q j)< mass μ x (D*radius R q j)

theorem nonheavy_log (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (hx : 1 ≤ μ x)
    (R q γ D δ : ℝ) (hR : 0< R) (hq : 0< q) (hγ : 0 ≤ γ) (hδ : 0< δ)
    (j : ℕ) (hj : nonheavy μ x R q γ D δ j) :
    Real.log (1+δ)< logarithm μ x R q γ D j := by
  have ha := hx.trans (mass_center μ hμ x _ (mul_nonneg hγ (radius_pos R q hR hq j).le))
  apply Real.log_lt_log (by linarith : 0< 1+δ)
  exact (lt_div_iff₀ (by linarith : 0< mass μ x (γ*radius R q j))).mpr hj

theorem nonheavy_count (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (hx : 1 ≤ μ x)
    (k R q γ D δ : ℝ) (hk : ∑ y, μ y ≤ k) (hR : 0< R) (hq : 0< q) (hγ : 0 ≤ γ)
    (hD : γ ≤ D) (hδ : 0< δ) (p J : ℕ) (hs : D*q^p ≤ γ) :
    ((range J).filter (nonheavy μ x R q γ D δ)).card ≤ 
      (p:ℝ)*Real.log k/Real.log (1+δ) := by
  have hl : 0< Real.log (1+δ) := Real.log_pos (by linarith)
  apply (le_div_iff₀ hl).mpr
  calc
    _ = ∑ j∈range J, if nonheavy μ x R q γ D δ j then Real.log (1+δ) else 0 := by
      rw [←sum_filter,sum_const,nsmul_eq_mul]
    _  ≤  ∑ j∈range J, logarithm μ x R q γ D j := by
      apply sum_le_sum
      intro j _
      split_ifs with hj
      · exact (nonheavy_log μ hμ x hx R q γ D δ hR hq hγ hδ j hj).le
      · exact logarithm_nonneg μ hμ x hx R q γ D hR hq hγ hD j
    _  ≤  _ := log_sum μ hμ x hx k R q γ D hk hR hq hγ hD p J hs

end UniformKServer.GeometricMass

end


end

end OAI
