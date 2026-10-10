import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserUniformVelocity
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserDifferenceBudget

namespace OAI

/-! A single integer controls the speed and the joint time-space
Lipschitz constant for every manufactured field. It is fixed before the
input instance and can be hardcoded into the rational Euler program. -/

noncomputable section
namespace ContinuumCoulomb

 theorem exists_uniform_velocity_integer (rho : ℕ) (hrho : 0 < rho) :
    ∃ C : ℕ, 0 < C ∧ ∀ V : Position → ℝ, ContDiff ℝ 6 V →
      (∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ (MoserDifferenceBudget.guard:ℝ)) →
      (∀ x, |manufacturedCharge V x| ≤ (rho:ℝ)/2) →
      (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x, ‖moserVelocity (rho:ℝ) V t x‖ ≤ C) ∧
      (∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ x y,
        ‖moserVelocity (rho:ℝ) V s x-moserVelocity (rho:ℝ) V t y‖ ≤
          (C:ℝ)*(|s-t|+‖x-y‖)) := by
  have hr : (0:ℝ) < rho := by exact_mod_cast hrho
  obtain ⟨A,hA,hAb⟩ := moserVelocity_family_derivative_bound hr
    (Nat.cast_nonneg MoserDifferenceBudget.guard)
  obtain ⟨C,hC⟩ := exists_nat_gt (max (1:ℝ) A)
  have hCp : 0 < C := by
    have he : (1:ℝ) < C := (le_max_left _ _).trans_lt hC
    exact_mod_cast (lt_trans zero_lt_one he)
  have hAC : A ≤ (C:ℝ) := ((le_max_right _ _).trans_lt hC).le
  refine ⟨C,hCp,?_⟩
  intro V hV hb hc
  let F : ℝ×Position → Position := fun p => moserVelocity (rho:ℝ) V p.1 p.2
  let S : Set (ℝ×Position) := Set.Icc (0:ℝ) 1 ×ˢ Set.univ
  have hdom : S ⊆ moserDomain (rho:ℝ) V := moserDomain_contains_time_slab hr V hc
  have hreg : ContDiffOn ℝ 4 F (moserDomain (rho:ℝ) V) :=
    moserVelocity_joint_C4 (rho:ℝ) V hV
  have hopen := moserDomain_isOpen (rho:ℝ) V hV
  have hd (p : ℝ×Position) (hp : p ∈ S) : ‖fderiv ℝ F p‖ ≤ (C:ℝ) := by
    have he := hAb V hV hb hc 1 (by norm_num) p.1 hp.1 p.2
    rw [norm_iteratedFDeriv_one] at he
    exact he.trans hAC
  have hDiff (p : ℝ×Position) (hp : p ∈ S) : DifferentiableAt ℝ F p :=
    (hreg.contDiffAt (hopen.mem_nhds (hdom hp))).differentiableAt (by norm_num)
  constructor
  · intro t ht x
    have he := hAb V hV hb hc 0 (by norm_num) t ht x
    rw [norm_iteratedFDeriv_zero] at he
    exact he.trans hAC
  · intro s hs t ht x y
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le hDiff hd
      ((convex_Icc (0:ℝ) 1).prod convex_univ)
      (show (t,y) ∈ S from ⟨ht,Set.mem_univ _⟩)
      (show (s,x) ∈ S from ⟨hs,Set.mem_univ _⟩)
    change ‖moserVelocity (rho:ℝ) V s x-moserVelocity (rho:ℝ) V t y‖ ≤ _ at he
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg C)
    rw [Prod.norm_def]
    change max ‖s-t‖ ‖x-y‖ ≤ |s-t|+‖x-y‖
    rw [Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _))

 theorem trajectory_coordinate_box (v : ℝ → Position → Position) (z : ℝ → Position)
    {M R : ℝ} (hM : 0 ≤ M)
    (hz : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt z (v t (z t)) (Set.Icc (0:ℝ) 1) t)
    (hv : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖v t (z t)‖ ≤ M)
    (hzero : ∀ a, |z 0 a| ≤ R) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ a, |z t a| ≤ R+M := by
  intro t ht a
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hz hv
    (convex_Icc (0:ℝ) 1) (show (0:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) ht
  have htm : ‖t-(0:ℝ)‖ ≤ 1 := by rw [sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1]; exact ht.2
  have hm : ‖z t-z 0‖ ≤ M := he.trans ((mul_le_mul_of_nonneg_left htm hM).trans_eq (mul_one _))
  have ha : |z t a-z 0 a| ≤ M := by
    have hc := PiLp.norm_apply_le (z t-z 0) a
    simpa only [Real.norm_eq_abs,PiLp.sub_apply] using hc.trans hm
  have htri := abs_add_le (z t a-z 0 a) (z 0 a)
  have hzid : z t a-z 0 a+z 0 a = z t a := by ring
  rw [hzid] at htri
  exact htri.trans (by simpa only [add_comm] using add_le_add ha (hzero a))

end ContinuumCoulomb

end

end OAI
