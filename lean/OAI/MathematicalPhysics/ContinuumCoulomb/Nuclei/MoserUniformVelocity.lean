import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserUniformDensity
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserFlowRegularity

namespace OAI

/-! The Moser velocity and flow have a common derivative bound over all
potentials with a common order-six bound. -/

noncomputable section
open scoped BigOperators ContDiff
namespace ContinuumCoulomb
open NeutralAtom (dirPartial axis)

private theorem product_four_bound (U : Set (ℝ × Position)) (hU : IsOpen U)
    (f g : ℝ × Position → ℝ) (hf : ContDiffOn ℝ 4 f U) (hg : ContDiffOn ℝ 4 g U)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) {x : ℝ × Position} (hx : x ∈ U)
    (hb : ∀ j ≤ 4, ‖iteratedFDeriv ℝ j f x‖ ≤ B)
    (hc : ∀ j ≤ 4, ‖iteratedFDeriv ℝ j g x‖ ≤ C)
    {k : ℕ} (hk : k ≤ 4) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤ 16*B*C := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx
    (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
  simp_rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := U) _ hU hx] at h
  apply h.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*B*C := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb i (hi'.trans hk)) (Nat.cast_nonneg _))
        (hc (k-i) ((Nat.sub_le k i).trans hk)) (norm_nonneg _) (by positivity)
    _ = (2:ℝ)^k*B*C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ 16*B*C := by
      apply mul_le_mul_of_nonneg_right _ hC
      apply mul_le_mul_of_nonneg_right _ hB
      exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)

private theorem partial_C4 (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (a : Fin 3) :
    ContDiff ℝ 4 (dirPartial V (axis a)) :=
  (hV.fderiv_right (by norm_num : (4 : WithTop ℕ∞)+1 ≤ 6)).clm_apply contDiff_const

private theorem partial_joint_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (a : Fin 3) {k : ℕ} (hk : k ≤ 4) (x : ℝ × Position) :
    ‖iteratedFDeriv ℝ k (fun p : ℝ × Position => dirPartial V (axis a) p.2) x‖ ≤ B := by
  apply contraction_four_bound (ContinuousLinearMap.snd ℝ ℝ Position)
    (ContinuousLinearMap.norm_snd_le ℝ ℝ Position) (dirPartial V (axis a)) (partial_C4 V hV a) hB
    (fun j hj y => ?_) hk x
  have h := dirPartial_iterated_norm_bound V hV (axis a) (show j ≤ 5 by omega) y
  have hn : ‖axis a‖ = 1 := by simp [axis]
  rw [hn, one_mul] at h
  exact h.trans (hb (j+1) (by omega) y)

/-- One bound controls all joint velocity derivatives through order four
for the entire bounded family of potentials. -/
theorem moserVelocity_family_derivative_bound {rho B : ℝ} (hrho : 0 < rho) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Position → ℝ), ContDiff ℝ 6 V →
      (∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B) →
      (∀ x, |manufacturedCharge V x| ≤ rho/2) →
      ∀ k ≤ 4, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
        ‖iteratedFDeriv ℝ k (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) (t,x)‖ ≤ C := by
  let D : ℝ := |rho|+16*(3*B/(4*Real.pi))
  obtain ⟨A,hA,hAb⟩ := uniform_reciprocal_four_bound (B := D) hrho
  refine ⟨48*(B+1)*A/(4*Real.pi), by positivity, ?_⟩
  intro V hV hb hcharge k hk t ht x
  let U := moserDomain rho V
  have hU : IsOpen U := moserDomain_isOpen rho V hV
  have hxU : (t,x) ∈ U := moserDomain_contains_time_slab hrho V hcharge ⟨ht,Set.mem_univ _⟩
  let d : ℝ × Position → ℝ := fun p => homotopyDensity rho V p.1 p.2
  let invd : ℝ × Position → ℝ := fun p => (d p)⁻¹
  have hd : ContDiff ℝ 4 d := homotopyDensity_joint_C4 rho V hV
  have hi : ContDiffOn ℝ 4 invd U := hd.contDiffOn.inv (fun p hp => hp)
  have hiB (j : ℕ) (hj : j ≤ 4) : ‖iteratedFDeriv ℝ j invd (t,x)‖ ≤ A :=
    hAb d hd (t,x) (homotopyDensity_bounds V hcharge ht.1 ht.2 x)
      (fun i hi => homotopyDensity_uniform_derivatives hB V hV hb hi ht x) j hj
  let f : Fin 3 → ℝ × Position → ℝ := fun a p =>
    -(4*Real.pi)⁻¹ * dirPartial V (axis a) p.2
  have hf (a : Fin 3) : ContDiff ℝ 4 (f a) :=
    contDiff_const.mul ((partial_C4 V hV a).comp contDiff_snd)
  have hfB (a : Fin 3) (j : ℕ) (hj : j ≤ 4) :
      ‖iteratedFDeriv ℝ j (f a) (t,x)‖ ≤ B/(4*Real.pi) := by
    change ‖iteratedFDeriv ℝ j (fun p : ℝ × Position =>
      (-(4*Real.pi)⁻¹) • dirPartial V (axis a) p.2) (t,x)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply'
      (f := fun p : ℝ × Position => dirPartial V (axis a) p.2)
      (a := -(4*Real.pi)⁻¹)
      (((partial_C4 V hV a).comp contDiff_snd).of_le (by exact_mod_cast hj)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left (partial_joint_bound V hV hB hb a hj (t,x))
      (by positivity)).trans_eq (by ring)
  let F : Fin 3 → ℝ × Position → ℝ := fun a p => f a p * invd p
  have hF (a : Fin 3) : ContDiffOn ℝ 4 (F a) U := (hf a).contDiffOn.mul hi
  have hFB (a : Fin 3) : ‖iteratedFDeriv ℝ k (F a) (t,x)‖ ≤ 16*(B/(4*Real.pi))*A :=
    product_four_bound U hU (f a) invd (hf a).contDiffOn hi
      (by positivity) hA.le hxU (hfB a) hiB hk
  let L : Fin 3 → ℝ →L[ℝ] Position := fun a =>
    (ContinuousLinearMap.id ℝ ℝ).smulRight (axis a)
  have hL (a : Fin 3) : ‖L a‖ = 1 := by
    simp [L, ContinuousLinearMap.norm_smulRight_apply, axis]
  have hsum : (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) =
      fun p => ∑ a : Fin 3, L a (F a p) := by
    funext p
    ext a
    simp [moserVelocity, L, F, f, invd, d, axis, Pi.single_apply, eq_comm, div_eq_mul_inv, mul_inv_rev, mul_assoc]; ring
  rw [hsum, iteratedFDeriv_fun_sum_apply
    (f := fun a p => L a (F a p)) (fun a _ =>
    (((L a).contDiff.comp_contDiffOn (hF a)).contDiffAt (hU.mem_nhds hxU)).of_le
      (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a : Fin 3, 16*(B/(4*Real.pi))*A := by
      apply Finset.sum_le_sum
      intro a _
      have h := (L a).norm_iteratedFDeriv_comp_left
        ((hF a).contDiffAt (hU.mem_nhds hxU))
        (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
      rw [hL, one_mul] at h
      exact h.trans (hFB a)
    _ ≤ 48*(B+1)*A/(4*Real.pi) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      have hp : 0 < 4*Real.pi := by positivity
      apply (le_div_iff₀ hp).mpr
      field_simp
      nlinarith

/-- The variational estimate has a constant fixed before the potential is chosen. -/
theorem moserFlow_family_derivative_bound (hpublished : PublishedC4FlowInput)
    {rho B : ℝ} (hrho : 0 < rho) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Position → ℝ), ContDiff ℝ 6 V →
      (∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B) →
      (∀ x, |manufacturedCharge V x| ≤ rho/2) →
      ∀ G : Position → ℝ → Position, IsUnitTimeFlow (moserVelocity rho V) G →
      ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
        ‖iteratedFDeriv ℝ k (fun y => G y t) x‖ ≤ C := by
  obtain ⟨A,hA,hAb⟩ := moserVelocity_family_derivative_bound hrho hB
  obtain ⟨C,hC,hCb⟩ := hpublished.uniform A hA.le
  refine ⟨C,hC,fun V hV hb hc G hG => ?_⟩
  exact hCb (moserDomain rho V) (moserDomain_isOpen rho V hV)
    (moserDomain_contains_time_slab hrho V hc) (moserVelocity rho V)
    (moserVelocity_joint_C4 rho V hV) (hAb V hV hb hc) G hG

end ContinuumCoulomb

end

end OAI
