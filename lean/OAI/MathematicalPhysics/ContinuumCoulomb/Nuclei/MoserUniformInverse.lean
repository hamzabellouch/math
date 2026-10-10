import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserUniformVelocity

namespace OAI

/-! Uniform separation of transported nodes: the inverse Lipschitz
constant is fixed over the same bounded family as the forward flow. -/

noncomputable section
open scoped Topology NNReal
namespace ContinuumCoulomb

private theorem velocity_lipschitz_of_joint_bound {rho C : ℝ} (hC : 0 ≤ C)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hc : ∀ x, |manufacturedCharge V x| ≤ rho/2) (hrho : 0 < rho)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ 1 (fun p : ℝ × Position => moserVelocity rho V p.1 p.2) (t,x)‖ ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, LipschitzWith ⟨C,hC⟩ (moserVelocity rho V t) := by
  let F : ℝ × Position → Position := fun p => moserVelocity rho V p.1 p.2
  let S := Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set Position)
  have hdom : S ⊆ moserDomain rho V := moserDomain_contains_time_slab hrho V hc
  have hopen := moserDomain_isOpen rho V hV
  have hreg : ContDiffOn ℝ 4 F (moserDomain rho V) := moserVelocity_joint_C4 rho V hV
  have hLip : LipschitzOnWith ⟨C,hC⟩ F S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun p hp => (hreg.contDiffAt (hopen.mem_nhds (hdom hp))).differentiableAt (by norm_num))
      (fun p hp => by
        have h := hb p.1 hp.1 p.2
        rw [norm_iteratedFDeriv_one] at h
        exact_mod_cast h)
      ((convex_Icc (0 : ℝ) 1).prod convex_univ)
  intro t ht
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [F, dist_prod_same_left] using hLip.dist_le_mul (t,x) ⟨ht,Set.mem_univ _⟩
    (t,y) ⟨ht,Set.mem_univ _⟩

private theorem trajectory_backward_of_lipschitz (rho : ℝ) (V : Position → ℝ)
    (K : ℝ≥0) (hK : ∀ t ∈ Set.Icc (0 : ℝ) 1, LipschitzWith K (moserVelocity rho V t))
    (α β : ℝ → Position)
    (hα : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt α (moserVelocity rho V t (α t)) (Set.Icc (0 : ℝ) 1) t)
    (hβ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt β (moserVelocity rho V t (β t)) (Set.Icc (0 : ℝ) 1) t) :
    dist (α 0) (β 0) ≤ Real.exp (K:ℝ)*dist (α 1) (β 1) := by
  let v : ℝ → Position → Position := fun s x => -(moserVelocity rho V (-s) x)
  have hmap : Set.MapsTo (Neg.neg : ℝ → ℝ) (Set.Icc (-1:ℝ) 0) (Set.Icc (0:ℝ) 1) := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have hd (γ : ℝ → Position)
      (hγ : ∀ t ∈ Set.Icc (0:ℝ) 1,
        HasDerivWithinAt γ (moserVelocity rho V t (γ t)) (Set.Icc (0:ℝ) 1) t)
      (s : ℝ) (hs : s ∈ Set.Ico (-1:ℝ) 0) :
      HasDerivWithinAt (γ ∘ Neg.neg) (v s ((γ ∘ Neg.neg) s)) (Set.Ici s) s := by
    have hmem : -s ∈ Set.Ioc (0:ℝ) 1 := by constructor <;> linarith [hs.1,hs.2]
    have hdγ : HasDerivWithinAt γ (moserVelocity rho V (-s) (γ (-s))) (Set.Iic (-s)) (-s) := by
      apply (hγ (-s) ⟨hmem.1.le,hmem.2⟩).mono_of_mem_nhdsWithin
      apply Filter.mem_of_superset (Icc_mem_nhdsLE hmem.1)
      exact Set.Icc_subset_Icc_right hmem.2
    have hm : Set.MapsTo (Neg.neg : ℝ → ℝ) (Set.Ici s) (Set.Iic (-s)) :=
      fun _ ht => neg_le_neg (Set.mem_Ici.mp ht)
    convert! HasFDerivWithinAt.comp_hasDerivWithinAt s hdγ
      (hasDerivAt_neg s).hasDerivWithinAt hm using 1
    simp [v]
  have hv (s : ℝ) (hs : s ∈ Set.Ico (-1:ℝ) 0) :
      LipschitzOnWith K (v s) (Set.univ : Set Position) :=
    (hK (-s) (hmap ⟨hs.1,hs.2.le⟩)).neg.lipschitzOnWith
  have h := dist_le_of_trajectories_ODE_of_mem (v := v) (s := fun _ => Set.univ) hv
    ((HasDerivWithinAt.continuousOn hα).comp continuous_neg.continuousOn hmap)
    (hd α hα) (fun _ _ => Set.mem_univ _)
    ((HasDerivWithinAt.continuousOn hβ).comp continuous_neg.continuousOn hmap)
    (hd β hβ) (fun _ _ => Set.mem_univ _)
    (le_refl (dist ((α ∘ Neg.neg) (-1)) ((β ∘ Neg.neg) (-1))))
    0 (show (0:ℝ) ∈ Set.Icc (-1:ℝ) 0 by constructor <;> norm_num)
  simpa only [Function.comp_apply, neg_zero, neg_neg, sub_neg_eq_add, zero_add, mul_one,
    mul_comm] using h

/-- One inverse Lipschitz constant works for every actual trajectory family
of every potential with the stated six-derivative bound. -/
theorem moserFlow_family_inverse_bound {rho B : ℝ} (hrho : 0 < rho) (hB : 0 ≤ B) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (V : Position → ℝ), ContDiff ℝ 6 V →
      (∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B) →
      (∀ x, |manufacturedCharge V x| ≤ rho/2) →
      ∀ G : Position → ℝ → Position, IsUnitTimeFlow (moserVelocity rho V) G →
        AntilipschitzWith K (fun x => G x 1) := by
  obtain ⟨C,hC,hCb⟩ := moserVelocity_family_derivative_bound hrho hB
  refine ⟨⟨Real.exp C,(Real.exp_pos C).le⟩,by exact_mod_cast Real.exp_pos C,?_⟩
  intro V hV hb hc G hG
  have hLip := velocity_lipschitz_of_joint_bound hC.le V hV hc hrho
    (fun t ht x => hCb V hV hb hc 1 (by norm_num) t ht x)
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  change dist x y ≤ Real.exp C * dist (G x 1) (G y 1)
  have h := trajectory_backward_of_lipschitz rho V ⟨C,hC.le⟩ hLip
    (G x) (G y) (hG.2 x) (hG.2 y)
  change dist (G x 0) (G y 0) ≤ Real.exp C * dist (G x 1) (G y 1) at h
  simpa only [hG.1] using h

end ContinuumCoulomb

end

end OAI
