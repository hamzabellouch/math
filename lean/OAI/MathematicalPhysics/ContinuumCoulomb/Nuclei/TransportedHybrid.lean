import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.TransportedCoulombDerivative

namespace OAI

/-! The transport correction is confined to the support of the field. Outside
that set only the integrable inverse-fifth Coulomb derivative remains. -/

noncomputable section
open Filter
open scoped Topology Classical
namespace ContinuumCoulomb

theorem coulomb_kernel_jets_hybrid_bound :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ (z : Position), z ≠ 0 → ∀ k : ℕ, k ≤ 4 →
        ‖iteratedFDeriv ℝ k Coulomb.coulombKernel z‖ ≤ C*(1+1/‖z‖^5)) ∧
      (∀ (z : Position), z ≠ 0 →
        ‖iteratedFDeriv ℝ 4 Coulomb.coulombKernel z‖ ≤ C/‖z‖^5) := by
  obtain ⟨C,hC,hbound⟩ := coulombKernel_derivative_decay
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  refine ⟨C,hC,?_,?_⟩
  · intro z hz k hk
    have hd : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hb := hbound ⟨k,by omega⟩ z hz
    by_cases hd1 : ‖z‖ ≤ 1
    · have hp : ‖z‖^5 ≤ ‖z‖^(k+1) :=
        pow_le_pow_of_le_one hd.le hd1 (by omega)
      have he : ‖iteratedFDeriv ℝ k Coulomb.coulombKernel z‖ ≤ C/‖z‖^5 := by
        apply (le_div_iff₀ (pow_pos hd 5)).mpr
        exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans hb
      rw [mul_add,mul_one,mul_one_div]
      linarith
    · have hp : 1 ≤ ‖z‖^(k+1) := one_le_pow₀ (le_of_not_ge hd1)
      have hm : ‖iteratedFDeriv ℝ k Coulomb.coulombKernel z‖ ≤
          ‖iteratedFDeriv ℝ k Coulomb.coulombKernel z‖*‖z‖^(k+1) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedFDeriv ℝ k Coulomb.coulombKernel z))
      have he := hm.trans hb
      rw [mul_add,mul_one,mul_one_div]
      linarith [div_nonneg hC0 (pow_nonneg hd.le 5)]
  · intro z hz
    apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hz) 5)).mpr
    exact hbound (4:Fin 5) z hz

theorem transportedCoulomb_hybrid_fourth_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Position → Position), ContDiff ℝ 4 G →
      ∀ (E : Set Position), IsClosed E → (∀ x, x ∉ E → G x = x) →
      ∀ (D : ℝ), 1 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ (y x : Position), y-G x ≠ 0 →
      ‖iteratedFDeriv ℝ 4 (fun b => Coulomb.coulombKernel (y-G b)) x‖ ≤
        24*C*D^4*(1/‖y-G x‖^5 + if x ∈ E then 1 else 0) := by
  classical
  obtain ⟨C,hC,hbound,hpure⟩ := coulomb_kernel_jets_hybrid_bound
  refine ⟨C,hC,fun G hG E hE hfix D hD hGD y x hne => ?_⟩
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  have hf : ContDiffAt ℝ 4 (fun z => Coulomb.coulombKernel (y-z)) (G x) :=
    ((coulombKernel_contDiffAt hne).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)).comp (G x)
        (contDiffAt_const.sub contDiffAt_id)
  by_cases hx : x ∈ E
  · have he := fourth_composite_norm_bound (fun z => Coulomb.coulombKernel (y-z)) G x hf hG
      (fun k hk => by rw [translatedCoulomb_derivative_norm]; exact hbound _ hne k hk)
      (hGD x)
    simp only [ite_eq_left hx]
    apply he.trans_eq
    ring
  · have hlocal : G =ᶠ[𝓝 x] id := by
      filter_upwards [hE.isOpen_compl.mem_nhds hx] with z hz
      exact hfix z hz
    have heq : (fun b => Coulomb.coulombKernel (y-G b)) =ᶠ[𝓝 x]
        (fun b => Coulomb.coulombKernel (y-b)) := by
      filter_upwards [hlocal] with b hb
      rw [hb]
      rfl
    rw [(heq.iteratedFDeriv ℝ 4).eq_of_nhds,translatedCoulomb_derivative_norm]
    have he := hpure (y-x) (by simpa only [hfix x hx] using hne)
    have hfac : C ≤ 24*C*D^4 := by nlinarith [one_le_pow₀ hD (n := 4)]
    simp only [ite_eq_right hx,add_zero,hfix x hx]
    exact he.trans (by simpa only [div_eq_mul_inv,mul_one,one_mul] using
      mul_le_mul_of_nonneg_right hfac (inv_nonneg.mpr (pow_nonneg (norm_nonneg (y-x)) 5)))

end ContinuumCoulomb

end

end OAI
