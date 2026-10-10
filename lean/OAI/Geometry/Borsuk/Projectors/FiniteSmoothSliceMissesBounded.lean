import Mathlib
import OAI.Geometry.Borsuk.Projectors.FiniteSmoothSliceMisses

namespace OAI

namespace BorsukNine
open scoped BigOperators
lemma finite_smooth_slice_misses_bounded (n m : ℕ) (hnm : n < m)
    {κ : Type*} [Fintype κ] (L : κ → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (g : κ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c)) :
    ∃ z : EuclideanSpace ℝ (Fin m), (∀ i, (2*(m:ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧ ∀ c x, L c x = 1 → g c x ≠ z := by
  have hm : 0 < m := by omega
  let V : Set (EuclideanSpace ℝ (Fin m)) := {y | ∀ i, 1 < y i ∧ y i < 2}
  have hVo : IsOpen V := by
    have he : V = ⋂ i, {y : EuclideanSpace ℝ (Fin m) | 1 < y i ∧ y i < 2} := by
      ext y; simp [V]
    rw [he]
    exact isOpen_iInter_of_finite (fun i => (isOpen_lt continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i)).inter
      (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i) continuous_const))
  have hVn : V.Nonempty := ⟨WithLp.toLp 2 (fun _ => (3/2:ℝ)),fun _ => by norm_num⟩
  obtain ⟨z,⟨y,hy,hz⟩,hp,hs,hmiss⟩ := finite_smooth_slice_misses n m hnm L g hg
    hVo hVn (fun y hy i => lt_trans zero_lt_one (hy i).1)
  have hmm : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hsum : 0 < ∑ i, y i := Finset.sum_pos (fun i _ => by linarith [(hy i).1])
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,hm⟩⟩)
  have hbound : ∑ i, y i < 2*(m:ℝ) := by
    have hh := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0,hm⟩⟩) (fun i _ => (hy i).2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hh
  refine ⟨z,?_,hs,hmiss⟩
  intro i
  rw [hz]
  change (2*(m:ℝ))⁻¹ < (∑ i, y i)⁻¹ * y i
  have hinv : (2*(m:ℝ))⁻¹ < (∑ i, y i)⁻¹ := by
    exact (inv_lt_inv₀ (by positivity) hsum).mpr hbound
  exact hinv.trans (by nlinarith [(hy i).1,inv_pos.mpr hsum])

lemma finite_smooth_slice_misses_general {D ι κ : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    [Fintype ι] [Fintype κ]
    (hd : Module.finrank ℝ D < Fintype.card ι)
    (L : κ → D →L[ℝ] ℝ) (g : κ → D → EuclideanSpace ℝ ι)
    (hg : ∀ c, ContDiff ℝ (⊤ : ℕ∞) (g c)) :
    ∃ z : EuclideanSpace ℝ ι, (∀ i, (2*(Fintype.card ι:ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧ ∀ c x, L c x = 1 → g c x ≠ z := by
  let eD := (stdOrthonormalBasis ℝ D).repr
  let eY := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  let L' := fun c => (L c).comp eD.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let g' := fun c x => eY (g c (eD.symm x))
  have hg' (c : κ) : ContDiff ℝ (⊤ : ℕ∞) (g' c) :=
    eY.toContinuousLinearEquiv.contDiff.comp ((hg c).comp eD.symm.toContinuousLinearEquiv.contDiff)
  obtain ⟨z,hp,hs,hm⟩ := finite_smooth_slice_misses_bounded _ _ hd L' g' hg'
  have heY (q : EuclideanSpace ℝ (Fin (Fintype.card ι))) (i : ι) :
      (eY.symm q) i = q ((Fintype.equivFin ι) i) := by
    simp [eY, LinearIsometryEquiv.piLpCongrLeft_symm,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  refine ⟨eY.symm z,?_,?_,?_⟩
  · intro i
    rw [heY]
    exact hp ((Fintype.equivFin ι) i)
  · simp only [heY]
    rw [Equiv.sum_comp]
    exact hs
  · intro c x hx he
    apply hm c (eD x)
    · simpa only [L',ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply] using hx
    · change eY (g c (eD.symm (eD x))) = z
      rw [LinearIsometryEquiv.symm_apply_apply,he,LinearIsometryEquiv.apply_symm_apply]
end BorsukNine

end OAI
