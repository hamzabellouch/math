import OAI.Analysis.AncientFlat.Profile.SphereCalculus
import OAI.Analysis.AncientFlat.Kernel.BilapNorm

namespace OAI
noncomputable section
open scoped ContDiff Laplacian
namespace CompactCore
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma id_jet_bound (x : V) (hx : ‖x‖≤1) (j : ℕ) (hj : j≤2) :
    ‖iteratedFDeriv ℝ j (id : V → V) x‖≤1 := by
  interval_cases j
  · simpa only [norm_iteratedFDeriv_zero,id_eq] using hx
  · simpa only [norm_iteratedFDeriv_one,fderiv_id] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := V))
  · rw [show (2:ℕ)=1+1 from rfl,←norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_one]
    change ‖fderiv ℝ (fun y : V => fderiv ℝ (id : V → V) y) x‖≤1
    simp only [fderiv_id,fderiv_const_apply]
    change ‖(0 : V →L[ℝ] (V →L[ℝ] V))‖ ≤ (1:ℝ)
    rw [ContinuousLinearMap.opNorm_zero]
    exact zero_le_one

lemma apply_jet_bound (f : V → V →L[ℝ] E) (hf : ContDiff ℝ ∞ f)
    (x : V) (hx : ‖x‖≤1) (M : ℝ) (hM : 0≤M)
    (hb : ∀ j : ℕ, j≤2 → ‖iteratedFDeriv ℝ j f x‖≤M) :
    ∀ j : ℕ, j≤2 → ‖iteratedFDeriv ℝ j (fun y => f y y) x‖≤4*M := by
  intro j hj
  have he := norm_iteratedFDeriv_clm_apply hf (contDiff_id : ContDiff ℝ ∞ (id : V → V)) x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  apply he.trans
  calc
    _ ≤ ∑ i∈Finset.range (j+1), ((j.choose i:ℕ):ℝ)*M := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i≤j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have ha := mul_le_mul_of_nonneg_left (hb i (by omega)) (Nat.cast_nonneg (j.choose i))
      exact (mul_le_mul ha (id_jet_bound x hx (j-i) (by omega))
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hM)).trans_eq (mul_one _)
    _ ≤ 4*M := by
      interval_cases j <;> norm_num [Finset.sum_range_succ,Nat.choose] <;> linarith
lemma correction_jet_bound (f : V → ℂ) (hf : ContDiff ℝ ∞ f)
    (x : V) (hx : ‖x‖≤1) (M : ℝ) (hM : 0≤M)
    (hb : ∀ j : ℕ, j≤4 → ‖iteratedFDeriv ℝ j f x‖≤M) :
    ∀ j : ℕ, j≤2 → ‖iteratedFDeriv ℝ j (correction f) x‖≤132*M := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by simp)
  have hb1 : ∀ j : ℕ, j≤2 → ‖iteratedFDeriv ℝ j (fderiv ℝ f) x‖≤M := by
    intro j hj
    rw [norm_iteratedFDeriv_fderiv]
    exact hb (j+1) (by omega)
  have hb2 : ∀ j : ℕ, j≤2 → ‖iteratedFDeriv ℝ j (fderiv ℝ (fderiv ℝ f)) x‖≤M := by
    intro j hj
    rw [norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_fderiv]
    exact hb (j+1+1) (by omega)
  have h1 := apply_jet_bound _ hd x hx M hM hb1
  have h2 := apply_jet_bound _ hdd x hx M hM hb2
  have h3 := apply_jet_bound _ (hdd.clm_apply contDiff_id) x hx (4*M) (by positivity) h2
  intro j hj
  have hs : correction f=(fun y => fderiv ℝ (fderiv ℝ f) y y y)+
      (29:ℂ) • (fun y => fderiv ℝ f y y) := by
    funext y
    simp only [correction,radialJet,iteratedFDeriv_one_apply,iteratedFDeriv_two_apply,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have ha : ContDiff ℝ (j:ℕ∞ω) (fun y => fderiv ℝ (fderiv ℝ f) y y y) := by
    simpa only [id_eq] using (((hdd.clm_apply contDiff_id).clm_apply contDiff_id).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))
  have hb' : ContDiff ℝ (j:ℕ∞ω) (fun y => fderiv ℝ f y y) := by
    simpa only [id_eq] using ((hd.clm_apply contDiff_id).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))
  have hadd := iteratedFDeriv_add ha (hb'.const_smul (29:ℂ))
  rw [hs]
  change ‖iteratedFDeriv ℝ j ((fun y => fderiv ℝ (fderiv ℝ f) y y y) +
    (fun y => (29:ℂ) • fderiv ℝ f y y)) x‖ ≤ 132*M
  rw [hadd,Pi.add_apply,iteratedFDeriv_const_smul_apply' hb'.contDiffAt]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul]
  norm_num
  have hh3 := h3 j hj
  simp only [id_eq] at hh3
  linarith [h1 j hj]
end CompactCore

end

end OAI
