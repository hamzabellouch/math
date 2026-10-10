import OAI.Analysis.LiebThirring.SobolevProjection

namespace OAI

universe u171 u172 u173 u174 u175 u176 u177 u178


noncomputable section
namespace SharpLiebThirring.SobolevProof.C1L2
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology

@[simp] lemma val_sub (u v : C1L2) (x : ℝ) : (u-v).val x = u.val x-v.val x := rfl
@[simp] lemma grad_sub (u v : C1L2) (x : ℝ) : (u-v).grad x = u.grad x-v.grad x := rfl

lemma cut_tendsto (u : C1L2) : Tendsto (fun n ↦ u.cut n) atTop (𝓝 u) := by
  have h : Tendsto (fun n ↦ ∫ x, (cutoff n x-1)^2*(u.val x*u.val x)) atTop (𝓝 0) := by
    simpa only [zero_mul] using integral_real_multiplier_tendsto (l := 0)
      (a := fun n x ↦ (cutoff n x-1)^2) (u.integrable_val_mul u)
      (fun n ↦ (((cutoff_contDiff n).continuous.sub continuous_const).pow 2).aestronglyMeasurable)
      (D := 4) (fun n x ↦ by
        rw [abs_pow]; have hb := abs_sub (cutoff n x) 1
        have hb' := cutoff_bound n x
        have hn := abs_nonneg (cutoff n x-1)
        norm_num at hb
        nlinarith)
      (fun x ↦ by simpa using ((cutoff_tendsto x).sub_const 1).pow 2)
  have heq (n : ℕ) : ‖u.cut n-u‖^2 = ∫ x, (cutoff n x-1)^2*(u.val x*u.val x) := by
    rw [← real_inner_self_eq_norm_sq,inner_eq_integral]
    apply integral_congr_ae
    exact ae_of_all _ (fun x ↦ by simp only [val_sub,cut_val]; ring)
  have hn : Tendsto (fun n ↦ ‖u.cut n-u‖) atTop (𝓝 0) := by
    have hh := h.sqrt
    simpa only [← heq,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

lemma eventually_cut_linearIndependent {ι : Type u171} [Finite ι] {u : ι → C1L2}
    (hu : LinearIndependent ℝ u) : ∀ᶠ n in atTop, LinearIndependent ℝ (fun i ↦ (u i).cut n) :=
  (tendsto_pi_nhds.mpr (fun i ↦ (u i).cut_tendsto)).eventually hu.eventually

lemma val_sum {ι : Type u172} (s : Finset ι) (u : ι → C1L2) (x : ℝ) :
    (∑ i ∈ s, u i).val x = ∑ i ∈ s, (u i).val x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simpa only [Finset.sum_insert ha,val_add] using congrArg ((u a).val x+·) ih

lemma grad_sum {ι : Type u173} (s : Finset ι) (u : ι → C1L2) (x : ℝ) :
    (∑ i ∈ s, u i).grad x = ∑ i ∈ s, (u i).grad x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simpa only [Finset.sum_insert ha,grad_add] using congrArg ((u a).grad x+·) ih

lemma compact_smul (c : ℝ) {u : C1L2} (hu : HasCompactSupport u.val) :
    HasCompactSupport (c • u).val := hu.mul_left

lemma compact_sum {ι : Type u174} (s : Finset ι) (u : ι → C1L2)
    (hu : ∀ i ∈ s, HasCompactSupport (u i).val) : HasCompactSupport (∑ i ∈ s, u i).val := by
  classical
  convert HasCompactSupport.finset_sum hu using 1; try rfl
  funext x
  simp only [val_sum, Finset.sum_apply]

lemma compact_of_mem_span {ι : Type u175} (u : ι → C1L2)
    (hu : ∀ i, HasCompactSupport (u i).val) {v : C1L2}
    (hv : v ∈ Submodule.span ℝ (range u)) : HasCompactSupport v.val := by
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i,rfl⟩ := hx; exact hu i
  | zero =>
      change IsCompact (tsupport (fun _ : ℝ ↦ (0 : ℝ)))
      simp
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact compact_smul c hx

lemma energy_add_left {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (u v w : C1L2) (hw : HasCompactSupport w.val) :
    energy W (u+v) w = energy W u w+energy W v w := by
  simp only [energy,grad_add,val_add,add_mul,mul_add]
  rw [integral_add (u.integrable_grad_mul w) (v.integrable_grad_mul w),
    integral_add (integrable_potential hW u w hw) (integrable_potential hW v w hw)]
  ring

lemma energy_smul_left (W : ℝ → ℝ) (c : ℝ) (u v : C1L2) :
    energy W (c • u) v = c*energy W u v := by
  simp only [energy,grad_smul,val_smul]
  simp_rw [show ∀ x, c*u.grad x*v.grad x = c*(u.grad x*v.grad x) by intros; ring,
    show ∀ x, W x*(c*u.val x)*v.val x = c*(W x*u.val x*v.val x) by intros; ring]
  rw [integral_const_mul,integral_const_mul]; ring

lemma energy_sum_left {ι : Type u176} {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (s : Finset ι) (u : ι → C1L2) (v : C1L2) (hv : HasCompactSupport v.val) :
    energy W (∑ i ∈ s, u i) v = ∑ i ∈ s, energy W (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [energy]
  | insert a s ha ih => rw [Finset.sum_insert ha,energy_add_left hW _ _ _ hv,ih,Finset.sum_insert ha]

lemma energy_sum_sum {ι : Type u177} [Fintype ι] {W : ℝ → ℝ}
    (hW : LocallyIntegrable W volume) (u : ι → C1L2)
    (hu : ∀ i, HasCompactSupport (u i).val) (c : ι → ℝ) :
    energy W (∑ i, c i • u i) (∑ i, c i • u i) =
      ∑ i, ∑ j, c i*c j*energy W (u i) (u j) := by
  classical
  rw [energy_sum_left hW _ _ _ (compact_sum _ _ (fun i _ ↦ compact_smul _ (hu i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [energy_symm,energy_sum_left hW _ _ _ (compact_smul _ (hu i))]
  apply Finset.sum_congr rfl
  intro j _
  rw [energy_smul_left,energy_symm,energy_smul_left]
  ring

lemma inner_sum_sum {ι : Type u178} [Fintype ι] (u : ι → C1L2) (c : ι → ℝ) :
    inner ℝ (∑ i, c i • u i) (∑ i, c i • u i) =
      ∑ i, ∑ j, c i*c j*inner ℝ (u i) (u j) := by
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (u j) (u i)]

end SharpLiebThirring.SobolevProof.C1L2

end

end OAI
