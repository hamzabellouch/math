import OAI.Geometry.Convex.GeneralMahler.Cone

namespace OAI
/-! Euclidean projection onto a closed convex cone and Moreau decomposition. -/
noncomputable section
open Set Filter Topology Real Metric InnerProductSpace Asymptotics
open scoped RealInnerProductSpace
namespace GeneralMahler
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def coneProj (C : ProperCone ℝ E) (u : E) : E :=
  (exists_norm_eq_iInf_of_complete_convex C.nonempty C.isClosed.isComplete C.convex u).choose

variable (C : ProperCone ℝ E)
local notation "f" => coneProj C

theorem proj_mem (x:E) : f x ∈ C :=
  (exists_norm_eq_iInf_of_complete_convex C.nonempty C.isClosed.isComplete C.convex x).choose_spec.1

theorem proj_vi (x:E) {v : E} (hv : v ∈ C) :
    ⟪x-f x,v-f x⟫ ≤ 0 := by
  exact ((norm_eq_iInf_iff_real_inner_le_zero C.convex (proj_mem C _)).mp
    ((exists_norm_eq_iInf_of_complete_convex C.nonempty C.isClosed.isComplete C.convex x).choose_spec.2))
    _ hv

theorem proj_unique {x v:E} (hv : v ∈ C) (he : ∀ y ∈ C, ⟪x-v,y-v⟫ ≤ 0) :
    f x = v := by
  have h₁ := proj_vi C x hv
  have h₂ := he _ (proj_mem C x)
  rw [show x-v = (x-f x)+(f x-v) by abel, inner_add_left,
    real_inner_self_eq_norm_sq, show f x-v = -(v-f x) by abel, inner_neg_right] at h₂
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [norm_neg] at h₂
  rw [norm_sub_rev]
  nlinarith

theorem proj_of_mem {x:E} (hx : x ∈ C) : f x = x :=
  proj_unique C hx (by simp)

theorem proj_orthogonal (x:E) : ⟪x-f x,f x⟫ = 0 := by
  have h₁ := proj_vi C x C.zero_mem
  have h₂ := proj_vi C x (C.add_mem (proj_mem C x) (proj_mem C x))
  rw [zero_sub,inner_neg_right] at h₁
  rw [add_sub_cancel_right] at h₂
  linarith

theorem proj_residual_dual (x:E) : f x - x ∈ posDual C := by
  rw [mem_posDual]
  intro y hy
  have h := proj_vi C x (C.add_mem hy (proj_mem C x))
  rw [add_sub_cancel_right] at h
  rw [real_inner_comm, show f x-x = -(x-f x) by abel, inner_neg_left]
  linarith

theorem proj_moreau (x:E) :
    coneProj (posDual C) (-x) = coneProj C x - x := by
  apply proj_unique (posDual C) (proj_residual_dual C x)
  intro y hy
  rw [show -x-(f x-x) = -f x by abel, inner_neg_left,inner_sub_right,
    show f x-x = -(x-f x) by abel, inner_neg_right, real_inner_comm (x-f x),
    proj_orthogonal]
  have he := (mem_posDual).mp hy (proj_mem C x)
  linarith

lemma proj_zero_of_dual (x : E) (hx : -x ∈ posDual C) :
    coneProj C x = 0 := by
  have h := proj_moreau C x
  rw [proj_of_mem _ hx] at h
  exact (by rw [← add_left_inj (-x)]; simpa [sub_eq_add_neg] using h.symm)

theorem proj_firm (x y:E) :
    ‖f x-f y‖^2 ≤ ⟪x-y,f x-f y⟫ := by
  have hx := proj_vi C x (proj_mem C y)
  have hy := proj_vi C y (proj_mem C x)
  rw [show f y-f x = -(f x-f y) by abel, inner_neg_right] at hx
  rw [show x-y = (x-f x)-(y-f y)+(f x-f y) by abel, inner_add_left,
    inner_sub_left,real_inner_self_eq_norm_sq]
  linarith

theorem coneProj_lip : LipschitzWith 1 f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one,one_mul]
  have h := (proj_firm C x y).trans (real_inner_le_norm ..)
  nlinarith [norm_nonneg (x-y),norm_nonneg (f x-f y)]

def energy (u:E) := ‖coneProj C u‖^2 /2

lemma energy_lower (x:E) {y:E} (hy : y ∈ C) :
    ⟪y,x⟫ - ‖y‖^2/2 ≤ energy C x := by
  have he : 0 ≤ ⟪y,f x - x⟫ := mem_posDual.mp (proj_residual_dual C x) hy
  rw [inner_sub_right] at he
  have hh := real_inner_le_norm y (f x)
  unfold energy; nlinarith [sq_nonneg (‖y‖-‖coneProj C x‖)]

theorem energy_eq (x:E) :
    energy C x = ⟪f x,x⟫ - ‖f x‖^2/2 := by
  have he := proj_orthogonal C x
  rw [inner_sub_left, real_inner_self_eq_norm_sq,real_inner_comm] at he
  unfold energy; nlinarith

theorem energy_minorant (x y:E) :
    ⟪f x,y-x⟫ ≤ energy C y-energy C x := by
  have h := energy_lower C y (proj_mem C x)
  rw [energy_eq C x, inner_sub_right]
  linarith

theorem energy_hasFDeriv (x:E) :
    HasFDerivAt (energy C) (innerSL ℝ (f x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,isLittleO_iff]
  intro c hc
  have hh := ball_mem_nhds (0:E) hc
  filter_upwards [hh] with v hv
  have h₁ := energy_minorant C x (x+v)
  have h₂ := energy_minorant C (x+v) x
  have h₃ := real_inner_le_norm (f (x+v)-f x) v
  have h₄ := coneProj_lip C |>.dist_le_mul (x+v) x
  simp only [add_sub_cancel_left] at h₁
  rw [show x-(x+v) = -v by abel, inner_neg_right] at h₂
  rw [inner_sub_left] at h₃
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,add_sub_cancel_left] at h₄
  have hv' := mem_ball_zero_iff.mp hv
  change ‖energy C (x+v) - energy C x - ⟪f x,v⟫‖ ≤ c*‖v‖
  rw [Real.norm_eq_abs]
  rw [abs_le]; constructor <;> nlinarith [norm_nonneg v]

theorem coneProj_fderiv_symmetric (x:E) (v w:E) :
    ⟪fderiv ℝ f x v,w⟫ = ⟪v,fderiv ℝ f x w⟫ := by
  by_cases h : DifferentiableAt ℝ f x
  · have hc : HasFDerivAt (fun y => innerSL ℝ (f y)) _ x :=
      (innerSL (E := E) ℝ).hasFDerivAt.comp x h.hasFDerivAt
    have he := second_derivative_symmetric_of_eventually_of_real
      (Filter.Eventually.of_forall (energy_hasFDeriv C)) hc v w
    change ⟪fderiv ℝ f x v,w⟫ = ⟪fderiv ℝ f x w,v⟫ at he
    rw [he,real_inner_comm]
  · simp [fderiv_zero_of_not_differentiableAt h]

theorem coneProj_fderiv_pos (x:E) (v : E) :
    0 ≤ ⟪v, fderiv ℝ f x v⟫ := by
  by_cases hx : DifferentiableAt ℝ f x
  · let line := fun t:ℝ => x+t • v
    let g := fun t => ⟪v,f (line t)⟫
    have hm : Monotone g := by
      intro a b hab
      rcases hab.eq_or_lt with h|h
      · simp [h]
      have hh := proj_firm C (line b) (line a)
      have he : line b-line a = (b-a) • v := by dsimp [line]; rw [sub_smul]; abel
      rw [he,real_inner_smul_left,inner_sub_right] at hh
      dsimp only [g]; nlinarith [sq_nonneg ‖f (line b)-f (line a)‖]
    have hd : HasDerivAt line v 0 := by
      change HasDerivAt ((fun _ : ℝ => x) + fun t : ℝ => t • v) v 0
      simpa only [line, Pi.add_apply, zero_add,one_smul] using ((hasDerivAt_const (x := (0:ℝ)) x).add
        ((hasDerivAt_id' (0:ℝ)).smul_const v))
    have ha : HasDerivAt g (⟪v,fderiv ℝ f x v⟫) 0 := by
      change HasDerivAt ((innerSL ℝ v) ∘ f ∘ line) _ _
      have he : line 0 = x := by simp [line]
      have Hx : HasFDerivAt f (fderiv ℝ f x) (line 0) := he ▸ hx.hasFDerivAt
      exact (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt _ (Hx.comp_hasDerivAt _ hd)
    rw [← ha.deriv]; exact hm.deriv_nonneg
  · simp [fderiv_zero_of_not_differentiableAt hx]
end GeneralMahler

end

end OAI
