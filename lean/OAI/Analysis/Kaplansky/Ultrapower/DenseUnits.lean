import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions

namespace OAI

noncomputable section

namespace KaplanskyConsequences

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def DenseUnits (A : Type*) [Monoid A] [TopologicalSpace A] : Prop := Dense {a : A | IsUnit a}

lemma isUnit_positive_shift {a : A} (ha : 0≤a) {r : ℝ} (hr : 0<r) :
    IsUnit (a+r • (1:A)) := by
  exact ((IsStrictlyPositive.smul hr isStrictlyPositive_one).nonneg_add ha).isUnit

lemma denseUnits_of_unitary_polar [Nontrivial A]
    (h : ∀ x : A, ∃ w : A, star w*w=1 ∧ w*star w=1 ∧ w*CFC.sqrt (star x*x)=x) :
    DenseUnits A := by
  rw [DenseUnits,Metric.dense_iff]
  intro x ε hε
  obtain ⟨w,hi,hf,hw⟩ := h x
  let b := CFC.sqrt (star x*x)
  have hb : 0≤b := CFC.sqrt_nonneg _
  let y := w*(b+(ε/2:ℝ) • (1:A))
  have hwunit : IsUnit w := ⟨⟨w,star w,hf,hi⟩,rfl⟩
  have hy : IsUnit y := hwunit.mul (isUnit_positive_shift hb (half_pos hε))
  have hn : ‖w‖ ≤ 1 := by
    have hh := CStarRing.norm_star_mul_self (x:=w)
    rw [hi,norm_one] at hh
    nlinarith [norm_nonneg w]
  refine ⟨y,?_,hy⟩
  rw [Metric.mem_ball,dist_comm,dist_eq_norm]
  have he : x-y= -((ε/2:ℝ) • w) := by
    dsimp [y]
    rw [mul_add,mul_smul_comm,mul_one,hw,sub_add_cancel_left]
  rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hε)]
  nlinarith

open scoped CStarAlgebra in
lemma DenseUnits.map (h : DenseUnits A) (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Surjective φ) :
    DenseUnits B := by
  have hd : Dense (φ '' {a : A | IsUnit a}) := hφ.denseRange.dense_image (map_continuous φ) h
  exact Dense.mono (fun b hb => by obtain ⟨a,ha,rfl⟩ := hb; exact ha.map φ.toMonoidHom) hd

lemma DenseUnits.finite [Nontrivial A] (h : DenseUnits A) (v : A) (hv : star v*v=1) : v*star v=1 := by
  have hn : ‖v‖≤1 := by
    have hh := CStarRing.norm_star_mul_self (x:=v)
    rw [hv,norm_one] at hh
    nlinarith [norm_nonneg v]
  obtain ⟨b,hbv,hb⟩ := Metric.dense_iff.mp h v 1 zero_lt_one
  have he : ‖1-star v*b‖ < 1 := by
    have hbound : ‖star v*(v-b)‖ ≤ ‖v-b‖ := by
      exact (norm_mul_le _ _).trans (by rw [norm_star]; exact mul_le_of_le_one_left (norm_nonneg _) hn)
    have hid : 1-star v*b=star v*(v-b) := by rw [mul_sub,hv]
    rw [hid]
    exact hbound.trans_lt (by simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hbv)
  have hs : IsUnit (star v*b) := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one he
  have hsv : IsUnit (star v) := (hb.mul_right_iff).mp hs
  obtain ⟨z,hz⟩ := hsv
  have hzinv : v= ↑(z⁻¹) := by
    rw [← hz] at hv
    exact ((Units.mul_eq_one_iff_inv_eq (u:=z)).mp hv).symm
  rw [← hz,hzinv]
  exact z.inv_val


end KaplanskyConsequences

end

end OAI
