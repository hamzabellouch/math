import OAI.Probability.ThorpShuffle.JointProjectors

namespace OAI

universe uH uI uE uJ

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical
variable {H : Type uH} {I : Type uI} {E : Type uE} [Group H] [Fintype H] [Fintype I] [AddCommGroup E] [Module ℂ E]

lemma integrated_single_mul (ρ : Representation ℂ (I → H) E) (i : I) (k : H → ℂ) (f : (I → H) → ℂ) :
    integrated (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) k * integrated ρ f =
      integrated ρ (fun g => ∑ h, k h * f (Pi.mulSingle i h⁻¹ * g)) := by
  simp only [integrated, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have he := Equiv.sum_comp (Equiv.mulLeft (Pi.mulSingle i h))
    (fun g : I → H => (k h * f (Pi.mulSingle i h⁻¹ * g)) • ρ g)
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  have hi : Pi.mulSingle i h⁻¹ = (Pi.mulSingle i h : I → H)⁻¹ :=
    (map_inv (MonoidHom.mulSingle (fun _ : I => H) i) h).symm.symm
  simp only [Equiv.coe_mulLeft, hi, inv_mul_cancel_left, smul_mul_smul,
    MonoidHom.comp_apply, MonoidHom.mulSingle_apply, map_mul]

end Thorp.Fourier

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

lemma jointKernel_single (a : I → F.Index) (i : I) (h : H) (g : I → H) :
    F.jointKernel a (Pi.mulSingle i h * g) =
      F.kernel (a i) (h * g i) * ∏ j ∈ Finset.univ.erase i, F.kernel (a j) (g j) := by
  rw [jointKernel, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Pi.mul_apply, Pi.mulSingle_eq_same]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji := (Finset.mem_erase.mp hj).1
  simp only [Pi.mulSingle_eq_of_ne hji, one_mul]

lemma jointKernel_split (a : I → F.Index) (i : I) (g : I → H) :
    F.jointKernel a g = F.kernel (a i) (g i) * ∏ j ∈ Finset.univ.erase i, F.kernel (a j) (g j) :=
  (Finset.mul_prod_erase Finset.univ (fun j => F.kernel (a j) (g j)) (Finset.mem_univ i)).symm

lemma jointKernel_single_convolution (a : I → F.Index) (i : I) (b : F.Index) (g : I → H) :
    ∑ h, F.kernel b h * F.jointKernel a (Pi.mulSingle i h⁻¹ * g) =
      if b = a i then F.jointKernel a g else 0 := by
  simp only [F.jointKernel_single, ← mul_assoc, ← Finset.sum_mul]
  change convolution (F.kernel b) (F.kernel (a i)) (g i) * _ = _
  rw [F.kernel_convolution]
  split_ifs with hb
  · simp only [hb]
    exact (F.jointKernel_split a i g).symm
  · simp

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

lemma projector_jointProjector (ρ : Representation ℂ (I → H) E) (a : I → F.Index)
    (i : I) (b : F.Index) :
    F.projector (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) b * F.jointProjector ρ a =
      if b = a i then F.jointProjector ρ a else 0 := by
  rw [projector, jointProjector, integrated_single_mul]
  simp only [F.jointKernel_single_convolution]
  split_ifs <;> simp only [integrated, zero_smul, Finset.sum_const_zero]

lemma low_fixes_joint (ρ : Representation ℂ (I → H) E) (a : I → F.Index)
    (i : I) (s : Finset F.Index) (ha : a i ∈ s) :
    (∑ b ∈ s, F.projector (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) b) * F.jointProjector ρ a =
      F.jointProjector ρ a := by
  rw [Finset.sum_mul]
  simp only [F.projector_jointProjector, Finset.sum_ite_eq', ha, ↓reduceIte]

end Thorp.Fourier.Family

namespace Thorp.Fourier
open scoped Classical

lemma norm_sum_sq_of_orthogonal {J : Type uJ} {E : Type uE} [Fintype J]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : J → E)
    (hv : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℂ = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have he : ⟪∑ i, v i, ∑ i, v i⟫_ℂ = ∑ i, ⟪v i, v i⟫_ℂ := by
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_eq_single i (fun j _ hji => hv j i hji) (by simp)
  have hr := congrArg Complex.re he
  simpa only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, Complex.ofReal_re] using hr

namespace Family
variable {H I : Type} [Group H] [Fintype H] [Fintype I] [Nonempty I] (F : Family H)

noncomputable def leastFactor (a : I → F.Index) : I :=
  Classical.choose (Finset.exists_min_image Finset.univ (fun i => F.degree (a i)) Finset.univ_nonempty)

lemma leastFactor_le (a : I → F.Index) (i : I) :
    F.degree (a (F.leastFactor a)) ≤ F.degree (a i) :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ
    (fun i => F.degree (a i)) Finset.univ_nonempty)).2 i (Finset.mem_univ i)

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Nonempty I] [FiniteDimensional ℂ E] in
lemma jointProjector_symmetric (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (a : I → F.Index) :
    (F.jointProjector ρ a).IsSymmetric := integrated_symmetric ρ hu _ (F.jointKernel_star a)

omit [Nonempty I] [FiniteDimensional ℂ E] in
lemma jointProjector_orthogonal (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (a b : I → F.Index) (hab : a ≠ b) (x y : E) :
    ⟪F.jointProjector ρ a x, F.jointProjector ρ b y⟫_ℂ = 0 := by
  rw [F.jointProjector_symmetric ρ hu a]
  change ⟪x, (F.jointProjector ρ a * F.jointProjector ρ b) y⟫_ℂ = 0
  rw [F.jointProjector_mul, ite_eq_right hab]
  simp

noncomputable def splitVector (ρ : Representation ℂ (I → H) E) (v : E) (i : I) : E :=
  ∑ a : I → F.Index, if F.leastFactor a = i then F.jointProjector ρ a v else 0

omit [FiniteDimensional ℂ E] in
lemma splitVector_sum (ρ : Representation ℂ (I → H) E) (v : E) :
    ∑ i, F.splitVector ρ v i = v := by
  simp only [splitVector]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← LinearMap.sum_apply, F.jointProjector_sum]
  rfl

omit [FiniteDimensional ℂ E] in
lemma splitVector_orthogonal (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (v : E) (i j : I) (hij : i ≠ j) :
    ⟪F.splitVector ρ v i, F.splitVector ρ v j⟫_ℂ = 0 := by
  simp only [splitVector, sum_inner, inner_sum]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  split_ifs with hai hbj
  · exact F.jointProjector_orthogonal ρ hu b a (by intro h; subst b; exact hij (hai.symm.trans hbj)) v v
  all_goals simp

omit [FiniteDimensional ℂ E] in
lemma splitVector_sq_sum (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (v : E) :
    ∑ i, ‖F.splitVector ρ v i‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [← norm_sum_sq_of_orthogonal _ (F.splitVector_orthogonal ρ hu v), F.splitVector_sum]

lemma leastFactor_pow_le (ρ : Representation ℂ (I → H) E)
    (a : I → F.Index) (ha : F.jointProjector ρ a ≠ 0) :
    F.degree (a (F.leastFactor a)) ^ Fintype.card I ≤ Module.finrank ℂ E := by
  calc
    _ = ∏ _ : I, F.degree (a (F.leastFactor a)) := by simp
    _ ≤ ∏ i, F.degree (a i) := Finset.prod_le_prod (fun i _ => F.leastFactor_le a i)
    _ ≤ _ := F.joint_degree_le ρ a ha

lemma splitVector_low (ρ : Representation ℂ (I → H) E) (v : E) (i : I) :
    (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
      F.projector (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) b) (F.splitVector ρ v i) =
        F.splitVector ρ v i := by
  unfold splitVector
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hai : F.leastFactor a = i
  · simp only [ite_eq_left hai]
    by_cases ha : F.jointProjector ρ a = 0
    · simp [ha]
    · have hb : a i ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa only [hai] using F.leastFactor_pow_le ρ a ha
      exact congrArg (fun f : Module.End ℂ E => f v) (F.low_fixes_joint ρ a i _ hb)
  · simp [hai]

end Family
end Thorp.Fourier

end

end OAI
