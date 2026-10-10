import OAI.Probability.ThorpShuffle.FourierFamilies

namespace OAI

universe uI uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical

lemma complex_cauchy {I : Type uI} (s : Finset I) (a b : I → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have ht : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun i => a i * b i)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖))

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem coefficient_evaluation (ρ : Representation ℂ G E) (s : Finset F.Index)
    (v w : E) (hv : (∑ i ∈ s, F.projector ρ i) v = v) :
    (Fintype.card G : ℝ) * ‖⟪w, v⟫_ℂ‖ ^ 2 ≤
      (∑ i ∈ s, (F.degree i : ℝ)^2) * ∑ g, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 := by
  have he : ⟪w, v⟫_ℂ = ∑ g, (∑ i ∈ s, F.kernel i g) * ⟪w, ρ g v⟫_ℂ := by
    conv_lhs => rw [← hv]
    conv_lhs => rw [show ∑ i ∈ s, F.projector ρ i = integrated ρ (∑ i ∈ s, F.kernel i) by
      simp only [projector, integrated_sum]]
    simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right,
      Finset.sum_apply]
  have hh := mul_le_mul_of_nonneg_left
    (complex_cauchy Finset.univ (fun g => ∑ i ∈ s, F.kernel i g) (fun g => ⟪w, ρ g v⟫_ℂ))
    (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  rw [← he, ← mul_assoc, F.kernel_sum_sq] at hh
  exact hh

end Family
end Thorp.Fourier

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

def jointKernel (a : I → F.Index) (g : I → H) : ℂ := ∏ i, F.kernel (a i) (g i)

lemma jointKernel_sum : (∑ a : I → F.Index, F.jointKernel a) = delta := by
  funext g
  simp only [Finset.sum_apply, jointKernel]
  rw [← Fintype.prod_sum (fun i (j : F.Index) => F.kernel j (g i))]
  have hh (i : I) : ∑ j : F.Index, F.kernel j (g i) = if g i = 1 then 1 else 0 :=
    by simpa only [Finset.sum_apply, delta] using congrFun F.kernel_sum (g i)
  simp only [hh]
  by_cases hg : g = 1
  · subst g; simp [delta]
  · have hn : ∃ i, g i ≠ 1 := by
      by_contra hn
      push Not at hn
      exact hg (funext hn)
    obtain ⟨i, hi⟩ := hn
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)]
    simp [delta, hg]

lemma jointKernel_convolution (a b : I → F.Index) :
    convolution (F.jointKernel a) (F.jointKernel b) = if a = b then F.jointKernel a else 0 := by
  funext g
  simp only [convolution, jointKernel, Pi.mul_apply, Pi.inv_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (h : H) => F.kernel (a i) h * F.kernel (b i) (h⁻¹ * g i))]
  have hh (i : I) : ∑ h, F.kernel (a i) h * F.kernel (b i) (h⁻¹ * g i) =
      if a i = b i then F.kernel (a i) (g i) else 0 := by
    have he := congrFun (F.kernel_convolution (a i) (b i)) (g i)
    simpa only [convolution, ite_apply, Pi.zero_apply] using he
  simp only [hh]
  by_cases hab : a = b
  · subst b; simp only [↓reduceIte, jointKernel]
  · rw [ite_eq_right hab]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra hn; push Not at hn; exact hab (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma jointKernel_star (a : I → F.Index) (g : I → H) :
    conj (F.jointKernel a g⁻¹) = F.jointKernel a g := by
  simp only [jointKernel, map_prod, Pi.inv_apply, F.kernel_star]

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

def jointProjector (ρ : Representation ℂ (I → H) E) (a : I → F.Index) : Module.End ℂ E :=
  integrated ρ (F.jointKernel a)

lemma jointProjector_mul (ρ : Representation ℂ (I → H) E) (a b : I → F.Index) :
    F.jointProjector ρ a * F.jointProjector ρ b = if a = b then F.jointProjector ρ a else 0 := by
  rw [jointProjector, jointProjector, ← integrated_convolution, jointKernel_convolution]
  split_ifs <;> simp only [integrated, Pi.zero_apply, zero_smul, Finset.sum_const_zero]

lemma jointProjector_idempotent (ρ : Representation ℂ (I → H) E) (a : I → F.Index) :
    IsIdempotentElem (F.jointProjector ρ a) := by
  simpa only [IsIdempotentElem, ↓reduceIte] using F.jointProjector_mul ρ a a

lemma jointProjector_sum (ρ : Representation ℂ (I → H) E) : ∑ a, F.jointProjector ρ a = 1 := by
  simp only [jointProjector]
  rw [← integrated_sum, F.jointKernel_sum, integrated_delta]

def tensorList (a : I → F.Index) : List I → FDRep ℂ (I → H)
  | [] => FDRep.of (Representation.trivial ℂ (I → H) ℂ)
  | i :: l => FDRep.of (Representation.tprod ((F.rep (a i)).comp (Pi.evalMonoidHom (fun _ : I => H) i)) (tensorList a l).ρ)

omit [Fintype I] in
lemma tensorList_character (a : I → F.Index) (l : List I) (g : I → H) :
    Representation.character (F.tensorList a l).ρ g = (l.map (fun i => (F.rep (a i)).character (g i))).prod := by
  induction l with
  | nil =>
    change LinearMap.trace ℂ ℂ (1 : Module.End ℂ ℂ) = 1
    simp
  | cons i l ih =>
    change (Representation.tprod ((F.rep (a i)).comp (Pi.evalMonoidHom (fun _ : I => H) i))
      (F.tensorList a l).ρ).character g = _
    rw [Representation.char_tensor ((F.rep (a i)).comp (Pi.evalMonoidHom (fun _ : I => H) i))
      (F.tensorList a l).ρ]
    change (F.rep (a i)).character (g i) * Representation.character (F.tensorList a l).ρ g = _
    rw [ih]
    rfl

def tensorFamily (a : I → F.Index) : FDRep ℂ (I → H) := F.tensorList a Finset.univ.toList

lemma tensorFamily_character (a : I → F.Index) (g : I → H) :
    Representation.character (F.tensorFamily a).ρ g = ∏ i, (F.rep (a i)).character (g i) := by
  rw [tensorFamily, tensorList_character]
  exact Finset.prod_map_toList _ _

lemma jointKernel_formula (a : I → F.Index) (g : I → H) :
    F.jointKernel a g = (∏ i, (F.degree (a i) : ℂ)) * (Fintype.card (I → H) : ℂ)⁻¹ *
      Representation.character (F.tensorFamily a).ρ g⁻¹ := by
  simp only [jointKernel, kernel, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, tensorFamily_character, Pi.inv_apply, Fintype.card_fun, Nat.cast_pow, inv_pow]

lemma trace_jointProjector [FiniteDimensional ℂ E] (ρ : Representation ℂ (I → H) E)
    (a : I → F.Index) : LinearMap.trace ℂ E (F.jointProjector ρ a) =
      (∏ i, (F.degree (a i) : ℂ)) * Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) := by
  let : Invertible (Nat.card (I → H) : ℂ) := invertibleOfNonzero (NeZero.ne _)
  rw [jointProjector, trace_integrated]
  simp only [jointKernel_formula]
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  simp only [Finset.mul_sum, Fintype.card_eq_nat_card]
  apply Finset.sum_congr rfl
  intro g _
  ring

theorem joint_degree_le [FiniteDimensional ℂ E] (ρ : Representation ℂ (I → H) E)
    (a : I → F.Index) (ha : F.jointProjector ρ a ≠ 0) :
    (∏ i, F.degree (a i)) ≤ Module.finrank ℂ E := by
  have hp := F.jointProjector_idempotent ρ a
  have ht := F.trace_jointProjector ρ a
  rw [(LinearMap.IsIdempotentElem.isProj_range _ hp).trace] at ht
  have hm : Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) ≠ 0 := by
    intro hz
    have hh := F.trace_jointProjector ρ a
    rw [hz, Nat.cast_zero, mul_zero] at hh
    exact ha (LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hp hh)
  have hn : Module.finrank ℂ (LinearMap.range (F.jointProjector ρ a)) =
      (∏ i, F.degree (a i)) * Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) := by
    exact_mod_cast ht
  calc
    _ ≤ (∏ i, F.degree (a i)) * Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm)
    _ = _ := hn.symm
    _ ≤ Module.finrank ℂ E := Submodule.finrank_le _

end Thorp.Fourier.Family

end

end OAI
