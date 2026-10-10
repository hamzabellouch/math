import OAI.Probability.ThorpShuffle.Reynolds

namespace OAI

universe uG uE uV

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical

structure Family (G : Type) [Group G] [Fintype G] where
  Index : Type
  [finiteIndex : Fintype Index]
  Space : Index → Type
  [normed : ∀ i, NormedAddCommGroup (Space i)]
  [innerSpace : ∀ i, InnerProductSpace ℂ (Space i)]
  [finiteDim : ∀ i, FiniteDimensional ℂ (Space i)]
  rep : ∀ i, Representation ℂ G (Space i)
  [irreducible : ∀ i, Representation.IsIrreducible (rep i)]
  positive : ∀ i, 0 < Module.finrank ℂ (Space i)
  unitary : ∀ i g x y, ⟪rep i g x, rep i g y⟫_ℂ = ⟪x, y⟫_ℂ
  distinct : ∀ i j, Nonempty (Representation.Equiv (rep i) (rep j)) → i = j
  regular : ∀ g, ∑ i, (Module.finrank ℂ (Space i) : ℂ) * (rep i).character g =
    if g = 1 then (Fintype.card G : ℂ) else 0

attribute [instance] Family.finiteIndex Family.normed Family.innerSpace Family.finiteDim Family.irreducible

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

def degree (i : F.Index) : ℕ := Module.finrank ℂ (F.Space i)

lemma orthogonal (i j : F.Index) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, (F.rep i).character g * (F.rep j).character g⁻¹ =
      if i = j then 1 else 0 := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne _)
  rw [Fintype.card_eq_nat_card, Representation.char_orthonormal]
  congr 1
  apply propext
  exact ⟨fun h => (F.distinct j i h).symm, fun h => by subst j; exact ⟨Representation.Equiv.refl _⟩⟩

lemma integrated_faithful (f : G → ℂ) (hf : ∀ i, integrated (F.rep i) f = 0) : f = 0 := by
  funext x
  have hh : ∑ i, (F.degree i : ℂ) * LinearMap.trace ℂ (F.Space i)
      (integrated (F.rep i) f * F.rep i x⁻¹) = 0 := by simp [hf]
  simp only [integrated, Finset.sum_mul, smul_mul_assoc, ← map_mul, map_sum, map_smul, smul_eq_mul] at hh
  change ∑ i, (F.degree i : ℂ) * ∑ g, f g * (F.rep i).character (g * x⁻¹) = 0 at hh
  simp_rw [Finset.mul_sum] at hh
  rw [Finset.sum_comm] at hh
  have he (g : G) : ∑ i, (F.degree i : ℂ) * (f g * (F.rep i).character (g * x⁻¹)) =
      f g * (if g * x⁻¹ = 1 then (Fintype.card G : ℂ) else 0) := by
    rw [← F.regular]
    simp only [Finset.mul_sum, degree]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [he, mul_inv_eq_one, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at hh
  exact (mul_eq_zero.mp hh).resolve_right (by exact_mod_cast Fintype.card_ne_zero)

lemma integrated_injective (f k : G → ℂ) (h : ∀ i, integrated (F.rep i) f = integrated (F.rep i) k) : f = k := by
  apply sub_eq_zero.mp
  apply F.integrated_faithful
  intro i
  rw [integrated_sub, h i, sub_self]

def kernel (i : F.Index) (g : G) : ℂ :=
  (F.degree i : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep i).character g⁻¹

lemma kernel_central (i : F.Index) (g h : G) : F.kernel i (h * g * h⁻¹) = F.kernel i g := by
  simp only [kernel, mul_inv_rev, inv_inv]
  rw [← mul_assoc, Representation.char_conj]

lemma integrated_kernel (i j : F.Index) : integrated (F.rep j) (F.kernel i) = if i = j then 1 else 0 := by
  obtain ⟨c, hc⟩ := central_scalar (F.rep j) (F.kernel i) (F.kernel_central i)
  have ht := congrArg (LinearMap.trace ℂ (F.Space j)) hc
  rw [trace_integrated, map_smul, LinearMap.trace_id, smul_eq_mul] at ht
  have hh : ∑ g, F.kernel i g * (F.rep j).character g =
      (F.degree i : ℂ) * (if j = i then 1 else 0) := by
    rw [← F.orthogonal j i]
    simp only [kernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    ring
  rw [hh] at ht
  have hd : (F.degree j : ℂ) ≠ 0 := by exact_mod_cast (F.positive j).ne'
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte, mul_one] at ht ⊢
    have he : c = 1 := (mul_right_cancel₀ hd (ht.symm.trans (one_mul _).symm))
    simpa only [he, one_smul, Module.End.one_eq_id] using hc
  · simp only [ite_eq_right (Ne.symm hij), mul_zero] at ht
    have he : c = 0 := (mul_eq_zero.mp ht.symm).resolve_right hd
    simp only [ite_eq_right hij, hc, he, zero_smul]

lemma kernel_convolution (i j : F.Index) : convolution (F.kernel i) (F.kernel j) =
    if i = j then F.kernel i else 0 := by
  apply F.integrated_injective
  intro k
  rw [integrated_convolution, F.integrated_kernel, F.integrated_kernel]
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte, integrated_kernel]
    split_ifs <;> simp
  · rw [ite_eq_right hij]
    simp only [integrated, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    by_cases hik : i = k
    · subst k; simp [Ne.symm hij]
    · simp [hik]

lemma kernel_sum : (∑ i, F.kernel i) = delta := by
  apply F.integrated_injective
  intro j
  rw [integrated_sum, integrated_delta]
  simp only [integrated_kernel, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end Family
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Fintype G] in
lemma character_inv (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (g : G) :
    ρ.character g⁻¹ = conj (ρ.character g) := by
  let b := stdOrthonormalBasis ℂ E
  simp only [Representation.character, LinearMap.trace_eq_sum_inner _ b, map_sum,
    inner_inv ρ hu, inner_conj_symm]

omit [FiniteDimensional ℂ E] in
lemma integrated_symmetric (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (f : G → ℂ) (hf : ∀ g, conj (f g⁻¹) = f g) : (integrated ρ f).IsSymmetric := by
  intro x y
  simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  have he := Equiv.sum_comp (Equiv.inv G) (fun g => conj (f g) * ⟪ρ g x, y⟫_ℂ)
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Equiv.inv_apply, hf]
  rw [← inner_inv ρ hu, inv_inv]

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

lemma kernel_star (i : F.Index) (g : G) : conj (F.kernel i g⁻¹) = F.kernel i g := by
  simp only [kernel, inv_inv, map_mul, map_inv₀, map_natCast, character_inv _ (F.unitary i)]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

def projector (ρ : Representation ℂ G V) (i : F.Index) : Module.End ℂ V := integrated ρ (F.kernel i)

lemma projector_mul (ρ : Representation ℂ G V) (i j : F.Index) :
    F.projector ρ i * F.projector ρ j = if i = j then F.projector ρ i else 0 := by
  rw [projector, projector, ← integrated_convolution, F.kernel_convolution]
  split_ifs <;> simp only [integrated, Pi.zero_apply, zero_smul, Finset.sum_const_zero]

lemma projector_idempotent (ρ : Representation ℂ G V) (i : F.Index) :
    IsIdempotentElem (F.projector ρ i) := by
  simpa only [IsIdempotentElem, ↓reduceIte] using F.projector_mul ρ i i

lemma projector_sum (ρ : Representation ℂ G V) : ∑ i, F.projector ρ i = 1 := by
  simp only [projector]
  rw [← integrated_sum, F.kernel_sum, integrated_delta]

lemma projector_commute (ρ : Representation ℂ G V) (i : F.Index) (g : G) :
    Commute (F.projector ρ i) (ρ g) := integrated_central ρ _ (F.kernel_central i) g

omit [FiniteDimensional ℂ E] in
lemma projector_symmetric (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (i : F.Index) :
    (F.projector ρ i).IsSymmetric := integrated_symmetric ρ hu _ (F.kernel_star i)

lemma kernel_sum_sq (s : Finset F.Index) :
    (Fintype.card G : ℝ) * ∑ g, ‖∑ i ∈ s, F.kernel i g‖ ^ 2 = ∑ i ∈ s, (F.degree i : ℝ) ^ 2 := by
  have hh (i j : F.Index) : (Fintype.card G : ℂ) * ∑ g, conj (F.kernel i g) * F.kernel j g =
      if i = j then (F.degree i : ℂ) ^ 2 else 0 := by
    have hc : ∀ g, conj (F.kernel i g) =
        (F.degree i : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep i).character g := by
      intro g
      calc
        _ = F.kernel i g⁻¹ := by simpa only [inv_inv] using F.kernel_star i g⁻¹
        _ = _ := by rw [kernel, inv_inv]
    simp_rw [hc]
    simp only [kernel]
    have he : (Fintype.card G : ℂ) * ∑ g,
        ((F.degree i : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep i).character g) *
          ((F.degree j : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep j).character g⁻¹) =
        (F.degree i : ℂ) * (F.degree j : ℂ) *
          ((Fintype.card G : ℂ)⁻¹ * ∑ g, (F.rep i).character g * (F.rep j).character g⁻¹) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      field_simp
    rw [he, F.orthogonal]
    split_ifs with h
    · subst j; ring
    · ring
  have he : (Fintype.card G : ℂ) * ∑ g, conj (∑ i ∈ s, F.kernel i g) * (∑ i ∈ s, F.kernel i g) =
      ∑ i ∈ s, (F.degree i : ℂ) ^ 2 := by
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    have hz (i : F.Index) : ∑ g, (Fintype.card G : ℂ) * (conj (F.kernel i g) * F.kernel j g) =
        if i = j then (F.degree i : ℂ)^2 else 0 := by rw [← Finset.mul_sum, hh]
    simp only [hz, Finset.sum_ite_eq', hj, ↓reduceIte]
  simp only [Complex.conj_mul'] at he
  apply Complex.ofReal_injective
  push_cast
  exact he

end Family
end Thorp.Fourier

end

end OAI
