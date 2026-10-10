import OAI.Probability.ThorpShuffle.ReciprocalDegrees

namespace OAI

universe uG uV uW uE uI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def integrated (ρ : Representation ℂ G V) (f : G → ℂ) : Module.End ℂ V :=
  ∑ g, f g • ρ g

def reynolds (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (A : V →ₗ[ℂ] W) : V →ₗ[ℂ] W :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, σ g ∘ₗ A ∘ₗ ρ g⁻¹

lemma reynolds_intertwines (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (A : V →ₗ[ℂ] W)
    (h : G) (v : V) : reynolds ρ σ A (ρ h v) = σ h (reynolds ρ σ A v) := by
  simp only [reynolds, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    map_smul, map_sum]
  congr 1
  have he := Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => σ g (A (ρ g⁻¹ (ρ h v))))
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  change σ (h * g) (A (ρ (h * g)⁻¹ (ρ h v))) = σ h (σ g (A (ρ g⁻¹ v)))
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
  congr 2
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

def reynoldsMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (A : V →ₗ[ℂ] W) :
    Representation.IntertwiningMap ρ σ :=
  (reynolds ρ σ A).intertwiningMap_of_isIntertwiningMap ρ σ (reynolds_intertwines ρ σ A)

lemma reynolds_scalar (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    [FiniteDimensional ℂ V] (A : Module.End ℂ V) :
    ∃ c : ℂ, reynolds ρ ρ A = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).surjective (reynoldsMap ρ ρ A)
  refine ⟨c, ?_⟩
  have hh := congrArg Representation.IntertwiningMap.toLinearMap hc
  exact hh.symm

lemma reynolds_zero (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hne : ¬ Nonempty (Representation.Equiv ρ σ)) (A : V →ₗ[ℂ] W) : reynolds ρ σ A = 0 := by
  rcases Representation.IsIrreducible.bijective_or_eq_zero (reynoldsMap ρ σ A) with h | h
  · exact (hne ⟨(reynoldsMap ρ σ A).ofBijective h⟩).elim
  · exact congrArg Representation.IntertwiningMap.toLinearMap h

lemma trace_reynolds (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] (A : Module.End ℂ V) :
    LinearMap.trace ℂ V (reynolds ρ ρ A) = LinearMap.trace ℂ V A := by
  simp only [reynolds, map_smul, map_sum]
  have hh (g : G) : LinearMap.trace ℂ V (ρ g ∘ₗ A ∘ₗ ρ g⁻¹) = LinearMap.trace ℂ V A := by
    rw [LinearMap.trace_comp_comm']
    rw [LinearMap.comp_assoc]
    have he : ρ g⁻¹ ∘ₗ ρ g = LinearMap.id := by
      change ρ g⁻¹ * ρ g = 1
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [he, LinearMap.comp_id]
  simp only [hh, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

lemma reynolds_eq_trace (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V ≠ 0) (A : Module.End ℂ V) :
    reynolds ρ ρ A = (LinearMap.trace ℂ V A / Module.finrank ℂ V) • LinearMap.id := by
  obtain ⟨c, hc⟩ := reynolds_scalar ρ A
  have ht := trace_reynolds ρ A
  rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul] at ht
  have hD : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hV
  rw [hc, ← ht, mul_div_cancel_right₀ _ hD]

section Unitary
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma inner_inv (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (g : G) (x y : E) :
    ⟪x, ρ g⁻¹ y⟫_ℂ = ⟪ρ g x, y⟫_ℂ := by
  have hh := hu g x (ρ g⁻¹ y)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh.symm

theorem coefficient_second_moment (ρ : Representation ℂ G E)
    [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (v w : E) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 =
      ‖v‖ ^ 2 * ‖w‖ ^ 2 / Module.finrank ℂ E := by
  have hh := congrArg (fun A : Module.End ℂ E => ⟪w, A w⟫_ℂ)
    (reynolds_eq_trace ρ hE (InnerProductSpace.rankOne ℂ v v).toLinearMap)
  simp only [reynolds, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    inner_smul_right, inner_sum, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, map_smul, inner_inv ρ hu,
    InnerProductSpace.trace_rankOne, LinearMap.id_apply] at hh
  have hc (g : G) : ⟪ρ g v, w⟫_ℂ * ⟪w, ρ g v⟫_ℂ = (‖⟪w, ρ g v⟫_ℂ‖ ^ 2 : ℝ) := by
    rw [← inner_conj_symm (ρ g v) w, Complex.conj_mul', Complex.ofReal_pow]
  simp only [hc, inner_self_eq_norm_sq_to_K] at hh
  have hr : (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 =
      ‖v‖ ^ 2 / Module.finrank ℂ E * ‖w‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal] using hh
  simpa only [div_mul_eq_mul_div] using hr

end Unitary
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

def convolution (f k : G → ℂ) (x : G) : ℂ := ∑ g, f g * k (g⁻¹ * x)

def delta : G → ℂ := fun g => if g = 1 then 1 else 0

lemma integrated_delta (ρ : Representation ℂ G V) : integrated ρ delta = 1 := by
  simp [integrated, delta]

lemma integrated_sum {I : Type uI} (ρ : Representation ℂ G V) (s : Finset I) (f : I → G → ℂ) :
    integrated ρ (∑ i ∈ s, f i) = ∑ i ∈ s, integrated ρ (f i) := by
  simp only [integrated, Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

lemma integrated_sub (ρ : Representation ℂ G V) (f k : G → ℂ) :
    integrated ρ (f - k) = integrated ρ f - integrated ρ k := by
  simp only [integrated, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

lemma integrated_convolution (ρ : Representation ℂ G V) (f k : G → ℂ) :
    integrated ρ (convolution f k) = integrated ρ f * integrated ρ k := by
  simp only [integrated, convolution, Finset.sum_smul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  have he := Equiv.sum_comp (Equiv.mulLeft g) (fun x => (f g * k (g⁻¹ * x)) • ρ x)
  rw [← he]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, smul_mul_smul]

lemma integrated_central (ρ : Representation ℂ G V) (f : G → ℂ)
    (hf : ∀ g h, f (h * g * h⁻¹) = f g) (h : G) :
    integrated ρ f * ρ h = ρ h * integrated ρ f := by
  rw [integrated, Finset.sum_mul, Finset.mul_sum]
  have he := Equiv.sum_comp (Equiv.mulLeft h |>.trans (Equiv.mulRight h⁻¹))
    (fun g => (f g • ρ g) * ρ h)
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, hf,
    smul_mul_assoc, mul_smul_comm, ← map_mul, inv_mul_cancel_right]

lemma central_scalar (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    [FiniteDimensional ℂ V] (f : G → ℂ) (hf : ∀ g h, f (h * g * h⁻¹) = f g) :
    ∃ c : ℂ, integrated ρ f = c • LinearMap.id := by
  let A : Representation.IntertwiningMap ρ ρ :=
    (integrated ρ f).intertwiningMap_of_isIntertwiningMap ρ ρ (by
      intro g v
      exact congrArg (fun A : Module.End ℂ V => A v) (integrated_central ρ f hf g))
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).surjective A
  exact ⟨c, (congrArg Representation.IntertwiningMap.toLinearMap hc).symm⟩

lemma trace_integrated (ρ : Representation ℂ G V) (f : G → ℂ) :
    LinearMap.trace ℂ V (integrated ρ f) = ∑ g, f g * ρ.character g := by
  simp only [integrated, map_sum, map_smul, smul_eq_mul, Representation.character]

end Thorp.Fourier

end

end OAI
