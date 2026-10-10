import OAI.Probability.ThorpShuffle.ProductProjectors

namespace OAI

universe uG uH uE uJ

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} {H : Type uH} [Group G] [Fintype G] [Group H] [Fintype H]

lemma coset_sum_reindex (φ : H →* G) (ν f : G → ℝ) :
    ∑ g, ν g * ∑ h, f (g * φ h) = ∑ g, (∑ h, ν (g * φ h)) * f g := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun g h => ν (g * φ h) * f g)]
  have he := Equiv.sum_comp (Equiv.inv H) (fun h => ∑ g, ν (g * φ h) * f g)
  rw [← he]
  apply Finset.sum_congr rfl
  intro h _
  have hh := Equiv.sum_comp (Equiv.mulRight ((φ h)⁻¹)) (fun g => ν g * f (g * φ h))
  rw [← hh]
  simp only [Equiv.coe_mulRight, Equiv.inv_apply, map_inv, inv_mul_cancel_right]

lemma weighted_coset_bound (φ : H →* G) (ν f : G → ℝ) (S C : ℝ)
    (hν : ∀ g, 0 ≤ ν g) (hf : ∀ g, 0 ≤ f g) (hS : 0 ≤ S)
    (heval : ∀ g, (Fintype.card H : ℝ) * f g ≤ S * ∑ h, f (g * φ h))
    (hcoset : ∀ g, ∑ h, ν (g * φ h) ≤ C) :
    (Fintype.card H : ℝ) * ∑ g, ν g * f g ≤ S * C * ∑ g, f g := by
  calc
    _ = ∑ g, ν g * ((Fintype.card H : ℝ) * f g) := by rw [Finset.mul_sum]; congr 1; funext g; ring
    _ ≤ ∑ g, ν g * (S * ∑ h, f (g * φ h)) :=
      Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (heval g) (hν g))
    _ = S * ∑ g, (∑ h, ν (g * φ h)) * f g := by
      rw [← coset_sum_reindex φ ν f, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ ≤ S * ∑ g, C * f g := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_right (hcoset g) (hf g))) hS
    _ = _ := by rw [← Finset.mul_sum]; ring

namespace Family
variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H] (F : Family H)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma coset_coefficient_evaluation (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (φ : H →* G) (s : Finset F.Index) (v w : E)
    (hv : (∑ i ∈ s, F.projector (ρ.comp φ) i) v = v) (g : G) :
    (Fintype.card H : ℝ) * ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤
      (∑ i ∈ s, (F.degree i : ℝ)^2) * ∑ h, ‖⟪w, ρ (g * φ h) v⟫_ℂ‖ ^ 2 := by
  have he := F.coefficient_evaluation (ρ.comp φ) s v (ρ g⁻¹ w) hv
  have hh (x : E) : ⟪ρ g⁻¹ w, x⟫_ℂ = ⟪w, ρ g x⟫_ℂ := by
    simpa only [inv_inv] using (inner_inv ρ hu g⁻¹ w x).symm
  simpa only [hh, MonoidHom.comp_apply, map_mul, Module.End.mul_apply] using he

theorem weighted_coefficient (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (φ : H →* G) (s : Finset F.Index) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g)
    (hcoset : ∀ g, ∑ h, ν (g * φ h) ≤ B * (Fintype.card H : ℝ) / Fintype.card G)
    (v w : E) (hv : (∑ i ∈ s, F.projector (ρ.comp φ) i) v = v) :
    ∑ g, ν g * ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤
      B * (∑ i ∈ s, (F.degree i : ℝ)^2) / Module.finrank ℂ E * (‖v‖ ^ 2 * ‖w‖ ^ 2) := by
  have hh := weighted_coset_bound φ ν (fun g => ‖⟪w, ρ g v⟫_ℂ‖ ^ 2)
    (∑ i ∈ s, (F.degree i : ℝ)^2) (B * (Fintype.card H : ℝ) / Fintype.card G)
    hν (fun _ => sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (F.coset_coefficient_evaluation ρ hu φ s v w hv) hcoset
  have hcG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hd : (Module.finrank ℂ E : ℝ) ≠ 0 := by exact_mod_cast hE
  have hs := coefficient_second_moment ρ hu hE v w
  have hs' : ∑ g, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 =
      (Fintype.card G : ℝ) * (‖v‖ ^ 2 * ‖w‖ ^ 2 / Module.finrank ℂ E) := by
    calc
      _ = (Fintype.card G : ℝ) * ((Fintype.card G : ℝ)⁻¹ * ∑ g, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2) := by field_simp
      _ = _ := by rw [hs]
  rw [hs'] at hh
  have he : (∑ i ∈ s, (F.degree i : ℝ)^2) * (B * (Fintype.card H : ℝ) / Fintype.card G) *
      ((Fintype.card G : ℝ) * (‖v‖ ^ 2 * ‖w‖ ^ 2 / Module.finrank ℂ E)) =
      (Fintype.card H : ℝ) * (B * (∑ i ∈ s, (F.degree i : ℝ)^2) /
        Module.finrank ℂ E * (‖v‖ ^ 2 * ‖w‖ ^ 2)) := by field_simp
  rw [he] at hh
  exact (mul_le_mul_iff_right₀ hcH).mp hh

end Family
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical

lemma norm_weighted_sum_sq {J : Type uJ} [Fintype J] (ν : J → ℝ) (f : J → ℂ)
    (hν : ∀ j, 0 ≤ ν j) (h1 : ∑ j, ν j = 1) :
    ‖∑ j, (ν j : ℂ) * f j‖ ^ 2 ≤ ∑ j, ν j * ‖f j‖ ^ 2 := by
  have ht : ‖∑ j, (ν j : ℂ) * f j‖ ≤ ∑ j, ν j * ‖f j‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hν _)] using
      norm_sum_le Finset.univ (fun j => (ν j : ℂ) * f j)
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := ν) (g := fun j => ν j * ‖f j‖ ^ 2) (r := fun j => ν j * ‖f j‖)
    (fun j _ => hν j) (fun j _ => mul_nonneg (hν j) (sq_nonneg _))
    (fun j _ => by nlinarith [sq_nonneg (ν j * ‖f j‖)])
  rw [h1, one_mul] at hc
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hc

namespace Family
variable {G H I : Type} [Group G] [Fintype G] [Group H] [Fintype H]
  [Fintype I] [Nonempty I] (F : Family H)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem split_weighted_coefficient (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (ψ : (I → H) →* G) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g)
    (hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card H : ℝ) / Fintype.card G) (v w : E) :
    ∑ g, ν g * ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤
      (Fintype.card I : ℝ) * B *
        (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
          (F.degree b : ℝ)^2) / Module.finrank ℂ E * (‖v‖ ^ 2 * ‖w‖ ^ 2) := by
  let z := F.splitVector (ρ.comp ψ) v
  let s := Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E)
  let S : ℝ := ∑ b ∈ s, (F.degree b : ℝ)^2
  have hz : ∑ i, z i = v := F.splitVector_sum (ρ.comp ψ) v
  have hz2 : ∑ i, ‖z i‖ ^ 2 = ‖v‖ ^ 2 := F.splitVector_sq_sum (ρ.comp ψ) (fun g => hu (ψ g)) v
  have hpoint (g : G) : ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2 := by
    have hh := complex_cauchy Finset.univ (fun _ : I => 1) (fun i => ⟪w, ρ g (z i)⟫_ℂ)
    simpa only [one_mul, norm_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, ← inner_sum, ← map_sum, hz] using hh
  have hi (i : I) : ∑ g, ν g * ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2 ≤
      B * S / Module.finrank ℂ E * (‖z i‖ ^ 2 * ‖w‖ ^ 2) := by
    exact F.weighted_coefficient ρ hu hE (ψ.comp (MonoidHom.mulSingle (fun _ : I => H) i))
      s ν B hν (hcoset i) (z i) w (F.splitVector_low (ρ.comp ψ) v i)
  calc
    _ ≤ ∑ g, ν g * ((Fintype.card I : ℝ) * ∑ i, ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2) :=
      Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (hpoint g) (hν g))
    _ = (Fintype.card I : ℝ) * ∑ i, ∑ g, ν g * ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2 := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      rw [← Finset.mul_sum]
      ring
    _ ≤ (Fintype.card I : ℝ) * ∑ i, B * S / Module.finrank ℂ E * (‖z i‖ ^ 2 * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, hz2]
      dsimp [S, s]
      ring

theorem integrated_norm_sq (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (ψ : (I → H) →* G) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1) (hB : 0 ≤ B)
    (hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card H : ℝ) / Fintype.card G) (v : E) :
    ‖integrated ρ (fun g => (ν g : ℂ)) v‖ ^ 2 ≤
      (Fintype.card I : ℝ) * B *
        (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
          (F.degree b : ℝ)^2) / Module.finrank ℂ E * ‖v‖ ^ 2 := by
  let A := integrated ρ (fun g => (ν g : ℂ))
  let R := (Fintype.card I : ℝ) * B *
        (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
          (F.degree b : ℝ)^2) / Module.finrank ℂ E
  have hc : ‖⟪A v, A v⟫_ℂ‖ ^ 2 ≤ R * (‖v‖ ^ 2 * ‖A v‖ ^ 2) := by
    calc
      _ = ‖∑ g, (ν g : ℂ) * ⟪A v, ρ g v⟫_ℂ‖ ^ 2 := by
        congr 2
        simp only [A, integrated, LinearMap.sum_apply, LinearMap.smul_apply,
          inner_sum, inner_smul_right]
      _ ≤ ∑ g, ν g * ‖⟪A v, ρ g v⟫_ℂ‖ ^ 2 := norm_weighted_sum_sq ν _ hν h1
      _ ≤ _ := F.split_weighted_coefficient ρ hu hE ψ ν B hν hcoset v (A v)
  have hinner : ‖⟪A v, A v⟫_ℂ‖ = ‖A v‖ ^ 2 := by simp [inner_self_eq_norm_sq_to_K]
  rw [hinner] at hc
  have hR : 0 ≤ R := by positivity
  by_cases hz : ‖A v‖ ^ 2 = 0
  · change ‖A v‖ ^ 2 ≤ R * ‖v‖ ^ 2
    rw [hz]
    exact mul_nonneg hR (sq_nonneg _)
  · have hp : 0 < ‖A v‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    change ‖A v‖ ^ 2 ≤ R * ‖v‖ ^ 2
    nlinarith

end Family
end Thorp.Fourier

end

end OAI
