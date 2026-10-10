import OAI.Analysis.NuclearUltrapower.SOSSemantics
import OAI.Analysis.NuclearUltrapower.IntegerMatrices
import OAI.Analysis.NuclearUltrapower.Laplacian

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.SOSEnergy
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

def energy (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) : ℝ :=
  ∑ s ∈ S, ‖ρ s x - x‖ ^ 2

theorem energy_nonneg (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    0 ≤ energy S ρ x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Telescoping a word uses only the unitary relations and the specified generators. -/
theorem word_norm_bound (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) (r : ℝ)
    (w : List Γ) (hw : ∀ s ∈ w, ‖ρ s x - x‖ ≤ r) :
    ‖ρ w.prod x - x‖ ≤ w.length * r := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := hw a (by simp)
    have ht := ih (fun s hs => hw s (by simp [hs]))
    have he : ρ (a * w.prod) x - x =
        ρ a (ρ w.prod x - x) + (ρ a x - x) := by
      rw [map_mul]
      change ρ a (ρ w.prod x) - x = _
      rw [map_sub]
      abel
    simp only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [he]
    calc
      _ ≤ ‖ρ a (ρ w.prod x - x)‖ + ‖ρ a x - x‖ := norm_add_le _ _
      _ = ‖ρ w.prod x - x‖ + ‖ρ a x - x‖ := by rw [(ρ a).norm_map]
      _ ≤ w.length * r + r := add_le_add ht ha
      _ = _ := by ring

/-- A length-at-most-four word has energy bounded by sixteen times the generator energy. -/
theorem word_sq_bound (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (w : List Γ) (hw : ∀ s ∈ w, s ∈ S) (hlen : w.length ≤ 4) :
    ‖ρ w.prod x - x‖ ^ 2 ≤ 16 * energy S ρ x := by
  have he := energy_nonneg S ρ x
  have hb : ∀ s ∈ w, ‖ρ s x - x‖ ≤ Real.sqrt (energy S ρ x) := by
    intro s hs
    apply (Real.le_sqrt (norm_nonneg _) he).mpr
    exact Finset.single_le_sum (fun t _ => sq_nonneg ‖ρ t x - x‖) (hw s hs)
  have hn := word_norm_bound ρ x _ w hb
  have h4 : (w.length : ℝ) ≤ 4 := by exact_mod_cast hlen
  have hn' : ‖ρ w.prod x - x‖ ≤ 4 * Real.sqrt (energy S ρ x) :=
    hn.trans (mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg _))
  nlinarith [Real.sq_sqrt he, norm_nonneg (ρ w.prod x - x), Real.sqrt_nonneg (energy S ρ x)]

/-- The exact real quadratic form of a unitary displacement. -/
theorem real_inner_unitary (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (g : Γ) (x : H) :
    (inner ℂ x (ρ g x)).re = ‖x‖ ^ 2 - ‖ρ g x - x‖ ^ 2 / 2 := by
  have h := norm_sub_sq (𝕜 := ℂ) (ρ g x) x
  rw [(ρ g).norm_map, inner_re_symm] at h
  change ‖ρ g x - x‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℂ x (ρ g x)).re + ‖x‖ ^ 2 at h
  linarith

def reInnerAdd (x : H) : H →+ ℝ :=
  Complex.reAddGroupHom.comp (innerₛₗ ℂ x).toAddMonoidHom

def polyVector (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) (p : List (Γ × ℤ)) : H :=
  (p.map (fun a => a.2 • ρ a.1 x)).sum

theorem polyVector_real_inner (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) (p : List (Γ × ℤ)) :
    (inner ℂ x (polyVector ρ x p)).re =
      ((p.map Prod.snd).sum : ℤ) * ‖x‖ ^ 2 -
        (p.map (fun a => (a.2 : ℝ) * ‖ρ a.1 x - x‖ ^ 2)).sum / 2 := by
  induction p with
  | nil => simp [polyVector]
  | cons a p ih =>
    have hz : (inner ℂ x (a.2 • ρ a.1 x)).re =
        (a.2 : ℝ) * (inner ℂ x (ρ a.1 x)).re := by
      change reInnerAdd x (a.2 • ρ a.1 x) = _
      rw [map_zsmul, zsmul_eq_mul]
      rfl
    simp only [polyVector, List.map_cons, List.sum_cons, inner_add_right,
      Complex.add_re] at ih ⊢
    rw [hz, ih, real_inner_unitary]
    push_cast
    ring

/-- An integer coefficient may have either sign; absolute coefficients suffice. -/
theorem weighted_displacement_le (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (p : List (Γ × ℤ)) (M : ℝ)
    (hb : ∀ a ∈ p, ‖ρ a.1 x - x‖ ^ 2 ≤ M) :
    (p.map (fun a => (a.2 : ℝ) * ‖ρ a.1 x - x‖ ^ 2)).sum ≤
      ((p.map (fun a => |a.2|)).sum : ℤ) * M := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ht := ih (fun b h => hb b (by simp [h]))
    have h1 : (a.2 : ℝ) * ‖ρ a.1 x - x‖ ^ 2 ≤ |(a.2 : ℝ)| * M :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hb a (by simp)) (abs_nonneg _))
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_abs]
    nlinarith

/-- Exact augmentation zero converts a short supported residual into an energy error.
The constant eight here combines the squared word bound 16 with the factor 1/2. -/
theorem residual_lower (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (p : List (Γ × ℤ)) (haug : (p.map Prod.snd).sum = 0)
    (hsupp : ∀ a ∈ p, ∃ w : List Γ, w.prod = a.1 ∧ w.length ≤ 4 ∧ ∀ s ∈ w, s ∈ S) :
    -(8 * ((p.map (fun a => |a.2|)).sum : ℤ) * energy S ρ x) ≤
      (inner ℂ x (polyVector ρ x p)).re := by
  have hb := weighted_displacement_le ρ x p (16 * energy S ρ x) (by
    intro a ha
    rcases hsupp a ha with ⟨w, hprod, hlen, hw⟩
    rw [← hprod]
    exact word_sq_bound S ρ x w hw hlen)
  rw [polyVector_real_inner, haug, Int.cast_zero, zero_mul, zero_sub]
  nlinarith

end NuclearUltrapower.SOSEnergy

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A sums-of-squares inequality for a positive operator produces a true gap
on the orthogonal complement of its kernel; no finite-dimensional hypothesis. -/
theorem positive_sq_gap (T : H →L[ℂ] H) (hT : 0 ≤ T) (κ : ℝ)
    (hgap : κ • T ≤ T*T) (x : H) (hx : x ∈ T.kerᗮ) :
    κ * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).re := by
  let R := CFC.sqrt T
  have hR : IsSelfAdjoint R := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)
  have hRR : R * R = T := CFC.sqrt_mul_sqrt_self T hT
  have hRnorm (y : H) : ‖R y‖ ^ 2 = (inner ℂ y (T y)).re := by
    rw [← hRR, mul_apply_eq_comp]
    have hr := hR.isSymmetric y (R y)
    change inner ℂ (R y) (R y) = inner ℂ y (R (R y)) at hr
    rw [← hr]
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (R y)
  have hker : R.ker = T.ker := by
    ext y
    change R y = 0 ↔ T y = 0
    constructor
    · intro h; rw [← hRR, mul_apply_eq_comp, h, map_zero]
    · intro h
      apply norm_eq_zero.mp
      have hn := hRnorm y
      rw [h, inner_zero_right, Complex.zero_re] at hn
      nlinarith [norm_nonneg (R y)]
  have hd : R.range.topologicalClosure = T.kerᗮ := by
    rw [← hker, R.orthogonal_ker]
    congr 1
    exact congrArg (fun A : H →L[ℂ] H => A.toLinearMap.range) hR.star_eq.symm
  have hc : IsClosed {y : H | κ * ‖y‖ ^ 2 ≤ (inner ℂ y (T y)).re} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hs : (R.range : Set H) ⊆ {y : H | κ * ‖y‖ ^ 2 ≤ (inner ℂ y (T y)).re} := by
    rintro _ ⟨y, rfl⟩
    change κ * ‖R y‖ ^ 2 ≤ (inner ℂ (R y) (T (R y))).re
    have hp := (ContinuousLinearMap.le_def.mp hgap).re_inner_nonneg_right y
    have hTy : T (R y) = R (T y) := by
      rw [← hRR]
      simp only [mul_apply_eq_comp]
    have hr := hR.isSymmetric (R y) (T y)
    change inner ℂ (R (R y)) (T y) = inner ℂ (R y) (R (T y)) at hr
    rw [hRnorm, hTy, ← hr, ← mul_apply_eq_comp, hRR]
    apply sub_nonneg.mp
    change 0 ≤ (inner ℂ y ((T*T - κ • T) y)).re at hp
    have ht := (IsSelfAdjoint.of_nonneg hT).isSymmetric y (T y)
    change inner ℂ (T y) (T y) = inner ℂ y (T (T y)) at ht
    simpa only [sub_apply, mul_apply_eq_comp, smul_apply, inner_sub_right,
      inner_smul_right_eq_smul, Complex.sub_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← ht] using hp
  apply (closure_minimal hs hc)
  change x ∈ (R.range.topologicalClosure : Set H)
  rwa [hd]
end NuclearUltrapower

namespace NuclearUltrapower.SOSEnergy
open scoped ComplexOrder
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

def polyOperator (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (p : List (Γ × ℤ)) : H →L[ℂ] H :=
  (p.map (fun a => a.2 • (ρ a.1 : H →L[ℂ] H))).sum

omit [CompleteSpace H] in
theorem polyOperator_apply (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (p : List (Γ × ℤ)) (x : H) :
    polyOperator ρ p x = polyVector ρ x p := by
  induction p with
  | nil => simp [polyOperator, polyVector]
  | cons a p ih => simpa only [polyOperator, polyVector, List.map_cons, List.sum_cons,
      add_apply, smul_apply, LinearIsometryEquiv.coe_coe''] using (congrArg (fun y : H => a.2 • ρ a.1 x + y) ih)

/-- The rational certificate's defect absorption, with its exact denominator and
certified l1 size. The support/augmentation premises will be discharged by the
matrix-labelled reflection certificate, never assumed of the main group. -/
theorem certificate_sq_gap (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H))
    (D Q : H →L[ℂ] H) (p : List (Γ × ℤ))
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (henergy : ∀ x, (inner ℂ x (D x)).re = energy S ρ x / 2)
    (haug : (p.map Prod.snd).sum = 0)
    (hl1 : (p.map (fun a => |a.2|)).sum = 29562852800)
    (hsupp : ∀ a ∈ p, ∃ w : List Γ, w.prod = a.1 ∧ w.length ≤ 4 ∧ ∀ s ∈ w, s ∈ S)
    (hcert : (10000000000000 : ℝ) • (D*D) - (1000000000000 : ℝ) • D =
      Q + polyOperator ρ p) : (1 / 20 : ℝ) • D ≤ D*D := by
  have hself := IsSelfAdjoint.of_nonneg hD
  have hsq : IsSelfAdjoint (D*D) := by simpa only [pow_two] using hself.pow 2
  have hs : IsSelfAdjoint (D*D - (1/20 : ℝ) • D) :=
    hsq.sub ((IsSelfAdjoint.all (1/20 : ℝ)).smul hself)
  apply ContinuousLinearMap.le_def.mpr
  refine ⟨hs.isSymmetric, ?_⟩
  intro x
  have hr := residual_lower S ρ x p haug hsupp
  rw [hl1] at hr
  have hq := (ContinuousLinearMap.nonneg_iff_isPositive.mp hQ).re_inner_nonneg_right x
  have hd := (ContinuousLinearMap.nonneg_iff_isPositive.mp hD).re_inner_nonneg_right x
  have hc := congrArg (fun T : H →L[ℂ] H => (inner ℂ x (T x)).re) hcert
  simp only [sub_apply, smul_apply, add_apply, inner_sub_right, inner_add_right,
    inner_smul_right_eq_smul, Complex.sub_re, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    polyOperator_apply] at hc
  change 0 ≤ (inner ℂ ((D*D - (1/20 : ℝ) • D) x) x).re
  change 0 ≤ RCLike.re (inner ℂ ((D*D - (1/20 : ℝ) • D) x) x)
  rw [inner_re_symm (𝕜 := ℂ)]
  change 0 ≤ (inner ℂ x ((D*D - (1/20 : ℝ) • D) x)).re
  simp only [sub_apply, smul_apply, inner_sub_right, inner_smul_right_eq_smul,
    Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  change 0 ≤ (inner ℂ x (D x)).re at hd
  change 0 ≤ (inner ℂ x (Q x)).re at hq
  rw [henergy] at hc hd ⊢
  norm_num at hr
  nlinarith

end NuclearUltrapower.SOSEnergy
end
end
end

section

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral

theorem genList_nodup : (generators.map eInterpret).Nodup := by
  have h : (generators.map interpret).Nodup := by decide +kernel
  have he : (generators.map eInterpret).map (fun g : E => (g : SL)) = generators.map interpret := by
    rw [List.map_map]
    apply List.map_congr_left
    intro m hm
    exact eInterpret_coe (goodWord_generator hm)
  rw [← he] at h
  exact List.Nodup.of_map _ h

theorem eGenSet_card : eGenSet.card = 12 := by
  rw [eGenSet, List.toFinset_card_of_nodup genList_nodup]
  rfl

section Algebra
variable {A : Type*} [CStarAlgebra A]

def value (ρ : E →* unitary A) (m : Mat3) : A := ρ (eInterpret m)

@[simp] theorem value_one (ρ : E →* unitary A) : value ρ matOne = 1 := by
  simp [value, eInterpret_one]

theorem value_mul (ρ : E →* unitary A) {n k : ℕ} (a b : Mat3)
    (ha : GoodWord n a) (hb : GoodWord k b) :
    value ρ (matMul a b) = value ρ a * value ρ b := by
  simp only [value, eInterpret_mul ha hb, map_mul, Submonoid.coe_mul]

theorem value_inv (ρ : E →* unitary A) {n : ℕ} (a : Mat3) (ha : GoodWord n a) :
    value ρ (matInv a) = star (value ρ a) := by
  simp only [value, eInterpret_inv ha, map_inv]
  rfl

theorem delta_value (ρ : E →* unitary A) :
    eval (value ρ) delta = (12 : ℤ) • (1:A) - ∑ g ∈ eGenSet, (ρ g : A) := by
  rw [eGenSet, List.sum_toFinset _ genList_nodup]
  simp only [delta, eval, List.map_cons, List.map_map, Function.comp_def,
    List.sum_cons, neg_one_zsmul]
  rw [value_one]
  simp only [List.sum_neg, sub_eq_add_neg, value, List.map_map, Function.comp_def]

theorem sum_gen_star (ρ : E →* unitary A) :
    ∑ g ∈ eGenSet, star (ρ g : A) = ∑ g ∈ eGenSet, (ρ g : A) := by
  apply Finset.sum_nbij' (fun g : E => g⁻¹) (fun g : E => g⁻¹)
    (fun _ h => eGenSet_inv h) (fun _ h => eGenSet_inv h)
    (fun _ _ => inv_inv _) (fun _ _ => inv_inv _)
  intro g _
  simp only [map_inv]
  rfl

theorem laplacian_eq_delta (ρ : E →* unitary A) :
    laplacian eGenSet (fun g => (ρ g : A)) = (2 : ℝ) • eval (value ρ) delta := by
  have h (g : E) : star ((ρ g : A) - 1) * ((ρ g : A) - 1) =
      1 - star (ρ g : A) - (ρ g : A) + 1 := by
    simp only [star_sub, star_one, sub_mul, mul_sub, Unitary.coe_star_mul_self,
      one_mul, mul_one]
    abel
  simp only [laplacian, h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_gen_star, Finset.sum_const, eGenSet_card, delta_value]
  module

theorem delta_eq_half_laplacian (ρ : E →* unitary A) :
    eval (value ρ) delta = (1/2 : ℝ) • laplacian eGenSet (fun g => (ρ g : A)) := by
  rw [laplacian_eq_delta, smul_smul]
  norm_num

theorem delta_nonneg [PartialOrder A] [StarOrderedRing A] (ρ : E →* unitary A) :
    0 ≤ eval (value ρ) delta := by
  rw [delta_eq_half_laplacian]
  exact smul_nonneg (by norm_num) (laplacian_nonneg _ _)
end Algebra

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitaryRep (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : E →* unitary (H →L[ℂ] H) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp ρ

@[simp] theorem unitaryRep_coe (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (g : E) :
    (unitaryRep ρ g : H →L[ℂ] H) = (ρ g : H →L[ℂ] H) := rfl

theorem delta_energy (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    (inner ℂ x (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta x)).re = SOSEnergy.energy eGenSet ρ x / 2 := by
  rw [delta_eq_half_laplacian]
  simp only [smul_apply, inner_smul_right_eq_smul, laplacian_inner, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    unitaryRep_coe, LinearIsometryEquiv.coe_coe'']
  change (1/2 : ℝ) * SOSEnergy.energy eGenSet ρ x = _
  ring
end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
