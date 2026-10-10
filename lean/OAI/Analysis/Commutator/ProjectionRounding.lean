import Mathlib
import OAI.Analysis.Commutator.NormalTraceProjection
import OAI.Analysis.Commutator.TracialConjugation

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (hnormal : BoundedWOTContinuous M τ)

variable (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include hτ hnormal hfaith in
theorem exists_rational_subprojection (hM : DiffuseProjection.HasNoMinimalProjections M)
    (e : M) (he : IsStarProjection e) (b : ℕ) (hb : 0<b) :
    ∃ (n : ℕ) (p : M), IsStarProjection p ∧ p≤e ∧
      (τ p).re=(n:ℝ)/(b:ℝ) ∧ (τ (e-p)).re<1/(b:ℝ) := by
  let n := ⌊(b:ℝ)*(τ e).re⌋₊
  have hbR : (0:ℝ)<b := Nat.cast_pos.mpr hb
  have he0 : 0≤(τ e).re := (τ.map_nonneg he.nonneg).1
  have hn : (n:ℝ)≤(b:ℝ)*(τ e).re := Nat.floor_le (mul_nonneg hbR.le he0)
  have hnt : (n:ℝ)/(b:ℝ)≤(τ e).re := (div_le_iff₀ hbR).mpr (by simpa only [mul_comm] using hn)
  obtain ⟨p,hp,hpe,hpt⟩ := exists_prescribed_projection_trace M τ hτ hnormal hfaith
    hM e he (div_nonneg (Nat.cast_nonneg _) hbR.le) hnt
  refine ⟨n,p,hp,hpe,hpt,?_⟩
  rw [map_sub,Complex.sub_re,hpt]
  apply (lt_div_iff₀ hbR).mpr
  have hlt : (b:ℝ)*(τ e).re<(n:ℝ)+1 := Nat.lt_floor_add_one _
  have hcancel : (n:ℝ)/(b:ℝ)*(b:ℝ)=(n:ℝ) := div_mul_cancel₀ _ hbR.ne'
  nlinarith

end Kadison.NormalGNS

namespace Kadison.ProjectionSum

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {I : Type*} [Fintype I]

omit [PartialOrder A] [StarOrderedRing A] in
lemma projection_sum (p : I → A) (hp : ∀ i,IsStarProjection (p i))
    (ho : ∀ i j,i≠j → p i*p j=0) : IsStarProjection (∑ i,p i) := by
  classical
  constructor
  · change (∑ i,p i)*(∑ i,p i)=∑ i,p i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,Finset.sum_eq_single i]
    · exact (hp i).isIdempotentElem.eq
    · intro j hj hji; exact ho i j hji.symm
    · simp
  · change star (∑ i,p i)=∑ i,p i
    simp only [star_sum]
    exact Finset.sum_congr rfl (fun i _ => (hp i).isSelfAdjoint.star_eq)

lemma subprojections_orthogonal {p q e f : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (hpe : p≤e) (hqf : q≤f) (hef : e*f=0) : p*q=0 := by
  have hb := (hp.le_iff_mul_eq_left he).mp hpe
  have hc := (hq.le_iff_mul_eq_right hf).mp hqf
  calc
    p*q=(p*e)*(f*q) := by rw [hb,hc]
    _=p*(e*f)*q := by simp only [mul_assoc]
    _=0 := by rw [hef,mul_zero,zero_mul]

lemma projection_sum_le (p q : I → A) (h : ∀ i,p i≤q i) : ∑ i,p i≤∑ i,q i :=
  Finset.sum_le_sum (fun i _ => h i)

lemma vector_projection_norm_sq (τ : A →ₚ[ℂ] ℂ) {p : A} (hp : IsStarProjection p) :
    ‖TracialGNS.algebraVector τ p‖^2=(τ p).re := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),TracialGNS.inner_algebraVector,
    hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  rfl

end Kadison.ProjectionSum

end

end
end

end OAI
