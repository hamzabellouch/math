import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLongCompletion
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTrivialSum

namespace OAI

/-! The literal grouped long-completion coefficient has the counting
bound used in the low-height Type-I argument, on every norm dyad. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_tail_counting_scale {n E U ε : ℝ}
    (hE : 0 < E) (hEn : E ≤ n) (hU : 0 ≤ U) (hε : ε ≤ 1/2) :
    n^(1/2+ε)*(U/n^3) ≤ U*E^(-5/2+ε) := by
  have hn : 0 < n := hE.trans_le hEn
  have he : n^(1/2+ε)/n^3 = n^(-5/2+ε) := by
    rw [←Real.rpow_natCast n 3,←Real.rpow_sub hn]
    congr 1
    ring
  calc
    _ = U*(n^(1/2+ε)/n^3) := by ring
    _ = U*n^(-5/2+ε) := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hE hEn (by linarith)) hU

theorem metaplectic_tail_dyad_counting {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r : Eisenstein), primary r →
      ∀ (ℓ : ℤ) (C F : ℝ) (S : Finset Eisenstein) (E U B M : ℝ),
      0 < E → 0 < U → 0 ≤ B → 0 ≤ M →
      (∀ e ∈ S, primary e ∧ E ≤ norm e ∧ norm e ≤ 2*E) →
      ∀ W : ℝ → ℂ, (∀ x : ℝ, B < x → W x = 0) → (∀ x, ‖W x‖ ≤ M) →
      ‖∑ e ∈ S, metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0‖ ≤
        D*B*M*U*E^(-3/2+ε) := by
  obtain ⟨D,hD,hcoeff⟩ := metaplecticTailCoefficient_bound hε
  refine ⟨648*D,by positivity,?_⟩
  intro r hr ℓ C F S E U B M hE hU hB hM hS W hcut hW
  have hcard : (S.card:ℝ) ≤ 36*E := by
    have hs : S ⊆ primaryElementBall (2*E) := by
      intro e he
      exact mem_primaryElementBall.mpr ⟨(hS e he).1,(hS e he).2.2⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans
      ((primaryElementBall_card_le (by positivity)).trans_eq (by ring))
  have hb (e : Eisenstein) (he : e ∈ S) :
      ‖metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0‖ ≤
        (18*D*B*M*U)*E^(-5/2+ε) := by
    have hne : 0 < norm e := norm_pos_of_ne_zero (primary_ne_zero (hS e he).1)
    rw [norm_mul]
    calc
      _ ≤ (D*norm e^(1/2+ε))*(18*B*M*(U/norm e^3)) :=
        mul_le_mul (hcoeff r ℓ C F e (hS e he).1)
          (metaplecticAngularSmoothSum_trivial hr ℓ W (div_pos hU (pow_pos hne 3)) hB hM hcut hW)
          (_root_.norm_nonneg _) (by positivity)
      _ = (18*D*B*M)*(norm e^(1/2+ε)*(U/norm e^3)) := by ring
      _ ≤ (18*D*B*M)*(U*E^(-5/2+ε)) := mul_le_mul_of_nonneg_left
        (metaplectic_tail_counting_scale hE (hS e he).2.1 hU.le hεsmall) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ _e ∈ S, (18*D*B*M*U)*E^(-5/2+ε) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hb)
    _ = (S.card:ℝ)*((18*D*B*M*U)*E^(-5/2+ε)) := by simp
    _ ≤ (36*E)*((18*D*B*M*U)*E^(-5/2+ε)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (648*D)*B*M*U*E^(-3/2+ε) := by
      have he : E*E^(-5/2+ε) = E^(-3/2+ε) := by
        conv_lhs => lhs; rw [←Real.rpow_one E]
        rw [←Real.rpow_add hE]
        congr 1
        ring
      calc
        _ = (648*D)*B*M*U*(E*E^(-5/2+ε)) := by ring
        _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
