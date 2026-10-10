import OAI.Analysis.KadisonKastler.FaithfulTraceGNS
import OAI.Analysis.KadisonKastler.FiniteAveraging
import OAI.Analysis.KadisonKastler.TraceLimits

namespace OAI

/-! # Finite conjugation averages in the tracial two-norm -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A G : Type*} [CStarAlgebra A] [Fintype G] [Group G]
  [PartialOrder A] [StarOrderedRing A]

def traceStateVectorLinear (τ : FaithfulTracialState A) : A →ₗ[ℂ] TraceStateHilbert τ where
  toFun := traceStateVector τ
  map_add' a b := by simp only [traceStateVector, map_add, UniformSpace.Completion.coe_add]
  map_smul' c a := by simp only [traceStateVector, map_smul, UniformSpace.Completion.coe_smul, RingHom.id_apply]

def tracialFiniteAverage (ρ : G →* unitary A) (x : A) : A :=
  finiteAverage (fun g => (ρ g : A) * x * star (ρ g : A))

omit [PartialOrder A] [StarOrderedRing A] in
theorem tracialFiniteAverage_commutes (ρ : G →* unitary A) (x : A) (g : G) :
    Commute (ρ g : A) (tracialFiniteAverage ρ x) := by
  have he : (∑ k : G, (ρ (g * k) : A) * x * star (ρ (g * k) : A)) =
      ∑ k : G, (ρ k : A) * x * star (ρ k : A) :=
    Equiv.sum_comp (Equiv.mulLeft g) (fun k => (ρ k : A) * x * star (ρ k : A))
  have hi : (ρ g : A) * tracialFiniteAverage ρ x * star (ρ g : A) =
      tracialFiniteAverage ρ x := by
    unfold tracialFiniteAverage finiteAverage
    simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
    congr 1
    simpa only [map_mul, Submonoid.coe_mul, star_mul, mul_assoc] using he
  have hh := congrArg (fun a : A => a * (ρ g : A)) hi
  change (ρ g : A) * tracialFiniteAverage ρ x = tracialFiniteAverage ρ x * (ρ g : A)
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem (ρ g).property, mul_one] using hh

omit [PartialOrder A] [StarOrderedRing A] in
theorem trace_tracialFiniteAverage (τ : FaithfulTracialState A)
    (ρ : G →* unitary A) (x : A) :
    τ.toLinearMap (tracialFiniteAverage ρ x) = τ.toLinearMap x := by
  have ht (g : G) : τ.toLinearMap ((ρ g : A) * x * star (ρ g : A)) = τ.toLinearMap x := by
    rw [τ.tracial, ← mul_assoc, Unitary.star_mul_self_of_mem (ρ g).property, one_mul]
  simpa only [tracialFiniteAverage, finiteAverage, map_smul, map_sum, ht] using
    (finiteAverage_const (G := G) (τ.toLinearMap x))

theorem traceTwoNorm_sub_tracialFiniteAverage_le (τ : FaithfulTracialState A)
    (ρ : G →* unitary A) (x : A) (δ : ℝ)
    (hδ : ∀ g, traceTwoNorm τ ((ρ g : A) * x - x * ρ g) ≤ δ) :
    traceTwoNorm τ (x - tracialFiniteAverage ρ x) ≤ δ := by
  let J := traceStateVectorLinear τ
  have he : J (x - tracialFiniteAverage ρ x) =
      finiteAverage (fun g => J (x - (ρ g : A) * x * star (ρ g : A))) := by
    simp only [tracialFiniteAverage, finiteAverage, map_sub, map_smul, map_sum,
      Finset.sum_sub_distrib, smul_sub]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]
  rw [← norm_traceStateVector]
  change ‖J (x - tracialFiniteAverage ρ x)‖ ≤ δ
  rw [he]
  apply norm_finiteAverage_le
  intro g
  change ‖traceStateVector τ _‖ ≤ δ
  rw [norm_traceStateVector]
  have hd : x - (ρ g : A) * x * star (ρ g : A) =
      -(((ρ g : A) * x - x * ρ g) * star (ρ g : A)) := by
    rw [sub_mul, mul_assoc x, Unitary.mul_star_self_of_mem (ρ g).property, mul_one]
    abel
  rw [hd, traceTwoNorm_neg, ← Unitary.coe_star, traceTwoNorm_mul_unitary]
  exact hδ g

/-- A finite matrix conjugation group with scalar commutant detects the
tracial distance to scalars by one of its unitaries. -/
theorem exists_unitary_trace_variance_of_finite_group (τ : FaithfulTracialState A)
    (ρ : G →* unitary A)
    (hscalar : ∀ a : A, (∀ g, Commute (ρ g : A) a) → ∃ c : ℂ, a = c • 1)
    (x : A) : ∃ u : unitary A,
      traceTwoNorm τ (x - τ.toLinearMap x • 1) ≤
        2 * traceTwoNorm τ ((u : A) * x - x * u) := by
  obtain ⟨c, hc⟩ := hscalar (tracialFiniteAverage ρ x) (tracialFiniteAverage_commutes ρ x)
  have htrace := trace_tracialFiniteAverage τ ρ x
  rw [hc, map_smul, τ.map_one, smul_eq_mul, mul_one] at htrace
  have havg : tracialFiniteAverage ρ x = τ.toLinearMap x • 1 := by rwa [← htrace]
  let d := traceTwoNorm τ (x - τ.toLinearMap x • 1)
  by_cases hd : d = 0
  · exact ⟨1, by change d ≤ _; rw [hd]; exact mul_nonneg (by norm_num) (traceTwoNorm_nonneg _ _)⟩
  by_contra h
  push Not at h
  have hb : d ≤ d / 2 := by
    change traceTwoNorm τ (x - τ.toLinearMap x • 1) ≤ _
    rw [← havg]
    apply traceTwoNorm_sub_tracialFiniteAverage_le τ ρ x
    intro g
    have hg := h (ρ g)
    change 2 * traceTwoNorm τ ((ρ g : A) * x - x * ρ g) < d at hg
    linarith
  have hn := traceTwoNorm_nonneg τ (x - τ.toLinearMap x • 1)
  change 0 ≤ d at hn
  exact hd (by linarith)

end

end KadisonKastler

end OAI
