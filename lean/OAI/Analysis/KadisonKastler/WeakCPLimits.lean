import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.KadisonKastler.RectangularHilbert
import OAI.Analysis.KadisonKastler.CompletelyPositive
import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

/-! # Positivity and norm bounds in pointwise weak operator limits

These lemmas retain the complete positivity of the maps obtained from
finite Hilbert-space tests. No normality of the limiting map is needed.
-/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι} [l.NeBot]

omit [CompleteSpace H] in
/-- Operator positivity is closed under convergence of every coefficient. -/
theorem isPositive_of_weak_limit (T : ι → H →L[ℂ] H) (S : H →L[ℂ] H)
    (hT : ∀ i, (T i).IsPositive)
    (ht : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l (𝓝 (inner ℂ y (S x)))) :
    S.IsPositive := by
  constructor
  · intro x y
    change inner ℂ (S x) y = inner ℂ x (S y)
    have hleft := (ht x y).star
    have hright := ht y x
    have he (i : ι) : star (inner ℂ y (T i x)) = inner ℂ x (T i y) := by
      change (starRingEnd ℂ) (inner ℂ y (T i x)) = _
      rw [inner_conj_symm]
      exact (hT i).isSymmetric x y
    have hleft' := hleft.congr (fun i => he i)
    change Tendsto _ l (𝓝 ((starRingEnd ℂ) (inner ℂ y (S x)))) at hleft'
    simpa only [inner_conj_symm] using tendsto_nhds_unique hleft' hright
  · intro x
    change 0 ≤ (inner ℂ (S x) x).re
    have hr := (Complex.continuous_re.tendsto _).comp (ht x x)
    have h := ge_of_tendsto hr
      (Eventually.of_forall (fun i => (hT i).re_inner_nonneg_right x))
    rw [show (inner ℂ (S x) x).re = (inner ℂ x (S x)).re from
      inner_re_symm (𝕜 := ℂ) (S x) x]
    exact h

omit [CompleteSpace H] in
/-- A uniform operator norm bound survives a weak coefficient limit. -/
theorem norm_le_of_weak_limit {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (T : ι → H →L[ℂ] K) (S : H →L[ℂ] K)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C)
    (ht : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l (𝓝 (inner ℂ y (S x)))) :
    ‖S‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  change (inner ℂ (S x) y).re ≤ C
  have hb (i : ι) : (inner ℂ y (T i x)).re ≤ C := by
    calc
      _ ≤ ‖inner ℂ y (T i x)‖ := Complex.re_le_norm _
      _ ≤ ‖y‖ * ‖T i x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (C * ‖x‖) := mul_le_mul_of_nonneg_left
        ((T i).le_of_opNorm_le (hT i) x) (norm_nonneg y)
      _ = C := by rw [hx, hy]; ring
  have hr := (Complex.continuous_re.tendsto _).comp (ht x y)
  rw [show (inner ℂ (S x) y).re = (inner ℂ y (S x)).re from
    inner_re_symm (𝕜 := ℂ) (S x) y]
  exact le_of_tendsto hr (Eventually.of_forall hb)

/-- Weak approximants from a fixed von Neumann algebra retain the limit
in that algebra; uniform approximation in operator norm is unnecessary. -/
theorem weak_limit_mem_of_weak_approximants (N : VonNeumannAlgebra H)
    (T : ι → H →L[ℂ] H) (S : H →L[ℂ] H) (a : ι → Algebra N)
    (ht : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l
      (𝓝 (inner ℂ y (S x))))
    (ha : ∀ x y, Tendsto (fun i => inner ℂ y (((a i : H →L[ℂ] H) - T i) x))
      l (𝓝 0)) : S ∈ N := by
  apply Generator.Tracial.weak_operator_limit_mem (l := l) N a S
  intro x y
  have h := (ha x y).add (ht x y)
  simpa only [sub_apply, inner_sub_right,
    sub_add_cancel, zero_add] using h

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [CompleteSpace H] [l.NeBot] [DecidableEq n] in
/-- Entrywise weak convergence gives weak convergence of each finite
operator-matrix amplification. -/
theorem hilbertMatrix_weak_limit (T : ι → CStarMatrix n n (H →L[ℂ] H))
    (S : CStarMatrix n n (H →L[ℂ] H))
    (ht : ∀ j k x y, Tendsto (fun i => inner ℂ y (T i j k x)) l
      (𝓝 (inner ℂ y (S j k x))))
    (x y : Generator.FiniteHilbert n H) :
    Tendsto (fun i => inner ℂ y (hilbertMatrix (T i) x)) l
      (𝓝 (inner ℂ y (hilbertMatrix S x))) := by
  have h := tendsto_finsetSum Finset.univ (fun j _ =>
    tendsto_finsetSum Finset.univ (fun k _ => ht j k (x k) (y j)))
  simpa only [PiLp.inner_apply, hilbertMatrix_apply, inner_sum] using h

omit [CompleteSpace H] [l.NeBot] [DecidableEq n] in
/-- The same coefficient limit statement for rectangular amplifications. -/
theorem rectangularHilbertMatrix_weak_limit {m : Type*} [Fintype m]
    (T : ι → CStarMatrix m n (H →L[ℂ] H)) (S : CStarMatrix m n (H →L[ℂ] H))
    (ht : ∀ j k x y, Tendsto (fun i => inner ℂ y (T i j k x)) l
      (𝓝 (inner ℂ y (S j k x))))
    (x : Generator.FiniteHilbert n H) (y : Generator.FiniteHilbert m H) :
    Tendsto (fun i => inner ℂ y (rectangularHilbertMatrix (T i) x)) l
      (𝓝 (inner ℂ y (rectangularHilbertMatrix S x))) := by
  have h := tendsto_finsetSum Finset.univ (fun j _ =>
    tendsto_finsetSum Finset.univ (fun k _ => ht j k (x k) (y j)))
  simpa only [PiLp.inner_apply, rectangularHilbertMatrix_apply, inner_sum] using h

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A pointwise weak limit, once bundled linearly, is completely positive. -/
def completelyPositive_of_pointwise_weak_limit
    (F : ι → A →CP (H →L[ℂ] H)) (S : A →ₗ[ℂ] (H →L[ℂ] H))
    (ht : ∀ a x y, Tendsto (fun i => inner ℂ y (F i a x)) l
      (𝓝 (inner ℂ y (S a x)))) : A →CP (H →L[ℂ] H) where
  toLinearMap := S
  map_cstarMatrix_nonneg' k X hX := by
    let T (i : ι) := hilbertMatrix (X.map (F i))
    let R := hilbertMatrix (X.map S)
    have hT (i : ι) : (T i).IsPositive := by
      have hp := map_nonneg (hilbertMatrixHom (H := H) (n := Fin k))
        ((F i).map_cstarMatrix_nonneg X hX)
      change (T i - 0).IsPositive at hp
      simpa only [sub_zero] using hp
    have hconv (x y : Generator.FiniteHilbert (Fin k) H) :=
      hilbertMatrix_weak_limit (fun i => X.map (F i)) (X.map S)
        (fun j k x y => ht (X j k) x y) x y
    have hp := isPositive_of_weak_limit T R hT hconv
    have hp' : 0 ≤ R := by
      change (R - 0).IsPositive
      simpa only [sub_zero] using hp
    apply (NonUnitalStarAlgHom.map_le_map_iff
      (hilbertMatrixHom (H := H) (n := Fin k)) hilbertMatrixHom_injective).mp
    rw [map_zero]
    change (hilbertMatrix (X.map S) - 0).IsPositive
    simpa only [sub_zero] using hp

/-- A uniform complete bound survives a pointwise weak limit. -/
theorem complete_bound_of_pointwise_weak_limit
    (F : ι → A →ₗ[ℂ] (H →L[ℂ] H)) (S ρ : A →ₗ[ℂ] (H →L[ℂ] H))
    (ht : ∀ a x y, Tendsto (fun i => inner ℂ y (F i a x)) l
      (𝓝 (inner ℂ y (S a x))))
    {e : ℝ} (he : 0 ≤ e) (hF : ∀ i, CompletelyBoundedBy (F i - ρ) e) :
    CompletelyBoundedBy (S - ρ) e := by
  intro p q X
  rw [← norm_rectangularHilbertMatrix]
  apply norm_le_of_weak_limit (l := l)
    (fun i => rectangularHilbertMatrix (CStarMatrix.mapₗ (F i - ρ) X))
    (rectangularHilbertMatrix (CStarMatrix.mapₗ (S - ρ) X))
    (mul_nonneg he (norm_nonneg X))
  · intro i
    rw [norm_rectangularHilbertMatrix]
    exact hF i p q X
  · intro x y
    apply rectangularHilbertMatrix_weak_limit
    intro j k a b
    simpa only [CStarMatrix.mapₗ_apply, CStarMatrix.map_apply, LinearMap.sub_apply,
      sub_apply, inner_sub_right] using
      (ht (X j k) a b).sub tendsto_const_nhds

/-- A family of unital completely positive maps has a simultaneous
pointwise weak ultralimit. The limiting map is again unital and CP. -/
theorem exists_unitalCP_weak_ultralimit (ω : Ultrafilter ι)
    (F : ι → A →CP (H →L[ℂ] H)) (hF : ∀ i, F i 1 = 1) :
    ∃ S : A →CP (H →L[ℂ] H), S 1 = 1 ∧
      ∀ a x y, Tendsto (fun i => inner ℂ y (F i a x)) (ω : Filter ι)
        (𝓝 (inner ℂ y (S a x))) := by
  choose S _hS ht using fun a : A => Generator.Tracial.exists_weak_operator_ultralimit
    ω (fun i => F i a) ‖a‖ (norm_nonneg a)
      (fun i => unital_completelyPositive_norm_le (F i) (hF i) a)
  have hadd (a b : A) : S (a + b) = S a + S b := by
    ext x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (a + b) x y)
    simpa only [map_add, add_apply, inner_add_right] using
      (ht a x y).add (ht b x y)
  have hsmul (c : ℂ) (a : A) : S (c • a) = c • S a := by
    ext x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (c • a) x y)
    simpa only [map_smul, smul_apply, inner_smul_right] using
      (ht a x y).const_mul c
  let L : A →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := S, map_add' := hadd, map_smul' := hsmul }
  let φ : A →CP (H →L[ℂ] H) := completelyPositive_of_pointwise_weak_limit F L ht
  refine ⟨φ, ?_, ht⟩
  ext x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y (S 1 x) = inner ℂ y x
  apply tendsto_nhds_unique (ht 1 x y)
  simpa only [hF, one_apply_eq_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ y x) (ω : Filter ι)
      (𝓝 (inner ℂ y x)))

end

end KadisonKastler

end OAI
