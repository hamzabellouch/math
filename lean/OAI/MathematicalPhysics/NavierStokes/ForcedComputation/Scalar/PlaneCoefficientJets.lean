import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCoefficientBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetCurves

namespace OAI

/-! The actual smooth coefficients define bounded continuous curves of every finite jet order. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped ContDiff NNReal BigOperators

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem collect_jet_bounds (k : ℕ) (f : ℝ × Plane → F) (T : ℝ)
    (hb : ∀ n ≤ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => f (t,y)) x‖ ≤ C)
    (hl : ∀ n ≤ k, ∃ L : ℝ≥0, ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => f (s,y)) x -
        iteratedFDeriv ℝ n (fun y => f (t,y)) x‖ ≤ L * |s-t|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L : ℝ≥0,
      (∀ t ∈ Icc (0 : ℝ) T, ∀ n ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ n (fun y => f (t,y)) x‖ ≤ C) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, ∀ n ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ n (fun y => f (s,y)) x -
          iteratedFDeriv ℝ n (fun y => f (t,y)) x‖ ≤ L * |s-t|) := by
  have hb' (i : Fin (k+1)) := hb i.val (Nat.le_of_lt_succ i.isLt)
  have hl' (i : Fin (k+1)) := hl i.val (Nat.le_of_lt_succ i.isLt)
  choose C hC hbound using hb'
  choose L hmod using hl'
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ∑ i, L i, ?_, ?_⟩
  · intro t ht n hn x
    let i : Fin (k+1) := ⟨n, Nat.lt_succ_of_le hn⟩
    exact (hbound i t ht x).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))
  · intro s hs t ht n hn x
    let i : Fin (k+1) := ⟨n, Nat.lt_succ_of_le hn⟩
    apply (hmod i s hs t ht x).trans
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact_mod_cast Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (L j).coe_nonneg)
      (Finset.mem_univ i)

theorem periodic_jet_bounds {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, PlanePeriodic (fun x => f (t,x))) (k : ℕ) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L : ℝ≥0,
      (∀ t ∈ Icc (0 : ℝ) T, ∀ n ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ n (fun y => f (t,y)) x‖ ≤ C) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, ∀ n ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ n (fun y => f (s,y)) x -
          iteratedFDeriv ℝ n (fun y => f (t,y)) x‖ ≤ L * |s-t|) := by
  have hper (n : ℕ) (t : ℝ) : PlanePeriodic (fun x => spatialParameterDerivative n f (t,x)) := by
    simpa only [spatialParameterDerivative_eq hf] using planePeriodic_iteratedFDeriv (hp t) n
  apply collect_jet_bounds k f T
  · intro n _
    simpa only [spatialParameterDerivative_eq hf] using
      planePeriodic_bound_on (spatialParameterDerivative_smooth hf n).continuous.continuousOn
        (fun t _ => hper n t) (a := 0) (b := T)
  · intro n _
    simpa only [spatialParameterDerivative_eq hf] using
      planePeriodic_time_lipschitz (spatialParameterDerivative_smooth hf n) (hper n) 0 T

theorem supported_spatialParameterDerivative {f : ℝ × Plane → F}
    (hf : ContDiff ℝ ∞ f) {K : Set Plane} (hK : IsClosed K) {t : ℝ}
    (hs : ∀ x ∉ K, f (t,x) = 0) (n : ℕ) (x : Plane) (hx : x ∉ K) :
    spatialParameterDerivative n f (t,x) = 0 := by
  rw [spatialParameterDerivative_eq hf]
  have hc : tsupport (fun y => f (t,y)) ⊆ K := by
    apply closure_minimal _ hK
    intro y hy
    by_contra h
    exact hy (hs y h)
  by_contra hn
  exact hx (hc (support_iteratedFDeriv_subset n hn))

theorem supported_jet_bounds {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f)
    {K : Set Plane} (hK : IsCompact K) (T : ℝ)
    (hs : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ K, f (t,x) = 0) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L : ℝ≥0,
      (∀ t ∈ Icc (0 : ℝ) T, ∀ n ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ n (fun y => f (t,y)) x‖ ≤ C) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, ∀ n ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ n (fun y => f (s,y)) x -
          iteratedFDeriv ℝ n (fun y => f (t,y)) x‖ ≤ L * |s-t|) := by
  have hsup (n : ℕ) : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ K,
      spatialParameterDerivative n f (t,x) = 0 :=
    fun t ht x hx => supported_spatialParameterDerivative hf hK.isClosed (hs t ht) n x hx
  apply collect_jet_bounds k f T
  · intro n _
    simpa only [spatialParameterDerivative_eq hf] using
      supported_bound_on hK (spatialParameterDerivative_smooth hf n).continuous.continuousOn (hsup n)
  · intro n _
    simpa only [spatialParameterDerivative_eq hf] using
      supported_time_lipschitz (spatialParameterDerivative_smooth hf n) hK 0 T (hsup n)

theorem exists_periodic_jet_curve {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, PlanePeriodic (fun x => f (t,x))) (k : ℕ) (T : ℝ) :
    ∃ J : C(Icc (0 : ℝ) T, BoundedSpatialJets.Space Plane F k),
      ∀ t x, BoundedSpatialJets.function Plane F k (J t) x = f (t,x) := by
  obtain ⟨C,_,L,hC,hL⟩ := periodic_jet_bounds hf hp k T
  refine ⟨BoundedSpatialJets.ofFunctionCurve Plane F k T (fun t x => f (t,x))
    (fun t _ => (hf.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) C hC L hL, ?_⟩
  exact fun t x => BoundedSpatialJets.function_ofFunctionCurve Plane F k T _ _ _ _ _ _ t x

theorem exists_supported_jet_curve {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f)
    {K : Set Plane} (hK : IsCompact K) (T : ℝ)
    (hs : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ K, f (t,x) = 0) (k : ℕ) :
    ∃ J : C(Icc (0 : ℝ) T, BoundedSpatialJets.Space Plane F k),
      ∀ t x, BoundedSpatialJets.function Plane F k (J t) x = f (t,x) := by
  obtain ⟨C,_,L,hC,hL⟩ := supported_jet_bounds hf hK T hs k
  refine ⟨BoundedSpatialJets.ofFunctionCurve Plane F k T (fun t x => f (t,x))
    (fun t _ => (hf.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) C hC L hL, ?_⟩
  exact fun t x => BoundedSpatialJets.function_ofFunctionCurve Plane F k T _ _ _ _ _ _ t x

end ForcedComputation

end

end OAI
