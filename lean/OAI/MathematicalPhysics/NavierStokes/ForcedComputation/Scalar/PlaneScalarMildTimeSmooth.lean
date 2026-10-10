import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildJetTime
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCoefficientTimeJets

namespace OAI

/-! Time smoothness of every spatial jet of the actual scalar mild solution. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Set ShearFlows
open scoped Topology ContDiff BigOperators

private theorem multiplication_contDiffOn {T : ℝ} {n : ℕ∞ω} (k : ℕ)
    {b u : ℝ → Jet k} (hb : ContDiffOn ℝ n b (Icc (0 : ℝ) T))
    (hu : ContDiffOn ℝ n u (Icc (0 : ℝ) T)) :
    ContDiffOn ℝ n (fun t => multiplication k (b t) (u t)) (Icc (0 : ℝ) T) := by
  let B := BoundedSpatialJets.bilinearCLM Plane ℝ ℝ ℝ k (ContinuousLinearMap.mul ℝ ℝ)
  let L := BoundedSpatialJets.operatorEquiv Plane ℝ ℝ k
  have hB : ContDiffOn ℝ n (fun t => B (b t)) (Icc (0 : ℝ) T) :=
    B.contDiff.comp_contDiffOn hb
  have hLb : IsBoundedLinearMap ℝ
      (fun A : BoundedSpatialJets.Operator Plane ℝ ℝ k => (L A : Jet k →L[ℝ] Jet k)) :=
    { map_add := fun _ _ => rfl
      map_smul := fun _ _ => rfl
      bound := ⟨1, zero_lt_one, fun A => by
        simpa only [one_mul] using (le_of_eq (L.norm_map A))⟩ }
  have hL : ContDiffOn ℝ n (fun t => L (B (b t))) (Icc (0 : ℝ) T) :=
    hLb.contDiff.comp_contDiffOn hB
  exact hL.clm_apply hu

private theorem path_add_eval {T : ℝ} (k : ℕ)
    (u v : WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) :
    (u+v) t = u t+v t := rfl

private theorem path_sum_eval {T : ℝ} (k : ℕ)
    (u : Fin 2 → WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) :
    (∑ j, u j) t = ∑ j, u j t := by
  change (ContinuousMap.evalCLM ℝ t) ((WeaklySingular.pathEquiv (Jet k) T) (∑ j, u j)) = _
  simp only [map_sum]
  rfl

private theorem path_three_eval {T : ℝ} (k : ℕ)
    (u v : WeaklySingular.Path (Jet k) T)
    (w : Fin 2 → WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) :
    (u+v+∑ j, w j) t = u t+v t+∑ j, w j t := by
  exact (path_add_eval k (u+v) (∑ j, w j) t).trans
    (congrArg₂ (fun a b : Jet k => a+b) (path_add_eval k u v t) (path_sum_eval k w t))

namespace CompatibleData

private def sourceJetValue {T : ℝ} (hT : 0 ≤ T) (D : CompatibleData T) (k : ℕ) : ℝ → Jet k :=
  WeaklySingular.extendPath (Jet k) hT (D.source k)

private def coefficientJetValue {T : ℝ} (hT : 0 ≤ T) (D : CompatibleData T)
    (k : ℕ) (i : Fin 3) : ℝ → Jet k :=
  CoefficientTimeJets.extend hT (D.coefficient k i)

private theorem effectiveSourceJet_formula {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) (t : ℝ) :
    WeaklySingular.extendPath (Jet k) hT (D.effectiveSource hT hν k) t =
      D.sourceJetValue hT k t +
        multiplication k (D.coefficientJetValue hT k 0 t) (D.solutionJetValue hT hν k t) +
        ∑ j : Fin 2, BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k (Pi.single j 1)
          (multiplication (k+1) (D.coefficientJetValue hT (k+1) j.succ t)
            (D.solutionJetValue hT hν (k+1) t)) := by
  let p := productPath k (D.coefficient k 0) (D.solutionJet hT hν k)
  let v : Fin 2 → WeaklySingular.Path (Jet k) T := fun j =>
    directionalPath k (Pi.single j 1) T
      (productPath (k+1) (D.coefficient (k+1) j.succ) (D.solutionJet hT hν (k+1)))
  let r := projIcc 0 T hT t
  change (D.source k + p + ∑ j, v j) r = _
  have hp : p r = multiplication k (D.coefficientJetValue hT k 0 t)
      (D.solutionJetValue hT hν k t) := rfl
  have hv (j : Fin 2) : v j r =
      BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k (Pi.single j 1)
        (multiplication (k+1) (D.coefficientJetValue hT (k+1) j.succ t)
          (D.solutionJetValue hT hν (k+1) t)) := rfl
  exact (path_three_eval k (D.source k) p v r).trans
    (congrArg₂ (fun a b : Jet k => a+b)
      (congrArg₂ (fun a b : Jet k => a+b) rfl hp)
      (Finset.sum_congr rfl (fun j _ => hv j)))

private theorem effectiveSourceJet_contDiffOn {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) {n : ℕ∞ω}
    (hs : ∀ k, ContDiffOn ℝ n (D.sourceJetValue hT k) (Icc (0 : ℝ) T))
    (hb : ∀ k i, ContDiffOn ℝ n (D.coefficientJetValue hT k i) (Icc (0 : ℝ) T))
    (hu : ∀ k, ContDiffOn ℝ n (D.solutionJetValue hT hν k) (Icc (0 : ℝ) T)) (k : ℕ) :
    ContDiffOn ℝ n (WeaklySingular.extendPath (Jet k) hT (D.effectiveSource hT hν k))
      (Icc (0 : ℝ) T) := by
  have hp := multiplication_contDiffOn k (hb k 0) (hu k)
  have hd (j : Fin 2) := (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k (Pi.single j 1)).contDiff.comp_contDiffOn
    (multiplication_contDiffOn (k+1) (hb (k+1) j.succ) (hu (k+1)))
  have he : WeaklySingular.extendPath (Jet k) hT (D.effectiveSource hT hν k) =
      (fun t => D.sourceJetValue hT k t +
        multiplication k (D.coefficientJetValue hT k 0 t) (D.solutionJetValue hT hν k t) +
        ∑ j : Fin 2, BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k (Pi.single j 1)
          (multiplication (k+1) (D.coefficientJetValue hT (k+1) j.succ t)
            (D.solutionJetValue hT hν (k+1) t))) :=
    funext (D.effectiveSourceJet_formula hT hν k)
  rw [he]
  exact ((hs k).add hp).add (ContDiffOn.sum (fun j _ => hd j))

/-- Smooth source and coefficient curves make every finite spatial jet smooth in time. -/
theorem solutionJetValue_smooth_time {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (D : CompatibleData T)
    (hs : ∀ k, ContDiffOn ℝ ∞ (WeaklySingular.extendPath (Jet k) hT.le (D.source k))
      (Icc (0 : ℝ) T))
    (hb : ∀ k i, ContDiffOn ℝ ∞ (CoefficientTimeJets.extend hT.le (D.coefficient k i))
      (Icc (0 : ℝ) T)) (k : ℕ) :
    ContDiffOn ℝ ∞ (D.solutionJetValue hT.le hν k) (Icc (0 : ℝ) T) := by
  have hall : ∀ m : ℕ, ∀ k,
      ContDiffOn ℝ m (D.solutionJetValue hT.le hν k) (Icc (0 : ℝ) T) := by
    intro m
    induction m with
    | zero => intro k; exact contDiffOn_zero.mpr (D.solutionJetValue_continuous hT.le hν k).continuousOn
    | succ m ih =>
      intro k
      have hq := D.effectiveSourceJet_contDiffOn hT.le hν
        (fun i => (hs i).of_le (by simp)) (fun i j => (hb i j).of_le (by simp)) ih k
      have hr : ContDiffOn ℝ m (D.timeRHSJet hT.le hν k) (Icc (0 : ℝ) T) :=
        (((laplacianJetCLM k).contDiff.comp_contDiffOn (ih (k+2))).const_smul ν).add hq
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
      refine ⟨fun t ht => (D.solutionJetValue_hasDerivWithinAt hT.le hν k ht).differentiableWithinAt,
        by simp, ?_⟩
      apply hr.congr
      intro t ht
      exact (D.solutionJetValue_hasDerivWithinAt hT.le hν k ht).derivWithin (uniqueDiffOn_Icc hT t ht)
  exact contDiffOn_infty.mpr (fun m => hall m k)

/-- The periodic data supplied by the compiler satisfy the time-smoothness hypotheses. -/
theorem periodic_solutionJetValue_smooth_time {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (D : CompatibleData T) {h : ℝ × Plane → ℝ} (hh : ContDiff ℝ ∞ h)
    (hph : ∀ t, PlanePeriodic (fun x => h (t,x)))
    {b : Fin 3 → ℝ × Plane → ℝ} (hbs : ∀ i, ContDiff ℝ ∞ (b i))
    (hpb : ∀ i t, PlanePeriodic (fun x => b i (t,x)))
    (hsource : ∀ k t x, BoundedSpatialJets.function Plane ℝ k (D.source k t) x = h (t.val,x))
    (hcoeff : ∀ k i t x, BoundedSpatialJets.function Plane ℝ k (D.coefficient k i t) x = b i (t.val,x))
    (k : ℕ) : ContDiffOn ℝ ∞ (D.solutionJetValue hT.le hν k) (Icc (0 : ℝ) T) := by
  apply D.solutionJetValue_smooth_time hT hν
  · intro n
    exact CoefficientTimeJets.periodic_curve_smooth hT hh hph
      ((WeaklySingular.pathEquiv (Jet n) T) (D.source n)) (hsource n)
  · intro n i
    exact CoefficientTimeJets.periodic_curve_smooth hT (hbs i) (hpb i)
      (D.coefficient n i) (hcoeff n i)

/-- A common compact support gives the same smoothness for the whole-plane data. -/
theorem supported_solutionJetValue_smooth_time {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν)
    (D : CompatibleData T) {K : Set Plane} (hK : IsCompact K)
    {h : ℝ × Plane → ℝ} (hh : ContDiff ℝ ∞ h)
    (hsh : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ K, h (t,x) = 0)
    {b : Fin 3 → ℝ × Plane → ℝ} (hbs : ∀ i, ContDiff ℝ ∞ (b i))
    (hsb : ∀ i t, t ∈ Icc (0 : ℝ) T → ∀ x ∉ K, b i (t,x) = 0)
    (hsource : ∀ k t x, BoundedSpatialJets.function Plane ℝ k (D.source k t) x = h (t.val,x))
    (hcoeff : ∀ k i t x, BoundedSpatialJets.function Plane ℝ k (D.coefficient k i t) x = b i (t.val,x))
    (k : ℕ) : ContDiffOn ℝ ∞ (D.solutionJetValue hT.le hν k) (Icc (0 : ℝ) T) := by
  apply D.solutionJetValue_smooth_time hT hν
  · intro n
    exact CoefficientTimeJets.supported_curve_smooth hT hh hK hsh
      ((WeaklySingular.pathEquiv (Jet n) T) (D.source n)) (hsource n)
  · intro n i
    exact CoefficientTimeJets.supported_curve_smooth hT (hbs i) hK (hsb i)
      (D.coefficient n i) (hcoeff n i)

end CompatibleData
end ForcedComputation.PlaneScalarMild

end

end OAI
