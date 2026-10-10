import OAI.Probability.DilutedSpin.GridIncrementSupport

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators

noncomputable def cavityIncrementError (α : ℝ≥0) (q : ℕ) (C : ℝ) (N : ℕ) : ℝ :=
  C*cavityBadRate α q N+6*scoreScale N/(N+1)+
  C*|(oneNewRate α q N:ℝ)-(α:ℝ)*(q+1)|+
  C*|(α:ℝ)*N-(reservoirRate α q N:ℝ)-(α:ℝ)*q|+
  (scoreScale (N+1)-scoreScale N)

lemma increment_cavityProxy_bound {q L : ℕ} (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ|≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h|≤H)
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun z : InteractionSample (q+1) => z.1)
      (fun z : InteractionSample (q+1) => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    (N : ℕ) (u : Spec L×ℕ → ℝ) :
    |increment (weights L) prior (gridExponents L) direction anchor M N u-
      cavityProxy M C H (N+1) L u|≤cavityIncrementError M.alpha q C (N+1) := by
  have heθ : id =ᵐ[M.disorder.toMeasure] clipSample C := hθ.mono (fun z hz => (clipSample_eq hz).symm)
  have heh : id =ᵐ[M.field.toMeasure] clipReal H := hh.mono (fun y hy => (clipReal_eq hy).symm)
  have h1 := clippedPhysicalMean_score_bound M hC hH (N+1) u
  have h2 := clippedPhysicalMean_reservoir_bound (N := N+1) M hC hH hsym u
  have h3 := energyCavityIncrement_proxy_bound (N := N+1) M hC hH u
  rw [← clippedCavityProxy_eq M C H (N+1) L u hθ hh]
  unfold increment
  rw [perturbedMean_congr _ _ (weights L) id (clipSample C) id (clipReal H) heθ heh,
    perturbedMean_congr _ _ (weights L) id (clipSample C) id (clipReal H) heθ heh]
  have halg (a b c d e A B D : ℝ) (h1 : |a-b|≤A) (h2 : |(b-c)-d|≤B) (h3 : |d-e|≤D) :
      |(a-c)-e|≤A+B+D := by
    have h := (abs_add_le ((a-b)+((b-c)-d)) (d-e)).trans
      (add_le_add ((abs_add_le (a-b) ((b-c)-d)).trans (add_le_add h1 h2)) h3)
    convert h using 1; congr 1; ring
  change |clippedReservoirIncrement M C H (N+1) u-clippedCavityProxy M C H (N+1) L u| ≤ _ at h3
  rw [NNReal.coe_sub (reservoirRate_le M.alpha q (N+1))] at h3
  have hf := halg _ _ _ _ _ _ _ _ h1 h2 h3
  simp only [clippedPhysicalMean,Nat.add_assoc,Nat.reduceAdd,Nat.cast_add,Nat.cast_one] at hf
  apply hf.trans_eq
  simp only [cavityIncrementError,
    NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_add,NNReal.coe_one,scoreRate_real,Nat.cast_add,Nat.cast_one]
  ring

end DilutedSpinGlass.UniversalDictionary

end

end OAI
