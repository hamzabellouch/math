import OAI.NumberTheory.JointDickman.Counting.GeometricWindowKernel
import OAI.NumberTheory.JointDickman.Probability.LogSampledKernel

namespace OAI

/-! # Coarse comparison for the actual box-summed spatial kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

noncomputable def endpointSpatialWeight (m B : ℕ) (t β : ℝ) (d : ℤ → ℝ)
    (w₁ w₂ w : ℝ → ℝ) (k : ℤ) (i j : Fin (channelFineCount m B)) : ℝ :=
  let zi := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t)
  let zj := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) j)/Real.exp ((k : ℝ)*t)
  d k*w₁ zi*w₂ zj*w (β*zi-β*zj)

theorem endpointSpatialWeight_bound (m B : ℕ) (t β : ℝ) (S : Finset ℤ)
    (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ) {D M₁ M₂ M : ℝ}
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hd : ∀ k ∈ S, |d k| ≤ D) (hw₁ : ∀ x, |w₁ x| ≤ M₁)
    (hw₂ : ∀ x, |w₂ x| ≤ M₂) (hw : ∀ x, |w x| ≤ M) :
    ∀ k ∈ S, ∀ i j, |endpointSpatialWeight m B t β d w₁ w₂ w k i j| ≤ D*M₁*M₂*M := by
  intro k hk i j
  unfold endpointSpatialWeight
  simp only [abs_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul (hd k hk) (hw₁ _) (abs_nonneg _) hD)
    (hw₂ _) (abs_nonneg _) (mul_nonneg hD hM₁)) (hw _) (abs_nonneg _)
      (mul_nonneg (mul_nonneg hD hM₁) hM₂)

theorem geometricWindowKernel_bilinear (m B : ℕ) (t L U : ℝ) (S : Finset ℤ)
    (u v : Fin (channelFineCount m B) → ℝ)
    (V : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    cellMassBilinear m B u v (geometricWindowKernel m B t L U S V) =
      (B : ℝ)*∑ k ∈ S, ∑ i ∈ geometricHistogramWindow m B t L U k,
        ∑ j ∈ geometricHistogramWindow m B t L U k, u i*v j*V k i j := by
  classical
  unfold cellMassBilinear geometricWindowKernel
  simp_rw [mul_sum]
  have hterm (i j : Fin (channelFineCount m B)) (k : ℤ) :
      u i*v j*((B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
        j ∈ geometricHistogramWindow m B t L U k then V k i j else 0)) =
      (B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
        j ∈ geometricHistogramWindow m B t L U k then u i*v j*V k i j else 0) := by
    split_ifs <;> ring
  simp_rw [hterm]
  have hrestrict (k : ℤ) :
      (∑ i : Fin (channelFineCount m B), ∑ j : Fin (channelFineCount m B),
        (B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then u i*v j*V k i j else 0)) =
      ∑ i ∈ geometricHistogramWindow m B t L U k,
        ∑ j ∈ geometricHistogramWindow m B t L U k, (B : ℝ)*(u i*v j*V k i j) := by
    have hinner (i : Fin (channelFineCount m B)) :
        (∑ j : Fin (channelFineCount m B),
          (B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
            j ∈ geometricHistogramWindow m B t L U k then u i*v j*V k i j else 0)) =
        if i ∈ geometricHistogramWindow m B t L U k then
          ∑ j ∈ geometricHistogramWindow m B t L U k, (B : ℝ)*(u i*v j*V k i j) else 0 := by
      by_cases hi : i ∈ geometricHistogramWindow m B t L U k
      · simp only [hi,true_and,ite_true,mul_ite,mul_zero]
        rw [← sum_filter]
        simp
      · simp [hi]
    simp_rw [hinner]
    rw [← sum_filter]
    simp
  calc
    _ = ∑ i : Fin (channelFineCount m B), ∑ k ∈ S,
        ∑ j : Fin (channelFineCount m B), (B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then u i*v j*V k i j else 0) := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ k ∈ S, ∑ i : Fin (channelFineCount m B),
        ∑ j : Fin (channelFineCount m B), (B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then u i*v j*V k i j else 0) := sum_comm
    _ = _ := sum_congr rfl (fun k _ => hrestrict k)

theorem sampledLogKernel_real (m B : ℕ)
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (a b x y : Fin (channelFineCount m B) → ℝ) (w : 𝓢(ℝ,ℝ)) :
    sampledLogKernel m B J J g h (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) x y w =
      ((∑ i ∈ J, ∑ j ∈ J, logCellSignedMass m B g i*logCellSignedMass m B h j*
        (a i*b j*w (x i-y j)) : ℝ) : ℂ) := by
  unfold sampledLogKernel
  push_cast
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem geometricSpatialKernel_coarse
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ε t L U D M₁ M₂ M : ℝ} (hε : 0 < ε) (ht : 0 < t) (hLU : L ≤ U)
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₀ : 0 ≤ M)
    (w₁ w₂ w : ℝ → ℝ) (hw₁ : ∀ x, |w₁ x| ≤ M₁)
    (hw₂ : ∀ x, |w₂ x| ≤ M₂) (hw : ∀ x, |w x| ≤ M) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop, ∀ S : Finset ℤ, ∀ β : ℝ,
      ∀ d : ℤ → ℝ, (∀ k ∈ S, |d k| ≤ D) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let K := geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β d w₁ w₂ w)
      |cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h) K-
        cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K| ≤
        2*(((1+U-L)/t+1)*(D*M₁*M₂*M))*(U-L+2)*ε := by
  obtain ⟨m,hm,he⟩ := logMassBilinear_coarse_band hSD hSW hM hMP hε
  refine ⟨m,hm,?_⟩
  filter_upwards [he,eventually_ge_atTop 1] with B heB hB
  intro S β d hd g h hg hh
  dsimp only
  have hV := endpointSpatialWeight_bound m B t β S d w₁ w₂ w hD hM₁ hM₂ hd hw₁ hw₂ hw
  have hbound := geometricWindowKernel_bounds hm hB ht hLU
    (show 0 ≤ D*M₁*M₂*M by positivity) S _ hV
  have hwidth : 0 ≤ 1+U-L := by linarith
  have hover : 0 ≤ ((1+U-L)/t+1)*(D*M₁*M₂*M) := by positivity
  have hs := heB g h hg hh _ (U-L+1) (((1+U-L)/t+1)*(D*M₁*M₂*M))
    (by linarith) hover hbound.1 hbound.2
  exact hs.trans_eq (by congr 1; ring)

end JointDickman

end OAI
