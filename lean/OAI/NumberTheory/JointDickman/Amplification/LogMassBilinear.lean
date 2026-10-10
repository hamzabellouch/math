import OAI.NumberTheory.JointDickman.Probability.CoarseKernelComparison
import OAI.NumberTheory.JointDickman.Probability.FineGridKernel

namespace OAI

/-! # Coarse approximation for the actual logarithmic mass kernel -/

namespace JointDickman
open Finset Filter

noncomputable def channelIndexEquiv (m B : ℕ) :
    Fin m × Fin (channelBlockCount m B) ≃ Fin (channelFineCount m B) := finProdFinEquiv

noncomputable def cellMassBilinear (m B : ℕ)
    (u v : Fin (channelFineCount m B) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) : ℝ :=
  ∑ i, ∑ k, u i*v k*K i k

noncomputable def coarseLogMass (m B : ℕ)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (i : Fin (channelFineCount m B)) : ℝ :=
  channelMesh (channelFineCount m B)*
    coarseGroupAverage (groupedManuscriptChannel m B g) ((channelIndexEquiv m B).symm i)

theorem cellMassBilinear_reindex (m B : ℕ)
    (u v : Fin (channelFineCount m B) → ℝ)
    (U V : Fin m × Fin (channelBlockCount m B) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hu : ∀ a, u (channelIndexEquiv m B a) = channelMesh (channelFineCount m B)*U a)
    (hv : ∀ a, v (channelIndexEquiv m B a) = channelMesh (channelFineCount m B)*V a) :
    cellMassBilinear m B u v K =
      finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B))
        (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b)) U V := by
  unfold cellMassBilinear finiteKernelBilinear finiteKernelAction
  rw [← (channelIndexEquiv m B).sum_comp]
  apply sum_congr rfl
  intro a _
  rw [← (channelIndexEquiv m B).sum_comp]
  simp only [hu,hv,mul_sum]
  apply sum_congr rfl
  intro b _
  ring

theorem logMassBilinear_reindex {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h) K =
      finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B))
        (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))
        (groupedManuscriptChannel m B g) (groupedManuscriptChannel m B h) :=
  cellMassBilinear_reindex m B _ _ _ _ K
    (fun a => (groupedManuscriptChannel_log_mass hm hB g a).symm)
    (fun a => (groupedManuscriptChannel_log_mass hm hB h a).symm)

theorem coarseLogMassBilinear_reindex (m B : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K =
      finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B))
        (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))
        (coarseGroupAverage (groupedManuscriptChannel m B g))
        (coarseGroupAverage (groupedManuscriptChannel m B h)) := by
  apply cellMassBilinear_reindex
  · intro a
    simp only [coarseLogMass,Equiv.symm_apply_apply]
  · intro a
    simp only [coarseLogMass,Equiv.symm_apply_apply]

/-- The actual logarithmic signed measures admit a fixed coarse approximation
uniformly over every kernel of height O(B) and width O(1/B). -/
theorem logMassBilinear_coarse_band
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ∀ K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ,
      ∀ C M : ℝ, 0 ≤ C → 0 ≤ M →
      (∀ i k, |K i k| ≤ M*B) →
      (∀ i k, K i k ≠ 0 → |channelLower (channelFineCount m B) i-
        channelLower (channelFineCount m B) k| ≤ C/B) →
      |cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h) K-
        cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K| ≤
        (2*M*(C+1))*ε := by
  obtain ⟨m,hm,hcoarse⟩ := groupedManuscriptChannel_bilinear_coarse hSD hSW hM hMP hε
  refine ⟨m,hm,?_⟩
  filter_upwards [hcoarse,eventually_ge_atTop 1] with B hc hB
  intro g h hg hh K C M hC hM' hK hsupp
  have hBpos : 0 < B := by omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hrpow : (B : ℝ)^(-(1/10 : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (-(1/10 : ℝ)) ≤ 0)
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans hrpow
  obtain ⟨hrow,hcol⟩ := fineGridKernel_schur (channelFineCount_pos hm hBpos) K
    hB0 hC hM' hmesh hK hsupp
  have hrow' (a : Fin m × Fin (channelBlockCount m B)) :
      (∑ b, channelMesh (channelFineCount m B)*
        |K (channelIndexEquiv m B a) (channelIndexEquiv m B b)|) ≤ 2*M*(C+1) := by
    rw [(channelIndexEquiv m B).sum_comp
      (fun k => channelMesh (channelFineCount m B)*|K (channelIndexEquiv m B a) k|)]
    exact hrow _
  have hcol' (b : Fin m × Fin (channelBlockCount m B)) :
      (∑ a, channelMesh (channelFineCount m B)*
        |K (channelIndexEquiv m B a) (channelIndexEquiv m B b)|) ≤ 2*M*(C+1) := by
    rw [(channelIndexEquiv m B).sum_comp
      (fun i => channelMesh (channelFineCount m B)*|K i (channelIndexEquiv m B b)|)]
    exact hcol _
  rw [logMassBilinear_reindex hm hBpos,coarseLogMassBilinear_reindex]
  exact hc g h hg hh _ (2*M*(C+1)) (by positivity) hrow' hcol'

end JointDickman

end OAI
