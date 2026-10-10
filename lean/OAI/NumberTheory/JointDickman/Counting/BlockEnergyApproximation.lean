import OAI.NumberTheory.JointDickman.Counting.ArithmeticBlockAverage

namespace OAI

/-! # Uniform error in replacing graph energy by its finite block average -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem arithmetic_block_energy_approximation
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      T ≤ auxiliaryCutoff B → ∀ H M : ℕ, H ≤ T → T ≤ M →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 2) →
      |arithmeticOffDiagonalGraph B L τ C T N F/((B : ℝ)*T) -
        arithmeticBlockAverage B L τ C T N H M F| ≤
          K*((H : ℝ)/T+(T : ℝ)/M)+ε := by
  obtain ⟨Ks,hKs,hshort⟩ := arithmetic_short_lags_removable hFord hMertens
  obtain ⟨Kb,hKb,hblock⟩ := arithmetic_block_endpoint_bound hFord hMertens
  refine ⟨Ks+Kb,add_pos hKs hKb,?_⟩
  filter_upwards [hshort,hblock] with B hBshort hBblock
  intro T hT hTs hTc H M hHT hTM ε hε
  filter_upwards [hBshort T hT hTs H hHT (hHT.trans hTc) (ε/2) (half_pos hε),
    hBblock T hT hTs hTc M hTM (ε/2) (half_pos hε)] with N hNs hNb
  intro L τ C F hF
  rw [arithmeticBlockAverage_eq_weighted B L τ C T N H M (hT.trans_le hTM) hTM F]
  have h1 := hNs L τ C F hF
  have h2 := hNb H L τ C F hF
  have hab := abs_sub_le (arithmeticOffDiagonalGraph B L τ C T N F/((B : ℝ)*T))
    (graphEnergyWithoutShortLags B L τ C T N H F)
    (blockWeightedGraphEnergy B L τ C T N H M F)
  have hcross1 : 0 ≤ Kb*((H : ℝ)/T) := by positivity
  have hcross2 : 0 ≤ Ks*((T : ℝ)/M) := by positivity
  have hsum : Ks*(H : ℝ)/T+ε/2+(Kb*(T : ℝ)/M+ε/2) ≤
      (Ks+Kb)*((H : ℝ)/T+(T : ℝ)/M)+ε := by
    calc
      _ ≤ Ks*(H : ℝ)/T+ε/2+(Kb*(T : ℝ)/M+ε/2)+
          (Kb*((H : ℝ)/T)+Ks*((T : ℝ)/M)) := by linarith only [hcross1,hcross2]
      _ = _ := by ring
  exact hab.trans ((add_le_add h1 h2).trans hsum)

end JointDickman

end OAI
