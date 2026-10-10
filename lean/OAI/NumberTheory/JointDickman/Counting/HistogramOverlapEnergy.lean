import OAI.NumberTheory.JointDickman.Counting.HistogramWindowBounds
import OAI.NumberTheory.JointDickman.Probability.ChannelNorm

namespace OAI

/-! # Summing the actual local channel energies using geometric overlap -/

namespace JointDickman
open Finset Filter
open scoped Topology

private theorem local_mass_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset κ) (J : κ → Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (K : ℝ) (hK : ∀ i, ((S.filter (fun k => i ∈ J k)).card : ℝ) ≤ K) :
    (∑ k ∈ S, ∑ i ∈ J k, w i) ≤ K*∑ i, w i := by
  classical
  have he (k : κ) : (∑ i ∈ J k, w i) = ∑ i, if i ∈ J k then w i else 0 := by
    rw [← sum_filter]
    simp
  simp_rw [he]
  rw [sum_comm,mul_sum]
  apply sum_le_sum
  intro i _
  have hc : (∑ k ∈ S, if i ∈ J k then w i else 0) =
      ((S.filter (fun k => i ∈ J k)).card : ℝ)*w i := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]
  rw [hc]
  exact mul_le_mul_of_nonneg_right (hK i) (hw i)

/-- The number of dyadic boxes does not multiply the global channel energy.
Only the fixed overlap constant remains. -/
theorem manuscript_histogram_overlap_energy
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ (t L U : ℝ), 0 < t → L ≤ U → ∀ S : Finset ℤ,
      ∀ g : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ k ∈ S, ∑ i ∈ histogramWindowCells (channelFineCount m B)
          (((k : ℝ)*t+L)/B) (((k : ℝ)*t+U)/B),
        ∑ r : (ZMod q)ˣ,
          (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
            manuscriptChannel m B q g (i,r)^2) ≤
        C*((1+U-L)/t+1)*(∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2) := by
  obtain ⟨C,hC,hbound⟩ := manuscriptChannel_square_bound hSD hSW hM hMP
  refine ⟨C,hC,?_⟩
  intro m hm
  filter_upwards [hbound m hm,eventually_ge_atTop 1] with B hboundB hB
  intro q _ hq t L U ht hLU S g
  have hBpos : 0 < B := by omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hδ := channelMesh_pos (channelFineCount_pos hm hBpos)
  let J := fun k : ℤ => histogramWindowCells (channelFineCount m B)
    (((k : ℝ)*t+L)/B) (((k : ℝ)*t+U)/B)
  let w := fun i : Fin (channelFineCount m B) =>
    ∑ r : (ZMod q)ˣ, (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
      manuscriptChannel m B q g (i,r)^2
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; positivity
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 := by
    have hp : (B : ℝ)^(-(1/10 : ℝ)) ≤ 1 := by
      simpa using (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ B by exact_mod_cast hB)
        (by norm_num : (-(1/10 : ℝ)) ≤ 0))
    exact (channelMesh_scale_bound hm hBpos).trans hp
  have hK : ∀ i, ((S.filter (fun k => i ∈ J k)).card : ℝ) ≤ (1+U-L)/t+1 := by
    intro i
    refine (histogramWindow_overlap hB0 ht hLU (channelFineCount_pos hm hBpos) S i).trans ?_
    exact add_le_add (div_le_div_of_nonneg_right (by linarith) ht.le) (le_refl _)
  have hsum := local_mass_sum S J w hw _ hK
  have hglobal : (∑ i, w i) ≤ C*(∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2) := by
    simpa only [w,Fintype.sum_prod_type] using hboundB q hq g
  have hK0 : 0 ≤ (1+U-L)/t+1 := by
    have hu : 0 ≤ 1+U-L := by linarith
    positivity
  exact hsum.trans ((mul_le_mul_of_nonneg_left hglobal hK0).trans_eq (by ring))

end JointDickman

end OAI
