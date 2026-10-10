import OAI.NumberTheory.JointDickman.Probability.HistogramProductIntegral
import OAI.NumberTheory.JointDickman.Counting.HistogramOverlapEnergy

namespace OAI

/-! # Summing the actual histogram energies over geometric boxes -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem geometric_histogram_window_length {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U : ℝ} (hLU : L ≤ U) (k : ℤ) :
    ((histogramWindowCells (channelFineCount m B) (((k : ℝ)*t+L)/B)
      (((k : ℝ)*t+U)/B)).card : ℝ)*channelMesh (channelFineCount m B) ≤ (U-L+2)/B := by
  have hBpos : 0 < B := by omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have horder : ((k : ℝ)*t+L)/B ≤ ((k : ℝ)*t+U)/B :=
    div_le_div_of_nonneg_right (by linarith) hB0.le
  have hh := histogramWindowCells_length (channelFineCount_pos hm hBpos) horder
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 := by
    refine (channelMesh_scale_bound hm hBpos).trans ?_
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ B by exact_mod_cast hB) (by norm_num : (-(1/10 : ℝ)) ≤ 0)
  refine hh.trans ?_
  apply (le_div_iff₀ hB0).mpr
  have he : (((k : ℝ)*t+U)/B-((k : ℝ)*t+L)/B)*(B : ℝ) = U-L := by field_simp; ring
  nlinarith

theorem manuscript_geometric_box_energy
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ t L U : ℝ, 0 < t → L ≤ U → ∀ S : Finset ℤ,
      (∑ k ∈ S, manuscriptAmplitudeEnergy m B q
        (histogramWindowCells (channelFineCount m B) (((k : ℝ)*t+L)/B) (((k : ℝ)*t+U)/B))) ≤
        ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*C*((1+U-L)/t+1) := by
  obtain ⟨C,hC,hbound⟩ := manuscript_histogram_overlap_energy hSD hSW hM hMP
  refine ⟨C,hC,?_⟩
  intro m hm
  filter_upwards [hbound m hm,eventually_ge_atTop 1] with B hboundB hB
  intro q _ hq t L U ht hLU S
  have hBpos : 0 < B := by omega
  let J := fun k : ℤ => histogramWindowCells (channelFineCount m B)
    (((k : ℝ)*t+L)/B) (((k : ℝ)*t+U)/B)
  let E := fun k => ∑ i ∈ J k, ∑ r : (ZMod q)ˣ,
    (channelMesh (channelFineCount m B)/(q.totient : ℝ))*manuscriptChannel m B q (fun _ => 1) (i,r)^2
  have hδ := (channelMesh_pos (channelFineCount_pos hm hBpos)).le
  have hE : ∀ k, 0 ≤ E k := fun k => by dsimp [E]; positivity
  have hlocal (k : ℤ) : manuscriptAmplitudeEnergy m B q (J k) ≤
      ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*E k := by
    unfold manuscriptAmplitudeEnergy
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (geometric_histogram_window_length hm hB hLU k) (by positivity)) (hE k)
  have hsum := hboundB q hq t L U ht hLU S (fun _ => 1)
  have hprob : (∑ x, fullPrimeMass (auxiliaryPrimes B) x*(1 : ℝ)^2) = 1 := by
    simpa only [one_pow,mul_one,fullPrimeMass] using
      bernoulliSiteMass_sum (fun p : auxiliaryPrimes B => 1/(p.val : ℝ))
  rw [hprob,mul_one] at hsum
  calc
    _ ≤ ∑ k ∈ S, ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*E k := sum_le_sum (fun k _ => hlocal k)
    _ = ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*(∑ k ∈ S, E k) := (mul_sum _ _ _).symm
    _ ≤ _ := by
      have hc0 : 0 ≤ ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B) := by
        have : 0 ≤ U-L+2 := by linarith
        positivity
      exact (mul_le_mul_of_nonneg_left hsum hc0).trans_eq (by ring)

end JointDickman

end OAI
