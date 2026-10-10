import OAI.Probability.InvariantIsing.Arrays.ReplicaCovariance

namespace OAI

/-! Error bookkeeping in the Gaussian GG comparison. -/

namespace InvariantIsing

/-- Compare the replica energy identity with its one-replica version, keeping
both the energy fluctuation and diagonal covariance errors. -/
lemma gaussianGG_of_energy_identities {t b c E U M V L L₀ O F P n : ℝ}
    (hE : 0 ≤ E) (hU : |U - b * V| ≤ c * E) (hM : |M - b| ≤ E)
    (hV : |V| ≤ c) (hu : U = t * (L + O - n * F))
    (hm : M = t * (L₀ - P)) :
    |t| * |n * F - V * P - O| ≤ 2 * c * E + |t| * |L - V * L₀| := by
  have hr : t * (n * F - V * P - O) = M * V - U + t * (L - V * L₀) := by
    rw [hm, hu]
    ring
  rw [← abs_mul, hr]
  calc
    _ ≤ |M * V - U| + |t * (L - V * L₀)| := abs_add_le _ _
    _ = |(M - b) * V - (U - b * V)| + |t| * |L - V * L₀| := by
      rw [abs_mul]
      congr 2
      ring
    _ ≤ (|M - b| * |V| + |U - b * V|) + |t| * |L - V * L₀| :=
      add_le_add (by simpa only [abs_mul] using (abs_sub ((M - b) * V) (U - b * V))) le_rfl
    _ ≤ (E * c + c * E) + |t| * |L - V * L₀| :=
      add_le_add (add_le_add (mul_le_mul hM hV (abs_nonneg _) hE) hU) le_rfl
    _ = _ := by ring

end InvariantIsing

end OAI
