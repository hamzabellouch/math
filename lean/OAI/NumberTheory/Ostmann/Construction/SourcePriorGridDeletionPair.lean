import OAI.NumberTheory.Ostmann.Construction.SourcePriorGridDeletionMass

namespace OAI

noncomputable section
namespace Ostmann.Construction.SourcePriorGridDeletion

theorem pair_grid_deletion_le (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (H : ℕ→ℕ→ℂ) {A : ℝ} (hA : 0≤A)
    (hH : ∀p∈logCellPrimes G,logCellWeight G p≠0→
      ∀q∈logCellPrimes G,logCellWeight G q≠0→‖H p q‖≤A) :
    ‖gridMean G E (fun p => gridMean G E (H p))-
      deletedMean G E (fun p => deletedMean G E (H p))‖≤
      deletionCap G E*(1+fullMassRatio G E)*A := by
  have hd := deletionCap_nonneg G E hZ
  have hR := fullMassRatio_nonneg G E hZ
  have hfirst := gridMean_sub_deletedMean_le G E hZ
    (fun p => gridMean G E (H p)) (mul_nonneg hR hA)
    (fun p hp hw => gridMean_norm_le G E hZ (H p) hA (hH p hp hw))
  have hsecond := deletedMean_norm_le G E hZ
    (fun p => gridMean G E (H p)-deletedMean G E (H p)) (mul_nonneg hd hA)
    (fun p hp hw => gridMean_sub_deletedMean_le G E hZ (H p) hA (hH p hp hw))
  have he : gridMean G E (fun p => gridMean G E (H p))-
      deletedMean G E (fun p => deletedMean G E (H p))=
      (gridMean G E (fun p => gridMean G E (H p))-
        deletedMean G E (fun p => gridMean G E (H p)))+
      deletedMean G E (fun p => gridMean G E (H p)-deletedMean G E (H p)) := by
    rw [deletedMean_sub]
    ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

theorem pair_grid_sub_source_cmean_le (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (H : ℕ→ℕ→ℂ) {A : ℝ} (hA : 0≤A)
    (hH : ∀p∈logCellPrimes G,logCellWeight G p≠0→
      ∀q∈logCellPrimes G,logCellWeight G q≠0→‖H p q‖≤A) :
    ‖gridMean G E (fun p => gridMean G E (H p))-
      (logCellPrimeSource G E hZ).law.cmean (fun p =>
        (logCellPrimeSource G E hZ).law.cmean (fun q => H p q))‖≤
      deletionCap G E*(1+fullMassRatio G E)*A := by
  simp_rw [source_cmean_eq_deletedMean]
  rw [source_cmean_eq_deletedMean G E hZ (fun p => deletedMean G E (H p))]
  exact pair_grid_deletion_le G E hZ H hA hH

theorem pair_grid_sub_source_cmean_le_three (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (H : ℕ→ℕ→ℂ) {A : ℝ} (hA : 0≤A) (hsmall : deletionCap G E≤1)
    (hH : ∀p∈logCellPrimes G,logCellWeight G p≠0→
      ∀q∈logCellPrimes G,logCellWeight G q≠0→‖H p q‖≤A) :
    ‖gridMean G E (fun p => gridMean G E (H p))-
      (logCellPrimeSource G E hZ).law.cmean (fun p =>
        (logCellPrimeSource G E hZ).law.cmean (fun q => H p q))‖≤
      3*deletionCap G E*A := by
  refine (pair_grid_sub_source_cmean_le G E hZ H hA hH).trans ?_
  have hR := (fullMassRatio_le_one_add G E hZ).trans (by linarith : 1+deletionCap G E≤2)
  have hδ := deletionCap_nonneg G E hZ
  have hm := mul_le_mul_of_nonneg_left (by linarith : 1+fullMassRatio G E≤3) hδ
  simpa only [mul_comm (deletionCap G E) 3] using mul_le_mul_of_nonneg_right hm hA

end Ostmann.Construction.SourcePriorGridDeletion

end

end OAI
