import OAI.Analysis.PlanarPacking.Nodes
import OAI.Analysis.PlanarPacking.Entries

namespace OAI

/-!
# Contact data for cardinal interpolation

The prescribed contacts and their Gaussian transforms give summable right hand sides for the interpolation equations.
-/

namespace SharpPlanar
noncomputable def transformedJets (p : CardinalData) (ni : Node×Bool) : ℝ :=
  if ni.2 then (D ni.1.val*K p 0 ni.1.val-K p 1 ni.1.val)/Q ni.1.val
  else -K p 0 ni.1.val/Q ni.1.val
noncomputable def dataMass (p : CardinalData) : ℝ :=
  25*|p.C|+densityBound*(|p.c₀|+|p.d₀|+‖p.x‖)
lemma dataMass_nonneg (p : CardinalData) : 0 ≤ dataMass p := by
  unfold dataMass
  exact add_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
    (mul_nonneg densityBound_nonneg (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)))
lemma transformedJets_bound (p : CardinalData) (ni : Node×Bool) :
    |transformedJets p ni| ≤ allNodeWeight*dataMass p*
      (kernelEnvelope 0 ni.1.val+kernelEnvelope 1 ni.1.val) := by
  have he0 := kernelEnvelope_nonneg 0 (ni.1.val:ℝ)
  have he1 := kernelEnvelope_nonneg 1 (ni.1.val:ℝ)
  have hd := dataMass_nonneg p
  have hq := Q_pos ni.1.val
  have h0 := K_bound p 0 (Nat.cast_nonneg ni.1.val)
  have h1 := K_bound p 1 (Nat.cast_nonneg ni.1.val)
  change |K p 0 ni.1.val| ≤ dataMass p*kernelEnvelope 0 ni.1.val at h0
  change |K p 1 ni.1.val| ≤ dataMass p*kernelEnvelope 1 ni.1.val at h1
  have hlocal : |transformedJets p ni| ≤ nodeWeight ni.1.val*dataMass p*
      (kernelEnvelope 0 ni.1.val+kernelEnvelope 1 ni.1.val) := by
    unfold transformedJets nodeWeight
    split
    · rw [abs_div,abs_of_pos hq]
      calc
        _ ≤ (|D ni.1.val| *|K p 0 ni.1.val|+|K p 1 ni.1.val|)/Q ni.1.val := by
          apply div_le_div_of_nonneg_right _ hq.le
          exact (abs_sub _ _).trans (by rw [abs_mul])
        _ ≤ (|D ni.1.val| *(dataMass p*kernelEnvelope 0 ni.1.val)+dataMass p*kernelEnvelope 1 ni.1.val)/Q ni.1.val := by gcongr
        _ ≤ _ := by
          apply (div_le_iff₀ hq).mpr
          field_simp
          nlinarith [mul_nonneg (abs_nonneg (D ni.1.val)) (mul_nonneg hd he1),mul_nonneg hd he0]
    · rw [abs_div,abs_neg,abs_of_pos hq]
      calc
        _ ≤ (dataMass p*kernelEnvelope 0 ni.1.val)/Q ni.1.val := by gcongr
        _ ≤ _ := by
          apply (div_le_iff₀ hq).mpr
          field_simp
          nlinarith [mul_nonneg (abs_nonneg (D ni.1.val)) (mul_nonneg hd (add_nonneg he0 he1)),mul_nonneg hd he1]
  exact hlocal.trans (by gcongr; exact nodeWeight_le ni.1)
lemma transformedJets_summable (p : CardinalData) : Summable (fun ni => |transformedJets p ni|) := by
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun ni => transformedJets_bound p ni)
    (pairEnvelope_summable.mul_left _)
noncomputable def transformedJetList (p : CardinalData) : X :=
  ⟨transformedJets p,memℓp_gen (by simpa using transformedJets_summable p)⟩
noncomputable def firstNode : Node := ⟨1,by norm_num [residues]⟩
noncomputable def contactList : X := columnVector firstNode true
noncomputable def g₁ : X := transformedJetList (fixed₂ 0)-contactList
noncomputable def g₂ : X := transformedJetList (fixed₁ 0)

end SharpPlanar

end OAI
