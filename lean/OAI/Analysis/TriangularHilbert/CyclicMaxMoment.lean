import OAI.Analysis.TriangularHilbert.MomentPower

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter Heat
open scoped Topology ENNReal
noncomputable section

lemma aemeasurable_cyclicMax (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    AEMeasurable (cyclicMax B C) volume := by
  apply AEMeasurable.iSup
  intro q
  exact (aemeasurable_cyclic_hard B C hB hC q.toEndpoints.lower_pos q.toEndpoints.lower_lt_upper.le).norm.ennreal_ofReal

def rationalMoment (B C : Plane → ℂ) (n : ℕ) (z : Plane) : ℝ≥0∞ :=
  ⨆ k : Fin (n+1), ENNReal.ofReal (complexMoment (cyclicKernelOutput B C
    (hardKernel (RatEndpoints.sequence k).toEndpoints.lower (RatEndpoints.sequence k).toEndpoints.upper) z))

lemma rationalMoment_mono (B C : Plane → ℂ) (z : Plane) : Monotone (fun n => rationalMoment B C n z) := by
  intro n m hnm
  apply iSup_le
  intro k
  exact le_iSup (fun k : Fin (m+1) => ENNReal.ofReal (complexMoment (cyclicKernelOutput B C
    (hardKernel (RatEndpoints.sequence k).toEndpoints.lower (RatEndpoints.sequence k).toEndpoints.upper) z)))
    ⟨k,lt_of_lt_of_le k.2 (Nat.add_le_add_right hnm 1)⟩

lemma cyclicMax_rpow_eq (B C : Plane → ℂ) (z : Plane) :
    cyclicMax B C z ^ ((3:ℝ)/2) = ⨆ n, rationalMoment B C n z := by
  rw [cyclicMax]
  change (ENNReal.orderIsoRpow ((3:ℝ)/2) (by norm_num)) _ = _
  rw [OrderIso.map_iSup]
  simp only [ENNReal.orderIsoRpow_apply, ← ofReal_complexMoment]
  apply le_antisymm
  · apply iSup_le
    intro q
    obtain ⟨n,rfl⟩ := RatEndpoints.sequence_surjective q
    exact le_iSup_of_le n (le_iSup (fun k : Fin (n+1) => ENNReal.ofReal (complexMoment (cyclicKernelOutput B C
      (hardKernel (RatEndpoints.sequence k).toEndpoints.lower (RatEndpoints.sequence k).toEndpoints.upper) z)))
      ⟨n,Nat.lt_succ_self n⟩)
  · apply iSup_le
    intro n
    apply iSup_le
    intro k
    exact le_iSup (fun q : RatEndpoints => ENNReal.ofReal (complexMoment (cyclicKernelOutput B C
      (hardKernel (q.1.1:ℝ) (q.1.2:ℝ)) z))) (RatEndpoints.sequence k)

lemma aemeasurable_rationalMoment (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) (n : ℕ) :
    AEMeasurable (rationalMoment B C n) volume := by
  unfold rationalMoment
  simp_rw [ofReal_complexMoment]
  apply AEMeasurable.iSup
  intro k
  exact ((aemeasurable_cyclic_hard B C hB hC (RatEndpoints.sequence k).toEndpoints.lower_pos
    (RatEndpoints.sequence k).toEndpoints.lower_lt_upper.le).norm.ennreal_ofReal).pow_const _

lemma lintegral_cyclicMax_moment_le (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    (∫⁻ z : Plane, cyclicMax B C z ^ ((3:ℝ)/2)) ≤
      ENNReal.ofReal (momentConstant*((∫ z : Plane, ‖B z‖^3)+(∫ z : Plane, ‖C z‖^3))) := by
  simp_rw [cyclicMax_rpow_eq]
  rw [lintegral_iSup' (aemeasurable_rationalMoment B C hB hC)
    (Eventually.of_forall (rationalMoment_mono B C))]
  apply iSup_le
  intro n
  have h := lintegral_cyclic_moment_le B C hB hC
    (fun k : Fin (n+1) => (RatEndpoints.sequence k).toEndpoints.lower)
    (fun k : Fin (n+1) => (RatEndpoints.sequence k).toEndpoints.upper)
    (fun k => (RatEndpoints.sequence k).toEndpoints.lower_pos)
    (fun k => (RatEndpoints.sequence k).toEndpoints.lower_lt_upper.le)
  simpa only [ofReal_finiteMoment,rationalMoment] using h
end
end TriangularHilbert
end

end OAI
