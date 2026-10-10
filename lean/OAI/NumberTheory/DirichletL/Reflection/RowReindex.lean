import OAI.NumberTheory.DirichletL.Reflection.OriginalMask

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def originalResidualRows (rows : Finset (Ideal Eis)) (R Q : Ideal Eis) : Finset (Ideal Eis) :=
  (representativeRowFiber rows R Q).image (fun I => rowResidualPart I Q)

lemma originalResidualRows_reconstruct (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (K : Ideal Eis) (hK : K∈originalResidualRows rows R Q) :
    reconstructFiberRow R Q K∈representativeRowFiber rows R Q ∧
      rowResidualPart (reconstructFiberRow R Q K) Q=K := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  have he := reconstructFiberRow_of_original rows R Q I hI (hrows I (Finset.mem_filter.mp hI).1)
  rw [he]
  exact ⟨hI,rfl⟩

lemma originalResidualRows_range (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes, P∣Q) (X : ℝ)
    (hrows : ∀ I∈rows, I≠0 ∧ (Ideal.absNorm I:ℝ)≤X)
    (K : Ideal Eis) (hK : K∈originalResidualRows rows R Q) :
    Admissible K ∧ (Ideal.absNorm K:ℝ)≤
      X/((Ideal.absNorm (rowPowerfulPart R):ℝ)*(Ideal.absNorm (rowMaskPart R Q):ℝ)) := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  exact mem_idealRange.mp (completedRowFiber_residual_range rows Q (rowPowerfulPart R)
    (rowMaskPart R Q) hbad X hrows I hI)

theorem original_fiber_sum_reindex {M : Type*} [AddCommMonoid M]
    (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (f : Ideal Eis→M) :
    (∑ I∈representativeRowFiber rows R Q,f I)=
      ∑ K∈originalResidualRows rows R Q,f (reconstructFiberRow R Q K) := by
  rw [originalResidualRows,Finset.sum_image (representativeRowFiber_injective rows R Q hrows)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [reconstructFiberRow_of_original rows R Q I hI (hrows I (Finset.mem_filter.mp hI).1)]

theorem original_fiber_energy_reindex (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (f : Ideal Eis→ℂ) :
    (∑ I∈representativeRowFiber rows R Q,‖f I‖^2)=
      ∑ K∈originalResidualRows rows R Q,‖f (reconstructFiberRow R Q K)‖^2 :=
  original_fiber_sum_reindex rows R Q hrows (fun I => ‖f I‖^2)

end
end SevenEighths.InverseReflectedPhase

end OAI
