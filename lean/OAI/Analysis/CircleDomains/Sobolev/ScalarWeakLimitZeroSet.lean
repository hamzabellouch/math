import OAI.Analysis.CircleDomains.Sobolev.SmoothScalarWeakLimit

namespace OAI

/-! Vanishing energy on a fixed measurable set survives the actual
retained weak derivative limit. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma ScalarSmoothWeakLimit.gradient_zero_of_energy
    {v : ℕ → EuclideanPlane → ℝ} {u : EuclideanPlane → ℝ}
    (L : ScalarSmoothWeakLimit v u)
    (hm : ∀ n i, MemLp (fun x => fderiv ℝ (v n) x (EuclideanSpace.single i 1)) 2 volume)
    {A : Set EuclideanPlane} (hA : MeasurableSet A)
    (ht : Tendsto (fun n => ∫ x in A, physicalSmoothEnergy (v n) x) atTop (𝓝 0)) :
    ∀ i, ∀ᵐ x ∂volume, x ∈ A → L.witness.weakGrad x i=0 := by
  have hG (i : Fin 2) : MemLp (fun x => L.witness.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using L.witness.weakGrad_component_memLp i
  have he := weak_pair_energy_restrict_le
    (fun n => hm (L.index n) 0) (fun n => hm (L.index n) 1)
    (fun x => L.witness.weakGrad x 0) (fun x => L.witness.weakGrad x 1)
    (hG 0) (hG 1) (L.pairing 0) (L.pairing 1) hA
    (B := 0) (ht.comp L.index_strict.tendsto_atTop)
    (.of_forall fun n => le_of_eq (zero_add _).symm)
  have hz : (∫ x in A, (L.witness.weakGrad x 0)^2+(L.witness.weakGrad x 1)^2)=0 :=
    le_antisymm he (integral_nonneg fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => add_nonneg (sq_nonneg (L.witness.weakGrad x 0))
      (sq_nonneg (L.witness.weakGrad x 1)))
    (((hG 0).restrict A).integrable_sq.add ((hG 1).restrict A).integrable_sq)).mp hz
  intro i
  apply (ae_restrict_iff' hA).mp
  filter_upwards [hae] with x hx
  change (L.witness.weakGrad x 0)^2+(L.witness.weakGrad x 1)^2=(0 : ℝ) at hx
  fin_cases i
  · change L.witness.weakGrad x 0=0
    nlinarith [sq_nonneg (L.witness.weakGrad x 1)]
  · change L.witness.weakGrad x 1=0
    nlinarith [sq_nonneg (L.witness.weakGrad x 0)]

end CircleDomainRigidity

end

end OAI
