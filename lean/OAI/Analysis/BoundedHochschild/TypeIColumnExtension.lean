import OAI.Analysis.BoundedHochschild.TypeIColumnArithmetic
import OAI.Analysis.BoundedHochschild.AbelianProjectionForms

namespace OAI

/-! Extend an abelian column family unless a homogeneous central piece exists. -/

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem extend_columns_of_no_homogeneous_piece (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : ∀ z : M, CentralProjection z → z ≠ 0 → ¬ HomogeneousTypeICorner z)
    {p : M} (hp : AbelianProjection p) (hpfull : IsCentralSupport p 1)
    {n : ℕ} (v : Fin n → PartialIso M) (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    ∃ w : PartialIso M, w.initial = p ∧ w.final ≤ 1 - ∑ i, (v i).final := by
  let r := 1 - ∑ i, (v i).final
  have hr : IsStarProjection r := (column_sum_projection v ho).one_sub
  obtain ⟨t, ht⟩ := exists_central_support e hr
  have ht1 : t = 1 := by
    by_contra ht1
    have hz : CentralProjection (1 - t) :=
      ⟨ht.1.1.one_sub, fun a => (Commute.one_left a).sub_left (ht.1.2 a)⟩
    have hz0 : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
    apply hno (1 - t) hz hz0
    apply homogeneousCorner_of_annihilated_residual hp hz hz0 v hi ho
    change (1 - t) * r = 0
    rw [sub_mul, one_mul, (hr.le_iff_mul_eq_right ht.1.1).mp ht.2.1, sub_self]
  have hrfull : IsCentralSupport r 1 := by simpa only [ht1] using ht
  obtain ⟨z, u, hz, hui, huf, hzf, hzi⟩ := trace_free_central_comparison e hp.1 hr
  by_cases hz0 : z = 0
  · refine ⟨u, ?_, huf⟩
    simpa only [hz0, sub_zero, one_mul] using hzi
  exfalso
  apply hno z hz hz0
  let c := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) u
  have hci : c.initial ≤ p := by
    apply le_trans _ hui
    apply (c.initial_proj.le_iff_mul_eq_left u.initial_proj).mpr
    simp only [c, centralCutPartialIso_initial, mul_assoc, u.initial_proj.isIdempotentElem.eq]
  have hcf : c.final = z * r := by
    simpa only [c, centralCutPartialIso_final] using hzf
  have habelr : AbelianProjection (z * r) := by
    rw [← hcf]
    exact abelian_partialIso c (HochschildTypeII.abelian_of_le hp c.initial_proj hci)
  have hzp : IsStarProjection (z * p) := hz.1.mul hp.1 (hz.2 p)
  have hzple : z * p ≤ p := (hzp.le_iff_mul_eq_left hp.1).mpr
    (by rw [mul_assoc, hp.1.isIdempotentElem.eq])
  have habelp := HochschildTypeII.abelian_of_le hp hzp hzple
  obtain ⟨w, hwi, hwf⟩ := abelian_equivalent_of_central_support e habelp habelr
    (hpfull.centralCut_one hp.1 hz) (hrfull.centralCut_one hr hz)
  let a (i : Fin n) := centralCutPartialIso z hz.1 (fun b => (hz.2 b).eq) (v i)
  have hai (i : Fin n) : (a i).initial = z * p := by
    simp only [a, centralCutPartialIso_initial, hi]
  have hao (i j : Fin n) (hij : i ≠ j) : (a i).final * (a j).final = 0 := by
    simp only [a, centralCutPartialIso_final]
    rw [central_idempotent_mul z hz.1.isIdempotentElem.eq (fun b => (hz.2 b).eq),
      ho i j hij, mul_zero]
  have haw (i : Fin n) : (a i).final * w.final = 0 := by
    simp only [a, centralCutPartialIso_final, hwf]
    rw [central_idempotent_mul z hz.1.isIdempotentElem.eq (fun b => (hz.2 b).eq),
      column_mul_residual v ho i, mul_zero]
  obtain ⟨b, hbi, hbo, hbs⟩ := exists_append_columns a hai hao w hwi haw
  have hsum : ∑ i, (b i).final = z := by
    rw [hbs, hwf]
    simp only [a, centralCutPartialIso_final, ← Finset.mul_sum]
    change z * (1 - ∑ i, (v i).final) + z * ∑ i, (v i).final = z
    noncomm_ring
  apply homogeneousCorner_of_annihilated_residual habelp hz hz0 b hbi hbo
  rw [hsum]
  exact hz.1.mul_one_sub_self

end KadisonRingrose
end BoundedHochschild

end

end OAI
