import OAI.Analysis.BoundedHochschild.AbelianCentralSupport
import OAI.Analysis.BoundedHochschild.OrthogonalProjectionSums

namespace OAI

/-! Orthogonal initial projections of partial isometries with final projections
under a given projection exhaust its central support. Only trace-free
comparison and normal projection sums are used. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_central_support_row (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p z : M} (hp : IsStarProjection p) (hz : IsCentralSupport p z) :
    ∃ S : Set (PartialIso M),
      (∀ v ∈ S, v.final ≤ p ∧ v.initial ≤ z) ∧
      (∀ v ∈ S, ∀ w ∈ S, v ≠ w → v.initial * w.initial = 0) ∧
      PredualTendsto e (fun s : Finset S => ∑ v ∈ s, v.val.initial) atTop z := by
  classical
  let A : Set (Set (PartialIso M)) := {S |
    (∀ v ∈ S, v.final ≤ p ∧ v.initial ≤ z) ∧
    (∀ v ∈ S, ∀ w ∈ S, v ≠ w → v.initial * w.initial = 0)}
  obtain ⟨S, hS⟩ := zorn_subset A (fun c hc hchain => by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro v hv
      obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
      exact (hc hs).1 v hvs
    · intro v hv w hw hvw
      obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
      obtain ⟨t, ht, hwt⟩ := Set.mem_sUnion.mp hw
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 v (hst hvs) w hwt hvw
      · exact (hc hs).2 v hvs w (hts hwt) hvw)
  have horth (v w : S) (hvw : v ≠ w) : v.val.initial * w.val.initial = 0 :=
    hS.1.2 v v.property w w.property (fun h => hvw (Subtype.ext h))
  obtain ⟨q, hq, hvq, hql, ht⟩ := exists_orthogonal_projection_sum e
    (fun v : S => v.val.initial) (fun v => v.val.initial_proj) horth
  have hqz : q ≤ z := hql z hz.1.1 (fun v => (hS.1.1 v v.property).2)
  have heq : q = z := by
    by_contra hne
    have hr : IsStarProjection (z - q) := (hq.le_iff_sub hz.1.1).mp hqz
    obtain ⟨a, ha⟩ := central_support_full e hp hz hr
      (sub_le_self _ hq.nonneg) (sub_ne_zero.mpr (Ne.symm hne))
    obtain ⟨w, hw0, hwi, hwf⟩ := partialIso_of_nonzero_corner e hp hr
      (p * a * (z - q)) ha
      (by rw [← mul_assoc, ← mul_assoc, hp.isIdempotentElem.eq])
      (by rw [mul_assoc, hr.isIdempotentElem.eq])
    have hqw : q * w.initial = 0 :=
      HochschildCentralComparison.orthogonal_of_le_sub hz.1.1 hq w.initial_proj hqz hwi
    have hvw (v : PartialIso M) (hv : v ∈ S) : v.initial * w.initial = 0 := by
      have hvq' := hvq ⟨v, hv⟩
      calc
        _ = (v.initial * q) * w.initial := by
          rw [(v.initial_proj.le_iff_mul_eq_left hq).mp hvq']
        _ = 0 := by rw [mul_assoc, hqw, mul_zero]
    have hnew : insert w S ∈ A := by
      refine ⟨?_, ?_⟩
      · intro v hv
        rcases hv with rfl | hv
        · exact ⟨hwf, hwi.trans (sub_le_self _ hq.nonneg)⟩
        · exact hS.1.1 v hv
      · intro v hv t ht hvt
        rcases hv with rfl | hv <;> rcases ht with rfl | ht
        · exact (hvt rfl).elim
        · exact PartialIso.orthogonal_initial_symm (hvw t ht)
        · exact hvw v hv
        · exact hS.1.2 v hv t ht hvt
    have hwS : w ∈ S := hS.2 hnew (Set.subset_insert w S) (Set.mem_insert w S)
    have hii : w.initial = 0 := by
      simpa only [w.initial_proj.isIdempotentElem.eq] using hvw w hwS
    apply hw0
    have hh := w.mul_initial
    rw [hii, mul_zero] at hh
    exact hh.symm
  exact ⟨S, hS.1.1, hS.1.2, heq ▸ ht⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
