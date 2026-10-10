import OAI.NumberTheory.CubicMoment.Estimates.PrimeTupleCoordinate
import OAI.NumberTheory.CubicMoment.Estimates.PrimeConvolutionBounds

namespace OAI

/-! Fixed multiplicity for the actual tuple remaining after a distinguished
coordinate is removed. The unit coordinate stays explicit. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma complementTuple_primary (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {g : ι → Eisenstein} (hg : g ∈ coordinateComplementTuples S i) :
    primary (∏ j, g j) := by
  obtain ⟨hgi,hg⟩ := (coordinateComplement_mem S i g).mp hg
  apply primary_finset_prod
  intro j _
  by_cases hj : j = i
  · simpa only [hj,hgi] using primary_one
  · exact (hS j (g j) (hg j hj)).1

lemma complementTuple_range_subset (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {f g : ι → Eisenstein} (hf : f ∈ coordinateComplementTuples S i)
    (hg : g ∈ coordinateComplementTuples S i)
    (hprod : (∏ j, g j) = ∏ j, f j) (j : ι) :
    g j ∈ Finset.univ.image f := by
  obtain ⟨hfi,hf⟩ := (coordinateComplement_mem S i f).mp hf
  obtain ⟨hgi,hg⟩ := (coordinateComplement_mem S i g).mp hg
  by_cases hji : j = i
  · exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simpa only [hji,hgi] using hfi⟩
  · have hp := hS j (g j) (hg j hji)
    have hd : g j ∣ ∏ k, f k := hprod ▸ Finset.dvd_prod_of_mem g (Finset.mem_univ j)
    obtain ⟨k,_,hk⟩ := (hp.2.dvd_finsetProd_iff f).mp hd
    have hki : k ≠ i := by
      intro he
      rw [he,hfi] at hk
      exact hp.2.not_isUnit (isUnit_of_dvd_one hk)
    have hpk := hS k (f k) (hf k hki)
    have he : g j = f k := primary_associated_eq hp.1 hpk.1
      ((hp.2.dvd_prime_iff_associated hpk.2).mp hk)
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,he.symm⟩

theorem complementTuple_fiber_card (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι) (r : Eisenstein) :
    ((coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r)).card ≤
      (Fintype.card ι)^(Fintype.card ι) := by
  let T := (coordinateComplementTuples S i).filter (fun g => (∏ j, g j) = r)
  by_cases hT : T.Nonempty
  · obtain ⟨f,hf⟩ := hT
    obtain ⟨hfs,hfr⟩ := Finset.mem_filter.mp hf
    have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.univ.image f) := by
      intro g hg
      obtain ⟨hgs,hgr⟩ := Finset.mem_filter.mp hg
      apply Fintype.mem_piFinset.mpr
      exact complementTuple_range_subset S hS i hfs hgs (hgr.trans hfr.symm)
    calc
      T.card ≤ (Fintype.piFinset (fun _ : ι => Finset.univ.image f)).card := Finset.card_le_card hsub
      _ = ((Finset.univ.image f).card)^(Fintype.card ι) := by simp [Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left (by
        simpa using (Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := f))) _
  · change T.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty]
    exact Nat.zero_le _

lemma complementTuple_prime_factor (S : ι → Finset Eisenstein)
    (hS : ∀ j, ∀ p ∈ S j, primaryPrime p) (i : ι)
    {g : ι → Eisenstein} (hg : g ∈ coordinateComplementTuples S i)
    {p : Eisenstein} (hp : primaryPrime p) (hpd : p ∣ ∏ j, g j) :
    ∃ j, j ≠ i ∧ p = g j := by
  obtain ⟨hgi,hg⟩ := (coordinateComplement_mem S i g).mp hg
  obtain ⟨j,_,hj⟩ := (hp.2.dvd_finsetProd_iff g).mp hpd
  have hji : j ≠ i := by
    intro he
    rw [he,hgi] at hj
    exact hp.2.not_isUnit (isUnit_of_dvd_one hj)
  exact ⟨j,hji,primary_associated_eq hp.1 (hS j (g j) (hg j hji)).1
    ((hp.2.dvd_prime_iff_associated (hS j (g j) (hg j hji)).2).mp hj)⟩

end CubicFirstMoment

end

end OAI
