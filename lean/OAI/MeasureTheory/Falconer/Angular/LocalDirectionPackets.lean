import OAI.MeasureTheory.Falconer.Estimates.PacketRepresentativeBand
import OAI.MeasureTheory.Falconer.Estimates.FinePacketCounts

namespace OAI

/-! Comparable original packets give separated local pencils. The total
number of representatives is controlled by the original tube union. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem local_direction_packet_refinement {δ ρ s K : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/2) (hδρ : δ ≤ ρ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPsmall : ∀ p ∈ P, |p 0| ≤ 1/4 ∧ |p 1| ≤ 1/4)
    (hT : ∀ p ∈ P, (T p).Nonempty ∧ NormalizedFiniteBallBound δ s K (T p) ∧
      ∀ l ∈ T p, |l 0| ≤ 1/2 ∧ TubeIncident ρ p l)
    (D : ℕ) (hD : ∀ p ∈ P, (T p).card ≤ D) :
    let J := Nat.log 2 D+1
    let q := fun p l : Space 2 => roundedIncidentLine ρ p (l 0)
    ∃ k : ℕ, ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ (J:ℝ)*(R.card:ℝ) ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ p ∈ R, U p ⊆ (T p).image (q p) ∧ (U p).Nonempty ∧
          InBoundedLineChart (U p) ∧ FiniteSeparatedAt ρ (U p) ∧
          NormalizedFiniteBallBound ρ s (2*(K*7^s)*(J:ℝ)) (U p) ∧
          (∀ a ∈ U p, TubeIncident ρ p a) ∧
          (T p).card ≤ J*((T p).filter fun l => q p l ∈ U p).card ∧
          (T p).card ≤ J*(2*2^k)*(U p).card ∧
          2^k*(U p).card ≤ (T p).card ∧
          ∀ a ∈ U p, 2^k ≤ ((T p).filter fun l => q p l = a).card ∧
            ((T p).filter fun l => q p l = a).card < 2^(k+1)) ∧
        (2:ℝ)^k*((R.biUnion U).card:ℝ) ≤ 13*((P.biUnion T).card:ℝ) := by
  let J := Nat.log 2 D+1
  let q := fun p l : Space 2 => roundedIncidentLine ρ p (l 0)
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hlocal (p : Space 2) (hp : p ∈ P) :
      ∃ k : ℕ, k < J ∧ ∃ A ⊆ (T p).image (q p), A.Nonempty ∧
        NormalizedFiniteBallBound ρ s (2*(K*7^s)*(J:ℝ)) A ∧
        ((T p).card:ℝ) ≤ (J:ℝ)*(∑ a ∈ A, (((T p).filter fun l => q p l = a).card:ℝ)) ∧
        ∀ a ∈ A, 2^k ≤ ((T p).filter fun l => q p l = a).card ∧
          ((T p).filter fun l => q p l = a).card < 2^(k+1) := by
    have hn : ∀ l ∈ T p, dist l (q p l) ≤ 6*ρ := by
      intro l hl
      have ht := (hT p hp).2.2 l hl
      apply rounded_incident_near_line hρ p l ((hPsmall p hp).1.trans (by norm_num))
      exact (tube_residual_le hρ.le (ht.1.trans (by norm_num)) ht.2).trans (by linarith)
    simpa only [show (6:ℝ)+1=7 by norm_num] using
      packet_representative_band hρ hδρ hs hK (C := 6) (by norm_num)
        (T p) (hT p hp).1 (q p) hn (hT p hp).2.1 D (hD p hp)
  let level := fun p => if hp : p ∈ P then (hlocal p hp).choose else 0
  let U := fun p => if hp : p ∈ P then ((hlocal p hp).choose_spec.2).choose else ∅
  have hlevel (p : Space 2) (hp : p ∈ P) : level p < J := by
    simpa only [level,dite_eq_left hp] using (hlocal p hp).choose_spec.1
  have hdata (p : Space 2) (hp : p ∈ P) : U p ⊆ (T p).image (q p) ∧ (U p).Nonempty ∧
      NormalizedFiniteBallBound ρ s (2*(K*7^s)*(J:ℝ)) (U p) ∧
      ((T p).card:ℝ) ≤ (J:ℝ)*(∑ a ∈ U p, (((T p).filter fun l => q p l = a).card:ℝ)) ∧
      ∀ a ∈ U p, 2^(level p) ≤ ((T p).filter fun l => q p l = a).card ∧
        ((T p).filter fun l => q p l = a).card < 2^(level p+1) := by
    simpa only [level,U,dite_eq_left hp] using ((hlocal p hp).choose_spec.2).choose_spec
  have hmap : ∀ p ∈ P, level p ∈ Finset.range J := fun p hp => Finset.mem_range.mpr (hlevel p hp)
  have hdiv : (Finset.range J).card • ((P.card:ℝ)/(J:ℝ)) ≤ (P.card:ℝ) := by
    simp only [Finset.card_range,nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hJ.ne']
  obtain ⟨k,_,hk⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (M := ℝ) hmap (show (Finset.range J).Nonempty from ⟨0,Finset.mem_range.mpr (by dsimp [J]; omega)⟩) hdiv
  let R := P.filter fun p => level p = k
  have hRP : R ⊆ P := Finset.filter_subset _ _
  have hR : R.Nonempty := by
    apply Finset.card_pos.mp
    exact Nat.cast_pos.mp ((div_pos (Nat.cast_pos.mpr hP.card_pos) hJ).trans_le hk)
  have hmass : (P.card:ℝ) ≤ (J:ℝ)*(R.card:ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hJ).mp hk
  have hband (p : Space 2) (hp : p ∈ R) (a : Space 2) (ha : a ∈ U p) :
      2^k ≤ ((T p).filter fun l => q p l = a).card ∧
        ((T p).filter fun l => q p l = a).card < 2^(k+1) := by
    simpa only [(Finset.mem_filter.mp hp).2] using (hdata p (hRP hp)).2.2.2.2 a ha
  have hUsub : R.biUnion U ⊆ P.biUnion (fun p => (T p).image (q p)) := by
    intro a ha
    obtain ⟨p,hp,ha⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨p,hRP hp,(hdata p (hRP hp)).1 ha⟩
  refine ⟨k,R,hRP,hR,hmass,U,?_,?_⟩
  · intro p hp
    obtain ⟨hsub,hne,hreg,hweight,_⟩ := hdata p (hRP hp)
    have hsum : (∑ a ∈ U p, ((T p).filter fun l => q p l = a).card) =
        ((T p).filter fun l => q p l ∈ U p).card :=
      Finset.sum_card_fiberwise_eq_card_filter _ _ _
    have hw : (T p).card ≤ J*(∑ a ∈ U p, ((T p).filter fun l => q p l = a).card) := by
      exact_mod_cast hweight
    refine ⟨hsub,hne,?_,?_,hreg,?_,by rwa [hsum] at hw,?_,?_,hband p hp⟩
    · intro a ha
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp (hsub ha)
      exact roundedIncidentLine_in_chart hρ hρ1 p (hPsmall p (hRP hp)).1
        (hPsmall p (hRP hp)).2 (l 0) ((hT p (hRP hp)).2.2 l hl).1
    · exact finiteSeparatedAt_subset hsub (roundedIncidentLine_family_separated hρ p
        (fun l : Space 2 => l 0) (T p))
    · intro a ha
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp (hsub ha)
      exact roundedIncidentLine_incident hρ p (l 0)
    · apply hw.trans
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      calc
        _ ≤ ∑ _a ∈ U p, 2*2^k := Finset.sum_le_sum fun a ha => by
          have hh := (hband p hp a ha).2
          rw [pow_succ] at hh
          omega
        _ = _ := by simp; ring
    · calc
        _ = ∑ _a ∈ U p, 2^k := by simp; ring
        _ ≤ ∑ a ∈ U p, ((T p).filter fun l => q p l = a).card :=
          Finset.sum_le_sum fun a ha => (hband p hp a ha).1
        _ = _ := hsum
        _ ≤ _ := Finset.card_filter_le _ _
  · have hlower : 2^k*(R.biUnion U).card ≤
        ∑ a ∈ R.biUnion U, (fineCoarsePacket ρ P T a).card := by
      calc
        _ = ∑ _a ∈ R.biUnion U, 2^k := by simp; ring
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro a ha
          obtain ⟨p,hp,ha⟩ := Finset.mem_biUnion.mp ha
          apply ((hband p hp a ha).1).trans
          apply Finset.card_le_card
          intro l hl
          obtain ⟨hl,he⟩ := Finset.mem_filter.mp hl
          exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨p,hRP hp,hl⟩,p,hRP hp,hl,he⟩
    have hres : ∀ p ∈ P, ∀ l ∈ T p, |p 1-l 0*p 0-l 1| ≤ 4*ρ := by
      intro p hp l hl
      have ht := (hT p hp).2.2 l hl
      exact (tube_residual_le hρ.le (ht.1.trans (by norm_num)) ht.2).trans (by linarith)
    have htotal := sum_fineCoarsePacket_card hρ P T
      (fun p hp => (hPsmall p hp).1.trans (by norm_num)) hres
    have hh := hlower.trans ((Finset.sum_le_sum_of_subset_of_nonneg hUsub
      (fun _ _ _ => Nat.zero_le _)).trans htotal)
    exact_mod_cast hh

end Falconer

end OAI
