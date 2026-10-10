import OAI.Combinatorics.Sensitivity.LabelingEvents
import OAI.Combinatorics.Sensitivity.LabelingEstimate
import OAI.Combinatorics.Sensitivity.TournamentCyclic

namespace OAI

/-! A finite union bound supplies a good edge labeling. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k r : ℕ} (T : Tournament k)

theorem goodLabeling_exists_of_power_bound (hr : 0 < r) (hN : 120 ≤ k*k)
    (hkr : k^16 < r^104) : Nonempty (GoodLabeling T r) := by
  have htotal : k^16*r^16*r^(k*k-120) < r^(k*k) := by
    calc
      k^16*r^16*r^(k*k-120) < r^104*r^16*r^(k*k-120) :=
        Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_right hkr (pow_pos hr 16)) (pow_pos hr _)
      _ = r^(104+16+(k*k-120)) := by rw [pow_add, pow_add]
      _ = r^(k*k) := congrArg (fun e : ℕ => r^e) (by omega)
  have hc : (T.badLabelings 16 r).card <
      (Finset.univ : Finset ((Fin k × Fin k) → Fin r)).card := by
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
      using (T.card_badLabelings_le (r := r) (n := 16)).trans_lt htotal
  obtain ⟨A,_,hA⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨⟨fun i j => A (i,j), ?_⟩⟩
  intro I hI m
  by_contra hn
  let e : Fin 16 ≃ I := (Finset.equivFinOfCardEq hI).symm
  let v : Fin 16 → Fin k := fun i => (e i).val
  have hv : Function.Injective v := Subtype.val_injective.comp e.injective
  have hevent : A ∈ T.labelingEvent v (fun i => m (v i)) := by
    apply T.mem_labelingEvent_iff hv |>.mpr
    intro i j ha
    by_contra h
    exact hn ⟨v i,(e i).property,v j,(e j).property,ha,h⟩
  apply hA
  exact T.labelingEvent_subset_bad hevent

end Tournament

theorem goodLabeling_exists {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2)
    (T : Tournament (2*M^2+1)) : Nonempty (GoodLabeling T r) := by
  have hr : 0 < r := (Nat.pow_pos_iff.mp
    (lt_of_lt_of_le (show 0 < M by omega) hMr)).resolve_right (by omega)
  exact T.goodLabeling_exists_of_power_bound hr (labeling_space_large hM)
    (labeling_power_bound hM hMr)

theorem regular_goodLabeling_exists {M : ℕ} (hM : 3 ≤ M) :
    Nonempty (GoodLabeling (regularCyclicTournament M).toTournament
      (Nat.ceil (Real.sqrt M))) :=
  goodLabeling_exists hM (le_ceil_sqrt_sq M) _

namespace GoodLabeling

theorem good_on_subset {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)
    (I : Finset (Fin k)) (hI : I.card = 16) (m : I → Fin r) :
    ∃ i ∈ I, ∃ j, ∃ hj : j ∈ I,
      T.Adj i j ∧ A.label i j ≠ m ⟨j,hj⟩ := by
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  let m' : Fin k → Fin r := fun i => if hi : i ∈ I then m ⟨i,hi⟩ else m ⟨j,hj⟩
  obtain ⟨a,ha,b,hb,hab,hne⟩ := A.good I hI m'
  refine ⟨a,ha,b,hb,hab,?_⟩
  simpa only [m', dite_eq_left hb] using hne

end GoodLabeling
end Paper320

end

end OAI
