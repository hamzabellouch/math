import OAI.Combinatorics.BalancedRyser.Candidates.CandidateValidityWitness

namespace OAI

namespace Balanced.CandidateExposedWitness

open CandidateValidityWitness

variable {F : Type*} [Field F]

def forcedPoint (a : MergedPairs F) (S : Line F) (d : Direction F) (s : Bool) : Point F :=
  lineIntersection S (constituent a d s)

theorem forcedPoint_on_target (a : MergedPairs F) (S : Line F) (d : Direction F)
    (hd : d ≠ S.1) (s : Bool) : OnLine (forcedPoint a S d s) S :=
  onLine_lineIntersection_left S (constituent a d s) (Ne.symm hd)

theorem forcedPoint_on_constituent (a : MergedPairs F) (S : Line F)
    (d : Direction F) (hd : d ≠ S.1) (s : Bool) :
    OnLine (forcedPoint a S d s) (constituent a d s) :=
  onLine_lineIntersection_right S (constituent a d s) (Ne.symm hd)

theorem eq_forcedPoint {a : MergedPairs F} {S : Line F} {d : Direction F}
    (hd : d ≠ S.1) {s : Bool} {x : Point F}
    (hx : OnLine x S) (hxd : OnLine x (constituent a d s)) :
    x = forcedPoint a S d s := by
  exact common_point_eq_of_lines_ne S (constituent a d s)
    (fun he => hd (congrArg Prod.fst he).symm) x (forcedPoint a S d s)
    hx hxd (forcedPoint_on_target a S d hd s)
    (forcedPoint_on_constituent a S d hd s)

theorem pairWitness_iff_forcedPoints {M a : MergedPairs F} {S : Line F}
    {d : Direction F} (hd : d ≠ S.1) (hMa : M d = a d)
    {x y : Point F} (hx : OnLine x S) (hy : OnLine y S) :
    PairWitness M d x y ↔ ∃ s : Bool,
      x = forcedPoint a S d s ∧ y = forcedPoint a S d (!s) := by
  have hline (s : Bool) : constituent M d s = constituent a d s := by
    simp only [constituent, hMa]
  constructor
  · rintro ⟨s, hxs, hys⟩
    rw [hline] at hxs hys
    exact ⟨s, eq_forcedPoint hd hx hxs, eq_forcedPoint hd hy hys⟩
  · rintro ⟨s, rfl, rfl⟩
    refine ⟨s, ?_, ?_⟩
    · rw [hline]
      exact forcedPoint_on_constituent a S d hd s
    · rw [hline]
      exact forcedPoint_on_constituent a S d hd (!s)

theorem successful_opposite_iff_fixed_positions
    [Fintype F] [DecidableEq F] {M a : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) {d : Direction F}
    (hd : d ≠ S.1) (hMa : M d = a d) (i : Fin 4) :
    PairWitness M d (tuplePoint M T i) (tuplePoint M T (i + 2)) ↔
      ∃ s : Bool, tuplePoint M T i = forcedPoint a S d s ∧
        tuplePoint M T (i + 2) = forcedPoint a S d (!s) :=
  pairWitness_iff_forcedPoints hd hMa (h.2.2.2 i) (h.2.2.2 (i + 2))

theorem exists_external_iff_forcedPoint {M a : MergedPairs F} {S : Line F}
    {d : Direction F} (hd : d ≠ S.1) (hMa : M d = a d)
    {y : Point F} (hy : OnLine y S) (R : Point F → Prop) :
    (∃ x, OnLine x S ∧ PairWitness M d x y ∧ R x) ↔
      ∃ s : Bool, y = forcedPoint a S d (!s) ∧ R (forcedPoint a S d s) := by
  constructor
  · rintro ⟨x, hx, hw, hR⟩
    obtain ⟨s, hxs, hys⟩ := (pairWitness_iff_forcedPoints hd hMa hx hy).mp hw
    exact ⟨s, hys, hxs ▸ hR⟩
  · rintro ⟨s, hys, hR⟩
    refine ⟨forcedPoint a S d s, forcedPoint_on_target a S d hd s, ?_, hR⟩
    exact (pairWitness_iff_forcedPoints hd hMa
      (forcedPoint_on_target a S d hd s) hy).mpr ⟨s, rfl, hys⟩

theorem external_point_unique [Fintype F] [DecidableEq F]
    {M : MergedPairs F} {T : FourTuple F} {S : Line F}
    (h : SuccessfulOn M T S) {d : Direction F} (hd : d ≠ S.1)
    (i : Fin 4) {x y : Point F}
    (hx : OnLine x S) (hy : OnLine y S)
    (hex : x ∉ designated M ⟨S, T⟩)
    (hxi : PairWitness M d x (tuplePoint M T i))
    (hyi : PairWitness M d y (tuplePoint M T i)) : x = y := by
  have hsym {u v : Point F} (huv : PairWitness M d u v) :
      PairWitness M d v u := by
    obtain ⟨s, hs, ht⟩ := huv
    exact ⟨!s, ht, by simpa using hs⟩
  have hne : tuplePoint M T i ≠ x := by
    intro he
    exact hex (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
  exact pairWitness_partner_unique hd (h.2.2.2 i) hx hy hne (hsym hxi) (hsym hyi)

end Balanced.CandidateExposedWitness

end OAI
