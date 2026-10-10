import OAI.Dynamics.ConditionalShuffle.SelectedSchedule

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Instrument
open Thorp Thorp.Conditional
lemma Data.ext {E S G Ω : Type} {I J : Data E S G Ω}
    (ho : I.obs = J.obs) (hi : I.inc = J.inc) (hn : I.next = J.next) : I = J := by
  cases I
  cases J
  cases ho
  cases hi
  cases hn
  rfl

variable {E E' S G Ω : Type} [fintype_S : Fintype S] [fintype_G : Fintype G] [group_G : Group G] [fintype_Ω : Fintype Ω] [nonempty_Ω : Nonempty Ω]
variable (I : Data E S G Ω) (J : Data E' S G Ω) (f : E → E')
  (ho : ∀ e c, J.obs (f e) c = I.obs e c)
  (hi : ∀ e c, J.inc (f e) c = I.inc e c)
  (hn : ∀ e s, J.next (f e) s = f (I.next e s))

include hn
lemma map_base (e : E) (n : ℕ) (p : Fin n → S) :
    base J (f e) n p = f (base I e n p) := by
  let retained_fintype_S := fintype_S
  let retained_fintype_G := fintype_G
  let retained_group_G := group_G
  let retained_fintype_Ω := fintype_Ω
  let retained_nonempty_Ω := nonempty_Ω
  induction n with
  | zero => rfl
  | succ n ih => rw [base, ih, hn]; rfl

include ho
lemma map_observed (e : E) (n : ℕ) (c : Fin n → Ω) :
    observed J (f e) n c = observed I e n c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [observed, ih, map_base I J f hn, ho]

include hi
lemma map_groupRun (e : E) (n : ℕ) (c : Fin n → Ω) :
    groupRun J (f e) n c = groupRun I e n c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [groupRun, map_observed I J f ho hn, map_base I J f hn, hi, ih]

lemma map_distance (e : E) (n : ℕ) : distance J (f e) n = distance I e n := by
  rw [distance_disintegration, distance_disintegration]
  have hh : pathJoint J (f e) n = pathJoint I e n := by
    unfold pathJoint
    simp_rw [map_observed I J f ho hn, map_groupRun I J f ho hi hn]
  rw [hh]

end Revealed.Instrument

end

end OAI
