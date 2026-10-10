import OAI.Analysis.FourierLLogL.Paths.Encore
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Troupe
open Plot

/-- Path additionally follows birth rules. -/
def Cast (j J : ℕ) (f : Grid M → ℝ) (s : Scene M) : Path M → Prop
| [] => s.Safe j J f
| b::l => b.pre=s ∧ (∃ k, Following j J f (ran b.pre b.post k)) ∧ Cast j J f (winds b) l

lemma stream_cast {s : Scene M} (v : Thread M s) (h : Following j J f v)
    (x : Grid M) : Cast j J f s (v.stream x) := by
  induction v with
  | blank => exact h
  | ran s q k ih =>
    let b := (step q).bit x
    exact ⟨rfl,⟨k,h⟩,ih b (h.2.2.2.2.2 b)⟩

def quarrel (p : Plot) (c : Board M) : Path M → Board M
| [] => c
| b::l => quarrel p (turn p c b.post) l
lemma quarrel_chart (p : Plot) (c : Board M) (l : Path M) :
    (quarrel p c l).chart = goal p.ix p.main c.chart l := by
  induction l generalizing c with
  | nil => rfl
  | cons b l ih => exact ih _

lemma quarrel_concat (p : Plot) (c : Board M) (l r : Path M) :
    quarrel p c (l++r)=quarrel p (quarrel p c l) r := by
  induction l generalizing c with
  | nil => rfl
  | cons b l ih => exact ih _

def oiled (p : Plot) (c : Board M) (l : Path M) :=
    cardStep p (quarrel p c l)

def heroPlot (g : Grade) (l : Path M) := stage g (chooseCap g l)

lemma oil_hero (g : Grade) (l : Path M) :
    oiled (heroPlot g l) (vacant M) l := by
  unfold oiled cardStep; rw [quarrel_chart]; exact (choice_bounds g l).2.1

lemma still_head {s : Scene M} (l : Path M) (h : Cast j J f s l)
    (p : Plot) (c : Board M) (he : Comes c s j J f) :
    c.chart.items ⊆ (quarrel p c l).chart.items := by
  induction l generalizing s c with
  | nil => exact Finset.Subset.refl _
  | cons b l ih =>
    obtain ⟨rfl,⟨k,hk⟩,ht⟩ := h
    apply Finset.Subset.trans _ (ih ht (turn p c b.post) (comes_down p hk he b.bit))
    exact (zoom_spec _ he.valid p.ix p.main hk).extend

lemma oily_cons {s : Scene M} (p : Plot) {c : Board M} {b : Beat M} {l : Path M}
    (h : Cast j J f s (b::l)) (ht : Comes c s j J f) (hv : oiled p c (b::l)) :
    boom p c b.post ∧ oiled p (turn p c b.post) l ∧ Comes (turn p c b.post) (winds b) j J f := by
  obtain ⟨rfl,⟨k,hk⟩,he⟩ := h
  have hi := comes_down p hk ht b.bit
  exact ⟨le_trans (Finset.card_le_card (still_head l he p _ hi)) hv,hv,hi⟩

lemma birth_just (p : Plot) (c : Board M) (s : Scene M) {b : Beat M} (l r : Path M)
    (h : Cast j J f s (l++b::r))
    (ht : Comes c s j J f) (hv : oiled p c (l++b::r)) :
    Comes (quarrel p c l) b.pre j J f ∧
      (∃ k, Following j J f (ran b.pre b.post k)) ∧ boom p (quarrel p c l) b.post := by
  induction l generalizing s c with
  | nil =>
    exact ⟨h.1.symm ▸ ht,h.2.1,(oily_cons p h ht hv).1⟩
  | cons a l ih =>
    have H := (oily_cons p h ht hv)
    exact ih (turn p c a.post) _ h.2.2 H.2.2 H.2.1

lemma still_rec {s : Scene M} (p : Plot) {c : Board M} (b : Beat M)
    (l m : Path M) (h : Cast j J f s (l++b::m)) (he : Comes c s j J f)
    (hv : oiled p c (l++b::m)) (q : Scene M)
    (hh : (turn p (quarrel p c l) b.post).previous=some q)
    (x : Grid M) (hx : x∈net q j p.ix p.main) :
    c.previous=some q ∨ ∃ u w : Path M, l=u++w ∧
      recital (grade p) x (w++(b::m)) ≤ showScore p c j (l++b::m) := by


  induction l generalizing s c with
  | nil =>
    have H := oily_cons p h he hv
    change (turn p c b.post).previous=some q at hh
    rw [prior_step _ _ _ H.1] at hh
    by_cases hi : p.freshAt c b.post
    · rw [ite_eq_left hi] at hh
      cases Option.some.inj hh
      refine Or.inr ⟨[],[],rfl,?_⟩
      change recital _ _ (b::m) ≤ _
      simp only [List.nil_append,showScore,ite_eq_left H.1,ite_eq_left hi]
      apply le_trans (b:=burst p b.post j (b::m))
      · exact Finset.single_le_sum (f:=fun x => recital (grade p) x (b::m))
          (fun x _ => le_trans (by norm_num) (rec_one _ _ _)) hx
      linarith [show_one p (turn p c b.post) j m]
    · exact Or.inl ((ite_eq_right hi).symm.trans hh)
  | cons a l ih =>
    let d := turn p c a.post
    have H := oily_cons p h he hv
    have HE : Cast j J f (winds a) (l++b::m) := h.2.2
    rcases ih (c:=d) HE H.2.2 H.2.1 hh with hv|⟨u,w,hw,hv⟩
    · unfold d at hv; rw [prior_step p c a.post H.1] at hv
      by_cases hi : freshAt p c a.post
      · rw [ite_eq_left hi] at hv
        cases Option.some.inj hv
        refine Or.inr ⟨[],a::l,rfl,?_⟩
        let r := a::(l++b::m)
        change recital _ _ r ≤ showScore _ _ _ (a::(l++b::m))
        simp only [showScore,ite_eq_left H.1,ite_eq_left hi]
        apply le_trans (b:=burst p a.post j r)
        · exact Finset.single_le_sum (f:=fun x => recital (grade p) x r)
            (fun x _ => le_trans (by norm_num) (rec_one _ _ _)) hx
        linarith [show_one p (turn p c a.post) j (l++b::m)]
      · exact Or.inl ((ite_eq_right hi).symm.trans hv)
    · apply Or.inr; refine ⟨a::u,w,by rw [hw]; rfl,?_⟩
      change _ ≤ showScore p c j (a::(l++b::m))
      rw [showScore,ite_eq_left H.1]; apply hv.trans
      apply le_add_of_nonneg_left; split; apply burst_pos; norm_num

def ringing (u : Grid M) (p : Plot) (j : ℕ) (l : Path M) (b : Beat M) :=
    p.catches b.post (quarrel p (vacant M) l) j u

lemma live_rec :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ,
      ∀ (u : Grid M) (g : Grade) (l r : Path M) (b : Beat M),
        let L := l++b::r
        let p := heroPlot g L
        Cast j J f s L → entitled g s j → ringing u p j l b →
        ∃ x : Grid M, p.aligned b.post j u x ∧ ∃ a k : Path M, l=a++k ∧
          2*log (recital g x (k++b::r)) ≤ timex g j L := by
  filter_upwards [currently] with j h M J s f u g l r b L p hC hE hp
  let c := vacant M
  have HC := vacant_comes (j:=j) (J:=J) (f:=f) s
  have He := oil_hero g L
  obtain ⟨ha,⟨k,hk⟩,hK⟩ := birth_just p c s l r hC HC He
  obtain ⟨q,H,hQ,w,hw,hW⟩ := h p (fun hx => (hE hx).1) M J f b.pre b.post k hk _ ha hK u hp
  refine ⟨w,hW,?_⟩
  rcases still_rec p b l r hC HC He q H w hw with h1|⟨v,z,hz,ht⟩
  · cases h1
  refine ⟨v,z,hz,?_⟩
  apply le_trans _ (timex_scores g j L).2
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact log_le_log (lt_of_lt_of_le (by norm_num) (rec_one g _ _)) ht

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
