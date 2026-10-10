import OAI.Analysis.TreePotential.SegmentPolar

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

/-- Cutting needs only ancestry, so it applies to finite heads and whole components. -/

def Initial (C : Set Node) : Prop := ∀ ⦃s t⦄, s ∈ C → Prefix t s → t ∈ C

lemma initial_complement {C : Set Node} (hC : Initial C) {s t : Node}
    (hs : s ∉ C) (hst : Prefix s t) : t ∉ C := fun ht => hs (hC ht hst)

lemma prefix_of_length_le {s t u : Node} (hs : Prefix s u) (ht : Prefix t u)
    (hle : s.2.val.length ≤ t.2.val.length) : Prefix s t :=
  ⟨hs.1.trans ht.1.symm, List.prefix_of_prefix_length_le hs.2 ht.2 hle⟩

lemma prefix_equal_length {s t : Node} (h : Prefix s t)
    (hlen : s.2.val.length=t.2.val.length) : s=t := by
  apply Prefix.antisymm h
  exact ⟨h.1.symm, (h.2.eq_of_length hlen).symm ▸ List.prefix_refl _⟩

lemma Segment.head_restriction (S : Segment) {C : Set Node} (hC : Initial C)
    (hn : (S.nodes.filter (fun v => v ∈ C)).Nonempty) :
    ∃ R : Segment, R.start=S.start ∧ R.finish ∈ S.nodes ∧
      R.nodes=S.nodes.filter (fun v => v ∈ C) := by
  obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image _ (fun v : Node => v.2.val.length) hn
  have hvS := (Finset.mem_filter.mp hv).1
  have hvC := (Finset.mem_filter.mp hv).2
  have hst := (S.mem_nodes v).mp hvS
  let R : Segment := ⟨S.start,v,hst.1⟩
  refine ⟨R,rfl,hvS,?_⟩
  ext w
  rw [R.mem_nodes, Finset.mem_filter, S.mem_nodes]
  change (Prefix S.start w ∧ Prefix w v) ↔
    (Prefix S.start w ∧ Prefix w S.finish) ∧ w ∈ C
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨⟨h1,h2.trans hst.2⟩, hC hvC h2⟩
  · rintro ⟨⟨h1,h2⟩,hw⟩
    refine ⟨h1,prefix_of_length_le h2 hst.2 ?_⟩
    exact hmax w (Finset.mem_filter.mpr ⟨(S.mem_nodes w).mpr ⟨h1,h2⟩,hw⟩)

lemma Segment.tail_restriction (S : Segment) {C : Set Node} (hC : Initial C)
    (hn : (S.nodes.filter (fun v => v ∉ C)).Nonempty) :
    ∃ R : Segment, R.finish=S.finish ∧ R.start ∈ S.nodes ∧
      R.nodes=S.nodes.filter (fun v => v ∉ C) := by
  obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image _ (fun v : Node => v.2.val.length) hn
  have hvS := (Finset.mem_filter.mp hv).1
  have hvC := (Finset.mem_filter.mp hv).2
  have hst := (S.mem_nodes v).mp hvS
  let R : Segment := ⟨v,S.finish,hst.2⟩
  refine ⟨R,rfl,hvS,?_⟩
  ext w
  rw [R.mem_nodes, Finset.mem_filter, S.mem_nodes]
  change (Prefix v w ∧ Prefix w S.finish) ↔
    (Prefix S.start w ∧ Prefix w S.finish) ∧ w ∉ C
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨⟨hst.1.trans h1,h2⟩, initial_complement hC hvC h1⟩
  · rintro ⟨⟨h1,h2⟩,hw⟩
    refine ⟨prefix_of_length_le hst.2 h2 ?_,h2⟩
    exact hmin w (Finset.mem_filter.mpr ⟨(S.mem_nodes w).mpr ⟨h1,h2⟩,hw⟩)

lemma incomparable_image {F : Finset Segment} (hF : Incomparable F)
    (R : Segment → Segment) (hR : ∀ S ∈ F, (R S).start ∈ S.nodes) :
    Incomparable (F.image R) ∧ Set.InjOn R (F : Set Segment) := by
  have hins : Set.InjOn R (F : Set Segment) := by
    intro S hS T hT he
    by_contra hne
    have hh := incomparable_nodes hF hS hT hne (hR S hS) (hR T hT)
    rw [he] at hh
    exact hh.1 (prefix_refl _)
  refine ⟨?_,hins⟩
  rintro U hU V hV hne
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hU
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hV
  exact incomparable_nodes hF hS hT (fun he => hne (congrArg R he)) (hR S hS) (hR T hT)

lemma unit_subsegment_family {g : Node → ℝ} (hg : IsUnitTest g)
    {F : Finset Segment} (hF : Incomparable F)
    (R : Segment → Segment) (hR : ∀ S ∈ F, (R S).start ∈ S.nodes) :
    (∑ S ∈ F, ((R S).eval g)^2) ≤ 1 := by
  obtain ⟨hi,hinj⟩ := incomparable_image hF R hR
  have hh := hg (F.image R) hi
  rw [Finset.sum_image hinj] at hh
  exact hh

lemma unit_head {C : Set Node} (hC : Initial C) {g : Node → ℝ} (hg : IsUnitTest g) :
    IsUnitTest (C.indicator g) := by
  intro F hF
  have hex (S : Segment) : ∃ R : Segment, R.start ∈ S.nodes ∧
      (S.eval (C.indicator g))^2 ≤ (R.eval g)^2 := by
    by_cases hn : (S.nodes.filter (fun v => v ∈ C)).Nonempty
    · obtain ⟨R,hstart,hfinish,hR⟩ := S.head_restriction hC hn
      refine ⟨R,hstart ▸ S.start_mem,?_⟩
      have he : S.eval (C.indicator g) = R.eval g := by
        simp only [Segment.eval, hR, Finset.sum_filter, Set.indicator_apply]
      rw [he]
    · have he : S.eval (C.indicator g) = 0 := by
        unfold Segment.eval
        apply Finset.sum_eq_zero
        intro v hv
        have hnot : v ∉ C := fun hc => hn ⟨v,Finset.mem_filter.mpr ⟨hv,hc⟩⟩
        simp [hnot]
      exact ⟨S,S.start_mem,by simpa only [he, zero_pow (by decide : 2 ≠ 0)] using sq_nonneg (S.eval g)⟩
  choose R hR using hex
  exact (Finset.sum_le_sum (s := F) (fun S hS => (hR S).2)).trans
    (unit_subsegment_family hg hF R (fun S _ => (hR S).1))

lemma unit_tail {C : Set Node} (hC : Initial C) {g : Node → ℝ} (hg : IsUnitTest g) :
    IsUnitTest (Cᶜ.indicator g) := by
  intro F hF
  have hex (S : Segment) : ∃ R : Segment, R.start ∈ S.nodes ∧
      (S.eval (Cᶜ.indicator g))^2 ≤ (R.eval g)^2 := by
    by_cases hn : (S.nodes.filter (fun v => v ∉ C)).Nonempty
    · obtain ⟨R,hfinish,hstart,hR⟩ := S.tail_restriction hC hn
      refine ⟨R,hstart,?_⟩
      have he : S.eval (Cᶜ.indicator g) = R.eval g := by
        simp only [Segment.eval, hR, Finset.sum_filter, Set.indicator_apply, Set.mem_compl_iff]
      rw [he]
    · have he : S.eval (Cᶜ.indicator g) = 0 := by
        unfold Segment.eval
        apply Finset.sum_eq_zero
        intro v hv
        have hmem : v ∈ C := by
          by_contra hnot
          exact hn ⟨v,Finset.mem_filter.mpr ⟨hv,hnot⟩⟩
        simp [hmem]
      exact ⟨S,S.start_mem,by simpa only [he, zero_pow (by decide : 2 ≠ 0)] using sq_nonneg (S.eval g)⟩
  choose R hR using hex
  exact (Finset.sum_le_sum (s := F) (fun S hS => (hR S).2)).trans
    (unit_subsegment_family hg hF R (fun S _ => (hR S).1))

/-- At the crucial shortening step the starts are unchanged. The squared
increase is paid out of the unused unit-test budget, not an assumed tail bound. -/
lemma shortening_loss {g : Node → ℝ} (hg : IsUnitTest g) {F : Finset Segment}
    (hF : Incomparable F) (R : Segment → Segment) (c : Segment → ℝ)
    (hstart : ∀ S ∈ F, (R S).start=S.start)
    (heval : ∀ S ∈ F, (R S).eval g=S.eval g-c S)
    (hopposite : ∀ S ∈ F, S.eval g*c S ≤ 0) :
    2*(∑ S ∈ F, |S.eval g*c S|) ≤ 1-(∑ S ∈ F, (S.eval g)^2) := by
  have hh := unit_subsegment_family hg hF R (fun S hS => (hstart S hS) ▸ S.start_mem)
  have hstep : (∑ S ∈ F, ((S.eval g)^2+2*|S.eval g*c S|)) ≤
      ∑ S ∈ F, ((R S).eval g)^2 := by
    apply Finset.sum_le_sum
    intro S hS
    rw [heval S hS, abs_of_nonpos (hopposite S hS)]
    nlinarith [sq_nonneg (c S)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hstep
  linarith

section FiniteMixtures
variable {I Q : Type*} [Fintype I] [Fintype Q]

/-- This is the unsigned product only on genuinely opposite signs. -/
def oppositeProduct (a b : ℝ) : ℝ := (|a*b|-a*b)/2

lemma oppositeProduct_nonneg (a b : ℝ) : 0 ≤ oppositeProduct a b := by
  unfold oppositeProduct
  linarith [le_abs_self (a*b)]

lemma oppositeProduct_eq (a b : ℝ) :
    oppositeProduct a b = if a*b < 0 then |a*b| else 0 := by
  unfold oppositeProduct
  split_ifs with h
  · rw [abs_of_neg h]
    ring
  · rw [abs_of_nonneg (le_of_not_gt h)]
    ring

lemma unsigned_energy_identity (p : I → ℝ) (r : I → Q → ℝ) :
    (∑ q, (∑ i, p i*|r i q|)^2)-(∑ q, (∑ i, p i*r i q)^2) =
      2*(∑ i, ∑ j, p i*p j*(∑ q, oppositeProduct (r i q) (r j q))) := by
  have hid (q : Q) : (∑ i, p i*|r i q|)^2-(∑ i, p i*r i q)^2 =
      2*(∑ i, ∑ j, p i*p j*oppositeProduct (r i q) (r j q)) := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      oppositeProduct, abs_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [← Finset.sum_sub_distrib]
  simp_rw [hid]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]

/-- The independent-copy cancellation step. No independence or expectation
identity is assumed: both expectations and their product are finite sums. -/
lemma unsigned_energy_bound (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (r : I → Q → ℝ) (d : I → ℝ)
    (hc : ∀ i j, (∑ q, oppositeProduct (r i q) (r j q)) ≤ d i+d j) :
    (∑ q, (∑ i, p i*|r i q|)^2) ≤
      (∑ q, (∑ i, p i*r i q)^2)+4*(∑ i, p i*d i) := by
  have hid := unsigned_energy_identity p r
  have hb : (∑ i, ∑ j, p i*p j*(∑ q, oppositeProduct (r i q) (r j q))) ≤
      ∑ i, ∑ j, p i*p j*(d i+d j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hc i j) (mul_nonneg (hp i) (hp j))
  have he : (∑ i, ∑ j, p i*p j*(d i+d j)) = 2*(∑ i, p i*d i) := by
    calc
      _ = (∑ i, ∑ j, ((p i*d i)*p j + p i*(p j*d j))) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 2*(∑ i, p i*d i) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_one,
          ← Finset.sum_mul, hp1, one_mul]
        ring
  linarith

/-- Jensen's square-root bound, in precisely the finite-state setting used in
the atom mixtures. -/
lemma weighted_sqrt_bound (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∑ i, p i*Real.sqrt (d i)) ≤ Real.sqrt (∑ i, p i*d i) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (p i)) (fun i => Real.sqrt (p i)*Real.sqrt (d i))
  have he : (∑ i, Real.sqrt (p i)*(Real.sqrt (p i)*Real.sqrt (d i))) =
      ∑ i, p i*Real.sqrt (d i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hp i)]
  have he1 : (∑ i, (Real.sqrt (p i))^2)=1 := by simpa only [Real.sq_sqrt (hp _)] using hp1
  have he2 : (∑ i, (Real.sqrt (p i)*Real.sqrt (d i))^2)=∑ i, p i*d i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hp i), Real.sq_sqrt (hd i)]
  rw [he, he1, he2, one_mul] at hh
  have hn : 0 ≤ ∑ i, p i*d i := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hd i)
  have hs := Real.sq_sqrt hn
  nlinarith [Real.sqrt_nonneg (∑ i, p i*d i)]

end FiniteMixtures

/-- The start-mass cost, literally the upward recursion, including infinite
values. The field m is restricted by the remaining height of recursion. -/
def startCost : ℕ → (List ℕ → ℝ≥0∞) → ℝ≥0∞
  | 0, m => m []
  | n+1, m => m [] + (∑' j : ℕ, (startCost n (fun s => m (j::s)))^2)^(1/2:ℝ)

lemma startCost_mono (n : ℕ) {m r : List ℕ → ℝ≥0∞} (h : ∀ s, m s ≤ r s) :
    startCost n m ≤ startCost n r := by
  induction n generalizing m r with
  | zero => exact h []
  | succ n ih =>
    apply add_le_add (h [])
    apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/2)
    apply ENNReal.tsum_le_tsum
    intro j
    exact pow_le_pow_left' (ih (fun s => h (j::s))) 2

@[simp] lemma startCost_zero (n : ℕ) : startCost n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (0:ℝ≥0∞)+(∑' j : ℕ, (startCost n 0)^2)^(1/2:ℝ) = 0
    rw [ih]
    norm_num

lemma initial_before (t : Node) : Initial {v | ¬Prefix t v} := by
  intro s v hs hvs ht
  exact hs (ht.trans hvs)

lemma Segment.shorten_before (S : Segment) {t : Node}
    (hst : Prefix S.start t) (htf : Prefix t S.finish) (hne : S.start ≠ t) :
    ∃ R : Segment, R.start=S.start ∧ ∀ g : Node → ℝ,
      R.eval g=S.eval g-(Segment.mk t S.finish htf).eval g := by
  have hn : (S.nodes.filter (fun v => v ∈ {v | ¬Prefix t v})).Nonempty := by
    refine ⟨S.start, Finset.mem_filter.mpr ⟨S.start_mem,?_⟩⟩
    exact fun h => hne (Prefix.antisymm hst h)
  obtain ⟨R,hstart,_,hR⟩ := S.head_restriction (C := {v | ¬Prefix t v}) (initial_before t) (by simpa using hn)
  refine ⟨R,hstart,?_⟩
  intro g
  let T : Segment := ⟨t,S.finish,htf⟩
  have he : S.nodes.filter (fun v => Prefix t v) = T.nodes := by
    ext v
    rw [Finset.mem_filter, S.mem_nodes, T.mem_nodes]
    change ((Prefix S.start v ∧ Prefix v S.finish) ∧ Prefix t v) ↔
      (Prefix t v ∧ Prefix v S.finish)
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hst.trans h.1,h.2⟩,h.1⟩⟩
  change (∑ v ∈ R.nodes, g v) = (∑ v ∈ S.nodes, g v)-(∑ v ∈ T.nodes, g v)
  rw [hR]
  have hh := Finset.sum_filter_add_sum_filter_not (s := S.nodes) (p := fun v => Prefix t v) (f := g)
  rw [he] at hh
  apply eq_sub_iff_add_eq.mpr
  simpa only [Set.mem_ofPred_eq, add_comm] using hh

/-- Replacing an endpoint after an exit does not affect a headed test. -/
lemma Segment.eval_to_exit {C : Set Node} (hC : Initial C) {g : Node → ℝ}
    (hg : ∀ v ∉ C, g v=0) (S : Segment) {q : Node} (hq : q ∈ S.nodes) (hqC : q ∉ C) :
    S.eval g=(Segment.mk S.start q ((S.mem_nodes q).mp hq).1).eval g := by
  let R : Segment := ⟨S.start,q,((S.mem_nodes q).mp hq).1⟩
  have hsub : R.nodes ⊆ S.nodes := by
    intro v hv
    obtain ⟨h1,h2⟩ := (R.mem_nodes v).mp hv
    exact (S.mem_nodes v).mpr ⟨h1,h2.trans ((S.mem_nodes q).mp hq).2⟩
  symm
  apply Finset.sum_subset hsub
  intro v hv hn
  apply hg v
  intro hvC
  obtain ⟨h1,h2⟩ := (S.mem_nodes v).mp hv
  have hc := prefix_chain h2 ((S.mem_nodes q).mp hq).2
  rcases hc with hc | hc
  · exact hn ((R.mem_nodes v).mpr ⟨h1,hc⟩)
  · exact hqC (hC hvC hc)

lemma Segment.shorten_at_exit {C : Set Node} (hC : Initial C) {g : Node → ℝ}
    (hg : ∀ v ∉ C, g v=0) (S T : Segment) {q : Node}
    (hqS : q ∈ S.nodes) (hqT : q ∈ T.nodes) (hqC : q ∉ C)
    (hst : Prefix S.start T.start) (hne : S.start ≠ T.start) :
    ∃ R : Segment, R.start=S.start ∧ R.eval g=S.eval g-T.eval g := by
  have htq := ((T.mem_nodes q).mp hqT).1
  have hqf := ((S.mem_nodes q).mp hqS).2
  obtain ⟨R,hRs,hR⟩ := S.shorten_before hst (htq.trans hqf) hne
  refine ⟨R,hRs,?_⟩
  rw [hR]
  congr 1
  let U : Segment := ⟨T.start,S.finish,htq.trans hqf⟩
  have hqU : q ∈ U.nodes := (U.mem_nodes q).mpr ⟨htq,hqf⟩
  rw [Segment.eval_to_exit hC hg U hqU hqC, Segment.eval_to_exit hC hg T hqT hqC]

/-- Minimal nodes outside an initial set, including roots of unused components. -/

def IsExit (C : Set Node) (q : Node) : Prop := q ∉ C ∧ ∀ s, Prefix s q → s ≠ q → s ∈ C

lemma exits_incomparable {C : Set Node} {q r : Node} (hq : IsExit C q)
    (hr : IsExit C r) (hne : q ≠ r) : ¬Prefix q r ∧ ¬Prefix r q := by
  exact ⟨fun h => hq.1 (hr.2 q h hne),fun h => hr.1 (hq.2 r h hne.symm)⟩

lemma Segment.tail_exit (S : Segment) {C : Set Node} (hC : Initial C)
    (hs : S.start ∈ C) (hn : (S.nodes.filter (fun v => v ∉ C)).Nonempty) :
    ∃ R : Segment, R.finish=S.finish ∧ R.start ∈ S.nodes ∧
      R.nodes=S.nodes.filter (fun v => v ∉ C) ∧ IsExit C R.start := by
  obtain ⟨R,hfinish,hstart,hR⟩ := S.tail_restriction hC hn
  have hm : R.start ∈ S.nodes.filter (fun v => v ∉ C) := by rw [← hR]; exact R.start_mem
  have hout : R.start ∉ C := (Finset.mem_filter.mp hm).2
  refine ⟨R,hfinish,hstart,hR,hout,?_⟩
  intro v hv hne
  by_contra hvC
  have hvS : v ∈ S.nodes := by
    obtain hvs | hsv := prefix_chain hv ((S.mem_nodes R.start).mp hstart).1
    · exact (hvC (hC hs hvs)).elim
    · exact (S.mem_nodes v).mpr ⟨hsv,hv.trans ((S.mem_nodes R.start).mp hstart).2⟩
  have hvR : v ∈ R.nodes := by rw [hR]; exact Finset.mem_filter.mpr ⟨hvS,hvC⟩
  exact hne (Prefix.antisymm hv ((R.mem_nodes v).mp hvR).1)

end BoundedTreePotentials.Segments

end

end OAI
