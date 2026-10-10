import OAI.Combinatorics.HalvingLines.Packing

namespace OAI

open Filter Topology

namespace PlanarHalving
open Set

lemma Generic.comp_strictMono {n m : ℕ} {P : Fin n → Point} (hP : Generic P)
    {f : Fin m → Fin n} (hf : StrictMono f) : Generic (P∘f) := by
  refine ⟨⟨hP.1.1.comp hf.injective,?_⟩,?_,?_,?_⟩
  · intro i j l hij hjl hil
    exact hP.1.2 _ _ _ (hf.injective.ne hij) (hf.injective.ne hjl) (hf.injective.ne hil)
  · intro i j hij
    exact hP.2.1 _ _ (hf.injective.ne hij)
  · intro i j a b hij hab he
    obtain ⟨hi,hj⟩ := hP.2.2.1 _ _ _ _ (hf hij) (hf hab) he
    exact ⟨hf.injective hi,hf.injective hj⟩
  · intro i j a b c d hij hab hcd hne hci hca z hzij hzab hzcd
    have hinj : Function.Injective (Prod.map f f) := hf.injective.prodMap hf.injective
    exact hP.2.2.2 _ _ _ _ _ _ (hf hij) (hf hab) (hf hcd)
      (hinj.ne hne) (hinj.ne hci) (hinj.ne hca) z hzij hzab hzcd

namespace Sweep
variable {n T k : ℕ} {P : Fin n → Point}

lemma States.outside_activity_constant (S : @States n T k P)
    {u v : Fin (T+1)} (huv : u ≤ v) {x : Fin n} (hx : x ∉ S.intervalActivity u v huv)
    {i : Fin (T+1)} (hui : u ≤ i) (hiv : i ≤ v) : x ∈ S.marks i  ↔  x ∈ S.marks u := by
  by_contra H
  apply hx
  rw [S.mem_intervalActivity huv]
  exact ⟨i,hui,hiv,by tauto⟩

lemma States.intervalActivity_self (S : @States n T k P) (u : Fin (T+1)) :
    S.intervalActivity u u le_rfl=∅ := by
  classical
  ext x
  simp only [Finset.notMem_empty,iff_false,S.mem_intervalActivity]
  rintro ⟨i,hi,hj,h⟩
  have he : i=u := le_antisymm hj hi
  subst i
  tauto

lemma States.intervalActivity_mono (S : @States n T k P)
    {u v w : Fin (T+1)} (huv : u ≤ v) (hvw : v ≤ w) :
    S.intervalActivity u v huv⊆S.intervalActivity u w (huv.trans hvw) := by
  intro x hx
  obtain ⟨i,hui,hiv,hi⟩ := (S.mem_intervalActivity huv).mp hx
  exact (S.mem_intervalActivity (huv.trans hvw)).mpr ⟨i,hui,hiv.trans hvw,hi⟩

lemma States.intervalActivity_step_subset (S : @States n T k P)
    {u : Fin (T+1)} (j : Fin T) (hu : u ≤ j.castSucc) :
    S.intervalActivity u j.succ (hu.trans (Fin.castSucc_le_succ j))⊆
      S.intervalActivity u j.castSucc hu ∪ ((S.marks j.castSucc\S.marks j.succ)∪
        (S.marks j.succ\S.marks j.castSucc)) := by
  classical
  intro x hx
  obtain ⟨i,hui,hij,hi⟩ := (S.mem_intervalActivity _).mp hx
  by_cases hprev : i ≤ j.castSucc
  · exact Finset.mem_union_left _ ((S.mem_intervalActivity hu).mpr ⟨i,hui,hprev,hi⟩)
  · have he : i=j.succ := Fin.ext (by change i.val=j.val+1;change i.val ≤ j.val+1 at hij;change ¬i.val ≤ j.val at hprev;omega)
    subst i
    by_cases hbefore : x ∈ S.intervalActivity u j.castSucc hu
    · exact Finset.mem_union_left _ hbefore
    · have hb := S.outside_activity_constant hu hbefore hu le_rfl
      apply Finset.mem_union_right
      simp only [Finset.mem_union,Finset.mem_sdiff]
      tauto

lemma States.intervalActivity_step_card (S : @States n T k P)
    {u : Fin (T+1)} (j : Fin T) (hu : u ≤ j.castSucc) :
    (S.intervalActivity u j.succ (hu.trans (Fin.castSucc_le_succ j))).card ≤
      (S.intervalActivity u j.castSucc hu).card+2 := by
  have h := Finset.card_le_card (S.intervalActivity_step_subset j hu)
  have h1 := Finset.card_union_le (S.intervalActivity u j.castSucc hu)
    ((S.marks j.castSucc\S.marks j.succ)∪(S.marks j.succ\S.marks j.castSucc))
  have h2 := Finset.card_union_le (S.marks j.castSucc\S.marks j.succ) (S.marks j.succ\S.marks j.castSucc)
  have h3 := S.step j
  have h4 := Finset.card_sdiff_comm ((S.card_marks j.castSucc).trans (S.card_marks j.succ).symm)
  change (S.marks j.castSucc\S.marks j.succ).card ≤ 1 at h3
  omega

end Sweep
end PlanarHalving
namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

noncomputable def States.activitySize (S : @States n T k P) (u v : Fin (T+1)) : ℕ :=
  if h : u ≤ v then (S.intervalActivity u v h).card else 0

lemma States.activitySize_eq (S : @States n T k P) {u v : Fin (T+1)} (h : u ≤ v) :
    S.activitySize u v=(S.intervalActivity u v h).card := dite_eq_left h

lemma States.activitySize_self (S : @States n T k P) (u : Fin (T+1)) : S.activitySize u u=0 := by
  rw [S.activitySize_eq le_rfl,S.intervalActivity_self,Finset.card_empty]

noncomputable def States.activityEligible (S : @States n T k P) (s : Fin (T+1)) (b : ℕ) : Finset (Fin (T+1)) :=
  Finset.univ.filter (fun t => s<t ∧ b ≤ S.activitySize s t)

noncomputable def States.activityNext (S : @States n T k P) (s : Fin (T+1)) (b : ℕ)
    (h : (S.activityEligible s b).Nonempty) : Fin (T+1) := (S.activityEligible s b).min' h

lemma States.activityNext_spec (S : @States n T k P) (s : Fin (T+1)) (b : ℕ)
    (h : (S.activityEligible s b).Nonempty) : s<S.activityNext s b h ∧ b ≤ S.activitySize s (S.activityNext s b h) := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2

lemma States.before_activityNext (S : @States n T k P) (s : Fin (T+1)) {b : ℕ} (hb : 0<b)
    (h : (S.activityEligible s b).Nonempty) {t : Fin (T+1)} (hst : s ≤ t) (ht : t<S.activityNext s b h) :
    S.activitySize s t<b := by
  by_cases he : t=s
  · subst t;simpa only [S.activitySize_self] using hb
  by_contra hh
  have hm : t ∈ S.activityEligible s b := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,lt_of_le_of_ne hst (Ne.symm he),le_of_not_gt hh⟩
  exact not_le_of_gt ht (Finset.min'_le _ _ hm)

lemma States.activityNext_bound (S : @States n T k P) (s : Fin (T+1)) {b : ℕ} (hb : 0<b)
    (h : (S.activityEligible s b).Nonempty) : S.activitySize s (S.activityNext s b h) ≤ b+1 := by
  have hs := (S.activityNext_spec s b h).1
  let j : Fin T := ⟨(S.activityNext s b h).val-1,by have:=(S.activityNext s b h).isLt;omega⟩
  have hj : j.succ=S.activityNext s b h := by apply Fin.ext;dsimp [j];omega
  have hsj : s ≤ j.castSucc := by change s.val ≤ (S.activityNext s b h).val-1;exact Nat.le_sub_one_of_lt hs
  have hprev := S.before_activityNext s hb h hsj (by rw [←hj];exact Fin.castSucc_lt_succ)
  have hstep := S.intervalActivity_step_card j hsj
  rw [←S.activitySize_eq,←S.activitySize_eq,hj] at hstep
  omega

structure States.ActivityGreedy (S : @States n T k P) (s : Fin (T+1)) (b : ℕ) where
  count : ℕ
  index : Fin (count+1) → Fin (T+1)
  first : index 0=s
  increasing : StrictMono index
  lower : ∀ j : Fin count, b ≤ S.activitySize (index j.castSucc) (index j.succ)
  upper : ∀ j : Fin count, S.activitySize (index j.castSucc) (index j.succ) ≤ b+1
  tail : S.activitySize (index (Fin.last count)) (Fin.last T)<b

noncomputable def States.activityGreedy (S : @States n T k P) (s : Fin (T+1)) (b : ℕ) (hb : 0<b) :
    S.ActivityGreedy s b := by
  classical
  by_cases h : (S.activityEligible s b).Nonempty
  · let t := S.activityNext s b h
    have ht : s<t := (S.activityNext_spec s b h).1
    let Q := S.activityGreedy t b hb
    refine ⟨Q.count+1,Fin.cons s Q.index,by simp,?_,?_,?_,?_⟩
    · apply Fin.strictMono_cons.mpr
      refine ⟨?_,Q.increasing⟩
      intro j
      exact ht.trans_le (by simpa only [Q.first] using Q.increasing.monotone (Fin.zero_le j))
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.castSucc_zero,Fin.cons_zero,Fin.cons_succ,Q.first] using (S.activityNext_spec s b h).2
      · simpa only [Fin.castSucc_succ,Fin.cons_succ] using Q.lower j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.castSucc_zero,Fin.cons_zero,Fin.cons_succ,Q.first] using S.activityNext_bound s hb h
      · simpa only [Fin.castSucc_succ,Fin.cons_succ] using Q.upper j
    · simpa only [Fin.cons_last] using Q.tail
  · refine ⟨0,fun _ => s,rfl,?_,(fun j => Fin.elim0 j),(fun j => Fin.elim0 j),?_⟩
    · intro i j hij
      exact False.elim (by have:=i.isLt;have:=j.isLt;change i.val<j.val at hij;omega)
    ·
      by_cases he : s=Fin.last T
      · subst s;simpa only [S.activitySize_self] using hb
      · by_contra hn
        exact h ⟨Fin.last T,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_of_le_of_ne (Fin.le_last _) he,le_of_not_gt hn⟩⟩
termination_by T-s.val
decreasing_by
  have ht := (S.activityNext_spec s b h).1
  change s.val<(S.activityNext s b h).val at ht
  omega

noncomputable def States.ActivityGreedy.intervals (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (Q : S.ActivityGreedy s b) : Finset (Fin (T+1) × Fin (T+1)) :=
  Finset.univ.image (fun j : Fin Q.count => (Q.index j.castSucc,Q.index j.succ))

lemma States.ActivityGreedy.intervals_card (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (Q : S.ActivityGreedy s b) : (Q.intervals S).card=Q.count := by
  classical
  rw [States.ActivityGreedy.intervals,Finset.card_image_of_injective,Finset.card_univ,Fintype.card_fin]
  intro i j he
  exact Fin.castSucc_inj.mp (Q.increasing.injective (congrArg Prod.fst he))

lemma States.ActivityGreedy.intervals_data (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (Q : S.ActivityGreedy s b) : StepDisjoint (Q.intervals S) ∧
      ∀ p ∈ Q.intervals S, p.1 ≤ p.2 ∧ b ≤ S.activitySize p.1 p.2 := by
  constructor
  · intro p hp q hq hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
    have hij : i≠j := by intro h;subst j;exact hne rfl
    rcases lt_or_gt_of_ne hij with h | h
    · have he : Q.index i.succ ≤ Q.index j.castSucc := Q.increasing.monotone (by change i.val+1 ≤ j.val;omega)
      exact Set.disjoint_left.mpr (fun _ hi hj => not_lt_of_ge (hi.2.trans he) hj.1)
    · have he : Q.index j.succ ≤ Q.index i.castSucc := Q.increasing.monotone (by change j.val+1 ≤ i.val;omega)
      exact Set.disjoint_left.mpr (fun _ hi hj => not_lt_of_ge (hj.2.trans he) hi.1)
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨Q.increasing.monotone (Fin.castSucc_le_succ i),Q.lower i⟩

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep
open Set

lemma continuous_lt_iff_of_no_eq {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {s t : ℝ} (hst : s≤t) (hne : ∀ u∈Icc s t, f u≠g u) : f s<g s ↔ f t<g t := by
  constructor
  · intro hs
    by_contra ht
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc hst (hf.sub hg).continuousOn
      (show (0:ℝ)∈Icc (f s-g s) (f t-g t) from ⟨sub_nonpos.mpr hs.le,sub_nonneg.mpr (le_of_not_gt ht)⟩)
    exact hne u hu (sub_eq_zero.mp he)
  · intro ht
    by_contra hs
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc' hst (hf.sub hg).continuousOn
      (show (0:ℝ)∈Icc (f t-g t) (f s-g s) from ⟨sub_nonpos.mpr ht.le,sub_nonneg.mpr (le_of_not_gt hs)⟩)
    exact hne u hu (sub_eq_zero.mp he)

lemma projection_eq_iff_slope {p q : Point} (hx : p.1≠q.1) {s : ℝ} :
    projection s p=projection s q ↔ s=slope p q := by
  rw [slope,eq_div_iff (sub_ne_zero.mpr hx.symm)]
  unfold projection
  constructor <;> intro h <;> linarith

lemma tied_projection (p q : Point) (hx : p.1≠q.1) :
    projection (slope p q) p=projection (slope p q) q :=
  (projection_eq_iff_slope hx).mpr rfl

variable {n : ℕ} {P : Fin n → Point}

lemma Traversal.cut_bounds (T : Traversal (criticalSlopes P)) (i : Fin T.size) :
    T.sample i.castSucc<T.cut i.succ.castSucc ∧ T.cut i.succ.castSucc<T.sample i.succ := by
  exact ⟨by simpa only [Fin.castSucc_succ] using (T.sample_bounds i.castSucc).2,
    (T.sample_bounds i.succ).1⟩

lemma Traversal.projection_ne_between (T : Traversal (criticalSlopes P)) (hP : Generic P)
    (i : Fin T.size) {a b : Fin n}
    (hne : projection (T.cut i.succ.castSucc) (P a)≠projection (T.cut i.succ.castSucc) (P b)) :
    ∀ u∈Icc (T.sample i.castSucc) (T.sample i.succ), projection u (P a)≠projection u (P b) := by
  have hab : a≠b := fun h => hne (by rw [h])
  intro u hu he
  have hs := (projection_eq_iff_slope (hP.2.1 a b hab)).mp he
  have hmem : u∈criticalSlopes P := hs ▸ mem_criticalSlopes P hab
  have hl : T.sample i.castSucc<u := lt_of_le_of_ne hu.1 (fun h => T.sample_not_mem _ (h ▸ hmem))
  have hr : u<T.sample i.succ := lt_of_le_of_ne hu.2 (fun h => T.sample_not_mem _ (h ▸ hmem))
  have hc := T.unique_critical i hmem hl hr
  exact hne (hc ▸ he)

lemma Traversal.comparison_cut (T : Traversal (criticalSlopes P)) (hP : Generic P)
    (i : Fin T.size) {a b : Fin n}
    (hne : projection (T.cut i.succ.castSucc) (P a)≠projection (T.cut i.succ.castSucc) (P b)) :
    (projection (T.sample i.castSucc) (P a)<projection (T.sample i.castSucc) (P b) ↔
      projection (T.cut i.succ.castSucc) (P a)<projection (T.cut i.succ.castSucc) (P b)) ∧
    (projection (T.sample i.succ) (P a)<projection (T.sample i.succ) (P b) ↔
      projection (T.cut i.succ.castSucc) (P a)<projection (T.cut i.succ.castSucc) (P b)) := by
  have ha : Continuous (fun s => projection s (P a)) := by unfold projection;fun_prop
  have hb : Continuous (fun s => projection s (P b)) := by unfold projection;fun_prop
  have hc := T.cut_bounds i
  have hn := T.projection_ne_between hP i hne
  exact ⟨continuous_lt_iff_of_no_eq ha hb hc.1.le
    (fun u hu => hn u ⟨hu.1,hu.2.trans hc.2.le⟩),
    (continuous_lt_iff_of_no_eq ha hb hc.2.le
      (fun u hu => hn u ⟨hc.1.le.trans hu.1,hu.2⟩)).symm⟩

lemma projection_ne_at_pair (hP : GeneralPosition P) {a b l : Fin n}
    (hab : a≠b) (hla : l≠a) (hlb : l≠b) (hxa : (P a).1≠(P b).1) :
    projection (slope (P a) (P b)) (P l)≠projection (slope (P a) (P b)) (P a) := by
  intro h
  apply hP.2 a b l hab hlb.symm hla.symm
  have he := (div_mul_cancel₀ ((P b).2-(P a).2) (sub_ne_zero.mpr hxa.symm))
  change slope (P a) (P b)*((P b).1-(P a).1)=(P b).2-(P a).2 at he
  unfold projection at h
  have hl : (P l).2-(P a).2=slope (P a) (P b)*((P l).1-(P a).1) := by linarith
  unfold orient
  rw [hl,← he]
  ring

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep
open Set

def Refines {n : ℕ} (P : Fin n → Point) (c s : ℝ) : Prop :=
  ∀ i j, projection c (P i)<projection c (P j) → projection s (P i)<projection s (P j)

lemma Traversal.sample_refines {n : ℕ} {P : Fin n → Point}
    (T : Traversal (criticalSlopes P)) (hP : Generic P) (i : Fin T.size) :
    Refines P (T.cut i.succ.castSucc) (T.sample i.castSucc) ∧
    Refines P (T.cut i.succ.castSucc) (T.sample i.succ) := by
  constructor <;> intro a b hab
  · exact (T.comparison_cut hP i (ne_of_lt hab)).1.mpr hab
  · exact (T.comparison_cut hP i (ne_of_lt hab)).2.mpr hab

noncomputable def belowSet {n : ℕ} (P : Fin n → Point) (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun l => projection (slope (P a) (P b)) (P l)<projection (slope (P a) (P b)) (P a))

lemma mem_belowSet {n : ℕ} (P : Fin n → Point) (a b l : Fin n) :
    l∈belowSet P a b ↔ projection (slope (P a) (P b)) (P l)<projection (slope (P a) (P b)) (P a) := by
  classical
  simp only [belowSet,Finset.mem_filter,Finset.mem_univ,true_and]

lemma card_belowSet {n : ℕ} (P : Fin n → Point) (a b : Fin n) :
    (belowSet P a b).card=belowCount P a b := rfl

lemma belowSet_eq_erase {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {s : ℝ} {M : Finset (Fin n)} (hM : Separates P s M) {a b : Fin n}
    (ha : a∈M) (hb : b∉M) (hx : (P a).1≠(P b).1)
    (hR : Refines P (slope (P a) (P b)) s) : belowSet P a b=M.erase a := by
  classical
  have hab : a≠b := fun h => hb (h ▸ ha)
  have ht := tied_projection (P a) (P b) hx
  ext l
  rw [mem_belowSet,Finset.mem_erase]
  constructor
  · intro hl
    have hla : l≠a := by intro he;subst l;exact lt_irrefl _ hl
    refine ⟨hla,?_⟩
    by_contra hn
    exact not_lt_of_gt (hM a ha l hn) (hR l a hl)
  · rintro ⟨hla,hl⟩
    have hlb : l≠b := fun he => hb (he ▸ hl)
    have hne := projection_ne_at_pair hP hab hla hlb hx
    by_contra hn
    have hgt := lt_of_le_of_ne (le_of_not_gt hn) hne.symm
    rw [ht] at hgt
    exact not_lt_of_gt (hM l hl b hb) (hR b l hgt)

lemma below_insert_separates {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {s : ℝ} {a b : Fin n} (hab : a≠b) (hx : (P a).1≠(P b).1)
    (hR : Refines P (slope (P a) (P b)) s)
    (hs : projection s (P a)<projection s (P b)) :
    Separates P s (insert a (belowSet P a b)) := by
  classical
  intro l hl m hm
  have hma : m≠a := by intro he;subst m;exact hm (Finset.mem_insert_self _ _)
  have hmB : m∉belowSet P a b := fun hh => hm (Finset.mem_insert_of_mem hh)
  have hcm : projection (slope (P a) (P b)) (P a)≤projection (slope (P a) (P b)) (P m) :=
    le_of_not_gt (fun hh => hmB ((mem_belowSet P a b m).mpr hh))
  rcases Finset.mem_insert.mp hl with he | hl
  · subst l
    by_cases hmb : m=b
    · simpa only [hmb] using hs
    · exact hR a m (lt_of_le_of_ne hcm (projection_ne_at_pair hP hab hma hmb hx).symm)
  · exact hR l m (((mem_belowSet P a b l).mp hl).trans_le hcm)

lemma projection_order_at_slope {p q : Point} (hx : p.1<q.1) {s t : ℝ}
    (hs : s<slope p q) (ht : slope p q<t) :
    projection s p<projection s q ∧ projection t q<projection t p := by
  have hdx : 0<q.1-p.1 := sub_pos.mpr hx
  have hs' := (lt_div_iff₀ hdx).mp hs
  have ht' := (div_lt_iff₀ hdx).mp ht
  unfold projection
  constructor <;> nlinarith

lemma belowSet_symm {n : ℕ} {P : Fin n → Point} {a b : Fin n} (hx : (P a).1≠(P b).1) :
    belowSet P b a=belowSet P a b := by
  classical
  ext l
  simp only [mem_belowSet,slope_symm (P b) (P a),tied_projection (P a) (P b) hx]

lemma belowCount_symm {n : ℕ} {P : Fin n → Point} {a b : Fin n} (hx : (P a).1≠(P b).1) :
    belowCount P b a=belowCount P a b := congrArg Finset.card (belowSet_symm hx)

end PlanarHalving.Sweep

end OAI
