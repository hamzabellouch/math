import OAI.Combinatorics.HalvingLines.RankMeasures

namespace OAI

open Filter Topology

namespace PlanarHalving.Sweep
open Set

noncomputable def setDistance {n : ℕ} (M N : Finset (Fin n)) : ℕ := (M\N).card

lemma setDistance_self {n : ℕ} (M : Finset (Fin n)) : setDistance M M=0 := by
  simp [setDistance]

lemma setDistance_comm {n : ℕ} {M N : Finset (Fin n)} (hc : M.card=N.card) :
    setDistance M N=setDistance N M := Finset.card_sdiff_comm hc

lemma setDistance_triangle {n : ℕ} (M N K : Finset (Fin n)) :
    setDistance M K ≤ setDistance M N+setDistance N K := by
  classical
  apply (Finset.card_le_card (show M\K ⊆ (M\N)∪(N\K) from ?_)).trans
    (Finset.card_union_le _ _)
  intro x hx
  by_cases hxN : x∈N
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxN,(Finset.mem_sdiff.mp hx).2⟩)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,hxN⟩)

structure States {n T k : ℕ} (P : Fin n → Point) where
  slope : Fin (T+1) → ℝ
  increasing : StrictMono slope
  marks : Fin (T+1) → Finset (Fin n)
  card_marks : ∀ i, (marks i).card=k
  separates : ∀ i, Separates P (slope i) (marks i)
  step : ∀ i : Fin T, setDistance (marks i.castSucc) (marks i.succ) ≤ 1

variable {n T k a : ℕ} {P : Fin n → Point}

noncomputable def States.distance (S : @States n T k P) (s t : Fin (T+1)) : ℕ :=
  setDistance (S.marks s) (S.marks t)

lemma States.distance_self (S : @States n T k P) (s : Fin (T+1)) : S.distance s s=0 :=
  setDistance_self _

lemma States.distance_comm (S : @States n T k P) (s t : Fin (T+1)) : S.distance s t=S.distance t s :=
  setDistance_comm (by rw [S.card_marks,S.card_marks])

lemma States.distance_triangle (S : @States n T k P) (s t u : Fin (T+1)) :
    S.distance s u ≤ S.distance s t+S.distance t u := setDistance_triangle _ _ _

noncomputable def States.eligible (S : @States n T k P) (s : Fin (T+1)) (a : ℕ) : Finset (Fin (T+1)) :=
  Finset.univ.filter (fun t => s<t ∧ a ≤ S.distance s t)

noncomputable def States.next (S : @States n T k P) (s : Fin (T+1)) (a : ℕ)
    (h : (S.eligible s a).Nonempty) : Fin (T+1) := (S.eligible s a).min' h

lemma States.next_spec (S : @States n T k P) (s : Fin (T+1)) (a : ℕ)
    (h : (S.eligible s a).Nonempty) : s<S.next s a h ∧ a≤S.distance s (S.next s a h) := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2

lemma States.before_next (S : @States n T k P) (s : Fin (T+1)) {a : ℕ} (ha : 0<a)
    (h : (S.eligible s a).Nonempty) {t : Fin (T+1)} (hst : s≤t) (ht : t<S.next s a h) :
    S.distance s t<a := by
  by_cases he : t=s
  · subst t; simpa only [S.distance_self] using ha
  by_contra hh
  have hmem : t∈S.eligible s a := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,lt_of_le_of_ne hst (Ne.symm he),le_of_not_gt hh⟩
  exact not_le_of_gt ht (Finset.min'_le _ _ hmem)

lemma States.next_distance (S : @States n T k P) (s : Fin (T+1)) {a : ℕ} (ha : 0<a)
    (h : (S.eligible s a).Nonempty) : S.distance s (S.next s a h)=a := by
  have hs := (S.next_spec s a h).1
  let b : Fin T := ⟨(S.next s a h).val-1,by have hn:=(S.next s a h).isLt; exact Nat.sub_lt_right_of_lt_add (by omega) (by omega)⟩
  have hb : b.succ=S.next s a h := by apply Fin.ext; dsimp [b]; omega
  have hb0 : s≤b.castSucc := by change s.val≤(S.next s a h).val-1; exact Nat.le_sub_one_of_lt hs
  have hb1 : b.castSucc<S.next s a h := by rw [← hb]; exact Fin.castSucc_lt_succ
  have hprev := S.before_next s ha h hb0 hb1
  have hjump := S.distance_triangle s b.castSucc b.succ
  have hstep := S.step b
  change S.distance b.castSucc b.succ≤1 at hstep
  rw [hb] at hjump hstep
  exact Nat.le_antisymm (by omega) (S.next_spec s a h).2

structure States.Greedy (S : @States n T k P) (s : Fin (T+1)) (a : ℕ) where
  count : ℕ
  index : Fin (count+1) → Fin (T+1)
  first : index 0=s
  increasing : StrictMono index
  distance : ∀ j : Fin count, S.distance (index j.castSucc) (index j.succ)=a
  hit : ∀ u v, s≤u → u≤v → 2*a-1≤S.distance u v →
    ∃ j : Fin count, u < index j.succ ∧ index j.succ ≤ v

lemma States.no_eligible_distance (S : @States n T k P) (s : Fin (T+1)) {a : ℕ} (ha : 0<a)
    (h : ¬(S.eligible s a).Nonempty) {t : Fin (T+1)} (hst : s≤t) : S.distance s t<a := by
  by_cases he : t=s
  · subst t; simpa only [S.distance_self] using ha
  by_contra hh
  exact h ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_le_of_ne hst (Ne.symm he),le_of_not_gt hh⟩⟩

lemma States.close_distance (S : @States n T k P) (s u v : Fin (T+1)) {a : ℕ}
    (ha : 0<a) (hu : S.distance s u<a) (hv : S.distance s v<a) : S.distance u v<2*a-1 := by
  have ht := S.distance_triangle u s v
  rw [S.distance_comm u s] at ht
  omega

noncomputable def States.greedy (S : @States n T k P) (s : Fin (T+1)) (a : ℕ) (ha : 0<a) :
    S.Greedy s a := by
  classical
  by_cases h : (S.eligible s a).Nonempty
  · let t := S.next s a h
    have ht : s<t := (S.next_spec s a h).1
    let Q := S.greedy t a ha
    refine ⟨Q.count+1,Fin.cons s Q.index,by simp,?_,?_,?_⟩
    · apply Fin.strictMono_cons.mpr
      refine ⟨?_,Q.increasing⟩
      intro j
      exact ht.trans_le (by simpa only [Q.first] using Q.increasing.monotone (Fin.zero_le j))
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.castSucc_zero,Fin.cons_zero,Fin.cons_succ,Q.first] using S.next_distance s ha h
      · simpa only [Fin.castSucc_succ,Fin.cons_succ] using Q.distance j
    · intro u v hsu huv hd
      by_cases htu : t≤u
      · obtain ⟨j,hj⟩ := Q.hit u v htu huv hd
        refine ⟨j.succ,?_⟩
        simpa only [Fin.cons_succ] using hj
      · have hut : u<t := lt_of_not_ge htu
        by_cases htv : t≤v
        · refine ⟨0,?_⟩
          simpa only [Fin.cons_succ,Q.first] using And.intro hut htv
        · have hv := S.before_next s ha h (hsu.trans huv) (lt_of_not_ge htv)
          have hu := S.before_next s ha h hsu hut
          exact False.elim (not_lt_of_ge hd (S.close_distance s u v ha hu hv))
  · refine ⟨0,fun _ => s,rfl,?_,?_,?_⟩
    · intro i j hij
      exact False.elim (by have hi:=i.isLt; have hj:=j.isLt; change i.val<j.val at hij; omega)
    · intro j; exact Fin.elim0 j
    · intro u v hsu huv hd
      exact False.elim (not_lt_of_ge hd (S.close_distance s u v ha
        (S.no_eligible_distance s ha h hsu) (S.no_eligible_distance s ha h (hsu.trans huv))))
termination_by T-s.val
decreasing_by
  have ht := (S.next_spec s a h).1
  change s.val<(S.next s a h).val at ht
  omega

noncomputable def States.greedySystem (S : @States n T k P) (a : ℕ) (ha : 0<a) :
    @Batches.System n (S.greedy 0 a ha).count k a P where
  slope := fun j => S.slope ((S.greedy 0 a ha).index j)
  increasing := S.increasing.comp (S.greedy 0 a ha).increasing
  marks := fun j => S.marks ((S.greedy 0 a ha).index j)
  card_marks := fun _j => S.card_marks _
  separates := fun _j => S.separates _
  distance := (S.greedy 0 a ha).distance

end PlanarHalving.Sweep
namespace PlanarHalving.Sweep
open Set

lemma slope_symm (p q : Point) : slope p q=slope q p := by
  unfold slope
  rw [← neg_sub q.2 p.2,← neg_sub q.1 p.1,neg_div_neg_eq]

noncomputable def criticalSlopes {n : ℕ} (P : Fin n → Point) : Finset ℝ :=
  (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1≠ij.2)).image
    (fun ij => slope (P ij.1) (P ij.2))

lemma mem_criticalSlopes {n : ℕ} (P : Fin n → Point) {i j : Fin n} (hij : i≠j) :
    slope (P i) (P j)∈criticalSlopes P := by
  classical
  exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩,rfl⟩

lemma projection_injective {n : ℕ} {P : Fin n → Point} (hx : Function.Injective (fun i => (P i).1))
    {s : ℝ} (hs : s∉criticalSlopes P) : Function.Injective (fun i => projection s (P i)) := by
  intro i j hij
  by_contra hn
  apply hs
  have hd : (P j).1-(P i).1≠0 := sub_ne_zero.mpr (fun h => hn (hx h.symm))
  have he : s=slope (P i) (P j) := by
    apply (eq_div_iff hd).mpr
    unfold projection at hij
    linarith
  rw [he]
  exact mem_criticalSlopes P hn

structure Traversal (C : Finset ℝ) where
  size : ℕ
  cut : Fin (size+2) → ℝ
  increasing : StrictMono cut
  critical : ∀ c, c∈C ↔ ∃ j : Fin size, cut j.succ.castSucc=c

lemma strictMono_snoc {m : ℕ} {f : Fin m → ℝ} {b : ℝ}
    (hf : StrictMono f) (hb : ∀ j, f j < b) : StrictMono (Fin.snoc f b) := by
  intro i j hij
  revert hij
  refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij
    have hi : i≠Fin.last m := ne_of_lt hij
    obtain ⟨i,rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    simpa only [Fin.snoc_castSucc,Fin.snoc_last] using hb i
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hij
      exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
    · intro hij
      simpa only [Fin.snoc_castSucc] using hf (Fin.castSucc_lt_castSucc_iff.mp hij)

noncomputable def traversal (C : Finset ℝ) : Traversal C := by
  classical
  let m := C.card
  let e := C.orderIsoOfFin rfl
  let lo := Classical.choose (C.finite_toSet.bddBelow.exists_le 0)
  have hlo := (Classical.choose_spec (C.finite_toSet.bddBelow.exists_le 0)).2
  let hi := Classical.choose (C.finite_toSet.bddAbove.exists_ge 0)
  have hhi := (Classical.choose_spec (C.finite_toSet.bddAbove.exists_ge 0)).2
  let upper := max lo hi
  have hup : ∀ c∈C, c≤upper := fun _ hc => (hhi _ hc).trans (le_max_right _ _)
  let f : Fin m → ℝ := fun j => (e j : ℝ)
  have hf : StrictMono f := fun i j hij => e.strictMono hij
  refine ⟨m,Fin.cons (lo-1) (Fin.snoc f (upper+1)),?_,?_⟩
  · apply Fin.strictMono_cons.mpr
    refine ⟨?_,strictMono_snoc hf ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.snoc_last]
        have hle : lo≤upper := le_max_left _ _
        linarith
      · simpa only [Fin.snoc_castSucc] using lt_of_lt_of_le (sub_lt_self lo (by norm_num : (0:ℝ) < 1)) (hlo _ (e i).property)
    · intro i
      exact lt_of_le_of_lt (hup _ (e i).property) (lt_add_one upper)
  · intro c
    constructor
    · intro hc
      refine ⟨e.symm ⟨c,hc⟩,?_⟩
      simpa only [Fin.castSucc_succ,Fin.cons_succ,Fin.snoc_castSucc,f] using
        congrArg Subtype.val (e.apply_symm_apply ⟨c,hc⟩)
    · rintro ⟨j,rfl⟩
      simpa only [Fin.castSucc_succ,Fin.cons_succ,Fin.snoc_castSucc,f] using (e j).property

variable {C : Finset ℝ}

noncomputable def Traversal.sample (T : Traversal C) (i : Fin (T.size+1)) : ℝ :=
  (T.cut i.castSucc+T.cut i.succ)/2

lemma Traversal.sample_bounds (T : Traversal C) (i : Fin (T.size+1)) :
    T.cut i.castSucc < T.sample i ∧ T.sample i < T.cut i.succ := by
  have h := T.increasing (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
  dsimp [Traversal.sample]
  constructor  <;> linarith

lemma Traversal.sample_increasing (T : Traversal C) : StrictMono T.sample := by
  intro i j hij
  have hc : i.succ≤j.castSucc := by change i.val+1≤j.val; exact Nat.succ_le_of_lt hij
  exact (T.sample_bounds i).2.trans_le (T.increasing.monotone hc) |>.trans (T.sample_bounds j).1

lemma Traversal.sample_not_mem (T : Traversal C) (i : Fin (T.size+1)) : T.sample i∉C := by
  intro h
  obtain ⟨j,hj⟩ := (T.critical _).mp h
  have hl := (T.sample_bounds i).1
  have hu := (T.sample_bounds i).2
  rw [← hj] at hl hu
  have hl' := T.increasing.lt_iff_lt.mp hl
  have hu' := T.increasing.lt_iff_lt.mp hu
  change i.val < j.val+1 at hl'
  change j.val+1 < i.val+1 at hu'
  omega

lemma Traversal.unique_critical (T : Traversal C) (i : Fin T.size) {c : ℝ} (hc : c∈C)
    (hl : T.sample i.castSucc < c) (hu : c < T.sample i.succ) : c=T.cut i.succ.castSucc := by
  obtain ⟨j,hj⟩ := (T.critical _).mp hc
  have hl' := (T.sample_bounds i.castSucc).1.trans hl
  have hu' := hu.trans (T.sample_bounds i.succ).2
  rw [← hj] at hl' hu'
  have hl'' := T.increasing.lt_iff_lt.mp hl'
  have hu'' := T.increasing.lt_iff_lt.mp hu'
  have he : j=i := by
    apply Fin.ext
    change i.val < j.val+1 at hl''
    change j.val+1 < i.val+1+1 at hu''
    omega
  simpa only [he] using hj.symm

lemma separates_step_distance {n k : ℕ} {P : Fin n → Point} (hP : Generic P)
    {s t : ℝ} (hst : s≤t) {M N : Finset (Fin n)} (hM : M.card=k) (hN : N.card=k)
    (hs : Separates P s M) (ht : Separates P t N)
    (hone : ∀ c∈criticalSlopes P, ∀ d∈criticalSlopes P,
      s < c → c < t → s < d → d < t → c=d) : setDistance M N≤1 := by
  classical
  rw [setDistance,Finset.card_le_one]
  intro i hi u hu
  have hne : (N\M).Nonempty := by
    have he := Finset.card_sdiff_comm (hM.trans hN.symm)
    have hp := Finset.card_pos.mpr (⟨i,hi⟩ : (M\N).Nonempty)
    rw [he] at hp
    exact Finset.card_pos.mp hp
  obtain ⟨j,hj⟩ := hne
  have hiJ : i≠j := by intro he; subst j; exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_sdiff.mp hi).1
  have huJ : u≠j := by intro he; subst j; exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_sdiff.mp hu).1
  have hsi := exchange_slope_between hst hs ht hi hj
  have hsu := exchange_slope_between hst hs ht hu hj
  have he := hone _ (mem_criticalSlopes P hiJ) _ (mem_criticalSlopes P huJ) hsi.1 hsi.2 hsu.1 hsu.2
  rw [slope_symm (P i) (P j),slope_symm (P u) (P j)] at he
  exact PlaneGraph.slope_eq_implies_eq_ne hP.1
    (hP.2.1 j i hiJ.symm) (hP.2.1 j u huJ.symm) he

noncomputable def states {n k : ℕ} (P : Fin n → Point) (hP : Generic P) (hk : k≤n) :
    @States n (traversal (criticalSlopes P)).size k P := by
  let T := traversal (criticalSlopes P)
  have hex (i : Fin (T.size+1)) := exists_state P (T.sample i) hk
    (projection_injective (PlaneGraph.Generic.x_injective hP) (T.sample_not_mem i))
  choose M hM hsep using hex
  refine ⟨T.sample,T.sample_increasing,M,hM,hsep,?_⟩
  intro i
  apply separates_step_distance hP (T.sample_increasing.monotone (Fin.castSucc_le_succ i)) (hM _) (hM _) (hsep _) (hsep _)
  intro c hc d hd hcs hct hds hdt
  exact (T.unique_critical i hc hcs hct).trans (T.unique_critical i hd hds hdt).symm

end PlanarHalving.Sweep
namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

def StepDisjoint (C : Finset (Fin (T+1) × Fin (T+1))) : Prop :=
  ∀ p∈C, ∀ q∈C, p≠q → Disjoint (Ioc p.1 p.2) (Ioc q.1 q.2)

lemma States.Greedy.packing (S : @States n T k P) {a : ℕ}
    (Q : S.Greedy 0 a) (C : Finset (Fin (T+1) × Fin (T+1)))
    (hC : StepDisjoint C) (horder : ∀ p∈C, p.1≤p.2)
    (hd : ∀ p∈C, 2*a-1≤S.distance p.1 p.2) : C.card≤Q.count := by
  classical
  have hex (p : ↥C) : ∃ j : Fin Q.count, p.val.1 < Q.index j.succ ∧ Q.index j.succ≤p.val.2 :=
    Q.hit _ _ (Fin.zero_le _) (horder _ p.property) (hd _ p.property)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro p q he
    by_contra hpq
    have hdis := hC _ p.property _ q.property (fun h => hpq (Subtype.ext h))
    exact Set.disjoint_left.mp hdis (hf p) (by simpa only [Set.mem_Ioc,he] using hf q)
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hinj

lemma States.greedy_packing (S : @States n T k P) {d : ℕ} (hd : 0 < d)
    (C : Finset (Fin (T+1) × Fin (T+1))) (hC : StepDisjoint C)
    (horder : ∀ p∈C, p.1≤p.2) (hdist : ∀ p∈C, d≤S.distance p.1 p.2) :
    C.card≤(S.greedy 0 ((d+1)/2) (by omega)).count := by
  apply (S.greedy 0 ((d+1)/2) (by omega)).packing S C hC horder
  intro p hp
  exact (show 2*((d+1)/2)-1≤d by omega).trans (hdist p hp)

lemma States.distance_packing_cubic (S : @States n T k P) (hP : Generic P) [NeZero n]
    {d : ℕ} (hd : 0 < d) (C : Finset (Fin (T+1) × Fin (T+1)))
    (hC : StepDisjoint C) (horder : ∀ p∈C, p.1≤p.2)
    (hdist : ∀ p∈C, d≤S.distance p.1 p.2) :
    (C.card : ℝ)^3*(d : ℝ)^4≤294912*(n : ℝ)^4 := by
  let a := (d+1)/2
  have ha : 0 < a := by dsimp [a]; omega
  let : NeZero a := ⟨ne_of_gt ha⟩
  let Q := S.greedy 0 a ha
  have hcount : C.card≤Q.count := S.greedy_packing hd C hC horder hdist
  have hbound := (S.greedySystem a ha).cubed_bound hP
  have hda : (d : ℝ)≤2*(a : ℝ) := by exact_mod_cast (show d≤2*a by dsimp [a]; omega)
  calc
    _ ≤ (Q.count : ℝ)^3*(2*(a : ℝ))^4 := by gcongr
    _ = 16*((Q.count : ℝ)^3*(a : ℝ)^4) := by ring
    _ ≤ 16*(18432*(n : ℝ)^4) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = _ := by ring

end PlanarHalving.Sweep
namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

noncomputable def States.intervalActivity (S : @States n T k P)
    (u v : Fin (T+1)) (h : u≤v) : Finset (Fin n) :=
  activity (fun i : ↥(Finset.Icc u v) => S.marks i) ⟨u,Finset.mem_Icc.mpr ⟨le_rfl,h⟩⟩

lemma States.mem_intervalActivity (S : @States n T k P)
    {u v : Fin (T+1)} (h : u≤v) {x : Fin n} : x∈S.intervalActivity u v h ↔
    ∃ i, u ≤ i ∧ i ≤ v ∧ ((x∈S.marks i ∧ x∉S.marks u) ∨ (x∉S.marks i ∧ x∈S.marks u)) := by
  classical
  rw [States.intervalActivity,mem_activity]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,(Finset.mem_Icc.mp i.property).1,(Finset.mem_Icc.mp i.property).2,hi⟩
  · rintro ⟨i,hu,hv,hi⟩
    exact ⟨⟨i,Finset.mem_Icc.mpr ⟨hu,hv⟩⟩,hi⟩

lemma States.intervalActivity_pos_distance (S : @States n T k P)
    {u v : Fin (T+1)} (h : u≤v) (ha : 0<(S.intervalActivity u v h).card) :
    1≤S.distance u v := by
  exact activity_pos_distance P (fun i : ↥(Finset.Icc u v) => S.slope i)
    (fun i => S.marks i) ⟨u,Finset.mem_Icc.mpr ⟨le_rfl,h⟩⟩
    ⟨v,Finset.mem_Icc.mpr ⟨h,le_rfl⟩⟩ (fun i => S.card_marks i)
    (fun i => S.separates i) (fun i => S.increasing.monotone (Finset.mem_Icc.mp i.property).1)
    (fun i => S.increasing.monotone (Finset.mem_Icc.mp i.property).2) ha

lemma states_intervalActivity_distance {n k : ℕ} (P : Fin n → Point) (hP : Generic P) (hk : k≤n)
    {c : ℕ} {u v : Fin ((traversal (criticalSlopes P)).size+1)} (huv : u≤v)
    (hc : 4*c≤((states P hP hk).intervalActivity u v huv).card) :
    (∃ hk' : k+c≤n, c≤(states P hP hk').distance u v) ∨
    (∃ hk' : k-c≤n, c≤k ∧ c≤(states P hP hk').distance u v) := by
  let S := states P hP hk
  have hi (i) : Function.Injective (fun x => projection (S.slope i) (P x)) :=
    projection_injective (PlaneGraph.Generic.x_injective hP) ((traversal _).sample_not_mem i)
  have hd := activity_distance P (fun i : ↥(Finset.Icc u v) => S.slope i)
    (fun i => S.marks i) ⟨u,Finset.mem_Icc.mpr ⟨le_rfl,huv⟩⟩
    ⟨v,Finset.mem_Icc.mpr ⟨huv,le_rfl⟩⟩ (fun i => S.card_marks i)
    (fun i => S.separates i) (fun i => S.increasing.monotone (Finset.mem_Icc.mp i.property).1)
    (fun i => S.increasing.monotone (Finset.mem_Icc.mp i.property).2) (hi u) (hi v) hc
  rcases hd with ⟨hk',E,E',hE,hE',hs,hs',hd⟩ | ⟨hck,E,E',hE,hE',hs,hs',hd⟩
  · left
    refine ⟨hk',?_⟩
    have he : E=(states P hP hk').marks u := states_unique hs (states P hP hk' |>.separates u) (hE.trans (states P hP hk' |>.card_marks u).symm)
    have he' : E'=(states P hP hk').marks v := states_unique hs' (states P hP hk' |>.separates v) (hE'.trans (states P hP hk' |>.card_marks v).symm)
    simpa only [he,he',States.distance,setDistance] using hd
  · right
    have hk' : k-c≤n := (Nat.sub_le _ _).trans hk
    refine ⟨hk',hck,?_⟩
    have he : E=(states P hP hk').marks u := states_unique hs (states P hP hk' |>.separates u) (hE.trans (states P hP hk' |>.card_marks u).symm)
    have he' : E'=(states P hP hk').marks v := states_unique hs' (states P hP hk' |>.separates v) (hE'.trans (states P hP hk' |>.card_marks v).symm)
    simpa only [he,he',States.distance,setDistance] using hd

lemma cube_add_le {x y : ℝ} (hx : 0≤x) (hy : 0≤y) : (x+y)^3≤4*(x^3+y^3) := by
  nlinarith [mul_nonneg (sq_nonneg (x-y)) (add_nonneg hx hy)]

lemma activity_packing_cubic {n k : ℕ} (P : Fin n → Point) (hP : Generic P)
    [NeZero n] (hk : k≤n) {b : ℕ} (hb : 0<b)
    (C : Finset (Fin ((traversal (criticalSlopes P)).size+1) × Fin ((traversal (criticalSlopes P)).size+1)))
    (hC : StepDisjoint C) (horder : ∀ p∈C, p.1≤p.2)
    (hactivity : ∀ p, ∀ hp : p∈C, b≤((states P hP hk).intervalActivity p.1 p.2 (horder p hp)).card) :
    (C.card : ℝ)^3*(b : ℝ)^4≤10000000000*(n : ℝ)^4 := by
  classical
  let S := states P hP hk
  by_cases hb4 : 4≤b
  · let c := b/4
    have hc : 0<c := by dsimp [c]; omega
    have hbLe : (b : ℝ)≤8*(c : ℝ) := by exact_mod_cast (show b≤8*c by dsimp [c]; omega)
    let A := C.filter (fun p => ∃ hk' : k+c≤n, c≤(states P hP hk').distance p.1 p.2)
    let B := C\A
    have hA : A⊆C := Finset.filter_subset _ _
    have hB : B⊆C := Finset.sdiff_subset
    have hbound (D : Finset _) (hD : D⊆C) (r : ℕ)
        (hd : ∀ p∈D, ∃ hr : r≤n, c≤(states P hP hr).distance p.1 p.2) :
        (D.card : ℝ)^3*(c : ℝ)^4≤294912*(n : ℝ)^4 := by
      by_cases hne : D.Nonempty
      · obtain ⟨p,hp⟩ := hne
        obtain ⟨hr,_⟩ := hd p hp
        apply (states P hP hr).distance_packing_cubic hP hc D
        · exact fun p hp q hq hpq => hC p (hD hp) q (hD hq) hpq
        · exact fun p hp => horder p (hD hp)
        · intro p hp
          obtain ⟨hr',hh⟩ := hd p hp
          exact hh
      · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero,zero_pow (by omega : (3:ℕ)≠0),zero_mul]
        positivity
    have hAb := hbound A hA (k+c) (fun p hp => (Finset.mem_filter.mp hp).2)
    have hBb := hbound B hB (k-c) (fun p hp => by
      have hpC := hB hp
      have hh := states_intervalActivity_distance P hP hk (horder p hpC)
        ((show 4*c≤b from Nat.mul_div_le b 4).trans (hactivity p hpC))
      rcases hh with hh | ⟨hr,_,hh⟩
      · exact False.elim ((Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨hpC,hh⟩))
      · exact ⟨hr,hh⟩)
    have hcard : (C.card : ℝ)=(A.card : ℝ)+(B.card : ℝ) := by
      exact_mod_cast (by simpa only [B,Nat.add_comm] using (Finset.card_sdiff_add_card_eq_card hA).symm : C.card=A.card+B.card)
    have hsum := mul_le_mul_of_nonneg_right (cube_add_le (show (0:ℝ)≤A.card by positivity) (show (0:ℝ)≤B.card by positivity)) (show (0:ℝ)≤(c : ℝ)^4 by positivity)
    rw [← hcard] at hsum
    have hcub : (C.card : ℝ)^3*(c : ℝ)^4≤2359296*(n : ℝ)^4 := by nlinarith [hAb,hBb]
    calc
      _ ≤ (C.card : ℝ)^3*(8*(c : ℝ))^4 := by gcongr
      _ = 4096*((C.card : ℝ)^3*(c : ℝ)^4) := by ring
      _ ≤ 4096*(2359296*(n : ℝ)^4) := mul_le_mul_of_nonneg_left hcub (by norm_num)
      _ ≤ _ := by nlinarith [sq_nonneg ((n : ℝ)^2)]
  · have hd := S.distance_packing_cubic hP (by omega : 0<1) C hC horder
      (fun p hp => S.intervalActivity_pos_distance (horder p hp) (lt_of_lt_of_le hb (hactivity p hp)))
    norm_num at hd
    have hbLe : (b : ℝ)≤3 := by exact_mod_cast (by omega : b≤3)
    calc
      _ ≤ (C.card : ℝ)^3*3^4 := by gcongr
      _ ≤ 294912*(n : ℝ)^4*3^4 := mul_le_mul_of_nonneg_right hd (by norm_num)
      _ ≤ _ := by nlinarith [sq_nonneg ((n : ℝ)^2)]

end PlanarHalving.Sweep

end OAI
