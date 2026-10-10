import OAI.Combinatorics.ListHadwiger.PaletteSampling

namespace OAI

namespace LinearListHadwiger.Assembly
open Filter Real

lemma small_woven_order_cutoff :
    ∀ᶠ t : ℝ in atTop, 2 ≤ t ∧ ∀ s : ℕ,
      1 ≤ s → s ≤ 2*⌈t/(Real.log t)^2⌉₊ →
      (s:ℝ) ≤ t ∧ 100000000*s*Real.log (2*s) < t/8000 := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (2:ℝ)
    (show (0:ℝ)<1 by norm_num)).bound (show (0:ℝ)<1/2 by norm_num)
  have hbig := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (10000000000000:ℝ))
  filter_upwards [eventually_ge_atTop (2:ℝ),hlog,hbig] with t ht hl hb
  have ht0 : 0<t := by linarith
  have hln : 0 < Real.log t := by linarith
  have hl2 : (Real.log t)^2 ≤ t/2 := by
    have hh : (Real.log t)^2 ≤ (1/2:ℝ)*t := by
      rw [←Real.rpow_natCast (Real.log t) 2]
      simpa only [Nat.cast_ofNat,Real.norm_eq_abs,Real.rpow_one,
        abs_of_nonneg (Real.rpow_nonneg hln.le (2:ℝ)),abs_of_pos ht0] using hl
    linarith
  refine ⟨ht,?_⟩
  intro s hs hsc
  have hs0 : (0:ℝ)<s := by exact_mod_cast (by omega : 0<s)
  have hsc' : (s:ℝ)≤2*(⌈t/(Real.log t)^2⌉₊:ℝ) := by exact_mod_cast hsc
  have hceil := Nat.ceil_lt_add_one (div_nonneg ht0.le (sq_nonneg (Real.log t)))
  have hsbound : (s:ℝ)*(Real.log t)^2 ≤ 3*t := by
    have hx : (s:ℝ)<2*(t/(Real.log t)^2+1) := by linarith
    have hm := mul_lt_mul_of_pos_right hx (sq_pos_of_pos hln)
    have he : (t/(Real.log t)^2)*((Real.log t)^2)=t :=
      div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hln))
    nlinarith
  have hst : (s:ℝ)≤t := by
    have hc : (3:ℝ)≤(Real.log t)^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hc hs0.le
    nlinarith
  refine ⟨hst,?_⟩
  have hlogs : Real.log (2*s) ≤ 2*Real.log t := by
    have hh := Real.log_le_log (show (0:ℝ)<2*s by positivity)
      (show (2:ℝ)*s≤2*t by linarith)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) ht0.ne'] at hh
    have htwo := Real.log_le_log (by norm_num : (0:ℝ)<2) ht
    linarith
  have hleft : 100000000*s*Real.log (2*s) ≤ 200000000*((s:ℝ)*Real.log t) := by
    have hh := mul_le_mul_of_nonneg_left hlogs (show (0:ℝ)≤100000000*s by positivity)
    nlinarith
  have hb' : (4800000000000:ℝ)<Real.log t := by linarith
  have hmul := mul_lt_mul_of_pos_left hb' (mul_pos hs0 hln)
  have htail : 200000000*((s:ℝ)*Real.log t)<t/8000 := by nlinarith [hsbound]
  exact hleft.trans_lt htail

end LinearListHadwiger.Assembly

namespace LinearListHadwiger.Assembly
open SimpleGraph Finset
variable {V O I : Type} [Fintype V] [DecidableEq V]
  [Fintype O] [Fintype I] [DecidableEq I]

theorem group_ports (G : SimpleGraph V) [DecidableRel G.Adj]
    (port : O → V) (label : O → I) (hs : Function.Surjective label)
    (hO : 1 ≤ Fintype.card O) (U : Finset V)
    (hN : ∀ o, Fintype.card O ≤ (U.filter (G.Adj (port o))).card)
    (hconn : KConnectedOn G U (65536*Fintype.card O)) :
    ∃ C : I → Set V,
      (∀ i, (G.induce (C i)).Connected) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (∀ i, C i ⊆ (↑U : Set V)) ∧
      ∀ o, ∃ v ∈ C (label o), G.Adj (port o) v := by
  classical
  obtain ⟨nbr,hni,hn⟩ := attach_ports (G := G) port U hN
  let nr : O → (↑U : Set V) := fun o => ⟨nbr o,(hn o).1⟩
  have hnr : Function.Injective nr := fun _ _ he => hni (congrArg Subtype.val he)
  let A : Finset (↑U : Set V) := univ.image nr
  have hAc : A.card = Fintype.card O := by
    rw [card_image_of_injective _ hnr,card_univ]
  have ha (o : O) : nr o ∈ A := mem_image.mpr ⟨o,mem_univ _,rfl⟩
  have hpre : ∀ a : ↥A, ∃ o, nr o = a.val := by
    intro a
    obtain ⟨o,_,ho⟩ := mem_image.mp a.property
    exact ⟨o,ho⟩
  choose idx hidx using hpre
  have hi (o : O) : idx ⟨nr o,ha o⟩ = o := hnr (hidx ⟨nr o,ha o⟩)
  let lab : ↥A → I := fun a => label (idx a)
  have hls : Function.Surjective lab := by
    intro i
    obtain ⟨o,rfl⟩ := hs i
    exact ⟨⟨nr o,ha o⟩,congrArg label (hi o)⟩
  have hc : KConnectedOn (G.induce (↑U : Set V)) univ (65536*A.card) := by
    rw [hAc]
    exact Knitting.induce_connected G U hconn
  obtain ⟨C,hC,hCC,hterm⟩ := Knitting.group_terminals (G.induce (↑U : Set V)) A lab hls
    (by omega) hc
  let M := Knitting.model_induce G U
  let D : I → Set V := fun i => M.expand (C i)
  have hDU : ∀ i, D i ⊆ (↑U : Set V) := by
    intro i v hv
    obtain ⟨w,_,hw⟩ := hv
    have he : v = w.val := hw
    exact he ▸ w.property
  refine ⟨D,fun i => M.expand_connected (hC i),
    fun i j hij => M.expand_disjoint (hCC i j hij),hDU,?_⟩
  intro o
  refine ⟨nbr o,?_,(hn o).2⟩
  refine ⟨nr o,?_,rfl⟩
  have ht := hterm ⟨nr o,ha o⟩
  simpa only [lab,hi] using ht

omit [Fintype V] in

lemma path_in_connected {G : SimpleGraph V} {S : Set V}
    (hS : (G.induce S).Connected) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    ∃ Q : G.Path x y, ∀ v ∈ Q.val.support, v ∈ S := by
  classical
  obtain ⟨w⟩ := hS.preconnected ⟨x,hx⟩ ⟨y,hy⟩
  let f : G.induce S →g G := ⟨Subtype.val,fun he => he⟩
  let q := w.map f
  refine ⟨q.toPath,?_⟩
  intro v hv
  have hv' := q.support_toPath_subset_support hv
  dsimp [q] at hv'
  rw [Walk.support_map] at hv'
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv'
  exact u.property

theorem weaving_from_core_groups (G : SimpleGraph V) {a p : ℕ}
    (roots : Fin a → V) (x y : Fin p → V) (hr : Function.Injective roots)
    (he : ∀ i j, i ≠ j → Disjoint ({x i,y i} : Set V) {x j,y j})
    (A B : Set V) (hAB : Disjoint A B)
    (hroot : ∀ j, roots j ∉ A ∧ roots j ∉ B)
    (hend : ∀ i, x i ∉ A ∧ x i ∉ B ∧ y i ∉ A ∧ y i ∉ B)
    (core : Fin a → Set V)
    (hcore : ∀ j, (G.induce (core j)).Connected)
    (hcoreA : ∀ j, core j ⊆ A)
    (hcores : ∀ i j, i ≠ j → Disjoint (core i) (core j))
    (hclique : ∀ i j, i ≠ j → ∃ v ∈ core i, ∃ w ∈ core j, G.Adj v w)
    (C : (Fin a ⊕ Fin p) → Set V)
    (hC : ∀ i, (G.induce (C i)).Connected)
    (hCB : ∀ i, C i ⊆ B)
    (hCC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hattach : ∀ j, ∃ v ∈ core j, ∃ w ∈ C (.inl j), G.Adj v w)
    (hattachRoot : ∀ j, ∃ w ∈ C (.inl j), G.Adj (roots j) w)
    (hattachX : ∀ i, ∃ w ∈ C (.inr i), G.Adj (x i) w)
    (hattachY : ∀ i, ∃ w ∈ C (.inr i), G.Adj (y i) w) :
    Nonempty (WeavingWithin G Set.univ roots x y) := by
  classical
  let bag (j : Fin a) := insert (roots j) (core j ∪ C (.inl j))
  have hb (j : Fin a) : (G.induce (bag j)).Connected := by
    obtain ⟨v,hv,w,hw,hvw⟩ := hattach j
    have hh := SimpleGraph.connected_induce_union (hcore j).preconnected
      (hC (.inl j)).preconnected hv hw hvw
    obtain ⟨w,hw,hew⟩ := hattachRoot j
    exact Incidence.connected_insert hh (Or.inr hw) hew
  have hbd (i j : Fin a) (hij : i ≠ j) : Disjoint (bag i) (bag j) := by
    apply Set.disjoint_left.mpr
    intro v hi hj
    rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj
    · exact hij (hr (hi.symm.trans hj))
    · exact (hroot i).1 (hi ▸ hcoreA j hj)
    · exact (hroot i).2 (hi ▸ hCB (.inl j) hj)
    · exact (hroot j).1 (hj ▸ hcoreA i hi)
    · exact Set.disjoint_left.mp (hcores i j hij) hi hj
    · exact Set.disjoint_left.mp hAB (hcoreA i hi) (hCB (.inl j) hj)
    · exact (hroot j).2 (hj ▸ hCB (.inl i) hi)
    · exact Set.disjoint_left.mp hAB (hcoreA j hj) (hCB (.inl i) hi)
    · exact Set.disjoint_left.mp (hCC (.inl i) (.inl j) (by simpa using hij)) hi hj
  let M : RootedCliqueModel G roots :=
    { branch := bag
      connected := hb
      disjoint := hbd
      adjacent := fun i j hij => by
        obtain ⟨v,hv,w,hw,hvw⟩ := hclique i j hij
        exact ⟨v,Or.inr (Or.inl hv),w,Or.inr (Or.inl hw),hvw⟩
      root_mem := fun _ => Or.inl rfl }
  let S (i : Fin p) := insert (x i) (insert (y i) (C (.inr i)))
  have hS (i : Fin p) : (G.induce (S i)).Connected := by
    obtain ⟨w,hw,hew⟩ := hattachY i
    have hh := Incidence.connected_insert (hC (.inr i)) hw hew
    obtain ⟨w,hw,hew⟩ := hattachX i
    exact Incidence.connected_insert hh (Or.inr hw) hew
  have hpaths : ∀ i, ∃ Q : G.Path (x i) (y i), ∀ v ∈ Q.val.support, v ∈ S i :=
    fun i => path_in_connected (hS i) (Or.inl rfl) (Or.inr (Or.inl rfl))
  choose Q hQ using hpaths
  refine ⟨⟨M,fun _ _ _ => Set.mem_univ _,Q,fun _ _ _ => Set.mem_univ _,?_,?_⟩⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hi hj
    have hi' := hQ i v hi
    have hj' := hQ j v hj
    have hterm : ∀ i, ∀ v ∈ ({x i,y i} : Set V), v ∉ B := by
      intro i v hv
      rcases hv with rfl | hv
      · exact (hend i).2.1
      · exact hv ▸ (hend i).2.2.2
    have hsplit : ∀ i v, v ∈ S i → v ∈ ({x i,y i} : Set V) ∨ v ∈ C (.inr i) := by
      intro i v hv
      rcases hv with hv | hv | hv
      · exact Or.inl (Or.inl hv)
      · exact Or.inl (Or.inr hv)
      · exact Or.inr hv
    rcases hsplit i v hi' with hi' | hi' <;> rcases hsplit j v hj' with hj' | hj'
    · exact Set.disjoint_left.mp (he i j hij) hi' hj'
    · exact hterm i v hi' (hCB (.inr j) hj')
    · exact hterm j v hj' (hCB (.inr i) hi')
    · exact Set.disjoint_left.mp (hCC (.inr i) (.inr j) (by simpa using hij)) hi' hj'
  · intro i j v hv hbag
    have hs := hQ i v hv
    change v ∈ insert (roots j) (core j ∪ C (.inl j)) at hbag
    rcases hs with hs | hs | hs
    · subst v
      rcases hbag with hb | hb | hb
      · exact ⟨⟨j,hb.symm⟩,Or.inl rfl⟩
      · exact ((hend i).1 (hcoreA j hb)).elim
      · exact ((hend i).2.1 (hCB (.inl j) hb)).elim
    · subst v
      rcases hbag with hb | hb | hb
      · exact ⟨⟨j,hb.symm⟩,Or.inr rfl⟩
      · exact ((hend i).2.2.1 (hcoreA j hb)).elim
      · exact ((hend i).2.2.2 (hCB (.inl j) hb)).elim
    · rcases hbag with hb | hb | hb
      · exact ((hroot j).2 (hb ▸ hCB (.inr i) hs)).elim
      · exact (Set.disjoint_left.mp hAB (hcoreA j hb) (hCB (.inr i) hs)).elim
      · exact (Set.disjoint_left.mp (hCC (.inr i) (.inl j) (by simp)) hs hb).elim

theorem weaving_from_connected_complement (G : SimpleGraph V) [DecidableRel G.Adj]
    {a p : ℕ} (ha : 1 ≤ a)
    (roots : Fin a → V) (x y : Fin p → V) (hr : Function.Injective roots)
    (he : ∀ i j, i ≠ j → Disjoint ({x i,y i} : Set V) {x j,y j})
    (A : Set V) (B : Finset V) (hAB : Disjoint A (↑B : Set V))
    (hroot : ∀ j, roots j ∉ A ∧ roots j ∉ B)
    (hend : ∀ i, x i ∉ A ∧ x i ∉ B ∧ y i ∉ A ∧ y i ∉ B)
    (core : Fin a → Set V)
    (hcore : ∀ j, (G.induce (core j)).Connected)
    (hcoreA : ∀ j, core j ⊆ A)
    (hcores : ∀ i j, i ≠ j → Disjoint (core i) (core j))
    (hclique : ∀ i j, i ≠ j → ∃ v ∈ core i, ∃ w ∈ core j, G.Adj v w)
    (hN : ∀ v, 2*(a+p) ≤ (B.filter (G.Adj v)).card)
    (hconn : KConnectedOn G B (65536*(2*(a+p)))) :
    Nonempty (WeavingWithin G Set.univ roots x y) := by
  classical
  have hp : ∀ j, ∃ v, v ∈ core j := fun j => by
    obtain ⟨v⟩ := (hcore j).nonempty
    exact ⟨v.val,v.property⟩
  choose cp hcp using hp
  let O := (Fin a ⊕ Fin p) × Bool
  let port : O → V := fun o => match o.1 with
    | .inl j => if o.2 then roots j else cp j
    | .inr i => if o.2 then y i else x i
  have hc : Fintype.card O = 2*(a+p) := by simp [O,Nat.mul_comm]
  obtain ⟨C,hC,hCC,hCB,hports⟩ := group_ports G port Prod.fst
    (fun i => ⟨(i,false),rfl⟩) (by rw [hc]; omega) B
    (fun _ => by rw [hc]; exact hN _) (by rw [hc]; exact hconn)
  apply weaving_from_core_groups G roots x y hr he A (↑B : Set V) hAB
    hroot hend core hcore hcoreA hcores hclique C hC hCB hCC
  · intro j
    obtain ⟨v,hv,he⟩ := hports (.inl j,false)
    exact ⟨cp j,hcp j,v,hv,he⟩
  · intro j
    exact hports (.inl j,true)
  · intro i
    exact hports (.inr i,false)
  · intro i
    exact hports (.inr i,true)

end LinearListHadwiger.Assembly

namespace LinearListHadwiger.Assembly
open SimpleGraph Finset
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in

lemma clique_minor_restrict {G : SimpleGraph V} {s t : ℕ}
    (h : HasCliqueMinor G t) (hst : s ≤ t) : HasCliqueMinor G s := by
  obtain ⟨B,hB,hD,hE⟩ := h
  refine ⟨fun i => B (Fin.castLE hst i),fun i => hB _,?_,?_⟩
  · intro i j hij
    exact hD _ _ (fun he => hij (Fin.ext (congrArg (fun x : Fin t => x.val) he)))
  · intro i j hij
    exact hE _ _ (fun he => hij (Fin.ext (congrArg (fun x : Fin t => x.val) he)))

lemma density_of_scaled_degree [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k c : ℕ} (hd : ∀ v, k ≤ c*G.degree v) :
    (k:ℚ) ≤ 2*c*Knitting.density G := by
  classical
  have hs := Finset.sum_le_sum (s := univ) (fun v _ => hd v)
  rw [←Finset.mul_sum,G.sum_degrees_eq_twice_card_edges] at hs
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  have hsq : (Fintype.card V : ℚ)*k ≤ c*(2*G.edgeFinset.card) := by exact_mod_cast hs
  have he : Knitting.density G * (Fintype.card V:ℚ) = (G.edgeFinset.card:ℚ) := by
    simpa only [SimpleGraph.edgeFinset_card,Fintype.card_eq_nat_card] using
      Knitting.density_mul_order G Fintype.card_pos
  have hnq : (0:ℚ)<Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  apply le_of_mul_le_mul_right ?_ hnq
  calc
    (k:ℚ)*Fintype.card V ≤ c*(2*G.edgeFinset.card) := by nlinarith [hsq]
    _ = (2*c*Knitting.density G)*Fintype.card V := by
      have hh := congrArg (fun q : ℚ => (2:ℚ)*c*q) he
      nlinarith only [hh]

lemma dense_split_core [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {s k : ℕ} (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hdeg : ∀ v, k ≤ 2000*(A.filter (G.Adj v)).card)
    (hthreshold : 100000000*s*Real.log (2*s) < (k:ℝ)/4000) :
    ∃ B : Fin s → Set V,
      (∀ i, (G.induce (B i)).Connected) ∧ (∀ i, B i ⊆ (↑A:Set V)) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w) := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  have hA : A.Nonempty := by
    have hh := hdeg v
    have hp : 0<(A.filter (G.Adj v)).card := by omega
    exact (Finset.card_pos.mp hp).mono (Finset.filter_subset _ _)
  let : Nonempty (↑A:Set V) := by obtain ⟨v,hv⟩ := hA; exact ⟨⟨v,hv⟩⟩
  let H := G.induce (↑A:Set V)
  have hd : (k:ℚ) ≤ 4000*Knitting.density H := by
    have hh := density_of_scaled_degree H (k := k) (c := 2000) (fun v => by
      rw [CoarseDensity.degree_induce_finset]
      exact hdeg v.val)
    norm_num at hh ⊢
    exact hh
  have hd' : (k:ℝ) ≤ 4000*((Knitting.density H:ℚ):ℝ) := by exact_mod_cast hd
  have hminor : HasCliqueMinor H s := by
    by_cases hs2 : 2 ≤ s
    · have hh : s ≤ hadwigerNumber H := by
        by_contra hn
        have hc := CoarseDensity.density_bound H hs2 (lt_of_not_ge hn)
        linarith
      exact clique_minor_restrict (hasCliqueMinor_hadwigerNumber H) hh
    · have he : s=1 := by omega
      rw [he]
      exact cliqueMinor_one H
  obtain ⟨C,hC,hD,hE⟩ := hminor
  let M := Knitting.model_induce G A
  refine ⟨fun i => M.expand (C i),fun i => M.expand_connected (hC i),?_,
    fun i j hij => M.expand_disjoint (hD i j hij),?_⟩
  · intro i v hv
    obtain ⟨w,_,hw⟩ := hv
    have he : v=w.val := hw
    exact he ▸ w.property
  · intro i j hij
    obtain ⟨v,hv,w,hw,hvw⟩ := hE i j hij
    exact ⟨v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,hvw⟩

end LinearListHadwiger.Assembly

namespace LinearListHadwiger.Assembly
open SimpleGraph Finset Filter

theorem small_districts_woven :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → ∀ s : ℕ,
      1 ≤ s → s ≤ 2*⌈(t:ℝ)/(Real.log t)^2⌉₊ →
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      (Fintype.card V : ℝ) ≤ (t:ℝ)^(53/50:ℝ) →
      KConnectedOn G univ ((100000*65536)*t) → Woven G s (3*t) := by
  obtain ⟨Tsplit,hTsplit⟩ := Sampling.sparse_split_on_cutoff
  obtain ⟨Torder,hTorder⟩ := eventually_atTop.mp small_woven_order_cutoff
  refine ⟨⌈max Tsplit Torder⌉₊,?_⟩
  intro t ht s hs hsc V _ _ G _ hord hc
  classical
  have htr : max Tsplit Torder ≤ (t:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast ht)
  obtain ⟨ht2,hnum⟩ := hTorder t ((le_max_right _ _).trans htr)
  obtain ⟨hstr,hthreshold⟩ := hnum s hs hsc
  have hst : s ≤ t := by exact_mod_cast hstr
  have htpos : 0<t := by exact_mod_cast (by linarith : (0:ℝ)<t)
  have : Nonempty V := Fintype.card_pos_iff.mp (by
    have hh := hc.1
    simp only [card_univ] at hh
    omega)
  intro roots hr _ p hp x y _ he
  let Z : Finset V := (univ.image roots) ∪ (univ.image x) ∪ (univ.image y)
  have hZ : Z.card ≤ 7*t := by
    have h1 : (univ.image roots).card ≤ s := by simpa using card_image_le (s := univ) (f := roots)
    have h2 : (univ.image x).card ≤ p := by simpa using card_image_le (s := univ) (f := x)
    have h3 : (univ.image y).card ≤ p := by simpa using card_image_le (s := univ) (f := y)
    have hu1 := card_union_le (univ.image roots) (univ.image x)
    have hu2 := card_union_le ((univ.image roots) ∪ (univ.image x)) (univ.image y)
    dsimp [Z]
    omega
  let S := univ \ Z
  let k : ℕ := 3276800000*t
  have hk : 1 ≤ k := by dsimp [k]; omega
  have htk : (t:ℝ)≤k := by dsimp [k]; push_cast; nlinarith
  have hZk : Z.card < (100000*65536)*t := by omega
  have hSk : KConnectedOn G S k := by
    have hh := Knitting.delete_connected G hc (subset_univ Z) hZk
    exact Knitting.kConnected_mono hh (by dsimp [k]; omega)
  have hdeg : ∀ v, k ≤ (S.filter (G.Adj v)).card := by
    intro v
    have hd := Knitting.min_degree G hc (mem_univ v)
    have hsub : Density.neighbors G univ v ⊆ (S.filter (G.Adj v)) ∪ Z := by
      intro w hw
      by_cases hwZ : w∈Z
      · exact mem_union_right _ hwZ
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hwZ⟩,
          ((Density.mem_neighbors G).mp hw).2⟩)
    have hcount := (card_le_card hsub).trans (card_union_le _ _)
    dsimp [k]
    omega
  have hn : (1:ℝ)≤(t:ℝ)^(53/50:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hpow : (t:ℝ)^(53/50:ℝ) ≤ (t:ℝ)^(11/10:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  obtain ⟨A,B,hAS,hBS,hAB,hN,hB⟩ := hTsplit t ((t:ℝ)^(53/50:ℝ))
    ((le_max_left _ _).trans htr) hn hpow V G S k htk hord hSk hdeg
  obtain ⟨core,hcore,hcoreA,hcores,hclique⟩ := dense_split_core G A hs hk
    (fun v => (hN v).1) (hthreshold.trans_le (by linarith))
  have hnot (F : Finset V) (hFS : F ⊆ S) (v : V) (hv : v∈Z) : v∉F :=
    fun hf => (mem_sdiff.mp (hFS hf)).2 hv
  apply weaving_from_connected_complement G hs roots x y hr he (↑A:Set V) B
    (by exact_mod_cast hAB) ?_ ?_ core hcore hcoreA hcores hclique ?_ ?_
  · intro j
    have hz : roots j∈Z := by simp [Z]
    exact ⟨hnot A hAS _ hz,hnot B hBS _ hz⟩
  · intro i
    have hx : x i∈Z := by simp [Z]
    have hy : y i∈Z := by simp [Z]
    exact ⟨hnot A hAS _ hx,hnot B hBS _ hx,hnot A hAS _ hy,hnot B hBS _ hy⟩
  · intro v
    have hh := (hN v).2
    dsimp [k] at hh
    omega
  · exact Knitting.kConnected_mono hB (by dsimp [k]; omega)

end LinearListHadwiger.Assembly

end OAI
