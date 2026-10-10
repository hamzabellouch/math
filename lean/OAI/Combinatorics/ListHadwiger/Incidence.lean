import OAI.Combinatorics.ListHadwiger.CoarseDensity

namespace OAI

namespace LinearListHadwiger.Incidence
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V  :  Type} [Fintype V] [DecidableEq V]

lemma hit_pool {V : Type} [Fintype V] [DecidableEq V] {I  :  Type} [Fintype I] (A  :  Finset V) (hA  :  A.Nonempty)
    (R  :  I → V → Prop) [DecidableRel R] (s  :  ℕ) (p  :  ℝ) (hp  :  0 ≤ p)
    (hmiss  :  ∀ i ,  ((A.filter fun v  =>  ¬ R i v).card : ℝ)  ≤  p * A.card)
    (hsmall  :  (Fintype.card I : ℝ) * p ^ s < 1)  :
    ∃ B ⊆ A ,  B.card ≤ s  ∧  ∀ i ,  ∃ v ∈ B ,  R i v  :=  by
  classical
  have hpos : (0 : ℝ) < A.card := by exact_mod_cast card_pos.mpr hA

  let w'  :  A → ℝ  :=  fun _  => (A.card : ℝ)⁻¹
  have hsum'  :  ∑ v  :  A ,  w' v = 1  :=  by
    simp only [w' , sum_const , card_univ , Fintype.card_coe , nsmul_eq_mul]
    exact mul_inv_cancel₀ hpos.ne'
  have hrow (i  :  I)  :  ∑ v  :  A ,  w' v * (if  ¬ R i v.val then 1 else 0)  ≤ p  :=  by
    have he  :  (univ.filter fun v  :  A  =>  ¬ R i v.val).card  =  (A.filter fun v  =>  ¬ R i v).card  :=  by
      apply card_bij (fun v _  => v.val)
      · intro v hv; exact mem_filter.mpr ⟨v.property , (mem_filter.mp hv).2⟩
      · intro v _ u _ he; exact Subtype.ext he
      · intro v hv; exact ⟨⟨v , (mem_filter.mp hv).1⟩ , mem_filter.mpr ⟨mem_univ _ , (mem_filter.mp hv).2⟩ , rfl⟩
    calc
      _  =  ((A.filter fun v  =>  ¬ R i v).card : ℝ) / A.card  :=  by
        simp only [w' , mul_ite , mul_one , mul_zero]
        rw [←sum_filter , sum_const , he]
        simp only [nsmul_eq_mul , div_eq_mul_inv]
      _  ≤  p  :=  (div_le_iff₀ hpos).mpr (hmiss i)
  obtain ⟨f , hf⟩  :=  ConnectivityTests.finite_hitting s w' (fun _  => by dsimp [w']; positivity)
    hsum' (fun i (v : A)  => R i v.val) p hp hrow hsmall
  refine ⟨univ.image (fun i  => (f i).val) , ?_ , ?_ , ?_⟩
  · intro v hv; obtain ⟨i , _ , rfl⟩  :=  mem_image.mp hv; exact (f i).property
  · exact (card_image_le).trans (by simp)
  · intro i
    obtain ⟨j , hj⟩  :=  hf i
    exact ⟨_ , mem_image.mpr ⟨j , mem_univ _ , rfl⟩ , hj⟩

lemma star_connected {V : Type} [Fintype V] [DecidableEq V] (G  :  SimpleGraph V) (c  :  V) (B  :  Finset V)
    (hB  :  ∀ v ∈ B ,  G.Adj c v)  :  (G.induce (↑(insert c B) : Set V)).Connected  :=  by
  classical
  have hc  :  c ∈ insert c B  :=  mem_insert_self _ _
  have hr  :  ∀ v  :  (↑(insert c B) : Set V) ,
      (G.induce (↑(insert c B) : Set V)).Reachable ⟨c , hc⟩ v  :=  by
    intro v
    by_cases he  :  v.val = c
    · have he'  :  v = ⟨c , hc⟩  :=  Subtype.ext he
      subst v; exact Reachable.rfl
    · have hv  :  v.val ∈ B  :=  mem_of_mem_insert_of_ne v.property he
      exact (show (G.induce (↑(insert c B) : Set V)).Adj ⟨c , hc⟩ v from hB v.val hv).reachable
  exact {preconnected  :=  fun v w  => (hr v).symm.trans (hr w) , nonempty  :=  ⟨⟨c , hc⟩⟩}

lemma fresh_star (G  :  SimpleGraph V) [DecidableRel G.Adj]
    (Z  :  Finset V) {q s  :  ℕ} (reps  :  Fin q → V) {d  :  ℝ}
    (hn  :  0 < Fintype.card V)
    (hz  :  2 * Z.card ≤ Fintype.card V)
    (hd  :  0 ≤ d) (hdsmall  :  4 * d ≤ Fintype.card V)
    (hdeg  :  ∀ v ,  ((univ.filter fun w  =>  ¬ G.Adj v w).card : ℝ) ≤ d)
    (hsmall  :  (q : ℝ) * (4 * d/Fintype.card V) ^ s < 1)  :
    ∃ D  :  Finset V ,  Disjoint D Z  ∧  (G.induce (↑D : Set V)).Connected  ∧
      D.card ≤ s + 1  ∧  ∀ i ,  ∃ v ∈ D ,  G.Adj (reps i) v  :=  by
  classical
  have hR  :  (univ\Z).Nonempty  :=  by
    apply card_pos.mp
    rw [card_sdiff_of_subset (subset_univ Z) , card_univ]
    omega
  obtain ⟨c , hc⟩  :=  hR
  let A  :  Finset V  :=  (univ\Z).filter (G.Adj c)
  have hcard  :  (Fintype.card V : ℝ)/4  ≤  A.card  :=  by
    have hbad  :=  hdeg c
    have hcover  :  univ  ⊆  Z ∪ A ∪ univ.filter (fun w  =>  ¬ G.Adj c w)  :=  by
      intro v _
      by_cases hv  :  v ∈ Z
      · exact mem_union_left _ (mem_union_left _ hv)
      · by_cases he  :  G.Adj c v
        · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _ , hv⟩ , he⟩))
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _ , he⟩)
    have hnat  :=  (card_le_card hcover).trans (card_union_le _ _)
    have hun  :=  card_union_le Z A
    have hz'  :  2 * (Z.card : ℝ) ≤ Fintype.card V  :=  by exact_mod_cast hz
    have hnat'  :  (Fintype.card V : ℝ) ≤ (Z∪A).card + (univ.filter fun w  =>  ¬ G.Adj c w).card  :=  by
      exact_mod_cast hnat
    have hun'  :  ((Z∪A).card : ℝ) ≤ Z.card + A.card  :=  by exact_mod_cast hun
    linarith
  have hA  :  A.Nonempty  :=  by
    apply card_pos.mp
    have hn'  :  (0 : ℝ) < Fintype.card V  :=  by exact_mod_cast hn
    have hh  :  (0 : ℝ) < A.card  :=  by linarith
    exact_mod_cast hh
  have hmiss (i  :  Fin q)  :  ((A.filter fun v  =>  ¬ G.Adj (reps i) v).card : ℝ)  ≤
      (4 * d/Fintype.card V) * A.card  :=  by
    have hsub  :  A.filter (fun v  =>  ¬ G.Adj (reps i) v)  ⊆  univ.filter (fun v  =>  ¬ G.Adj (reps i) v)  :=
      filter_subset_filter _ (subset_univ _)
    have hh  :  ((A.filter fun v  =>  ¬ G.Adj (reps i) v).card : ℝ) ≤ d  :=
      by
      have hg : ((A.filter fun v => ¬ G.Adj (reps i) v).card : ℝ) ≤
          (univ.filter fun v => ¬ G.Adj (reps i) v).card := by exact_mod_cast card_le_card hsub
      exact hg.trans (hdeg (reps i))
    have hn'  :  (0 : ℝ) < Fintype.card V  :=  by exact_mod_cast hn
    have hx  :  d  ≤  (4 * d/Fintype.card V) * A.card  :=  by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hn').mpr
      nlinarith
    exact hh.trans hx
  obtain ⟨B , hBA , hBs , hhit⟩  :=  hit_pool A hA (fun i v  => G.Adj (reps i) v) s
    (4 * d/Fintype.card V) (by positivity) hmiss (by simpa using hsmall)
  refine ⟨insert c B , ?_ , star_connected G c B (fun v hv  => (mem_filter.mp (hBA hv)).2) , ?_ , ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hzv
    rcases mem_insert.mp hv with he|hv
    · subst v; exact (mem_sdiff.mp hc).2 hzv
    · exact (mem_sdiff.mp (mem_filter.mp (hBA hv)).1).2 hzv
  · exact (card_insert_le _ _).trans (by omega)
  · intro i; obtain ⟨v , hv , he⟩  :=  hhit i
    exact ⟨v , mem_insert_of_mem hv , he⟩

structure BoundedBags (G : SimpleGraph V) (q b : ℕ) where
  bag : Fin q → Finset V
  connected : ∀ i, (G.induce (↑(bag i) : Set V)).Connected
  disjoint : ∀ i j, i ≠ j → Disjoint (bag i) (bag j)
  adjacent : ∀ i j, i ≠ j → ∃ v ∈ bag i, ∃ w ∈ bag j, G.Adj v w
  small : ∀ i, (bag i).card ≤ b

lemma BoundedBags.minor {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {q b : ℕ} (B : BoundedBags G q b) :
    HasCliqueMinor G q :=
  ⟨fun i => ↑(B.bag i), B.connected,
    fun i j h => Finset.disjoint_coe.mpr (B.disjoint i j h),B.adjacent⟩

lemma BoundedBags.succ {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {q b : ℕ} (B : BoundedBags G q b)
    (D : Finset V) (hc : (G.induce (↑D:Set V)).Connected)
    (hd : ∀ i, Disjoint D (B.bag i)) (hs : D.card ≤ b)
    (ha : ∀ i, ∃ v ∈ D, ∃ w ∈ B.bag i, G.Adj v w) :
    Nonempty (BoundedBags G (q+1) b) := by
  classical
  refine ⟨{bag := Fin.cases D B.bag,connected := ?_, disjoint := ?_,adjacent := ?_,small := ?_}⟩
  · intro i; exact Fin.cases hc B.connected i
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases (fun h => (h rfl).elim) (fun b _ => hd b) j
    · refine Fin.cases (fun _ => (hd a).symm) (fun b h => ?_) j
      exact B.disjoint a b (fun he => h (congrArg Fin.succ he))
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases (fun h => (h rfl).elim) (fun b _ => ha b) j
    · refine Fin.cases (fun _ => ?_) (fun b h => ?_) j
      · obtain ⟨v,hv,w,hw,he⟩ := ha a
        exact ⟨w,hw,v,hv,he.symm⟩
      · exact B.adjacent a b (fun he => h (congrArg Fin.succ he))
  · intro i; exact Fin.cases hs B.small i

theorem near_complete_minor (G : SimpleGraph V) [DecidableRel G.Adj]
    {t s : ℕ} {d : ℝ} (hn : 0<Fintype.card V)
    (hnlarge : 2*t*(s+1)≤Fintype.card V)
    (hd : 0≤d) (hdsmall : 4*d≤Fintype.card V)
    (hdeg : ∀ v, ((univ.filter fun w => ¬G.Adj v w).card:ℝ)≤d)
    (hsmall : (t:ℝ)*(4*d/Fintype.card V)^s<1) : HasCliqueMinor G t := by
  classical
  have all (q : ℕ) (hq : q≤t) : Nonempty (BoundedBags G q (s+1)) := by
    induction q with
    | zero =>
      exact ⟨{ bag := Fin.elim0
               connected := fun i => Fin.elim0 i
               disjoint := fun i => Fin.elim0 i
               adjacent := fun i => Fin.elim0 i
               small := fun i => Fin.elim0 i }⟩
    | succ q ih =>
      obtain ⟨B⟩ := ih (by omega)
      let Z := univ.biUnion B.bag
      have hZ : Z.card ≤ q*(s+1) := by
        calc
          _ ≤ ∑ i, (B.bag i).card := card_biUnion_le
          _ ≤ ∑ _i : Fin q, (s+1) := sum_le_sum (fun i _ => B.small i)
          _ = _ := by simp
      have hz : 2*Z.card ≤ Fintype.card V := by nlinarith
      have hr : ∀ i, ∃ v, v ∈ B.bag i := by
        intro i
        obtain ⟨v⟩ := (B.connected i).nonempty
        exact ⟨v.val,v.property⟩
      choose reps hreps using hr
      have hqsmall : (q:ℝ)*(4*d/Fintype.card V)^s<1 := by
        have hq' : (q:ℝ)≤t := by exact_mod_cast (show q≤t by omega)
        exact (mul_le_mul_of_nonneg_right hq' (by positivity)).trans_lt hsmall
      obtain ⟨D,hDZ,hDc,hDs,hDa⟩ := fresh_star G Z reps hn hz hd hdsmall hdeg hqsmall
      apply B.succ D hDc (fun i => Disjoint.mono_right (subset_biUnion_of_mem B.bag (mem_univ i)) hDZ) hDs
      intro i
      obtain ⟨v,hv,he⟩ := hDa i
      exact ⟨v,hv,reps i,hreps i,he.symm⟩
  obtain ⟨B⟩ := all t le_rfl
  exact B.minor

theorem missing_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    {t s : ℕ} {δ : ℝ} (ht : 1 ≤ t)
    (hex : ¬ HasCliqueMinor G t)
    (hn : 2*t*(s+1) ≤ Fintype.card V)
    (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*Fintype.card V)
    (hprob : (t:ℝ)*(8*δ)^s < 1) :
    ∃ v, δ*Fintype.card V ≤ ((univ.filter fun w => w ≠ v ∧ ¬G.Adj v w).card : ℝ) := by
  classical
  by_contra hc
  push Not at hc
  have hcard : 0<Fintype.card V := by nlinarith
  have hdeg (v : V) : ((univ.filter fun w => ¬G.Adj v w).card : ℝ) ≤ 2*δ*Fintype.card V := by
    have he : univ.filter (fun w => ¬G.Adj v w) =
        insert v (univ.filter fun w => w ≠ v ∧ ¬G.Adj v w) := by
      ext w
      simp only [mem_filter,mem_univ,true_and,mem_insert]
      by_cases hw : w=v
      · subst w; simp
      · simp [hw]
    rw [he,card_insert_of_notMem (by simp)]
    push_cast
    linarith [hc v]
  apply hex
  apply near_complete_minor G hcard hn (d := 2*δ*Fintype.card V) (by positivity)
  · have hn' : (0:ℝ) ≤ Fintype.card V := by positivity
    nlinarith
  · exact hdeg
  · have hn' : (Fintype.card V:ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
    convert hprob using 1; field_simp; ring

def addStar (H : SimpleGraph V) (u : V) (N : Finset V) : SimpleGraph V where
  Adj a b := H.Adj a b ∨ (a = u ∧ b ∈ N ∧ a ≠ b) ∨ (b = u ∧ a ∈ N ∧ a ≠ b)
  symm := ⟨by
    intro a b h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.1,h.2.1,h.2.2.symm⟩)
    · exact Or.inr (Or.inl ⟨h.1,h.2.1,h.2.2.symm⟩)⟩
  loopless := ⟨by intro v h; rcases h with h | h | h
                  · exact H.irrefl h
                  · exact h.2.2 rfl
                  · exact h.2.2 rfl⟩

lemma addStar_le {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (u : V) (N : Finset V) : H ≤ addStar H u N :=
  fun _ _ h => Or.inl h

lemma addStar_edges (H : SimpleGraph V) (u : V) (N : Finset V) :
    H.edgeFinset.card + (N.filter fun w => w ≠ u ∧ ¬ H.Adj u w).card ≤
      (addStar H u N).edgeFinset.card := by
  classical
  let M := N.filter fun w => w ≠ u ∧ ¬ H.Adj u w
  let E := M.image fun w => s(u,w)
  have hinj : Set.InjOn (fun w : V => s(u,w)) (↑M : Set V) := by
    intro a ha b hb he
    rcases Sym2.eq_iff.mp he with he | he
    · exact he.2
    · exact he.2.trans he.1
  have hcard : E.card = M.card := card_image_of_injOn hinj
  have hdis : Disjoint H.edgeFinset E := by
    apply Finset.disjoint_left.mpr
    intro e he hg
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hg
    exact (mem_filter.mp hw).2.2 (by simpa using he)
  have hsub : H.edgeFinset ∪ E ⊆ (addStar H u N).edgeFinset := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact SimpleGraph.edgeFinset_mono (addStar_le H u N) he
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp he
      have hw' := mem_filter.mp hw
      exact SimpleGraph.mem_edgeFinset.mpr (Or.inr (Or.inl ⟨rfl,hw'.1,hw'.2.1.symm⟩))
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis,hcard] at hc
  exact hc

lemma connected_insert {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {S : Set V} (hc : (G.induce S).Connected)
    {u v : V} (hu : u ∈ S) (he : G.Adj v u) : (G.induce (insert v S)).Connected := by
  have hS : S ⊆ insert v S := Set.subset_insert _ _
  have hv : v ∈ insert v S := Set.mem_insert _ _
  have hr : ∀ a : (insert v S : Set V), (G.induce (insert v S)).Reachable a ⟨u,hS hu⟩ := by
    rintro ⟨a,ha⟩
    rcases ha with ha | ha
    · subst a
      exact (show (G.induce (insert v S)).Adj ⟨v,hv⟩ ⟨u,hS hu⟩ from he).reachable
    · exact (hc.preconnected ⟨a,ha⟩ ⟨u,hu⟩).map (G.induceHomOfLE hS).toHom
  exact {preconnected := fun a b => (hr a).trans (hr b).symm, nonempty := ⟨⟨v,hv⟩⟩}

noncomputable def extendModel {W : Type} [DecidableEq W] {P : SimpleGraph V}
    {H : SimpleGraph W} (M : MinorModel P H) (root : W → V)
    (hroot : ∀ a, root a ∈ M.branch a) (v : V)
    (hv : ∀ a, v ∉ M.branch a) (N : Finset W)
    (hneigh : ∀ a ∈ N, P.Adj v (root a)) (u : W) (hu : u ∈ N) :
    MinorModel P (addStar H u N) where
  branch a := if a=u then insert v (M.branch a) else M.branch a
  connected a := by
    by_cases ha : a=u
    · rw [ite_eq_left ha]
      exact connected_insert (M.connected a) (hroot a) (hneigh a (ha ▸ hu))
    · rw [ite_eq_right ha]
      exact M.connected a
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro w ha hb
    by_cases hau : a=u <;> by_cases hbu : b=u
    · exact hab (hau.trans hbu.symm)
    · simp only [ite_eq_left hau,ite_eq_right hbu,Set.mem_insert_iff] at ha hb
      rcases ha with rfl | ha
      · exact hv b hb
      · exact Set.disjoint_left.mp (M.disjoint a b hab) ha hb
    · simp only [ite_eq_right hau,ite_eq_left hbu,Set.mem_insert_iff] at ha hb
      rcases hb with rfl | hb
      · exact hv a ha
      · exact Set.disjoint_left.mp (M.disjoint a b hab) ha hb
    · simp only [ite_eq_right hau,ite_eq_right hbu] at ha hb
      exact Set.disjoint_left.mp (M.disjoint a b hab) ha hb
  adjacent := by
    intro a b h
    have hsub (c : W) : M.branch c ⊆ if c=u then insert v (M.branch c) else M.branch c := by
      split_ifs <;> simp
    rcases h with h | h | h
    · obtain ⟨x,hx,y,hy,he⟩ := M.adjacent h
      exact ⟨x,hsub a hx,y,hsub b hy,he⟩
    · exact ⟨v,by simp [h.1],root b,hsub b (hroot b),hneigh b h.2.1⟩
    · exact ⟨root a,hsub a (hroot a),v,by simp [h.1],(hneigh a h.2.1).symm⟩

lemma missing_in_set {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (N : Finset V)
    {t s : ℕ} {δ : ℝ} (ht : 1 ≤ t) (hex : ¬ HasCliqueMinor H t)
    (hn : 2*t*(s+1) ≤ N.card) (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*N.card) (hprob : (t:ℝ)*(8*δ)^s < 1) :
    ∃ u ∈ N, δ*N.card ≤ ((N.filter fun w => w ≠ u ∧ ¬H.Adj u w).card : ℝ) := by
  classical
  let J := H.induce (↑N : Set V)
  have hn' : 2*t*(s+1) ≤ Fintype.card (↑N : Set V) := by simpa using hn
  have hex' : ¬HasCliqueMinor J t := fun hh => hex ((Knitting.model_induce H N).lift_clique hh)
  have hδn' : 1 ≤ δ*Fintype.card (↑N : Set V) := by simpa using hδn
  obtain ⟨u,hu⟩ := missing_vertex J ht hex' hn' hδ hδsmall hδn' hprob
  have he : (univ.filter fun w : (↑N : Set V) => w ≠ u ∧ ¬J.Adj u w).card =
      (N.filter fun w => w ≠ u.val ∧ ¬H.Adj u.val w).card := by
    apply card_bij (fun w _ => w.val)
    · intro w hw
      obtain ⟨hw₁,hw₂⟩ := (mem_filter.mp hw).2
      exact mem_filter.mpr ⟨w.property,(fun he => hw₁ (Subtype.ext he)),hw₂⟩
    · intro a _ b _ he; exact Subtype.ext he
    · intro w hw
      obtain ⟨hwN,hwU,hwE⟩ := mem_filter.mp hw
      refine ⟨⟨w,hwN⟩,mem_filter.mpr ⟨mem_univ _,?_,hwE⟩,rfl⟩
      exact fun hh => hwU (congrArg Subtype.val hh)
  refine ⟨u.val,u.property,?_⟩
  have hcn : Fintype.card (↑N : Set V) = N.card := by simp
  rw [hcn,he] at hu
  exact hu

lemma filter_subtype_card {V : Type} [Fintype V] [DecidableEq V] (A : Finset V) (p : V → Prop) :
    (univ.filter fun a : (↑A : Set V) => p a.val).card = (A.filter p).card := by
  classical
  apply card_bij (fun a _ => a.val)
  · intro a ha; exact mem_filter.mpr ⟨a.property,(mem_filter.mp ha).2⟩
  · intro a _ b _ he; exact Subtype.ext he
  · intro v hv
    exact ⟨⟨v,(mem_filter.mp hv).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩,rfl⟩

theorem incidence_model (P : SimpleGraph V) (A T : Finset V)
    {t s : ℕ} {δ : ℝ} (ht : 1 ≤ t) (hex : ¬ HasCliqueMinor P t)
    (hdis : Disjoint A T)
    (hlarge : ∀ v ∈ T, 2*t*(s+1) ≤ (A.filter (P.Adj v)).card)
    (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*(2*t*(s+1))) (hprob : (t:ℝ)*(8*δ)^s < 1) :
    ∃ (H : SimpleGraph (↑A : Set V)) (M : MinorModel P H),
      (∀ a, a.val ∈ M.branch a) ∧
      (∀ a, M.branch a ⊆ (↑(A∪T) : Set V)) ∧
      δ*(∑ v ∈ T, ((A.filter (P.Adj v)).card : ℝ)) ≤ H.edgeFinset.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    let H : SimpleGraph (↑A : Set V) := ⊥
    let M : MinorModel P H :=
      { branch := fun a => {a.val}
        connected := fun a => by
          have : Nonempty ({a.val} : Set V) := ⟨⟨a.val,rfl⟩⟩
          exact Connected.of_subsingleton
        disjoint := fun a b hn => Set.disjoint_singleton.mpr (fun he => hn (Subtype.ext he))
        adjacent := by intro a b h; exact h.elim }
    refine ⟨H,M,fun a => rfl,?_,?_⟩
    · intro a v hv
      have he : v=a.val := hv
      simp [he,a.property]
    · simp
  | @insert v T hvT ih =>
    have hdisT : Disjoint A T := Finset.disjoint_of_subset_right (subset_insert _ _) hdis
    have hvA : v ∉ A := fun hh => Finset.disjoint_left.mp hdis hh (mem_insert_self _ _)
    obtain ⟨H,M,hroot,hsupp,hcount⟩ := ih hdisT (fun w hw => hlarge w (mem_insert_of_mem hw))
    let N : Finset (↑A:Set V) := univ.filter fun a => P.Adj v a.val
    have hNc : N.card = (A.filter (P.Adj v)).card := filter_subtype_card A (P.Adj v)
    have hNlarge : 2*t*(s+1) ≤ N.card := by rw [hNc]; exact hlarge v (mem_insert_self _ _)
    have hNm : 1 ≤ δ*N.card := by
      have hN' : (2:ℝ)*t*(s+1) ≤ N.card := by exact_mod_cast hNlarge
      exact hδn.trans (mul_le_mul_of_nonneg_left hN' hδ)
    have hexH : ¬ HasCliqueMinor H t := fun h => hex (M.lift_clique h)
    obtain ⟨u,hu,hgain⟩ := missing_in_set H N ht hexH hNlarge hδ hδsmall hNm hprob
    have hvM : ∀ a, v ∉ M.branch a := by
      intro a ha
      rcases mem_union.mp (hsupp a ha) with hh | hh
      · exact hvA hh
      · exact hvT hh
    let M' := extendModel M Subtype.val hroot v hvM N (fun a ha => (mem_filter.mp ha).2) u hu
    have hnew := addStar_edges H u N
    refine ⟨addStar H u N,M',?_,?_,?_⟩
    · intro a
      change a.val ∈ if a=u then insert v (M.branch a) else M.branch a
      split_ifs <;> simp [hroot]
    · intro a w hw
      change w ∈ (if a=u then insert v (M.branch a) else M.branch a) at hw
      split_ifs at hw with ha
      · rcases hw with rfl | hw
        · exact mem_union_right _ (mem_insert_self _ _)
        · rcases mem_union.mp (hsupp a hw) with hw | hw
          · exact mem_union_left _ hw
          · exact mem_union_right _ (mem_insert_of_mem hw)
      · rcases mem_union.mp (hsupp a hw) with hw | hw
        · exact mem_union_left _ hw
        · exact mem_union_right _ (mem_insert_of_mem hw)
    · have hnew' : (H.edgeFinset.card:ℝ) + (N.filter fun w => w ≠ u ∧ ¬H.Adj u w).card ≤
          (addStar H u N).edgeFinset.card := by exact_mod_cast hnew
      rw [sum_insert hvT]
      rw [hNc] at hgain
      nlinarith

theorem incidence_finite (P : SimpleGraph V) (A T : Finset V)
    {t s : ℕ} {δ : ℝ} (ht : 2 ≤ t) (hex : hadwigerNumber P < t)
    (hdis : Disjoint A T)
    (hlarge : ∀ v ∈ T, 2*t*(s+1) ≤ (A.filter (P.Adj v)).card)
    (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*(2*t*(s+1))) (hprob : (t:ℝ)*(8*δ)^s < 1) :
    δ*(∑ v ∈ T, ((A.filter (P.Adj v)).card : ℝ)) ≤
      100000000*t*Real.log (2*t)*A.card := by
  classical
  by_cases hA : A = ∅
  · simp [hA]
  have hn : 0 < Fintype.card (↑A : Set V) := by simpa using card_pos.mpr (nonempty_iff_ne_empty.mpr hA)
  obtain ⟨H,M,_,_,hcount⟩ := incidence_model P A T (by omega) (fun h => (not_lt_of_ge (cliqueMinor_le_hadwigerNumber h)) hex)
    hdis hlarge hδ hδsmall hδn hprob
  have hd := CoarseDensity.density_bound H ht (M.hadwiger_le.trans_lt hex)
  have he : (H.edgeFinset.card : ℝ) = ((Knitting.density H : ℚ):ℝ)*A.card := by
    have hh := Knitting.density_mul_order H hn
    have hh' : ((Knitting.density H : ℚ):ℝ)*Fintype.card (↑A : Set V) = H.edgeFinset.card := by exact_mod_cast hh
    simpa using hh'.symm
  exact hcount.trans (he.le.trans (mul_le_mul_of_nonneg_right hd (by positivity)))

open Filter in
lemma incidence_cutoff : ∀ᶠ z : ℝ in atTop,
    2 ≤ z ∧ 8*z^(-(1/200:ℝ)) ≤ 1 ∧
    1 ≤ z^(-(1/200:ℝ))*(2*z*(1600+1)) ∧
    z*(8*z^(-(1/200:ℝ)))^1600 < 1 ∧
    100000000*Real.log (2*z) ≤ z^(1/200:ℝ) := by
  have hsmall : ∀ᶠ z : ℝ in atTop, 8*z^(-(1/200:ℝ)) ≤ 1 := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/200)).const_mul 8
    apply Tendsto.eventually_le_const (by norm_num : (8:ℝ)*0<1) hh
  have hprob : ∀ᶠ z : ℝ in atTop, (8:ℝ)^1600 * z^(-(7:ℝ)) < 1 := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7)).const_mul ((8:ℝ)^1600)
    apply Tendsto.eventually_lt_const (by simp : (8:ℝ)^1600*0<1) hh
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/200)).bound
    (show (0:ℝ)<1/200000000 by norm_num)
  have hconst : ∀ᶠ z : ℝ in atTop, 200000000*Real.log 2 ≤ z^(1/200:ℝ) :=
    (tendsto_atTop.mp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200))) _
  filter_upwards [eventually_ge_atTop (2:ℝ),hsmall,hprob,hlog,hconst] with z hz hs hp hl hc
  have hzpos : 0<z := by linarith
  have hzone : 1≤z := by linarith
  refine ⟨hz,hs,?_,?_,?_⟩
  · have hpow : z^(-(1/200:ℝ))*z = z^(199/200:ℝ) := by
      rw [←Real.rpow_add_one hzpos.ne']
      norm_num
    have hone := Real.one_le_rpow hzone (show (0:ℝ)≤199/200 by norm_num)
    calc
      _ = 3202*(z^(-(1/200:ℝ))*z) := by ring
      _ = 3202*z^(199/200:ℝ) := by rw [hpow]
      _ ≥ 1 := by linarith
  · have hpw : (z^(-(1/200:ℝ)))^1600 = z^(-(8:ℝ)) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hzpos.le]
      norm_num
    have he : z*z^(-(8:ℝ))=z^(-(7:ℝ)) := by
      calc
        _ = z^(1:ℝ)*z^(-(8:ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hzpos]; norm_num
    calc
      _ = (8:ℝ)^1600 * (z*(z^(-(1/200:ℝ)))^1600) := by rw [mul_pow]; ac_rfl
      _ = (8:ℝ)^1600 * z^(-(7:ℝ)) := by rw [hpw,he]
      _ < 1 := hp
  · have hl' : Real.log z ≤ (1:ℝ)/200000000*z^(1/200:ℝ) := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hzone),
        abs_of_nonneg (Real.rpow_nonneg hzpos.le _)] using hl
    rw [Real.log_mul (by norm_num) hzpos.ne']
    linarith

theorem incidence_bound : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (P : SimpleGraph W),
    hadwigerNumber P < t → ∀ A T : Finset W, Disjoint A T →
    (∑ v ∈ T.filter (fun v => 3202*t ≤ (A.filter (P.Adj v)).card),
      ((A.filter (P.Adj v)).card : ℝ)) ≤ (t:ℝ)^(101/100:ℝ)*A.card := by
  classical
  obtain ⟨t₀,ht₀⟩ := Filter.eventually_atTop.mp incidence_cutoff.natCast_atTop
  refine ⟨t₀,?_⟩
  intro t htt W _ _ P hex A T hdis
  obtain ⟨ht,hs,hn,hp,hl⟩ := ht₀ t htt
  have htn : 2≤t := by exact_mod_cast ht
  have htpos : (0:ℝ)<t := by linarith
  let T' := T.filter (fun v => 3202*t ≤ (A.filter (P.Adj v)).card)
  have hdis' : Disjoint A T' := Finset.disjoint_of_subset_right (filter_subset _ _) hdis
  have hlarge : ∀ v ∈ T', 2*t*(1600+1) ≤ (A.filter (P.Adj v)).card := by
    intro v hv
    have hh := (mem_filter.mp hv).2
    nlinarith
  have hδ : (0:ℝ)<(t:ℝ)^(-(1/200:ℝ)) := Real.rpow_pos_of_pos htpos _
  have hh := incidence_finite P A T' htn hex hdis' hlarge hδ.le hs hn hp
  have he : (t:ℝ)^(-(1/200:ℝ))*(t:ℝ)^(101/100:ℝ) = (t:ℝ)*(t:ℝ)^(1/200:ℝ) := by
    calc
      _ = (t:ℝ)^((-(1/200:ℝ))+(101/100:ℝ)) := (Real.rpow_add htpos _ _).symm
      _ = (t:ℝ)^((1:ℝ)+(1/200:ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add htpos,Real.rpow_one]
  apply (mul_le_mul_iff_right₀ hδ).mp
  calc
    _ ≤ 100000000*t*Real.log (2*t)*A.card := hh
    _ = (t:ℝ)*(100000000*Real.log (2*t))*A.card := by ring
    _ ≤ (t:ℝ)*(t:ℝ)^(1/200:ℝ)*A.card := by gcongr
    _ = (t:ℝ)^(-(1/200:ℝ))*((t:ℝ)^(101/100:ℝ)*A.card) := by rw [←mul_assoc,he]

end LinearListHadwiger.Incidence

end OAI
