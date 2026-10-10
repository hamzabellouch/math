import OAI.Combinatorics.ListHadwiger.Incidence

namespace OAI

namespace LinearListHadwiger.District
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

def Statement : Prop := ∀ K : ℕ, 0 < K → ∃ D : ℕ,
  max (400*3202) (12800*K) < D ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
  ∀ (W : Type) [Fintype W] [Nonempty W] [DecidableEq W] (P : SimpleGraph W),
  hadwigerNumber P < t → (D*t*Fintype.card W : ℕ) ≤ P.edgeFinset.card →
  ∃ S : Finset W, KConnectedOn P S (K*t) ∧ (S.card : ℝ) ≤ (t:ℝ)^(53/50:ℝ)

def outside (G : SimpleGraph V) (H : Finset V) : Finset V :=
  univ.filter fun w => w ∉ H ∧ ∃ v ∈ H, G.Adj v w

@[simp] lemma mem_outside (G : SimpleGraph V) (H : Finset V) (w : V) :
    w ∈ outside G H ↔ w ∉ H ∧ ∃ v ∈ H, G.Adj v w := by simp [outside]

lemma outside_disjoint (G : SimpleGraph V) (H : Finset V) : Disjoint H (outside G H) := by
  exact disjoint_left.mpr (fun v hv ho => (mem_outside G H v).mp ho |>.1 hv)

lemma degree_sum_comm {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H S : Finset V) :
    ∑ v ∈ H, (S.filter (G.Adj v)).card = ∑ w ∈ S, (H.filter (G.Adj w)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro w hw
  apply sum_congr rfl
  intro v hv
  simp only [G.adj_comm]

lemma degree_sum_split (G : SimpleGraph V) (H S : Finset V) :
    ∑ v ∈ H, (S.filter (G.Adj v)).card =
      ∑ w ∈ S ∩ H, (H.filter (G.Adj w)).card +
      ∑ w ∈ S ∩ outside G H, (H.filter (G.Adj w)).card := by
  rw [degree_sum_comm]
  have hsub : S ∩ H ⊆ S := inter_subset_left
  rw [←sum_sdiff hsub]
  have he : ∑ w ∈ S \ (S ∩ H), (H.filter (G.Adj w)).card =
      ∑ w ∈ S ∩ outside G H, (H.filter (G.Adj w)).card := by
    apply (sum_subset ?_ ?_).symm
    · intro w hw
      obtain ⟨hs,ho⟩ := mem_inter.mp hw
      exact mem_sdiff.mpr ⟨hs, fun hh => ((mem_outside _ _ _).mp ho).1 (mem_inter.mp hh).2⟩
    · intro w hw hn
      obtain ⟨hs,hh⟩ := mem_sdiff.mp hw
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvH,hvw⟩ := mem_filter.mp hv
      apply hn
      refine mem_inter.mpr ⟨hs,(mem_outside _ _ _).mpr ⟨?_,v,hvH,hvw.symm⟩⟩
      intro hwH
      exact hh (mem_inter.mpr ⟨hs,hwH⟩)
  rw [he,add_comm]

def loss2 (G : SimpleGraph V) (H : Finset V) : ℕ :=
  (Density.darts G H).card + 2*∑ w ∈ outside G H, ((H.filter (G.Adj w)).card-1)

lemma outside_pos (G : SimpleGraph V) (H : Finset V) {w : V}
    (hw : w ∈ outside G H) : 1 ≤ (H.filter (G.Adj w)).card := by
  obtain ⟨_,v,hv,hvw⟩ := (mem_outside _ _ _).mp hw
  exact card_pos.mpr ⟨v,mem_filter.mpr ⟨hv,hvw.symm⟩⟩

lemma darts_sum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : Finset V) :
    (Density.darts G H).card = ∑ v ∈ H, (H.filter (G.Adj v)).card := by
  simp only [Density.darts]
  rw [card_eq_sum_ones, sum_filter, sum_product]
  simp only [card_eq_sum_ones, sum_filter]

lemma loss2_identity (G : SimpleGraph V) (H : Finset V) :
    loss2 G H + (Density.darts G H).card + 2*(outside G H).card =
      2*∑ v ∈ H, G.degree v := by
  have hx := degree_sum_split G H univ
  simp only [univ_inter] at hx
  have hd : ∀ v, (univ.filter (G.Adj v)).card = G.degree v := by
    intro v
    have he : univ.filter (G.Adj v) = G.neighborFinset v := by ext w; simp
    rw [he,SimpleGraph.card_neighborFinset_eq_degree]
  simp only [hd] at hx
  have hc : (∑ w ∈ outside G H, ((H.filter (G.Adj w)).card-1)) + (outside G H).card =
      ∑ w ∈ outside G H, (H.filter (G.Adj w)).card := by
    rw [show (outside G H).card = (∑ _w ∈ outside G H, (1:ℕ)) by simp,←sum_add_distrib]
    apply sum_congr rfl
    intro w hw
    exact Nat.sub_add_cancel (outside_pos G H hw)
  rw [←darts_sum] at hx
  unfold loss2
  omega

theorem restricted_degree_loss (G : SimpleGraph V) (H S : Finset V) (hHS : H ⊆ S) :
    (∑ v ∈ H, (S.filter (G.Adj v)).card) ≤
      (S ∩ outside G H).card + loss2 G H := by
  rw [degree_sum_split,inter_eq_right.mpr hHS,←darts_sum]
  have hs : ∑ w ∈ S ∩ outside G H, ((H.filter (G.Adj w)).card-1) ≤
      ∑ w ∈ outside G H, ((H.filter (G.Adj w)).card-1) := sum_le_sum_of_subset inter_subset_right
  have hc : ∑ w ∈ S ∩ outside G H, (H.filter (G.Adj w)).card =
      (S ∩ outside G H).card + ∑ w ∈ S ∩ outside G H, ((H.filter (G.Adj w)).card-1) := by
    rw [show (S ∩ outside G H).card = (∑ _w ∈ S ∩ outside G H, (1:ℕ)) by simp,←sum_add_distrib]
    apply sum_congr rfl
    intro w hw
    have hh := outside_pos G H (mem_inter.mp hw).2
    omega
  rw [hc]
  unfold loss2
  omega

lemma outside_insert (G : SimpleGraph V) (H : Finset V) {w : V}
    (hw : w ∈ outside G H) :
    outside G (insert w H) = (outside G H).erase w ∪ (G.neighborFinset w \ H) := by
  ext z
  simp only [mem_outside,mem_insert,not_or,mem_union,mem_erase,mem_sdiff,SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨hzw,hzH⟩,v,(rfl|hv),h⟩
    · exact Or.inr ⟨h,hzH⟩
    · exact Or.inl ⟨hzw,⟨hzH,v,hv,h⟩⟩
  · rintro (⟨hzw,hzH,v,hv,h⟩|⟨h,hzH⟩)
    · exact ⟨⟨hzw,hzH⟩,v,Or.inr hv,h⟩
    · exact ⟨⟨h.ne.symm,hzH⟩,w,Or.inl rfl,h⟩

lemma neighborhood_increment (G : SimpleGraph V) (H : Finset V) {w : V}
    (hw : w ∈ outside G H) :
    (outside G (insert w H)).card + ((outside G H).filter (G.Adj w)).card +
      (H.filter (G.Adj w)).card + 1 = (outside G H).card + G.degree w := by
  have hi : (outside G H).erase w ∩ (G.neighborFinset w \ H) =
      (outside G H).filter (G.Adj w) := by
    ext z
    simp only [mem_inter,mem_erase,mem_sdiff,SimpleGraph.mem_neighborFinset,mem_filter]
    constructor
    · rintro ⟨⟨_,hz⟩,h,_⟩; exact ⟨hz,h⟩
    · rintro ⟨hz,h⟩; exact ⟨⟨h.ne.symm,hz⟩,h,((mem_outside _ _ _).mp hz).1⟩
  have hc := card_union_add_card_inter ((outside G H).erase w) (G.neighborFinset w \ H)
  rw [←outside_insert G H hw,hi,card_erase_of_mem hw] at hc
  have he : G.neighborFinset w ∩ H = H.filter (G.Adj w) := by ext z; simp [and_comm]
  have hd := card_sdiff_add_card_inter (G.neighborFinset w) H
  rw [he,SimpleGraph.card_neighborFinset_eq_degree] at hd
  have hp := card_pos.mpr ⟨w,hw⟩
  omega

lemma loss2_insert (G : SimpleGraph V) (H : Finset V) {w : V}
    (hw : w ∈ outside G H) :
    loss2 G (insert w H) = loss2 G H + 2*(1+((outside G H).filter (G.Adj w)).card) := by
  have hwH := ((mem_outside _ _ _).mp hw).1
  have h1 := loss2_identity G H
  have h2 := loss2_identity G (insert w H)
  have h3 := neighborhood_increment G H hw
  have h4 := Density.darts_erase G (mem_insert_self w H)
  rw [erase_insert hwH] at h4
  have hn : Density.neighbors G (insert w H) w = H.filter (G.Adj w) := by
    ext z
    simp only [Density.mem_neighbors,mem_insert,mem_filter]
    exact ⟨fun ⟨h,ha⟩ => ⟨h.resolve_left ha.ne.symm,ha⟩,fun ⟨h,ha⟩ => ⟨Or.inr h,ha⟩⟩
  rw [hn] at h4
  rw [sum_insert hwH] at h2
  omega

@[simp] lemma loss2_singleton (G : SimpleGraph V) (v : V) : loss2 G {v} = 0 := by
  unfold loss2
  have hd : Density.darts G {v} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hx,hy,h⟩ := (Density.mem_darts G).mp hx
    have h1 : x.1=v := mem_singleton.mp hx
    have h2 : x.2=v := mem_singleton.mp hy
    exact h.ne (h1.trans h2.symm)
  rw [hd,card_empty,zero_add]
  apply (mul_eq_zero).mpr
  right
  apply sum_eq_zero
  intro w hw
  have hh : (({v}:Finset V).filter (G.Adj w)).card ≤ 1 := (card_filter_le _ _).trans (by simp)
  omega

theorem surviving_core (G : SimpleGraph V) (A : Finset V) (d : ℚ)
    (hd : 0 ≤ d)
    (he : (d/4)*Fintype.card V + (1/8:ℚ)*(2*G.edgeFinset.card) <
      ((Density.darts G A).card:ℚ)/2) :
    ∃ S ⊆ A, S.Nonempty ∧ ∀ v ∈ S,
      d/4 ≤ ((S.filter (G.Adj v)).card:ℚ) ∧
      (G.degree v : ℚ)/8 ≤ (S.filter (G.Adj v)).card := by
  classical
  let budget : Finset V → ℚ := fun S =>
    (d/4)*S.card + (1/8:ℚ)*(∑v∈S,(G.degree v:ℚ))
  have hb : 0 ≤ budget A := by dsimp [budget]; positivity
  have hstart : budget A < ((Density.darts G A).card:ℚ)/2 := by
    have hcard : (A.card:ℚ) ≤ Fintype.card V := by exact_mod_cast card_le_univ A
    have hsum : ∑v∈A,(G.degree v:ℚ) ≤ 2*G.edgeFinset.card := by
      calc
        _ ≤ ∑v : V,(G.degree v:ℚ) := sum_le_univ_sum_of_nonneg (fun _ => by positivity)
        _ = _ := by exact_mod_cast G.sum_degrees_eq_twice_card_edges
    dsimp [budget]
    have hc := mul_le_mul_of_nonneg_left hcard (show (0:ℚ)≤d/4 by positivity)
    linarith
  have aux : ∀ n : ℕ, ∀ S ⊆ A, S.card = n → budget S < ((Density.darts G S).card:ℚ)/2 →
      ∃ T ⊆ S, T.Nonempty ∧ ∀ v ∈ T,
        d/4 ≤ ((T.filter (G.Adj v)).card:ℚ) ∧
        (G.degree v : ℚ)/8 ≤ (T.filter (G.Adj v)).card := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hSA hn hs
      by_cases hgood : ∀ v ∈ S, d/4 ≤ ((S.filter (G.Adj v)).card:ℚ) ∧
        (G.degree v : ℚ)/8 ≤ (S.filter (G.Adj v)).card
      · refine ⟨S,Subset.rfl,?_,hgood⟩
        by_contra hne
        have hz : S=∅ := not_nonempty_iff_eq_empty.mp hne
        simp [hz,budget,Density.darts] at hs
      push Not at hgood
      obtain ⟨v,hv,hvbad⟩ := hgood
      have hbdel : budget S = budget (S.erase v) + d/4 + (G.degree v:ℚ)/8 := by
        dsimp [budget]
        rw [←sum_erase_add _ _ hv]
        have hc : (S.card:ℚ) = (S.erase v).card+1 := by exact_mod_cast (card_erase_add_one hv).symm
        rw [hc]
        ring
      have hedel : ((Density.darts G S).card:ℚ)/2 =
          ((Density.darts G (S.erase v)).card:ℚ)/2 + (S.filter (G.Adj v)).card := by
        have hh := Density.darts_erase G hv
        have hh' : ((Density.darts G S).card:ℚ) = (Density.darts G (S.erase v)).card +
          2*(S.filter (G.Adj v)).card := by exact_mod_cast hh
        linarith
      have hvs : ((S.filter (G.Adj v)).card:ℚ) < d/4 + (G.degree v:ℚ)/8 := by
        by_cases hfirst : d/4 ≤ ((S.filter (G.Adj v)).card:ℚ)
        · have hh := hvbad hfirst
          linarith
        · push Not at hfirst
          have : (0:ℚ) ≤ G.degree v := by positivity
          linarith
      have hnew : budget (S.erase v) < ((Density.darts G (S.erase v)).card:ℚ)/2 := by linarith
      obtain ⟨T,hTS,hT,hgoodT⟩ := ih (S.erase v).card (by rw [←hn]; exact card_erase_lt_of_mem hv)
        (S.erase v) (erase_subset _ _ |>.trans hSA) rfl hnew
      exact ⟨T,hTS.trans (erase_subset _ _),hT,hgoodT⟩
  exact aux A.card A Subset.rfl rfl hstart

lemma outside_card_le (G : SimpleGraph V) (H : Finset V) :
    (outside G H).card ≤ ∑ v ∈ H, G.degree v := by
  have hs : outside G H ⊆ H.biUnion (fun v => G.neighborFinset v) := by
    intro w hw
    obtain ⟨_,v,hv,ha⟩ := (mem_outside _ _ _).mp hw
    exact mem_biUnion.mpr ⟨v,hv,by simpa using ha⟩
  exact (card_le_card hs).trans (card_biUnion_le.trans (by simp))

theorem cheap_neighborhood (G : SimpleGraph V) (S X : Finset V) (p : ℕ) (lam M : ℚ)
    (hp : 1 ≤ p) (hlam : 4 ≤ lam) (hM : 0 ≤ M) (hS : S.Nonempty) (hSX : Disjoint S X)
    (hsdeg : ∀ v ∈ S, 25*lam ≤ ((S.filter (G.Adj v)).card:ℚ) ∧
      (G.degree v:ℚ)/8 ≤ (S.filter (G.Adj v)).card)
    (hhigh : ∀ v ∈ S, (G.degree v:ℚ) < M)
    (hXdeg : ∀ v ∈ S, ((X.filter (G.Adj v)).card:ℚ) < lam/4)
    (hnocheap : ∀ H ⊆ S, (G.induce (↑H:Set V)).Connected → H.card=p →
      2*lam*(H.card-1:ℚ) < loss2 G H) :
    ∃ N : Finset V, Disjoint N X ∧ N.Nonempty ∧
      (N.card:ℚ) ≤ p*M ∧ (lam/32)*N.card ≤ (Density.darts G N).card := by
  classical
  let good : Finset (Finset V) := S.powerset.filter fun H => H.Nonempty ∧
    (G.induce (↑H:Set V)).Connected ∧ H.card ≤ p ∧ (loss2 G H:ℚ) ≤ 2*lam*(H.card-1:ℚ)
  obtain ⟨v,hv⟩ := hS
  have hvG : ({v}:Finset V) ∈ good := by
    simp only [good,mem_filter,mem_powerset]
    refine ⟨singleton_subset_iff.mpr hv,by simp,?_,by simpa,by simp⟩
    have he : (↑({v}:Finset V):Set V) = {v} := by ext x; simp
    rw [he]
    exact SimpleGraph.Connected.of_subsingleton
  obtain ⟨H,hHg,hmax⟩ := exists_max_image good card ⟨{v},hvG⟩
  obtain ⟨hHS,hH,hconn,hHp,hcheap⟩ : H ⊆ S ∧ H.Nonempty ∧
      (G.induce (↑H:Set V)).Connected ∧ H.card ≤ p ∧ (loss2 G H:ℚ) ≤ 2*lam*(H.card-1:ℚ) := by
    simpa only [good,mem_filter,mem_powerset,and_assoc] using hHg
  have hplt : H.card < p := lt_of_le_of_ne hHp (fun h => (not_lt_of_ge hcheap) (hnocheap H hHS hconn h))
  let N := outside G H
  have hNS : ∀ w ∈ N ∩ S, lam < 1+((N.filter (G.Adj w)).card:ℚ) := by
    intro w hw
    obtain ⟨hwN,hwS⟩ := mem_inter.mp hw
    by_contra hbad
    push Not at hbad
    have hwH := ((mem_outside _ _ _).mp hwN).1
    obtain ⟨_,u,hu,ha⟩ := (mem_outside _ _ _).mp hwN
    have hnewconn : (G.induce (↑(insert w H):Set V)).Connected := by
      rw [Finset.coe_insert]
      exact Incidence.connected_insert hconn hu ha.symm
    have hnewloss : (loss2 G (insert w H):ℚ) = loss2 G H + 2*(1+(N.filter (G.Adj w)).card) := by
      exact_mod_cast loss2_insert G H hwN
    have hnew : insert w H ∈ good := by
      simp only [good,mem_filter,mem_powerset]
      refine ⟨insert_subset hwS hHS,insert_nonempty _ _,hnewconn,?_,?_⟩
      · rw [card_insert_of_notMem hwH]; omega
      · rw [hnewloss,card_insert_of_notMem hwH]
        push_cast
        nlinarith
    have hh := hmax (insert w H) hnew
    rw [card_insert_of_notMem hwH] at hh
    omega
  let a : ℚ := ∑ v ∈ H, ((S.filter (G.Adj v)).card:ℚ)
  let b : ℚ := ∑ v ∈ H, (G.degree v:ℚ)
  have ha : 25*lam*H.card ≤ a := by
    calc
      _ = ∑ _v ∈ H, 25*lam := by simp [mul_comm]
      _ ≤ a := sum_le_sum (fun v hv => (hsdeg v (hHS hv)).1)
  have hab : b/8 ≤ a := by
    dsimp [a,b]
    rw [sum_div]
    exact sum_le_sum (fun v hv => (hsdeg v (hHS hv)).2)
  have hNb : (N.card:ℚ) ≤ b := by
    dsimp [N,b]
    exact_mod_cast outside_card_le G H
  have haloss : a ≤ (N ∩ S).card + 2*lam*(H.card-1:ℚ) := by
    have hh : a ≤ (S ∩ N).card + (loss2 G H:ℚ) := by
      dsimp [a,N]
      exact_mod_cast restricted_degree_loss G H S hHS
    rw [inter_comm] at hh
    linarith
  have hratio : (N.card:ℚ)/16 ≤ (N ∩ S).card := by nlinarith
  have hNpos : (N ∩ S).Nonempty := by
    have hpH : (0:ℚ) < H.card := by exact_mod_cast card_pos.mpr hH
    have hnpos : (0:ℚ)<(N ∩ S).card := by nlinarith
    exact card_pos.mp (by exact_mod_cast hnpos)
  have hNdeg : ∀ w ∈ N ∩ S, lam/2 ≤ (((N \ X).filter (G.Adj w)).card:ℚ) := by
    intro w hw
    have hh := hNS w hw
    have hx := hXdeg w (mem_inter.mp hw).2
    have hle : (N.filter (G.Adj w)).card ≤ ((N \ X).filter (G.Adj w)).card + (X.filter (G.Adj w)).card := by
      have hsub : N.filter (G.Adj w) ⊆ ((N \ X).filter (G.Adj w)) ∪ X.filter (G.Adj w) := by
        intro z hz
        obtain ⟨hzN,ha⟩ := mem_filter.mp hz
        by_cases hzX : z∈X
        · exact mem_union_right _ (mem_filter.mpr ⟨hzX,ha⟩)
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hzN,hzX⟩,ha⟩)
      exact (card_le_card hsub).trans (card_union_le _ _)
    have hle' : ((N.filter (G.Adj w)).card:ℚ) ≤ ((N \ X).filter (G.Adj w)).card + (X.filter (G.Adj w)).card := by exact_mod_cast hle
    linarith
  have hNSsub : N ∩ S ⊆ N \ X := by
    intro w hw
    exact mem_sdiff.mpr ⟨(mem_inter.mp hw).1,fun hh => disjoint_left.mp hSX (mem_inter.mp hw).2 hh⟩
  refine ⟨N \ X,sdiff_disjoint,hNpos.mono hNSsub,?_,?_⟩
  · have hdeg : b ≤ H.card*M := by
      calc
        _ ≤ ∑ _v ∈ H, M := sum_le_sum (fun v hv => (hhigh v (hHS hv)).le)
        _ = _ := by simp [mul_comm]
    have hpn : (H.card:ℚ)≤p := by exact_mod_cast hHp
    have hcN : ((N \ X).card:ℚ)≤N.card := by exact_mod_cast card_le_card sdiff_subset
    have hmul := mul_le_mul_of_nonneg_right hpn hM
    linarith
  · have hdarts : (lam/2)*(N ∩ S).card ≤ (Density.darts G (N \ X)).card := by
      rw [darts_sum]
      push_cast
      calc
        _ = ∑ _w ∈ N ∩ S, lam/2 := by simp [mul_comm]
        _ ≤ ∑ w ∈ N ∩ S, (((N \ X).filter (G.Adj w)).card:ℚ) := sum_le_sum hNdeg
        _ ≤ ∑ w ∈ N \ X, (((N \ X).filter (G.Adj w)).card:ℚ) :=
          sum_le_sum_of_subset_of_nonneg hNSsub (fun _ _ _ => by positivity)
    have hcard : ((N \ X).card:ℚ) ≤ N.card := by exact_mod_cast card_le_card sdiff_subset
    nlinarith

abbrev ContractVertex (H : Finset V) := ↥Hᶜ ⊕ Unit

def contractSet (G : SimpleGraph V) (H : Finset V) : SimpleGraph (ContractVertex H) where
  Adj a b := match a,b with
    | .inl a,.inl b => G.Adj a.val b.val
    | .inl a,.inr _ => ∃ v ∈ H, G.Adj a.val v
    | .inr _,.inl b => ∃ v ∈ H, G.Adj v b.val
    | .inr _,.inr _ => False
  symm := ⟨by
    rintro (a|a) (b|b) h
    · exact h.symm
    · obtain ⟨v,hv,ha⟩ := h; exact ⟨v,hv,ha.symm⟩
    · obtain ⟨v,hv,ha⟩ := h; exact ⟨v,hv,ha.symm⟩
    · exact h⟩
  loopless := ⟨by rintro (a|a) h; exact h.ne rfl; exact h⟩

def contractSet_model (G : SimpleGraph V) (H : Finset V)
    (hc : (G.induce (↑H:Set V)).Connected) : MinorModel G (contractSet G H) where
  branch a := match a with | .inl a => {a.val} | .inr _ => ↑H
  connected a := by
    cases a with
    | inl a => exact Connected.of_subsingleton
    | inr a => exact hc
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    cases a with
    | inl a =>
      have hva : v=a.val := hv
      cases b with
      | inl b => exact hab (congrArg Sum.inl (Subtype.ext (hva.symm.trans hw)))
      | inr b => exact (mem_compl.mp a.property) (hva ▸ hw)
    | inr a =>
      cases b with
      | inl b => exact (mem_compl.mp b.property) ((show v=b.val from hw) ▸ hv)
      | inr b => exact hab (by congr)
  adjacent := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact ⟨_,rfl,_,rfl,h⟩
      | inr b => obtain ⟨v,hv,ha⟩ := h; exact ⟨_,rfl,v,hv,ha⟩
    | inr a =>
      cases b with
      | inl b => obtain ⟨v,hv,ha⟩ := h; exact ⟨v,hv,_,rfl,ha⟩
      | inr b => exact h.elim

lemma contract_card (H : Finset V) :
    Fintype.card (ContractVertex H) = Fintype.card V - H.card + 1 := by
  simp [ContractVertex]

lemma contract_root_degree (G : SimpleGraph V) (H : Finset V) :
    (Density.neighbors (contractSet G H) univ (.inr ())).card = (outside G H).card := by
  symm
  apply card_bij (fun w hw => Sum.inl ⟨w,mem_compl.mpr (((mem_outside _ _ _).mp hw).1)⟩)
  · intro w hw
    obtain ⟨_,v,hv,ha⟩ := (mem_outside _ _ _).mp hw
    exact (Density.mem_neighbors _).mpr ⟨mem_univ _,v,hv,ha⟩
  · intro a ha b hb heq
    exact congrArg Subtype.val (Sum.inl.inj heq)
  · intro a ha
    have h := ((Density.mem_neighbors _).mp ha).2
    cases a with
    | inl a =>
      obtain ⟨v,hv,ha⟩ := h
      refine ⟨a.val,(mem_outside _ _ _).mpr ⟨mem_compl.mp a.property,v,hv,ha⟩,rfl⟩
    | inr a => exact h.elim

lemma contract_remaining_darts (G : SimpleGraph V) (H : Finset V) :
    (Density.darts (contractSet G H) (univ.erase (.inr ()))).card =
      (Density.darts G Hᶜ).card := by
  symm
  apply card_bij (fun e he =>
    (Sum.inl ⟨e.1,((Density.mem_darts G).mp he).1⟩,
     Sum.inl ⟨e.2,((Density.mem_darts G).mp he).2.1⟩))
  · intro e he
    obtain ⟨ha,hb,he⟩ := (Density.mem_darts G).mp he
    exact (Density.mem_darts _).mpr ⟨by simp,by simp,he⟩
  · intro a ha b hb he
    apply Prod.ext
    · exact congrArg Subtype.val (Sum.inl.inj (congrArg Prod.fst he))
    · exact congrArg Subtype.val (Sum.inl.inj (congrArg Prod.snd he))
  · rintro ⟨a,b⟩ he
    obtain ⟨ha,hb,he⟩ := (Density.mem_darts _).mp he
    cases a with
    | inr a => exact (mem_erase.mp ha).1 (by congr) |>.elim
    | inl a =>
      cases b with
      | inr b => exact (mem_erase.mp hb).1 (by congr) |>.elim
      | inl b => exact ⟨(a.val,b.val),(Density.mem_darts G).mpr ⟨a.property,b.property,he⟩,rfl⟩

lemma contract_darts (G : SimpleGraph V) (H : Finset V) :
    2*(contractSet G H).edgeFinset.card = (Density.darts G Hᶜ).card + 2*(outside G H).card := by
  have hh := Density.darts_erase (contractSet G H) (mem_univ (.inr ()))
  rwa [Density.darts_univ,contract_remaining_darts,contract_root_degree] at hh

lemma degree_partition (G : SimpleGraph V) (H : Finset V) (v : V) :
    G.degree v = (H.filter (G.Adj v)).card + (Hᶜ.filter (G.Adj v)).card := by
  have he : G.neighborFinset v = H.filter (G.Adj v) ∪ Hᶜ.filter (G.Adj v) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset,mem_union,mem_filter,mem_compl]
    tauto
  have hd : Disjoint (H.filter (G.Adj v)) (Hᶜ.filter (G.Adj v)) :=
    disjoint_of_subset_left (filter_subset _ _) (disjoint_of_subset_right (filter_subset _ _) disjoint_compl_right)
  rw [←SimpleGraph.card_neighborFinset_eq_degree,he,card_union_of_disjoint hd]

lemma darts_partition (G : SimpleGraph V) (H : Finset V) :
    2*G.edgeFinset.card + (Density.darts G H).card =
      (Density.darts G Hᶜ).card + 2*∑v∈H,G.degree v := by
  have hH : (∑v∈H,G.degree v) = (Density.darts G H).card + ∑v∈H,(Hᶜ.filter (G.Adj v)).card := by
    simp only [degree_partition G H, sum_add_distrib, darts_sum]
  have hC : (∑v∈Hᶜ,G.degree v) = (Density.darts G Hᶜ).card + ∑v∈Hᶜ,(H.filter (G.Adj v)).card := by
    have hh : ∀ v, G.degree v = (Hᶜ.filter (G.Adj v)).card + (H.filter (G.Adj v)).card := by
      intro v; simpa only [compl_compl] using degree_partition G Hᶜ v
    simp only [hh,sum_add_distrib,darts_sum]
  rw [degree_sum_comm] at hH
  have hs := sum_add_sum_compl H (fun v => G.degree v)
  rw [G.sum_degrees_eq_twice_card_edges] at hs
  omega

theorem loss2_contract (G : SimpleGraph V) (H : Finset V) :
    2*(contractSet G H).edgeFinset.card + loss2 G H = 2*G.edgeFinset.card := by
  have h1 := contract_darts G H
  have h2 := darts_partition G H
  have h3 := loss2_identity G H
  omega

lemma expand_card {W : Type} [DecidableEq W] (G : SimpleGraph V) (Q : SimpleGraph W)
    (M : MinorModel G Q) (H : Finset W) :
    (M.expand (↑H:Set W)).toFinset.card = ∑ w ∈ H, (M.branch w).toFinset.card := by
  have he : (M.expand (↑H:Set W)).toFinset = H.biUnion (fun w => (M.branch w).toFinset) := by
    ext v
    rw [@Set.mem_toFinset V (M.expand (↑H:Set W)) _ v]
    simp only [MinorModel.expand, Set.mem_ofPred_eq, mem_coe,mem_biUnion,Set.mem_toFinset]
  rw [he]
  apply card_biUnion
  intro a ha b hb hab
  exact Set.disjoint_toFinset.mpr (M.disjoint a b hab)

structure CheapMinor (G : SimpleGraph V) (p : ℕ) (lam : ℚ) where
  W : Type
  [fintype : Fintype W]
  graph : SimpleGraph W
  model : MinorModel G graph
  sizes : ∀ w, (model.branch w).toFinset.card = 1 ∨ (model.branch w).toFinset.card = p
  budget : (G.edgeFinset.card:ℚ) - graph.edgeFinset.card ≤ lam*(Fintype.card V-(Fintype.card W:ℚ))
  upper : graph.edgeFinset.card ≤ G.edgeFinset.card
attribute [instance] CheapMinor.fintype

noncomputable def CheapMinor.initial (G : SimpleGraph V) (p : ℕ) (lam : ℚ) : CheapMinor G p lam where
  W := V
  graph := G
  model := Knitting.model_singletons G
  sizes w := Or.inl (by
    rw [Set.toFinset_congr (show (Knitting.model_singletons G).branch w = {w} from rfl)]
    simp)
  budget := by simp
  upper := le_rfl

lemma CheapMinor.exists_minimum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (p : ℕ) (lam : ℚ) :
    ∃ M : CheapMinor G p lam, ∀ N : CheapMinor G p lam, Fintype.card M.W ≤ Fintype.card N.W := by
  have hex : ∃ n : ℕ, ∃ M : CheapMinor G p lam, Fintype.card M.W = n :=
    ⟨Fintype.card V,CheapMinor.initial G p lam,rfl⟩
  obtain ⟨M,hm⟩ := Nat.find_spec hex
  exact ⟨M,fun N => hm ▸ Nat.find_min' hex ⟨N,rfl⟩⟩

noncomputable def CheapMinor.big {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) : Finset M.W := univ.filter fun w => (M.model.branch w).toFinset.card=p

lemma CheapMinor.small {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) {w : M.W} (hw : w ∉ M.big) : (M.model.branch w).toFinset.card=1 := by
  have hn : (M.model.branch w).toFinset.card≠p := by simpa [CheapMinor.big] using hw
  exact (M.sizes w).resolve_right hn

lemma CheapMinor.big_card {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) : p*M.big.card ≤ Fintype.card V := by
  classical
  have hh := expand_card G M.graph M.model M.big
  have hs : ∑w∈M.big,(M.model.branch w).toFinset.card = p*M.big.card := by
    calc
      _ = ∑ _w∈M.big,p := sum_congr rfl (fun w hw => (mem_filter.mp hw).2)
      _ = _ := by simp [mul_comm]
  rw [hs] at hh
  exact hh ▸ card_le_univ _

noncomputable def CheapMinor.contract {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) (H : Finset M.W) (hc : (M.graph.induce (↑H:Set M.W)).Connected)
    (hcard : H.card=p) (hsmall : ∀ w ∈ H, w ∉ M.big)
    (hcheap : (loss2 M.graph H:ℚ) ≤ 2*lam*(H.card-1:ℚ)) : CheapMinor G p lam where
  W := ContractVertex H
  graph := contractSet M.graph H
  model := Knitting.compose_model M.model (contractSet_model M.graph H hc)
  sizes w := by
    cases w with
    | inl w =>
      have he : (Knitting.compose_model M.model (contractSet_model M.graph H hc)).branch (.inl w) =
          M.model.branch w.val := by ext v; simp [Knitting.compose_model,MinorModel.expand,contractSet_model]
      rw [he]
      exact M.sizes w.val
    | inr w =>
      right
      change (M.model.expand (↑H:Set M.W)).toFinset.card = p
      rw [expand_card]
      calc
        _ = ∑_w∈H,(1:ℕ) := sum_congr rfl (fun w hw => M.small (hsmall w hw))
        _ = p := by simp [hcard]
  budget := by
    have hcW : H.card ≤ Fintype.card M.W := card_le_univ H
    have he := loss2_contract M.graph H
    have he' : 2*((contractSet M.graph H).edgeFinset.card:ℚ)+(loss2 M.graph H:ℚ)=2*M.graph.edgeFinset.card := by exact_mod_cast he
    have horder : (Fintype.card (ContractVertex H):ℚ)=(Fintype.card M.W:ℚ)-H.card+1 := by
      rw [contract_card,Nat.cast_add,Nat.cast_sub hcW,Nat.cast_one]
    rw [horder]
    have hbudget := M.budget
    nlinarith
  upper := by
    have hh := loss2_contract M.graph H
    have hle : (contractSet M.graph H).edgeFinset.card ≤ M.graph.edgeFinset.card := by omega
    exact hle.trans M.upper

theorem CheapMinor.no_cheap {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) (hp : 2 ≤ p)
    (hmin : ∀ N : CheapMinor G p lam, Fintype.card M.W ≤ Fintype.card N.W)
    (H : Finset M.W) (hc : (M.graph.induce (↑H:Set M.W)).Connected)
    (hcard : H.card=p) (hsmall : ∀ w ∈ H, w ∉ M.big) :
    2*lam*(H.card-1:ℚ) < loss2 M.graph H := by
  by_contra hn
  push Not at hn
  let N := M.contract H hc hcard hsmall hn
  have hh := hmin N
  change Fintype.card M.W ≤ Fintype.card (ContractVertex H) at hh
  rw [contract_card] at hh
  have hcW := card_le_univ H
  omega

lemma kConnected_image {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (f : W → V) (hf : Function.Injective f)
    {S : Finset W} {k : ℕ} (hc : KConnectedOn Q S k)
    (ha : ∀ u ∈ S, ∀ v ∈ S, Q.Adj u v → G.Adj (f u) (f v)) :
    KConnectedOn G (S.image f) k := by
  classical
  refine ⟨by simpa only [card_image_of_injective _ hf] using hc.1,?_⟩
  intro Z hZS hz
  let X := S.filter fun w => f w ∈ Z
  have hXS : X ⊆ S := filter_subset _ _
  have he : X.image f = Z := by
    ext v
    constructor
    · rintro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hw).2
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp (hZS hv)
      exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hv⟩,rfl⟩
  have hx : X.card < k := by rw [←card_image_of_injective X hf,he]; exact hz
  let g : (Q.induce (↑(S \ X):Set W)) →g (G.induce (↑(S.image f \ Z):Set V)) :=
    { toFun := fun w => ⟨f w.val,mem_sdiff.mpr ⟨mem_image.mpr ⟨w.val,(mem_sdiff.mp w.property).1,rfl⟩,
        fun hz => (mem_sdiff.mp w.property).2 (mem_filter.mpr ⟨(mem_sdiff.mp w.property).1,hz⟩)⟩⟩
      map_rel' := fun {u v} huv => ha u.val (mem_sdiff.mp u.property).1 v.val (mem_sdiff.mp v.property).1 huv }
  apply (hc.2 X hXS hx).map g
  intro v
  obtain ⟨w,hw,heq⟩ := mem_image.mp (mem_sdiff.mp v.property).1
  have hwx : w ∈ S \ X := mem_sdiff.mpr ⟨hw,fun hx =>
    (mem_sdiff.mp v.property).2 (heq ▸ (mem_filter.mp hx).2)⟩
  exact ⟨⟨w,hwx⟩,Subtype.ext heq⟩

lemma CheapMinor.lift_small {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) {S : Finset M.W} {k : ℕ}
    (hc : KConnectedOn M.graph S k) (hsmall : Disjoint S M.big) :
    ∃ T : Finset V, KConnectedOn G T k ∧ T.card = S.card := by
  classical
  let f : M.W → V := fun w => (M.model.connected w).nonempty.some.val
  have hfmem : ∀ w, f w ∈ M.model.branch w := fun w => (M.model.connected w).nonempty.some.property
  have hfi : Function.Injective f := by
    intro a b he
    by_contra hn
    exact Set.disjoint_left.mp (M.model.disjoint a b hn) (hfmem a) (he ▸ hfmem b)
  refine ⟨S.image f,kConnected_image f hfi hc ?_,card_image_of_injective _ hfi⟩
  intro u hu v hv huv
  obtain ⟨a,ha,b,hb,hab⟩ := M.model.adjacent huv
  have he (w : M.W) (hw : w ∈ S) {x : V} (hx : x ∈ M.model.branch w) : x=f w := by
    have hcard := M.small (disjoint_left.mp hsmall hw)
    have hm1 : x ∈ (M.model.branch w).toFinset := Set.mem_toFinset.mpr hx
    have hm2 : f w ∈ (M.model.branch w).toFinset := Set.mem_toFinset.mpr (hfmem w)
    exact (card_le_one.mp hcard.le) x hm1 (f w) hm2
  simpa only [he u hu ha,he v hv hb] using hab

def badY (R : SimpleGraph V) (X : Finset V) (d : ℚ) : Finset V :=
  Xᶜ.filter fun v => d/400 ≤ ((X.filter (R.Adj v)).card:ℚ)
def badZ (R : SimpleGraph V) (d : ℚ) (q : ℕ) : Finset V :=
  univ.filter fun v => d*q^4 ≤ (R.degree v:ℚ)
def badSet (R : SimpleGraph V) (X : Finset V) (d : ℚ) (q : ℕ) : Finset V :=
  X ∪ badY R X d ∪ badZ R d q

lemma bad_size (R : SimpleGraph V) (X : Finset V) (n q t : ℕ) (d : ℚ)
    (hq : 1 ≤ q) (ht : 1 ≤ t) (hd : 1280800*t < d)
    (hx : q^5*X.card ≤ n) (hupper : (R.edgeFinset.card:ℚ) ≤ d*n)
    (hinc : ∀ A T : Finset V, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    (q:ℚ)^3*(badSet R X d q).card ≤ 7*n := by
  classical
  have hqr : (1:ℚ) ≤ q := by exact_mod_cast hq
  have htr : (1:ℚ) ≤ t := by exact_mod_cast ht
  have hdpos : 0<d := by nlinarith
  let Y := Xᶜ.filter fun v => d/400 ≤ ((X.filter (R.Adj v)).card:ℚ)
  let Z := univ.filter fun v => d*q^4 ≤ (R.degree v:ℚ)
  let B := X ∪ Y ∪ Z
  have hyX : Disjoint X Y := disjoint_of_subset_right (filter_subset _ _) disjoint_compl_right
  have hyinc := hinc X Y hyX
  have heY : Y.filter (fun v => 3202*t ≤ (X.filter (R.Adj v)).card) = Y := by
    apply filter_eq_self.mpr
    intro v hv
    have hh := (mem_filter.mp hv).2
    have : (3202*t:ℚ) ≤ (X.filter (R.Adj v)).card := by linarith
    exact_mod_cast this
  rw [heY] at hyinc
  have hylo : (t:ℚ)*Y.card ≤ ∑v∈Y,((X.filter (R.Adj v)).card:ℚ) := by
    calc
      _ = ∑_v∈Y,(t:ℚ) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv => by have hh := (mem_filter.mp hv).2; linarith)
  have hy : (Y.card:ℚ) ≤ 4*q^2*X.card := by nlinarith
  have hzlo : d*q^4*Z.card ≤ ∑v∈Z,(R.degree v:ℚ) := by
    calc
      _ = ∑_v∈Z,d*q^4 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv => (mem_filter.mp hv).2)
  have hzup : (∑v∈Z,(R.degree v:ℚ)) ≤ 2*R.edgeFinset.card := by
    calc
      _ ≤ ∑v : V,(R.degree v:ℚ) := sum_le_univ_sum_of_nonneg (fun _ => by positivity)
      _ = _ := by exact_mod_cast R.sum_degrees_eq_twice_card_edges
  have hz : (q:ℚ)^4*Z.card ≤ 2*n := by nlinarith
  have hxn : (q:ℚ)^5*X.card ≤ n := by exact_mod_cast hx
  have hbn : (B.card:ℚ) ≤ X.card+Y.card+Z.card := by
    exact_mod_cast (card_union_le (X ∪ Y) Z).trans (Nat.add_le_add_right (card_union_le X Y) _)
  have hqpow : (q:ℚ)^3 ≤ (q:ℚ)^4 := pow_le_pow_right₀ hqr (by omega)
  have hqpow2 : (q:ℚ)^3 ≤ (q:ℚ)^5 := by
    exact pow_le_pow_right₀ hqr (by omega)
  have hB : (q:ℚ)^3*B.card ≤ 7*n := by
    have h1 := mul_le_mul_of_nonneg_left hbn (show 0≤(q:ℚ)^3 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hy (show 0≤(q:ℚ)^3 by positivity)
    have h3 := mul_le_mul_of_nonneg_right hqpow (show 0≤(Z.card:ℚ) by positivity)
    have h4 := mul_le_mul_of_nonneg_right hqpow2 (show 0≤(X.card:ℚ) by positivity)
    nlinarith
  exact hB

lemma bad_degree_sum (R : SimpleGraph V) (B : Finset V) (n q t : ℕ)
    (hq : 1 ≤ q) (hn : Fintype.card V ≤ n)
    (hB : (q:ℚ)^3*B.card ≤ 7*n)
    (hcoarse : ∀ A : Finset V, ((Density.darts R A).card:ℚ) ≤ 2*t*q*A.card)
    (hinc : ∀ A T : Finset V, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    (∑v∈B,(R.degree v:ℚ)) ≤ 3244*t*n := by
  classical
  have hqr : (1:ℚ)≤q := by exact_mod_cast hq
  have hcross := hinc B Bᶜ disjoint_compl_right
  let U := Bᶜ.filter fun v => 3202*t ≤ (B.filter (R.Adj v)).card
  have hcrossall : (∑v∈Bᶜ,((B.filter (R.Adj v)).card:ℚ)) ≤ 3202*t*n+4*t*q^2*B.card := by
    rw [←sum_filter_add_sum_filter_not Bᶜ (fun v => 3202*t ≤ (B.filter (R.Adj v)).card)]
    have hlo : (∑v∈Bᶜ.filter (fun v => ¬3202*t ≤ (B.filter (R.Adj v)).card),
        ((B.filter (R.Adj v)).card:ℚ)) ≤ 3202*t*n := by
      calc
        _ ≤ ∑_v∈Bᶜ.filter (fun v => ¬3202*t ≤ (B.filter (R.Adj v)).card),(3202*t:ℚ) :=
          sum_le_sum (fun v hv => by exact_mod_cast (le_of_lt (not_le.mp (mem_filter.mp hv).2)))
        _ = (3202*t:ℚ)*(Bᶜ.filter (fun v => ¬3202*t ≤ (B.filter (R.Adj v)).card)).card := by simp [mul_comm]
        _ ≤ 3202*t*n := by gcongr; exact_mod_cast (card_le_univ _).trans hn
    linarith
  have hds : (∑v∈B,(R.degree v:ℚ)) = (Density.darts R B).card +
      ∑v∈Bᶜ,((B.filter (R.Adj v)).card:ℚ) := by
    have he : ∑v∈B,R.degree v = (Density.darts R B).card + ∑v∈Bᶜ,(B.filter (R.Adj v)).card := by
      simp only [degree_partition R B,sum_add_distrib,darts_sum,degree_sum_comm]
    exact_mod_cast he
  have hq1 : (q:ℚ) ≤ (q:ℚ)^3 := by simpa only [pow_one] using (pow_le_pow_right₀ hqr (show 1≤3 by omega))
  have hq2 : (q:ℚ)^2 ≤ (q:ℚ)^3 := pow_le_pow_right₀ hqr (by omega)
  have hdegB : (∑v∈B,(R.degree v:ℚ)) ≤ 3244*t*n := by
    have hc := hcoarse B
    have h1 := mul_le_mul_of_nonneg_right hq1 (show 0≤(B.card:ℚ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hq2 (show 0≤(B.card:ℚ) by positivity)
    have h3 : (q:ℚ)*B.card ≤ 7*n := h1.trans hB
    have h4 : (q:ℚ)^2*B.card ≤ 7*n := h2.trans hB
    have h5 := mul_le_mul_of_nonneg_left h3 (show 0≤2*(t:ℚ) by positivity)
    have h6 := mul_le_mul_of_nonneg_left h4 (show 0≤4*(t:ℚ) by positivity)
    nlinarith
  exact hdegB

theorem bad_set_core (R : SimpleGraph V) (X : Finset V) (n q t : ℕ) (d : ℚ)
    (hq : 1 ≤ q) (ht : 1 ≤ t) (hd : 1280800*t < d)
    (hnposNat : 0 < n) (hn : Fintype.card V ≤ n) (hx : q^5*X.card ≤ n)
    (hupper : (R.edgeFinset.card:ℚ) ≤ d*n)
    (hlower : (99/100:ℚ)*d*n ≤ R.edgeFinset.card)
    (hcoarse : ∀ A : Finset V, ((Density.darts R A).card:ℚ) ≤ 2*t*q*A.card)
    (hinc : ∀ A T : Finset V, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    ∃ S : Finset V, S.Nonempty ∧ Disjoint S X ∧
      (∀ v ∈ S, d/4 ≤ ((S.filter (R.Adj v)).card:ℚ) ∧
        (R.degree v:ℚ)/8 ≤ (S.filter (R.Adj v)).card) ∧
      (∀ v ∈ S, (R.degree v:ℚ) < d*q^4) ∧
      (∀ v ∈ S, ((X.filter (R.Adj v)).card:ℚ) < d/400) := by
  classical
  have hqr : (1:ℚ)≤q := by exact_mod_cast hq
  have htr : (1:ℚ)≤t := by exact_mod_cast ht
  have hdpos : 0<d := by nlinarith
  let B := badSet R X d q
  have hB := bad_size R X n q t d hq ht hd hx hupper hinc
  have hdegB := bad_degree_sum R B n q t hq hn hB hcoarse hinc
  have hnpos : (0:ℚ)<n := by exact_mod_cast hnposNat
  have hremain : (d/4)*Fintype.card V+(1/8:ℚ)*(2*R.edgeFinset.card) <
      ((Density.darts R Bᶜ).card:ℚ)/2 := by
    have hpart : 2*(R.edgeFinset.card:ℚ)+(Density.darts R B).card =
        (Density.darts R Bᶜ).card+2*∑v∈B,(R.degree v:ℚ) := by exact_mod_cast darts_partition R B
    have hnn : (Fintype.card V:ℚ) ≤ n := by exact_mod_cast hn
    have hdnt := mul_lt_mul_of_pos_right hd hnpos
    have hdnn := mul_le_mul_of_nonneg_left hnn hdpos.le
    have hdn := mul_le_mul_of_nonneg_left hupper (by norm_num : (0:ℚ)≤1/4)
    have hnn2 := mul_le_mul_of_nonneg_left hdnn (by norm_num : (0:ℚ)≤1/4)
    have hdarts : (0:ℚ)≤(Density.darts R B).card := by positivity
    linarith
  obtain ⟨S,hS,hSn,hSd⟩ := surviving_core R Bᶜ d hdpos.le hremain
  have hnot (v : V) (hv : v∈S) : v∉B := mem_compl.mp (hS hv)
  refine ⟨S,hSn,?_,hSd,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hx
    exact hnot v hv (mem_union_left _ (mem_union_left _ hx))
  · intro v hv
    by_contra hh
    exact hnot v hv (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,le_of_not_gt hh⟩))
  · intro v hv
    by_contra hh
    have hvX : v∉X := fun hx => hnot v hv (mem_union_left _ (mem_union_left _ hx))
    exact hnot v hv (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_compl.mpr hvX,le_of_not_gt hh⟩)))

theorem district_finite (G : SimpleGraph V) [Nonempty V] (q t k : ℕ)
    (hq : 2 ≤ q) (ht : 1 ≤ t) (hk : 1 ≤ k)
    (hd : max (1280800*t:ℚ) (12800*k) < Knitting.density G)
    (hcoarse : ∀ (W : Type) [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      MinorModel G R → ∀ A : Finset W, ((Density.darts R A).card:ℚ) ≤ 2*t*q*A.card)
    (hinc : ∀ (W : Type) [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      MinorModel G R → ∀ A T : Finset W, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    ∃ S : Finset V, KConnectedOn G S k ∧
      (S.card:ℚ) ≤ Knitting.density G*q^9 := by
  classical
  let d := Knitting.density G
  let lam := d/100
  obtain ⟨M,hmin⟩ := CheapMinor.exists_minimum G (q^5) lam
  have hp : 2≤q^5 := by
    have hh : q ≤ q^5 := by simpa only [pow_one] using (Nat.pow_le_pow_right (by omega : 0<q) (show 1≤5 by omega))
    omega
  have hd1 : (1280800*t:ℚ)<d := (le_max_left _ _).trans_lt hd
  have hd2 : (12800*k:ℚ)<d := (le_max_right _ _).trans_lt hd
  have htr : (1:ℚ)≤t := by exact_mod_cast ht
  have hkr : (1:ℚ)≤k := by exact_mod_cast hk
  have hdpos : 0<d := by nlinarith
  have heq : d*Fintype.card V = G.edgeFinset.card := Knitting.density_mul_order G Fintype.card_pos
  have hup : (M.graph.edgeFinset.card:ℚ) ≤ d*Fintype.card V := by
    rw [heq]; exact_mod_cast M.upper
  have hlo : (99/100:ℚ)*d*Fintype.card V ≤ M.graph.edgeFinset.card := by
    have hh := M.budget
    have ho : (0:ℚ)≤Fintype.card M.W := by positivity
    have hh' : lam*Fintype.card M.W ≥ 0 := by dsimp [lam]; positivity
    dsimp [lam] at hh hh'
    rw [←heq] at hh
    linarith
  obtain ⟨S,hSn,hSX,hSd,hhigh,hXdeg⟩ := bad_set_core M.graph M.big
    (Fintype.card V) q t d (by omega) ht hd1 Fintype.card_pos
    (Knitting.model_card_le M.model) M.big_card hup hlo
    (hcoarse _ M.graph M.model) (hinc _ M.graph M.model)
  have hnocheap : ∀ H ⊆ S, (M.graph.induce (↑H:Set M.W)).Connected → H.card=q^5 →
      2*lam*(H.card-1:ℚ) < loss2 M.graph H := by
    intro H hHS hc hcard
    exact M.no_cheap hp hmin H hc hcard (fun w hw => disjoint_left.mp hSX (hHS hw))
  obtain ⟨N,hNX,hNn,hNcard,hNden⟩ := cheap_neighborhood M.graph S M.big (q^5) lam (d*q^4)
    (by omega) (by dsimp [lam]; linarith) (by positivity) hSn hSX
    (fun v hv => by obtain ⟨ha,hb⟩ := hSd v hv; exact ⟨by dsimp [lam]; linarith,hb⟩)
    hhigh (fun v hv => by have hh := hXdeg v hv; dsimp [lam]; linarith) hnocheap
  have hNpos : (0:ℚ)<N.card := by exact_mod_cast card_pos.mpr hNn
  have hNedges : 4*k*N.card < (Density.darts M.graph N).card := by
    have hh := mul_lt_mul_of_pos_right hd2 hNpos
    have hden : (d/3200)*N.card ≤ (Density.darts M.graph N).card := by
      dsimp [lam] at hNden; linarith
    have : (4*(k:ℚ)*N.card) < (Density.darts M.graph N).card := by linarith
    exact_mod_cast this
  obtain ⟨T,hTN,hTc⟩ := Density.connectivity_of_density M.graph N hk hNedges
  obtain ⟨U,hUc,hUcard⟩ := M.lift_small hTc (disjoint_of_subset_left hTN hNX)
  refine ⟨U,hUc,?_⟩
  calc
    (U.card:ℚ) = T.card := by exact_mod_cast hUcard
    _ ≤ N.card := by exact_mod_cast card_le_card hTN
    _ ≤ (q^5:ℕ)*(d*q^4) := hNcard
    _ = d*q^9 := by push_cast; ring

lemma darts_induce (G : SimpleGraph V) (A : Finset V) :
    (Density.darts G A).card = 2*(G.induce (↑A:Set V)).edgeFinset.card := by
  classical
  rw [darts_sum,←SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp only [CoarseDensity.degree_induce_finset]
  exact (Finset.sum_coe_sort A (fun v => (A.filter (G.Adj v)).card)).symm

lemma coarse_darts (G : SimpleGraph V) {q t : ℕ} (ht : 2≤t)
    (hex : hadwigerNumber G<t) (hl : 100000000*Real.log (2*t) ≤ (q:ℝ))
    (A : Finset V) : ((Density.darts G A).card:ℚ) ≤ 2*t*q*A.card := by
  classical
  let H := G.induce (↑A:Set V)
  have hi := (Knitting.model_induce G A).hadwiger_le.trans_lt hex
  have hd := CoarseDensity.density_bound H ht hi
  have hdq : ((Knitting.density H:ℚ):ℝ) ≤ (t:ℝ)*q := by
    calc
      _ ≤ 100000000*t*Real.log (2*t) := hd
      _ = (t:ℝ)*(100000000*Real.log (2*t)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  by_cases hA : A.Nonempty
  · have hn : 0<Fintype.card (↑A:Set V) := by simpa using card_pos.mpr hA
    have he := Knitting.density_mul_order H hn
    have he' : ((Knitting.density H:ℚ):ℝ)*A.card = H.edgeFinset.card := by
      have hr := congrArg (fun x : ℚ => (x:ℝ)) he
      convert hr using 1 <;> simp
      congr 1
    have hh := mul_le_mul_of_nonneg_right hdq (show (0:ℝ)≤A.card by positivity)
    rw [he'] at hh
    rw [darts_induce]
    have : (2*(H.edgeFinset.card:ℝ)) ≤ 2*t*q*A.card := by linarith
    exact_mod_cast this
  · have he : A=∅ := not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [Density.darts]

open Filter Real Asymptotics in
lemma district_cutoff : ∀ᶠ z : ℝ in atTop,
    2 ≤ z ∧ 2 ≤ z^(1/200:ℝ) ∧ 1024 ≤ z^(1/100:ℝ) ∧
      100000000*Real.log (2*z) ≤ z^(1/200:ℝ) := by
  have h1 := (tendsto_atTop.mp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200))) 2
  have h2 := (tendsto_atTop.mp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100))) 1024
  filter_upwards [Incidence.incidence_cutoff,h1,h2] with z hz hz1 hz2
  exact ⟨hz.1,hz1,hz2,hz.2.2.2.2⟩

lemma district_order {t q : ℕ} (ht : (2:ℝ)≤t)
    (hq : (q:ℝ)≤2*(t:ℝ)^(1/200:ℝ))
    (hpow : (1024:ℝ)≤(t:ℝ)^(1/100:ℝ)) :
    (t:ℝ)*q^10 ≤ (t:ℝ)^(53/50:ℝ) := by
  have htpos : (0:ℝ)<t := by linarith
  have he : (t:ℝ)*((t:ℝ)^(1/200:ℝ))^10 = (t:ℝ)^(21/20:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul htpos.le]
    calc
      _ = (t:ℝ)^(1:ℝ)*(t:ℝ)^((1/200:ℝ)*(10:ℝ)) := by norm_num
      _ = _ := by rw [←Real.rpow_add htpos]; norm_num
  have hp := pow_le_pow_left₀ (show (0:ℝ)≤q by positivity) hq 10
  calc
    _ ≤ (t:ℝ)*(2*(t:ℝ)^(1/200:ℝ))^10 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 1024*((t:ℝ)*((t:ℝ)^(1/200:ℝ))^10) := by ring
    _ = 1024*(t:ℝ)^(21/20:ℝ) := by rw [he]
    _ ≤ (t:ℝ)^(1/100:ℝ)*(t:ℝ)^(21/20:ℝ) := by gcongr
    _ = _ := by rw [←Real.rpow_add htpos]; norm_num

theorem district : Statement := by
  classical
  intro K hK
  let D := max 1280800 (12800*K)+1
  refine ⟨D,by dsimp [D]; norm_num,?_⟩
  obtain ⟨t₁,ht₁⟩ := Incidence.incidence_bound
  obtain ⟨t₂,ht₂⟩ := Filter.eventually_atTop.mp district_cutoff.natCast_atTop
  refine ⟨max t₁ t₂,?_⟩
  intro t htt W _ _ _ P hex hedges
  obtain ⟨htr,hpow2,hpow1024,hlog⟩ := ht₂ t (le_trans (le_max_right _ _) htt)
  have ht : 2≤t := by exact_mod_cast htr
  have htpos : (0:ℝ)<t := by linarith
  let q := Nat.ceil ((t:ℝ)^(1/200:ℝ))
  have hqlo : (t:ℝ)^(1/200:ℝ) ≤ q := Nat.le_ceil _
  have hq : 2≤q := by exact_mod_cast hpow2.trans hqlo
  have hqhi : (q:ℝ)≤2*(t:ℝ)^(1/200:ℝ) := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg htpos.le (1/200:ℝ))
    change (q:ℝ)<(t:ℝ)^(1/200:ℝ)+1 at hh
    linarith
  have hlogq : 100000000*Real.log (2*t) ≤ (q:ℝ) := hlog.trans hqlo
  have hdense : (D*t:ℚ) ≤ Knitting.density P := by
    have hn : (0:ℚ)<Fintype.card W := by exact_mod_cast Fintype.card_pos
    apply (le_div_iff₀ hn).mpr
    exact_mod_cast hedges
  have hD1 : (1280800:ℚ)<D := by exact_mod_cast (show 1280800<D by dsimp [D]; omega)
  have hD2 : (12800*K:ℚ)<D := by exact_mod_cast (show 12800*K<D by dsimp [D]; omega)
  have htq : (0:ℚ)<t := by exact_mod_cast (show 0<t by omega)
  have hden : max (1280800*t:ℚ) (12800*(K*t)) < Knitting.density P := by
    apply max_lt
    · exact (mul_lt_mul_of_pos_right hD1 htq).trans_le hdense
    · have hh := mul_lt_mul_of_pos_right hD2 htq
      nlinarith
  have hpowinc : (t:ℝ)^(101/100:ℝ) ≤ 4*t*q^2 := by
    have he : (t:ℝ)^(101/100:ℝ) = (t:ℝ)*((t:ℝ)^(1/200:ℝ))^2 := by
      rw [←Real.rpow_natCast,←Real.rpow_mul htpos.le]
      calc
        _ = (t:ℝ)^((1:ℝ)+(1/200:ℝ)*2) := by norm_num
        _ = _ := by rw [Real.rpow_add htpos,Real.rpow_one]; norm_num
    rw [he]
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg htpos.le _) hqlo 2
    have hx := mul_le_mul_of_nonneg_left hh htpos.le
    nlinarith [sq_nonneg (q:ℝ)]
  obtain ⟨S,hSc,hScard⟩ := district_finite P q t (K*t) hq (by omega) (by nlinarith) (by simpa only [Nat.cast_mul] using hden)
    (fun U _ _ R M A => coarse_darts R ht (M.hadwiger_le.trans_lt hex) hlogq A)
    (by
      intro U _ _ R M A T hdis
      have hh := ht₁ t (le_trans (le_max_left _ _) htt) U R
        (M.hadwiger_le.trans_lt hex) A T hdis
      have hp := mul_le_mul_of_nonneg_right hpowinc (show (0:ℝ)≤A.card by positivity)
      have hbound : (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℝ)) ≤ 4*t*q^2*A.card := hh.trans hp
      exact_mod_cast hbound)
  refine ⟨S,hSc,?_⟩
  have hd := CoarseDensity.density_bound P ht hex
  have hdq : ((Knitting.density P:ℚ):ℝ) ≤ (t:ℝ)*q := by
    have hh := mul_le_mul_of_nonneg_left hlogq htpos.le
    nlinarith
  have hcard : (S.card:ℝ) ≤ ((Knitting.density P:ℚ):ℝ)*q^9 := by exact_mod_cast hScard
  have hm := mul_le_mul_of_nonneg_right hdq (show (0:ℝ)≤(q:ℝ)^9 by positivity)
  calc
    _ ≤ ((Knitting.density P:ℚ):ℝ)*q^9 := hcard
    _ ≤ (t:ℝ)*q*q^9 := hm
    _ = (t:ℝ)*q^10 := by ring
    _ ≤ _ := district_order htr hqhi hpow1024

end
end LinearListHadwiger.District

end OAI
