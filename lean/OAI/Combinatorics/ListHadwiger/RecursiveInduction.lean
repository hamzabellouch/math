import OAI.Combinatorics.ListHadwiger.RecursiveJunction

namespace OAI

namespace LinearListHadwiger.Recursion
open Finset Stage SmallList SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma neighbors_on {O : Type} [Fintype O] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Z : Finset V) (port : O → V) (hp : ∀ o, port o∈S) {k : ℕ}
    (hc : KConnectedOn G S k) (hk : Fintype.card O+Z.card≤k) :
    ∃ n : O → V, Function.Injective n ∧ ∀ o, n o∈S\Z ∧ G.Adj (port o) (n o) := by
  classical
  apply Assembly.attach_ports G port (S\Z)
  intro o
  have hdeg := Knitting.min_degree G hc (hp o)
  have he : Density.neighbors G S (port o) \ Z=(S\Z).filter (G.Adj (port o)) := by
    ext v
    simp only [Density.neighbors,mem_sdiff,mem_filter]
    tauto
  have hh := card_le_card (show Density.neighbors G S (port o)⊆
    Density.neighbors G S (port o)\Z∪Z from fun v hv => by
      by_cases hz : v∈Z
      · exact mem_union_right _ hz
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hv,hz⟩))
  have hu := card_union_le (Density.neighbors G S (port o)\Z) Z
  rw [he] at hh hu
  have hbound : Fintype.card O≤((S\Z).filter (G.Adj (port o))).card := by omega
  exact hbound

omit [Fintype V] in
lemma connected_induce_univ (G : SimpleGraph V) (J : Finset V) {k : ℕ}
    (hc : KConnectedOn G J k) : KConnectedOn (G.induce (↑J:Set V)) univ k := by
  have hh := under_connected G (U:=J) (A:=J) (subset_refl J) hc
  have he : under J J=univ := by ext v; simp [under]
  rwa [he] at hh

theorem fresh_model : ∃ S : ℕ, 1≤S ∧ ∃ T : ℕ, 1≤T ∧
    ∀ a K Q : ℕ, 1≤a → 1≤K → T≤64*a →
    (∀ (W : Type) [Fintype W] [DecidableEq W] (P : SimpleGraph W),
      KConnectedOn P univ (K*child a) → Q*child a≤listChromaticNumber P →
      Woven P (child a) (3*child a) ∨ FractionalObstruction P) →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (H : Finset V) (r : Fin a → V), Function.Injective r → (∀ i, r i∈H) →
      hadwigerNumber G<64*a → KConnectedOn G H (K₀*(64*a)) →
      3*S*(64*a)+3*a≤ell G H →
      Q*child a+6*(K*child a)+2*S*(64*a)+3*a<ell G H →
      (∃ M : RootedCliqueModel G r, ∀ i, M.branch i⊆(↑H:Set V)) ∨ FractionalObstruction G := by
  obtain ⟨S,hS,T,hT,hs⟩ := three_regions
  refine ⟨S,hS,T,hT,?_⟩
  intro a K Q ha hK ht ih V _ _ G H r hr hrH hm hc hsep hl
  classical
  let R := univ.image r
  have hR : R.card=a := by simp only [R,card_image_of_injective _ hr,card_univ,Fintype.card_fin]
  have hRH : R⊆H := by rintro v hv; obtain ⟨i,_,rfl⟩ := mem_image.mp hv; exact hrH i
  obtain ⟨n,hn,hnH⟩ := neighbors_on G H R (fun o : Fin a × Fin 2 => r o.1)
    (fun _ => hrH _) hc (by simp only [Fintype.card_prod,Fintype.card_fin,hR]; dsimp [K₀]; omega)
  let N := univ.image n
  have hN : N.card=2*a := by simp only [N,card_image_of_injective _ hn,card_univ,Fintype.card_prod,Fintype.card_fin]; omega
  let B := R∪N
  have hB : B.card≤3*a := by have := card_union_le R N; dsimp [B]; omega
  have hdel := ell_delete G H B
  have ha' : 1≤child a := by unfold child; omega
  rcases hs (64*a) ht V G (H\B) (K*child a) (Q*child a) (by nlinarith) hm
    (by omega) (by omega) with ⟨J,hJH,hJJ,hJc,hJl⟩|hb
  swap
  · exact Or.inr hb
  have hchild (d : Fin 3) : WovenOn G (↑(J d):Set V) (child a) (3*child a) ∨ FractionalObstruction G := by
    rcases ih (↑(J d):Set V) (G.induce (↑(J d):Set V))
      (connected_induce_univ G (J d) (hJc d)) (Nat.le_of_lt (hJl d)) with hw|hb
    · exact Or.inl (woven_induce G (J d) hw)
    · exact Or.inr (obstruction_induce G (J d) hb)
  by_cases hb : FractionalObstruction G
  · exact Or.inr hb
  have hw (d) : WovenOn G (↑(J d):Set V) (child a) (3*child a) := (hchild d).resolve_right hb
  have hroots (d : Fin 3) : ∃ u : Fin (child a) → V,
      Function.Injective u ∧ ∀ i, u i∈J d := by
    apply choose_vertices
    have hh := (hJc d).1
    nlinarith
  choose u hu huJ using hroots
  have hconn : KConnectedOn G (H\univ.image r) (65536*(4*a)) := by
    apply Knitting.kConnected_mono (Knitting.delete_connected G hc hRH (by rw [hR]; dsimp [K₀]; omega))
    rw [hR]
    dsimp [K₀]
    omega
  apply Or.inl
  apply three_district_model G ha H r hr hrH n hn
    (fun o => (mem_sdiff.mp (hnH o).1).1)
    (fun o i he => (mem_sdiff.mp (hnH o).1).2 (he ▸ mem_image.mpr ⟨i,mem_univ _,rfl⟩))
    (fun o => (hnH o).2.symm) (fun d => (↑(J d):Set V))
    (fun d => (hJH d).trans sdiff_subset) ?_ ?_ (fun d e hne => by exact_mod_cast hJJ d e hne)
    hw u hu huJ hconn
  · intro d i hi
    exact (mem_sdiff.mp (hJH d hi)).2 (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))
  · intro d o ho
    exact (mem_sdiff.mp (hJH d ho)).2 (mem_union_right _ (mem_image.mpr ⟨o,mem_univ _,rfl⟩))

end LinearListHadwiger.Recursion

namespace LinearListHadwiger.Recursion
open Finset Stage SmallList SimpleGraph
attribute [local instance] Classical.propDecidable

theorem recursive_woven_or_obstruction : ∃ K Q : ℕ, 100≤K ∧ 1≤Q ∧
    ∀ a : ℕ, 1≤a → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      KConnectedOn G univ (K*a) → Q*a≤listChromaticNumber G →
      Woven G a (3*a) ∨ FractionalObstruction G := by
  obtain ⟨A,hA,T₁,hT₁,houter⟩ := outer_region
  obtain ⟨S,hS,T₂,hT₂,hfresh⟩ := fresh_model
  let K := A+100
  let a₀ := max 24 (max T₁ T₂)
  let B := ⌊(200000000:ℝ)*(64*a₀:ℕ)*Real.log (2*(64*a₀:ℕ))⌋₊+1
  let c : ℕ := 4*32768+42+5+6*K₀
  let Q := B+A+18*K+512*S+40+256*c+1
  have hK : 100≤K := by dsimp [K]; omega
  have hQ : 1≤Q := by dsimp [Q]; omega
  have hQA : A+7<Q := by dsimp [Q]; omega
  have hQbig : 18*K+512*S+40+256*c<Q := by dsimp [Q]; omega
  have hQB : B<Q := by dsimp [Q]; omega
  refine ⟨K,Q,hK,hQ,?_⟩
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro ha V _ _ G hc hl
    classical
    have hka : 100*a≤K*a := Nat.mul_le_mul_right a hK
    by_cases hminor : 64*a≤hadwigerNumber G
    · exact Or.inl (large_minor_woven G ha (Knitting.kConnected_mono hc hka) hminor)
    have hm : hadwigerNumber G<64*a := by omega
    have ha₀ : a₀<a := by
      by_contra hn
      have hma : hadwigerNumber G<64*a₀ := hm.trans_le (by omega)
      have hb := CoarseDensity.coarse_list_bound G (show 2≤64*a₀ by dsimp [a₀]; omega) hma
      change listChromaticNumber G≤B at hb
      nlinarith only [ha,hl,hQB,hb]
    have hac : 24<a := (le_max_left _ _).trans_lt ha₀
    obtain ⟨hcpos,hclt,hcshrink⟩ := child_shrink hac
    have ht₁ : T₁≤64*a := by have := (le_max_left T₁ T₂).trans (le_max_right 24 _); omega
    have ht₂ : T₂≤64*a := by have := (le_max_right T₁ T₂).trans (le_max_right 24 _); omega
    by_cases hbad : FractionalObstruction G
    · exact Or.inr hbad
    left
    intro roots hr _ p hp x y _ hxy
    let O := Fin a ⊕ (Fin p × Bool)
    let port : O → V := Sum.elim roots (fun z => if z.2 then y z.1 else x z.1)
    let Z := univ.image port
    have hO : Fintype.card O=a+2*p := by simp [O]; omega
    have hZ : Z.card≤7*a := by
      have hh := card_image_le (s:=univ) (f:=port)
      rw [card_univ,hO] at hh
      calc Z.card≤a+2*p := hh
           _≤7*a := by omega
    obtain ⟨proxy,hproxy,hadj⟩ := distinct_proxies G port Z hc
      (show Fintype.card O+Z.card≤K*a by rw [hO]; omega)
    let R := univ\Z
    let P := G.induce (↑R:Set V)
    let proxy' (o : O) : (↑R:Set V) := ⟨proxy o,mem_sdiff.mpr ⟨mem_univ _,(hadj o).1⟩⟩
    have hproxy' : Function.Injective proxy' := fun i j he => hproxy (congrArg Subtype.val he)
    let e : (Fin p × Bool) ≃ Fin (2*p) := Fintype.equivOfCardEq (by simp; omega)
    let r (i : Fin a) := proxy' (.inl i)
    let n (j : Fin (2*p)) := proxy' (.inr (e.symm j))
    have hr' : Function.Injective r := hproxy'.comp Sum.inl_injective
    have hn' : Function.Injective n := hproxy'.comp (Sum.inr_injective.comp e.symm.injective)
    have hrn (i j) : r i≠n j := by intro he; cases hproxy' he
    have hcR : KConnectedOn G R (30*a) := by
      apply Knitting.kConnected_mono (Knitting.delete_connected G hc (subset_univ Z) (by omega))
      omega
    have hcP : KConnectedOn P univ (30*a) := connected_induce_univ G R hcR
    have hmP : hadwigerNumber P<64*a := (Knitting.model_induce G R).hadwiger_le.trans_lt hm
    have hdel := ell_delete G univ Z
    rw [ell_univ] at hdel
    change listChromaticNumber G≤listChromaticNumber P+Z.card at hdel
    have hQAa := Nat.mul_lt_mul_of_pos_right hQA (show 0<a by omega)
    have hPA : A*a<listChromaticNumber P := by nlinarith only [hQAa,hdel,hl,hZ]
    have noP : ¬FractionalObstruction P := fun hb => hbad (obstruction_induce G R hb)
    obtain ⟨H,D,U,⟨routing⟩,hHD,hHc,hDc,hHl⟩ :=
      (houter a ha ht₁ p hp (↑R:Set V) P r n hr' hn' hrn hcP hmP hPA).resolve_right noP
    have hcall (W : Type) [Fintype W] [DecidableEq W] (L : SimpleGraph W)
        (hconn : KConnectedOn L univ (K*child a)) (hlist : Q*child a≤listChromaticNumber L) :
        Woven L (child a) (3*child a) ∨ FractionalObstruction L :=
      ih (child a) hclt hcpos W L hconn hlist
    have hsep : 3*S*(64*a)+3*a≤ell P H := by
      change listChromaticNumber P≤ell P H+c*(64*a) at hHl
      have hb : 192*S+10+64*c<Q := by omega
      have hh := Nat.mul_lt_mul_of_pos_right hb (show 0<a by omega)
      nlinarith only [hh,hHl,hdel,hl,hZ]
    have hstep : Q*child a+6*(K*child a)+2*S*(64*a)+3*a<ell P H := by
      change listChromaticNumber P≤ell P H+c*(64*a) at hHl
      have hq := Nat.mul_le_mul_left Q hcshrink
      have hk := Nat.mul_le_mul_left (6*K) hcshrink
      have hh := Nat.mul_lt_mul_of_pos_right hQbig (show 0<a by omega)
      nlinarith only [hh,hq,hk,hHl,hdel,hl,hZ]
    obtain ⟨M,hMH⟩ := (hfresh a K Q ha (by omega) ht₂ hcall (↑R:Set V) P H routing.fresh
      routing.fresh_injective routing.fresh_mem hmP hHc hsep hstep).resolve_right noP
    have hgroup : KConnectedOn P D (65536*Fintype.card (Roles a (2*p))) := by
      apply Knitting.kConnected_mono hDc
      simp only [Roles,Fintype.card_sum,Fintype.card_fin]
      dsimp [K₀]
      omega
    obtain ⟨C₀,hC₀,hCC₀,hE₀,hrC₀,hnC₀⟩ := junction_groups P ha r n e H D _ U hHD routing M hMH hgroup
    let lift := Knitting.model_induce G R
    let C (i : Fin a ⊕ Fin p) := lift.expand (C₀ i)
    have hC (i) : (G.induce (C i)).Connected := lift.expand_connected (hC₀ i)
    have hCC (i j) (hij : i≠j) : Disjoint (C i) (C j) := lift.expand_disjoint (hCC₀ i j hij)
    have hCZ (i v) (hv : v∈C i) : v∉Z := by
      obtain ⟨w,_,hw⟩ := hv
      have he : v=w.val := hw
      exact he ▸ (mem_sdiff.mp w.property).2
    have hpZ (o : O) : port o∈Z := mem_image.mpr ⟨o,mem_univ _,rfl⟩
    apply weaving_from_proxy_groups G roots x y hr hxy C hC hCC
      (fun i j hv => hCZ i _ hv (hpZ (.inl j)))
      (fun i j hv => hCZ i _ hv (hpZ (.inr (j,false))))
      (fun i j hv => hCZ i _ hv (hpZ (.inr (j,true))))
    · intro i j hij
      obtain ⟨v,hv,w,hw,he⟩ := hE₀ i j hij
      exact ⟨v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,he⟩
    · intro i
      exact ⟨proxy (.inl i),⟨r i,hrC₀ i,rfl⟩,(hadj (.inl i)).2⟩
    · intro i
      have hh := hnC₀ (i,false)
      have he : n (e (i,false))=proxy' (.inr (i,false)) := by simp [n]
      rw [he] at hh
      exact ⟨proxy (.inr (i,false)),⟨proxy' (.inr (i,false)),hh,rfl⟩,(hadj (.inr (i,false))).2⟩
    · intro i
      have hh := hnC₀ (i,true)
      have he : n (e (i,true))=proxy' (.inr (i,true)) := by simp [n]
      rw [he] at hh
      exact ⟨proxy (.inr (i,true)),⟨proxy' (.inr (i,true)),hh,rfl⟩,(hadj (.inr (i,true))).2⟩

end LinearListHadwiger.Recursion

end OAI
