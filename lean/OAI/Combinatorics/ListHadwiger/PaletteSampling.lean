import OAI.Combinatorics.ListHadwiger.StagePacking

namespace OAI

namespace LinearListHadwiger.Sampling
open Finset ConnectivityTests
variable {V Ω : Type} [Fintype V] [DecidableEq V] [Fintype Ω]

theorem complement_failure_thousand (G : SimpleGraph V) [DecidableRel G.Adj]
    {n r ε : ℝ} {k : ℕ} (hk : 64 ≤ k) (hr : 0 < r) (hrk : r ≤ k)
    (hord : (Fintype.card V : ℝ) ≤ n) (hconn : KConnectedOn G univ k)
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (U : Ω → Finset V)
    (hsurv : ∀ v, probability μ (fun ω => v ∈ U ω) ≤ 1/1000)
    (hε : 0 ≤ ε)
    (htail : ∀ A : Finset V, probability μ (fun ω => r/100 ≤
      |((U ω ∩ A).card : ℝ)-expectation μ (fun z => ((U z ∩ A).card : ℝ))|) ≤ ε) :
    probability μ (fun ω => ¬((∀ v, k ≤ 2*((univ \ U ω).filter (G.Adj v)).card) ∧
      KConnectedOn G (univ \ U ω) (k/32))) ≤
      (n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1))*ε := by
  classical
  obtain ⟨F,hFcard,hF,hFtest⟩ := cut_test G hk hord hconn
  have hD (v : V) : ∃ D ⊆ Density.neighbors G univ v, D.card=k :=
    exists_subset_card_eq (Knitting.min_degree G hconn (mem_univ v))
  choose D hD hDc using hD
  let Idx := V ⊕ ↥F
  let A : Idx → Finset V := fun i => match i with
    | .inl v => D v
    | .inr E => endpoints E.val
  let bad : Idx → Ω → Prop := fun i ω => r/100 ≤
    |((U ω ∩ A i).card : ℝ)-expectation μ (fun z => ((U z ∩ A i).card : ℝ))|
  have hbad (i : Idx) : probability μ (bad i) ≤ ε := htail (A i)
  have hgood (ω : Ω) (havoid : ∀ i, ¬bad i ω) :
      (∀ v, k ≤ 2*((univ \ U ω).filter (G.Adj v)).card) ∧
      KConnectedOn G (univ \ U ω) (k/32) := by
    have hsmall (i : Idx) (hAk : (A i).card ≤ k) : 32*(U ω ∩ A i).card < k := by
      have he := expectation_inter_card_le U hsurv (A i)
      have hAc : ((A i).card : ℝ) ≤ k := by exact_mod_cast hAk
      have hm : expectation μ (fun z => ((U z ∩ A i).card : ℝ)) ≤ (k:ℝ)/1000 := by
        nlinarith
      have hdev := (abs_lt.mp (lt_of_not_ge (havoid i))).2
      have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hh : (32:ℝ)*((U ω ∩ A i).card : ℝ) < k := by
        nlinarith
      exact_mod_cast hh
    have hneigh (v : V) : k ≤ 2*((univ \ U ω).filter (G.Adj v)).card := by
      have hc := hsmall (.inl v) (by dsimp [A]; exact (hDc v).le)
      have hd : (D v \ U ω).card+(D v ∩ U ω).card=k := by
        rw [card_sdiff_add_card_inter,hDc]
      have hsub : D v \ U ω ⊆ (univ \ U ω).filter (G.Adj v) := by
        intro w hw
        obtain ⟨hwD,hwU⟩ := mem_sdiff.mp hw
        have hadj := hD v hwD
        simp only [Density.neighbors,mem_filter,mem_univ,true_and] at hadj
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hwU⟩,hadj⟩
      have hcard := card_le_card hsub
      dsimp [A] at hc
      rw [inter_comm] at hc
      omega
    refine ⟨hneigh,hFtest (U ω) hneigh ?_⟩
    intro E hE
    have he := (hF E hE).1
    have hcard : (endpoints E).card ≤ k := by
      have hb := endpoints_card_le E
      have hd := Nat.div_mul_le_self k 8
      omega
    have hc := hsmall (.inr ⟨E,hE⟩) hcard
    simpa [A,inter_comm] using hc
  have hprob : probability μ (fun ω => ¬((∀ v, k ≤ 2*((univ \ U ω).filter (G.Adj v)).card) ∧
      KConnectedOn G (univ \ U ω) (k/32))) ≤ probability μ (fun ω => ∃ i, bad i ω) := by
    apply probability_mono hμ
    intro ω h
    by_contra hn
    push Not at hn
    exact h (hgood ω hn)
  calc
    _ ≤ probability μ (fun ω => ∃ i, bad i ω) := hprob
    _ ≤ ∑ i, probability μ (bad i) := probability_union_le hμ bad
    _ ≤ ∑ _ : Idx, ε := sum_le_sum (fun i _ => hbad i)
    _ = ((Fintype.card V : ℝ)+F.card)*ε := by simp [Idx]
    _ ≤ _ := by gcongr

noncomputable def coin (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

lemma coin_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ coin p b := by cases b <;> simp [coin] <;> linarith

lemma coin_sum (p : ℝ) : ∑ b : Bool, coin p b = 1 := by
  simp [coin]

noncomputable def chosen (x : V → Bool) : Finset V := univ.filter (fun v => x v = true)

lemma chosen_marginal (p : ℝ) (v : V) :
    probability (productMass (fun _ : V => coin p)) (fun x => v ∈ chosen x) = p := by
  classical
  have he : (fun x : V → Bool => v ∈ chosen x) = (fun x => x v = true) := by
    funext x
    simp [chosen]
  rw [he,probability_coordinate (fun _ => coin_sum p) v (fun b => b = true)]
  simp [probability,coin]

lemma chosen_mean (p : ℝ) (D : Finset V) :
    expectation (productMass (fun _ : V => coin p))
      (fun x => ((chosen x ∩ D).card : ℝ)) = (D.card : ℝ)*p := by
  rw [expectation_inter_card]
  simp only [chosen_marginal,sum_const,nsmul_eq_mul]

lemma chosen_bounded_change (D : Finset V) (i : V) (x y : V → Bool)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    |((chosen x ∩ D).card : ℝ)-(chosen y ∩ D).card| ≤ 1 := by
  classical
  have he : (chosen x ∩ D).erase i = (chosen y ∩ D).erase i := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [chosen,hj,hxy j hj]
  have hx := card_erase_le (s := chosen x ∩ D) (a := i)
  have hy := card_erase_le (s := chosen y ∩ D) (a := i)
  have hx' := pred_card_le_card_erase (s := chosen x ∩ D) (a := i)
  have hy' := pred_card_le_card_erase (s := chosen y ∩ D) (a := i)
  have hec := congrArg Finset.card he
  have h₁ : (chosen x ∩ D).card ≤ (chosen y ∩ D).card+1 := by omega
  have h₂ : (chosen y ∩ D).card ≤ (chosen x ∩ D).card+1 := by omega
  have h₁r : ((chosen x ∩ D).card : ℝ) ≤ (chosen y ∩ D).card+1 := by exact_mod_cast h₁
  have h₂r : ((chosen y ∩ D).card : ℝ) ≤ (chosen x ∩ D).card+1 := by exact_mod_cast h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma chosen_concentration {p u : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hn : 1 ≤ Fintype.card V) (hu : 0 < u) (D : Finset V) :
    probability (productMass (fun _ : V => coin p))
      (fun x => u ≤ |((chosen x ∩ D).card : ℝ)-(D.card : ℝ)*p|) ≤
      2*Real.exp (-u^2/(2*Fintype.card V)) := by
  have hh := bounded_differences_general hn (fun _ : V => coin p)
    (fun _ => coin_nonneg hp hp1) (fun _ => coin_sum p)
    (fun x => ((chosen x ∩ D).card : ℝ)) (by norm_num : (0:ℝ)<1) hu
    (chosen_bounded_change D)
  simpa only [chosen_mean,one_pow,mul_one] using hh

theorem exists_sparse_split {I : Type} [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {n : ℝ}
    (hk : 64 ≤ k) (hord : (Fintype.card V : ℝ) ≤ n)
    (hc : KConnectedOn G univ k) (D : I → Finset V)
    (hD : ∀ i, (D i).card = k)
    (hsmall : ((Fintype.card I : ℝ)+n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1)) *
      (2*Real.exp (-((k:ℝ)/2000)^2/(2*Fintype.card V))) < 1) :
    ∃ A : Finset V,
      (∀ i, k ≤ 2000*(A ∩ D i).card ∧ k ≤ 2*((univ \ A) ∩ D i).card) ∧
      KConnectedOn G (univ \ A) (k/32) := by
  classical
  let μ := productMass (fun _ : V => coin (1/1000))
  let ε := 2*Real.exp (-((k:ℝ)/2000)^2/(2*Fintype.card V))
  have hkpos : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have hn : 1 ≤ Fintype.card V := by
    have hh := hc.1
    simp only [card_univ] at hh
    omega
  have hμ : ∀ x, 0 ≤ μ x := productMass_nonneg
    (fun _ => coin_nonneg (by norm_num) (by norm_num))
  have hμs : ∑ x, μ x = 1 := productMass_sum (fun _ => coin_sum _)
  let bad (i : I) (x : V → Bool) : Prop := ¬(k ≤ 2000*(chosen x ∩ D i).card ∧
    k ≤ 2*((univ \ chosen x) ∩ D i).card)
  have hbad (i : I) : probability μ (bad i) ≤ ε := by
    have hh := chosen_concentration (V := V) (p := 1/1000) (by norm_num)
      (by norm_num) hn (show (0:ℝ)<k/2000 by positivity) (D i)
    refine (probability_mono hμ ?_).trans hh
    intro x hx
    by_contra hd
    have hdev := abs_lt.mp (lt_of_not_ge hd)
    rw [hD i] at hdev
    have he : ((univ \ chosen x) ∩ D i).card + (chosen x ∩ D i).card = k := by
      rw [show (univ \ chosen x) ∩ D i = D i \ chosen x by ext; simp; tauto,
        inter_comm (chosen x)]
      exact (card_sdiff_add_card_inter _ _).trans (hD i)
    have he' : (((univ \ chosen x) ∩ D i).card : ℝ) + (chosen x ∩ D i).card = k := by
      exact_mod_cast he
    apply hx
    constructor
    · have hh : (k:ℝ) ≤ 2000*(chosen x ∩ D i).card := by linarith
      exact_mod_cast hh
    · have hh : (k:ℝ) ≤ 2*((univ \ chosen x) ∩ D i).card := by linarith
      exact_mod_cast hh
  let cbad (x : V → Bool) : Prop := ¬((∀ v,
    k ≤ 2*((univ \ chosen x).filter (G.Adj v)).card) ∧
    KConnectedOn G (univ \ chosen x) (k/32))
  have hcomp : probability μ cbad ≤
      (n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1))*ε := by
    apply complement_failure_thousand G hk hkpos le_rfl hord hc hμ chosen
    · intro v
      exact (chosen_marginal (1/1000) v).le
    · dsimp [ε]; positivity
    · intro A
      have hh := chosen_concentration (V := V) (p := 1/1000) (by norm_num)
        (by norm_num) hn (show (0:ℝ)<k/2000 by positivity) A
      refine (probability_mono hμ ?_).trans hh
      intro x hx
      rw [chosen_mean] at hx
      exact (by linarith : (k:ℝ)/2000 ≤ k/100).trans hx
  have hfail : probability μ (fun x => (∃ i, bad i x) ∨ cbad x) < 1 := by
    have hu := probability_union_le hμ bad
    have hs : (∑ i, probability μ (bad i)) ≤ (Fintype.card I : ℝ)*ε := by
      calc
        _ ≤ ∑ _i : I, ε := sum_le_sum (fun i _ => hbad i)
        _ = _ := by simp
    have ho := probability_or_le hμ (fun x => ∃ i, bad i x) cbad
    have he : ((Fintype.card I:ℝ)+n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1))*ε =
        (Fintype.card I : ℝ)*ε+(n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1))*ε := by ring
    rw [he] at hsmall
    linarith
  obtain ⟨x,_,hx⟩ := exists_positive_avoiding hμ hμs hfail
  refine ⟨chosen x,?_,?_⟩
  · intro i
    by_contra hh
    exact hx (Or.inl ⟨i,hh⟩)
  · have hh : ¬cbad x := fun hh => hx (Or.inr hh)
    exact (not_not.mp hh).2

open Filter

lemma sparse_split_numeric_cutoff :
    ∀ᶠ t : ℝ in atTop, ∀ n k N m : ℝ,
      1 ≤ N → N ≤ n → n ≤ t^(11/10:ℝ) → t ≤ k → 0 ≤ m → m ≤ n →
      (m+n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1)) *
        (2*Real.exp (-(k/2000)^2/(2*N))) < 1 := by
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<1/5 by norm_num)).eventually
    (eventually_ge_atTop (8000000:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hp,complement_numeric_cutoff]
    with t ht hp hc
  intro n k N m hN hNn hn htk hm hmn
  have htpos : 0<t := by linarith
  have hkpos : 0<k := lt_of_lt_of_le htpos htk
  have hn1 : 1≤n := hN.trans hNn
  have hp7 : 0≤t^(7/10:ℝ) := Real.rpow_nonneg htpos.le _
  have hpow : t^(7/10:ℝ)*(t^(1/5:ℝ)*t^(11/10:ℝ))=t^2 := by
    rw [← Real.rpow_add htpos,← Real.rpow_add htpos]
    norm_num
  have hbase : t^(7/10:ℝ)*(8000000*N) ≤ k^2 := by
    calc
      _ ≤ t^(7/10:ℝ)*(8000000*t^(11/10:ℝ)) := by gcongr; exact hNn.trans hn
      _ ≤ t^(7/10:ℝ)*(t^(1/5:ℝ)*t^(11/10:ℝ)) := by gcongr
      _ = t^2 := hpow
      _ ≤ k^2 := by nlinarith
  have he : t^(7/10:ℝ) ≤ (k/2000)^2/(2*N) := by
    apply (le_div_iff₀ (by linarith : 0<2*N)).mpr
    nlinarith
  have htail : 2*Real.exp (-(k/2000)^2/(2*N)) ≤ 2*Real.exp (-t^(7/10:ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  let H : ℝ := n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1)
  have hHpos : 0 ≤ H := by dsimp [H]; positivity
  have hcoef : m+n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1) ≤ 2*H := by
    dsimp [H]
    have hp0 : 0≤(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1) := by positivity
    linarith
  calc
    _ ≤ (2*H)*(2*Real.exp (-(k/2000)^2/(2*N))) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ (2*H)*(2*Real.exp (-t^(7/10:ℝ))) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 2*(H*(2*Real.exp (-t^(7/10:ℝ)))) := by ring
    _ ≤ 2*(1/100) := mul_le_mul_of_nonneg_left (hc n k hn1 hn htk) (by norm_num)
    _ < 1 := by norm_num

theorem sparse_split_cutoff :
    ∃ T : ℝ, ∀ t n : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      ∀ (V I : Type) [Fintype V] [DecidableEq V] [Fintype I],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      ∀ k : ℕ, t ≤ k → (Fintype.card V : ℝ) ≤ n → (Fintype.card I : ℝ) ≤ n →
      KConnectedOn G univ k → ∀ D : I → Finset V, (∀ i, (D i).card=k) →
      ∃ A : Finset V,
        (∀ i, k ≤ 2000*(A ∩ D i).card ∧ k ≤ 2*((univ \ A) ∩ D i).card) ∧
        KConnectedOn G (univ \ A) (k/32) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp sparse_split_numeric_cutoff
  refine ⟨max T 64,?_⟩
  intro t n ht hn hnt V I _ _ _ G _ k htk hord hI hc D hD
  have hk : 64≤k := by
    have hh : (64:ℝ)≤k := (le_max_right T 64).trans (ht.trans htk)
    exact_mod_cast hh
  apply exists_sparse_split G hk hord hc D hD
  have hN : (1:ℝ)≤Fintype.card V := by
    have hh := hc.1
    simp only [card_univ] at hh
    exact_mod_cast (by omega : 1≤Fintype.card V)
  exact hT t ((le_max_left _ _).trans ht) n k (Fintype.card V) (Fintype.card I)
    hN hord hnt htk (Nat.cast_nonneg _) hI

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

theorem sparse_split_on_cutoff :
    ∃ T : ℝ, ∀ t n : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      ∀ (S : Finset V) (k : ℕ), t ≤ k → (Fintype.card V : ℝ) ≤ n →
      KConnectedOn G S k → (∀ v, k ≤ (S.filter (G.Adj v)).card) →
      ∃ A B : Finset V, A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧
        (∀ v, k ≤ 2000*(A.filter (G.Adj v)).card ∧
          k ≤ 2*(B.filter (G.Adj v)).card) ∧ KConnectedOn G B (k/32) := by
  obtain ⟨T,hT⟩ := sparse_split_cutoff
  refine ⟨T,?_⟩
  intro t n ht hn hnt V _ _ G _ S k htk hord hc hdeg
  classical
  let N (v : V) : Finset (↑S : Set V) := univ.filter (fun w => G.Adj v w.val)
  have hNc (v : V) : (N v).card=(S.filter (G.Adj v)).card := by
    rw [←card_image_of_injective (N v) Subtype.val_injective]
    congr 1
    ext w
    simp only [N,mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,hu⟩
    · rintro ⟨hw,hvw⟩
      exact ⟨⟨w,hw⟩,hvw,rfl⟩
  have hD : ∀ v, ∃ D ⊆ N v, D.card=k := fun v =>
    exists_subset_card_eq (by rw [hNc]; exact hdeg v)
  choose D hDN hDc using hD
  have hSord : (Fintype.card (↑S : Set V) : ℝ) ≤ n := by
    have hs : Fintype.card (↑S : Set V) ≤ Fintype.card V := Fintype.card_subtype_le _
    exact (show (Fintype.card (↑S : Set V) : ℝ) ≤ Fintype.card V by
      exact_mod_cast hs).trans hord
  obtain ⟨A',hA',hB'⟩ := hT t n ht hn hnt (↑S : Set V) V (G.induce (↑S : Set V))
    k htk hSord hord (Knitting.induce_connected G S hc) D hDc
  let A := A'.image Subtype.val
  let B := (univ\A').image Subtype.val
  have himage_subset (E : Finset (↑S : Set V)) : E.image Subtype.val ⊆ S := by
    intro v hv
    obtain ⟨w,_,rfl⟩ := mem_image.mp hv
    exact w.property
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    obtain ⟨u,hu,huv⟩ := mem_image.mp hva
    obtain ⟨w,hw,hwv⟩ := mem_image.mp hvb
    have he : u=w := Subtype.val_injective (huv.trans hwv.symm)
    exact (mem_sdiff.mp hw).2 (he ▸ hu)
  have hcount (E : Finset (↑S : Set V)) (v : V) :
      (E ∩ D v).card ≤ ((E.image Subtype.val).filter (G.Adj v)).card := by
    rw [←card_image_of_injective (E ∩ D v) Subtype.val_injective]
    apply card_le_card
    intro w hw
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hw
    exact mem_filter.mpr ⟨mem_image.mpr ⟨u,(mem_inter.mp hu).1,rfl⟩,
      (mem_filter.mp (hDN v (mem_inter.mp hu).2)).2⟩
  refine ⟨A,B,himage_subset _,himage_subset _,hdis,?_,?_⟩
  · intro v
    exact ⟨(hA' v).1.trans (Nat.mul_le_mul_left _ (hcount A' v)),
      (hA' v).2.trans (Nat.mul_le_mul_left _ (hcount (univ\A') v))⟩
  · exact Knitting.kConnected_image G Subtype.val Subtype.val_injective hB'

end LinearListHadwiger.Sampling

end OAI
