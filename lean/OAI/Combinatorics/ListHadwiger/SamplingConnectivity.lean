import OAI.Combinatorics.ListHadwiger.Thinning

namespace OAI

namespace LinearListHadwiger.Sampling
open Finset
variable {κ ι Ω V : Type} [Fintype κ] [Fintype ι] [Fintype Ω] [Fintype V]
  [DecidableEq V] [DecidableEq κ] [DecidableEq ι]

lemma probability_product_curry (μ : κ → ι → Ω → ℝ) (P : (κ → ι → Ω) → Prop) :
    probability (productMass (fun k => productMass (μ k))) P =
      probability (productMass (fun j : κ × ι => μ j.1 j.2))
        (fun x => P (fun k i => x (k,i))) := by
  classical
  let e : (κ × ι → Ω) ≃ (κ → ι → Ω) := Equiv.curry κ ι Ω
  have hm (x : κ × ι → Ω) :
      productMass (fun k => productMass (μ k)) (e x) =
        productMass (fun j : κ × ι => μ j.1 j.2) x := by
    simp [productMass,e,Fintype.prod_prod_type]
  unfold probability
  rw [←e.sum_comp]
  apply sum_congr rfl
  intro x _
  change (if P (fun k i => x (k,i)) then _ else 0) = _
  rw [hm]

lemma unionRemainders_survival {π : Ω → ℝ} (hπ : ∀ ω, 0 ≤ π ω)
    (hs : ∑ ω, π ω=1) (E : ι → Finset V) (I : Ω → Finset V) (v : V) :
    probability (productMass (fun _ : κ × ι => π)) (fun x => v∈unionRemainders E I x) ≤
      (Fintype.card κ : ℝ)*probability (productMass (fun _ : ι => π))
        (fun x => v∈remainder E I x) := by
  classical
  let μ := productMass (fun _ : ι => π)
  have hμ : ∀ ω, 0 ≤ μ ω := productMass_nonneg (fun _ => hπ)
  have hsum : ∑ ω, μ ω=1 := productMass_sum (fun _ => hs)
  have he : probability (productMass (fun _ : κ × ι => π))
      (fun x => v∈unionRemainders E I x) =
      probability (productMass (fun _ : κ => μ)) (fun x => ∃ k, v∈remainder E I (x k)) := by
    rw [probability_product_curry (fun _ _ => π)]
    congr 1
    funext x
    simp only [unionRemainders,mem_biUnion,mem_univ,true_and]
  rw [he]
  calc
    _ ≤ ∑ k, probability (productMass (fun _ : κ => μ))
        (fun x => v∈remainder E I (x k)) := probability_union_le (productMass_nonneg (fun _ => hμ)) _
    _ = ∑ _ : κ, probability μ (fun x => v∈remainder E I x) := by
      apply sum_congr rfl
      intro k _
      exact probability_coordinate (fun _ => hsum) k (fun x => v∈remainder E I x)
    _ = _ := by simp [μ]

theorem bounded_sampler (G : SimpleGraph V) {n r : ℝ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (horder : (Fintype.card V : ℝ) ≤ n)
    (hf : Fractional.number G ≤ r) :
    ∃ (π : Finset V → ℝ) (I : Finset V → Finset V),
      (∀ s, 0 ≤ π s) ∧ (∑ s, π s=1) ∧
      (∀ s, Fractional.Stable G (I s) ∧ (I s).card ≤ ⌈n/r⌉₊) ∧
      ∀ v, probability π (fun s => v∈I s)=1/(2*r) := by
  classical
  obtain ⟨π,hπ,hs,hstable,hmarg⟩ := Fractional.bounded_sampling G hn hr horder hf
  let I (s : Finset V) : Finset V :=
    if Fractional.Stable G s ∧ s.card ≤ ⌈n/r⌉₊ then s else ∅
  refine ⟨π,I,hπ,hs,?_,?_⟩
  · intro s
    dsimp [I]
    split_ifs with h
    · exact h
    · exact ⟨Fractional.stable_empty G,by simp⟩
  · intro v
    rw [←hmarg v]
    unfold probability Fractional.marginal
    apply sum_congr rfl
    intro s _
    by_cases hπs : π s=0
    · simp [hπs]
    · simp only [I,ite_eq_left (hstable s hπs)]

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Filter Finset Fractional

theorem source_private_fractional :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈192*r*Real.log (2*y)⌉₊
      let M := ⌈n/r⌉₊
      let q := ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2
      ∀ (V Ω κ : Type) [Fintype V] [DecidableEq V] [Fintype Ω]
        [Fintype κ] [DecidableEq κ], Fintype.card κ=q →
      ∀ G : SimpleGraph V, ∀ π : Ω → ℝ,
      (∀ ω, 0 ≤ π ω) → (∑ ω, π ω=1) →
      ∀ (I : Ω → Finset V) (E : Fin N → Finset V) (H : Finset V),
      (∀ ω, (I ω).card ≤ M) →
      (∀ v, probability π (fun ω => v∈I ω)=1/(2*r)) →
      (∀ v, (N:ℝ)/2 ≤ (univ.filter (fun j => v∈E j)).card) →
      r/4 < expectation (productMass (fun _ : Fin N => π))
        (fun x => number (G.induce (↑(remainder E I x ∩ H) : Set V))) →
      probability (productMass (fun _ : κ => productMass (fun _ : Fin N => π)))
        (fun x => ∃ i, number (G.induce
          (↑(privateCopy (fun z => remainder E I z ∩ H) i x) : Set V)) ≤ r/8) < 1/50 := by
  classical
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp parameter_range_cutoff
  obtain ⟨T₁,hT₁⟩ := source_uniform_concentration (by norm_num : (1:ℕ)≤192)
    (by norm_num : (0:ℝ)<1/20)
  obtain ⟨T₂,hT₂⟩ := eventually_atTop.mp private_tail_cutoff
  refine ⟨max T₀ (max T₁ T₂),?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro V Ω κ _ _ _ _ _ hκ G π hπ hs I E H hI hmarg hE hmean
  have hp := hT₀ t ((le_max_left _ _).trans ht)
  obtain ⟨hr,hy,hyt,hry,hry'⟩ := hp.2.2 r hrl hru
  have htpos : 0 < t := by linarith [hp.1]
  obtain ⟨hN,hN',hM,hM'⟩ := sample_size_parameters hp.1 hn hnt hr hy hry
    (by norm_num : (1:ℕ)≤192)
  have hq := source_q_pos htpos hr
  let N := ⌈192*r*Real.log (2*max 1 (t/r))⌉₊
  let q := ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2
  let p := Real.exp (-((N:ℝ)/(4*r)))
  let μ := productMass (fun _ : Fin N => π)
  let W := fun z => remainder E I z ∩ H
  have hμ : ∀ x, 0 ≤ μ x := productMass_nonneg (fun _ => hπ)
  have hμs : ∑ x, μ x=1 := productMass_sum (fun _ => hs)
  have hcard : Fintype.card (Fin N) ≤ q*N := by
    rw [Fintype.card_fin]
    simpa only [one_mul] using Nat.mul_le_mul_right N hq
  have hNcard : 1 ≤ Fintype.card (Fin N) := by simpa [N] using hN
  have hc := hT₁ t n r ((le_max_left _ _).trans ((le_max_right _ _).trans ht))
    hn hnt hrl hru (Fin N) Ω hNcard hcard (fun _ => π) (fun _ => hπ) (fun _ => hs)
  have hsurv (v : V) : probability μ (fun x => v∈W x) ≤ p := by
    have hh := remainder_survival_bound (fun _ : Fin N => hs) E I
      (by linarith : 1 ≤ r) (fun _ => hmarg) (by simpa [N] using hE) v
    exact (probability_mono hμ (fun _ h => (mem_inter.mp h).1)).trans
      (by simpa only [μ,p,Fintype.card_fin,N,neg_div] using hh)
  have hcomm (z : Fin N → Ω) :
      number (G.induce (↑(H ∩ remainder E I z) : Set V)) =
      number (G.induce (↑(W z) : Set V)) :=
    congrArg (fun S : Finset V => number (G.induce (↑S : Set V))) (inter_comm _ _)
  have htail := hc (fun z => number (G.induce (↑(H ∩ remainder E I z) : Set V)))
    (remainder_fractional_bounded_changes G E I hI H)
  have hhigh : probability μ (fun z => number (G.induce (↑(W z) : Set V)) ≤ r/5) ≤
      2*Real.exp (-t^(7/10:ℝ)) := by
    have hh := probability_mono hμ (A := fun z => number (G.induce (↑(W z) : Set V)) ≤ r/5)
      (B := fun z => r/20 ≤ |number (G.induce (↑(W z) : Set V)) -
        expectation μ (fun x => number (G.induce (↑(W x) : Set V)))|)
      (by intro z hz; have ha := neg_le_abs (number (G.induce (↑(W z) : Set V)) -
          expectation μ (fun x => number (G.induce (↑(W x) : Set V))));
          change r/4 < expectation μ (fun x => number (G.induce (↑(W x) : Set V))) at hmean
          linarith)
    exact hh.trans (by simpa only [hcomm,show (1/20:ℝ)*r=r/20 by ring] using htail)
  have hfail := private_fractional_failure (ι := κ) G hμ hμs W
    (by linarith : 0 < r) (Real.exp_pos _).le hsurv hhigh
  have hsparse := (source_sparseness hp.1.le hr hru).2.1
  have hqt := hT₂ t ((le_max_right _ _).trans ((le_max_right _ _).trans ht)) r hrl hru
  have hqm : ((q-1:ℕ):ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
  have hcollision : 4*(q:ℝ)*((q-1:ℕ):ℝ)*p ≤ 4/10000 := by
    calc
      _ ≤ 4*(q:ℝ)*(q:ℝ)*p := by gcongr
      _ = 4*((q:ℝ)^2*p) := by ring
      _ ≤ _ := by dsimp [p,N,q]; linarith
  change probability (productMass (fun _ : κ => μ))
    (fun x => ∃ i, number (G.induce (↑(privateCopy W i x) : Set V)) ≤ r/8) < 1/50
  rw [hκ] at hfail
  dsimp only [q] at hcollision
  linarith

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Knitting
open Finset
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

lemma kConnected_image {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] (G : SimpleGraph V) (f : W → V) (hf : Function.Injective f)
    {T : Finset W} {k : ℕ} (hc : KConnectedOn (G.comap f) T k) :
    KConnectedOn G (T.image f) k := by
  classical
  refine ⟨by simpa only [card_image_of_injective _ hf] using hc.1,?_⟩
  intro X hX hx
  let Y := T.filter (fun w => f w∈X)
  have hYT : Y ⊆ T := filter_subset _ _
  have hYX : Y.image f=X := by
    ext v
    constructor
    · rintro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hw).2
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp (hX hv)
      exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hv⟩,rfl⟩
  have hYc : Y.card=X.card := by rw [←hYX,card_image_of_injective _ hf]
  have hcon := hc.2 Y hYT (hYc ▸ hx)
  let g : (G.comap f).induce (↑(T\Y) : Set W) →g
      G.induce (↑(T.image f\X) : Set V) :=
    { toFun := fun w => ⟨f w.val,mem_sdiff.mpr
        ⟨mem_image.mpr ⟨w.val,(mem_sdiff.mp w.property).1,rfl⟩,by
          intro h
          exact (mem_sdiff.mp w.property).2
            (mem_filter.mpr ⟨(mem_sdiff.mp w.property).1,h⟩)⟩⟩
      map_rel' := by intro u v h; exact h }
  apply hcon.map g
  intro v
  obtain ⟨w,hw,he⟩ := mem_image.mp (mem_sdiff.mp v.property).1
  have hwY : w∉Y := by
    intro hh
    exact (mem_sdiff.mp v.property).2 (he ▸ (mem_filter.mp hh).2)
  exact ⟨⟨w,mem_sdiff.mpr ⟨hw,hwY⟩⟩,Subtype.ext he⟩

end LinearListHadwiger.Knitting

namespace LinearListHadwiger.Sampling
open Finset
variable {V Ω : Type} [Fintype V] [DecidableEq V] [Fintype Ω]

theorem complement_failure_on (G : SimpleGraph V) [DecidableRel G.Adj]
    {n r ε : ℝ} {k : ℕ} (hk : 64 ≤ k) (hr : 0 < r) (hrk : r ≤ k)
    (H : Finset V) (hord : (H.card : ℝ) ≤ n) (hconn : KConnectedOn G H k)
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (U : Ω → Finset V)
    (hsurv : ∀ v, probability μ (fun ω => v∈U ω) ≤ 1/10000)
    (hε : 0 ≤ ε)
    (htail : ∀ A : Finset V, probability μ (fun ω => r/100 ≤
      |((U ω ∩ A).card : ℝ)-expectation μ (fun z => ((U z ∩ A).card : ℝ))|) ≤ ε) :
    probability μ (fun ω => ¬((∀ v∈H, k ≤ 2*((H\U ω).filter (G.Adj v)).card) ∧
      KConnectedOn G (H\U ω) (k/32))) ≤
      (n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1))*ε := by
  classical
  let U' (ω : Ω) : Finset ↥H := univ.filter (fun v => v.val∈U ω)
  have hsurv' (v : ↥H) : probability μ (fun ω => v∈U' ω) ≤ 1/10000 := by
    simpa only [U',mem_filter,mem_univ,true_and] using hsurv v.val
  have hcard (A : Finset ↥H) (ω : Ω) :
      (U' ω ∩ A).card=(U ω ∩ A.image Subtype.val).card := by
    rw [←card_image_of_injective (U' ω ∩ A) Subtype.val_injective]
    congr 1
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      exact mem_inter.mpr ⟨(mem_filter.mp (mem_inter.mp hw).1).2,
        mem_image.mpr ⟨w,(mem_inter.mp hw).2,rfl⟩⟩
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp (mem_inter.mp hv).2
      exact mem_image.mpr ⟨w,mem_inter.mpr
        ⟨mem_filter.mpr ⟨mem_univ _,(mem_inter.mp hv).1⟩,hw⟩,rfl⟩
  have ht' (A : Finset ↥H) := htail (A.image Subtype.val)
  have hc := complement_failure (G.induce (↑H : Set V)) hk hr hrk
    (by simpa using hord) (Knitting.induce_connected G H hconn) hμ U' hsurv' hε
    (by intro A; simpa only [hcard] using ht' A)
  have himage (ω : Ω) : (univ\U' ω).image Subtype.val=H\U ω := by
    ext v
    simp only [mem_image,mem_sdiff,mem_univ,true_and,U',mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.property,hw⟩
    · rintro ⟨hv,hu⟩
      exact ⟨⟨v,hv⟩,hu,rfl⟩
  have hncard (ω : Ω) (v : ↥H) :
      (((univ\U' ω).filter ((G.induce (↑H : Set V)).Adj v)).card) =
        ((H\U ω).filter (G.Adj v.val)).card := by
    rw [←card_image_of_injective _ Subtype.val_injective,←himage ω]
    congr 1
    ext w
    simp only [mem_image,mem_filter]
    constructor
    · rintro ⟨z,⟨hz,hzv⟩,rfl⟩
      exact ⟨⟨z,hz,rfl⟩,hzv⟩
    · rintro ⟨⟨z,hz,rfl⟩,hzv⟩
      exact ⟨z,⟨hz,hzv⟩,rfl⟩
  have hg (ω : Ω) (hh :
      (∀ v : ↥H, k ≤ 2*((univ\U' ω).filter ((G.induce (↑H : Set V)).Adj v)).card) ∧
        KConnectedOn (G.induce (↑H : Set V)) (univ\U' ω) (k/32)) :
      (∀ v∈H, k ≤ 2*((H\U ω).filter (G.Adj v)).card) ∧
        KConnectedOn G (H\U ω) (k/32) := by
    constructor
    · intro v hv
      simpa only [hncard] using hh.1 ⟨v,hv⟩
    · have hi := Knitting.kConnected_image G Subtype.val Subtype.val_injective hh.2
      exact (congrArg (fun T : Finset V => KConnectedOn G T (k/32)) (himage ω)).mp hi
  exact (probability_mono hμ (fun ω hbad hgood => hbad (hg ω hgood))).trans hc

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Filter Finset

theorem source_complement_on {B : ℕ} (hB : 1 ≤ B) :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈B*r*Real.log (2*y)⌉₊
      let M := ⌈n/r⌉₊
      let q := ⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2
      ∀ (V ι Ω : Type) [Fintype V] [DecidableEq V] [Fintype ι] [Fintype Ω]
        [DecidableEq ι],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (H : Finset V),
      64 ≤ k → r ≤ k → t ≤ k → (H.card : ℝ) ≤ n → KConnectedOn G H k →
      1 ≤ Fintype.card ι → Fintype.card ι ≤ q*N →
      ∀ (μ : ι → Ω → ℝ), (∀ i ω, 0 ≤ μ i ω) → (∀ i, ∑ ω, μ i ω=1) →
      ∀ U : (ι → Ω) → Finset V,
      (∀ v, probability (productMass μ) (fun x => v∈U x) ≤ 1/10000) →
      (∀ (A : Finset V) i x x', (∀ j, j ≠ i → x j=x' j) →
        |((A ∩ U x).card : ℝ)-(A ∩ U x').card| ≤ 2*M) →
      probability (productMass μ) (fun x =>
        ¬((∀ v∈H, k ≤ 2*((H \ U x).filter (G.Adj v)).card) ∧
          KConnectedOn G (H \ U x) (k/32))) ≤ 1/100 := by
  classical
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp parameter_range_cutoff
  obtain ⟨T₁,hT₁⟩ := source_uniform_concentration hB (show (0:ℝ)<1/100 by norm_num)
  obtain ⟨T₂,hT₂⟩ := eventually_atTop.mp complement_numeric_cutoff
  refine ⟨max T₀ (max T₁ T₂),?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro V ι Ω _ _ _ _ _ G _ k H hk hrk htk hord hconn hi hiq μ hμ hs U hsurv hchange
  have hr := (hT₀ t ((le_max_left _ _).trans ht)).2.2 r hrl hru
  have hconc := hT₁ t n r ((le_max_left _ _).trans ((le_max_right _ _).trans ht))
    hn hnt hrl hru ι Ω hi hiq μ hμ hs
  have htail (A : Finset V) : probability (productMass μ) (fun x => r/100 ≤
      |((U x ∩ A).card : ℝ)-expectation (productMass μ)
        (fun z => ((U z ∩ A).card : ℝ))|) ≤ 2*Real.exp (-t^(7/10:ℝ)) := by
    have hh := hconc (fun z => ((A ∩ U z).card : ℝ)) (hchange A)
    simpa only [inter_comm,show (1/100:ℝ)*r=r/100 by ring] using hh
  have hh := complement_failure_on G hk (by linarith [hr.1]) hrk H hord hconn
    (productMass_nonneg hμ) U hsurv (by positivity) htail
  exact hh.trans (hT₂ t ((le_max_right _ _).trans ((le_max_right _ _).trans ht)) n k hn hnt htk)

end LinearListHadwiger.Sampling

end OAI
