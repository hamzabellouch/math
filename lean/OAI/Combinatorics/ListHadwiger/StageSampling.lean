import OAI.Combinatorics.ListHadwiger.SamplingConnectivity

namespace OAI

namespace LinearListHadwiger.Sampling
open Filter Finset Fractional
attribute [local instance] Classical.propDecidable

theorem source_thinning_failure_structure :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈192*r*Real.log (2*y)⌉₊
      let q := ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2
      let k := ⌈(1000000*65536:ℝ)*t*y⌉₊
      ∀ (V : Type) [Fintype V] [DecidableEq V], ∀ G : SimpleGraph V,
      (Fintype.card V : ℝ) ≤ n → number G ≤ r →
      ∀ E : Fin N → Finset V,
      (∀ v, (N:ℝ)/2 ≤ (univ.filter (fun j => v∈E j)).card) →
      (∀ J : Fin N → Finset V, (∀ j, Stable G (J j)) →
        r/2 < number (G.induce
          (↑(univ\univ.biUnion (fun j => J j∩E j)) : Set V))) →
      ∃ (H U : Finset V) (S : Fin q → Finset V),
        KConnectedOn G H k ∧
        (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
        (∀ i, S i ⊆ H ∩ U) ∧
        (∀ i, r/8 < number (G.induce (↑(S i) : Set V))) ∧
        (∀ v∈H, k ≤ 2*((H\U).filter (G.Adj v)).card) ∧
        KConnectedOn G (H\U) (k/32) := by
  classical
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp parameter_range_cutoff
  obtain ⟨T₁,hT₁⟩ := source_fixed_region
  obtain ⟨T₂,hT₂⟩ := source_private_fractional
  obtain ⟨T₃,hT₃⟩ := source_complement_on (by norm_num : (1:ℕ) ≤ 192)
  refine ⟨max (max T₀ T₁) (max T₂ T₃),?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro V _ _ G hord hf E hE hfail
  have ht₀ := (le_max_left T₀ T₁).trans ((le_max_left _ _).trans ht)
  have ht₁ := (le_max_right T₀ T₁).trans ((le_max_left _ _).trans ht)
  have ht₂ := (le_max_left T₂ T₃).trans ((le_max_right _ _).trans ht)
  have ht₃ := (le_max_right T₂ T₃).trans ((le_max_right _ _).trans ht)
  have hp := hT₀ t ht₀
  obtain ⟨hr,hy,hyt,hry,hry'⟩ := hp.2.2 r hrl hru
  have htpos : 0 < t := by linarith [hp.1]
  let N := ⌈192*r*Real.log (2*max 1 (t/r))⌉₊
  let q := ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2
  let k := ⌈(1000000*65536:ℝ)*t*max 1 (t/r)⌉₊
  let M := ⌈n/r⌉₊
  obtain ⟨π,I,hπ,hπs,hI,hmarg⟩ := bounded_sampler G hn (by linarith : 1 ≤ r) hord hf
  have hN := (sample_size_parameters hp.1 hn hnt hr hy hry (by norm_num : (1:ℕ)≤192)).1
  have hq : 1 ≤ q := source_q_pos htpos hr
  obtain ⟨H,hH,hmean⟩ := hT₁ t n r ht₁ hn hnt hrl hru V (Finset V) G hord
    π hπ hπs I E (fun ω => (hI ω).2) hmarg hE (by
      intro x _
      exact hfail (fun j => I (x j)) (fun j => (hI (x j)).1))
  let μ := productMass (fun _ : Fin q × Fin N => π)
  let U (x : Fin q × Fin N → Finset V) := unionRemainders E I x
  let S (x : Fin q × Fin N → Finset V) (i : Fin q) :=
    privateCopy (fun z => remainder E I z ∩ H) i (fun j l => x (j,l))
  let privateBad (x : Fin q × Fin N → Finset V) : Prop :=
    ∃ i, number (G.induce (↑(S x i) : Set V)) ≤ r/8
  let complementBad (x : Fin q × Fin N → Finset V) : Prop :=
    ¬((∀ v∈H, k ≤ 2*((H\U x).filter (G.Adj v)).card) ∧
      KConnectedOn G (H\U x) (k/32))
  have hprivate : probability μ privateBad < 1/50 := by
    have hh := hT₂ t n r ht₂ hn hnt hrl hru V (Finset V) (Fin q)
      (by simp [q]) G π hπ hπs I E H (fun ω => (hI ω).2) hmarg hE hmean
    rw [probability_product_curry (fun _ : Fin q => fun _ : Fin N => π)] at hh
    exact hh
  have hb := attachment_budget (γ := 65536) htpos hr hru hy
    (le_max_right 1 (t/r)) (by norm_num)
  have hrk : r ≤ k := hb.1
  have hk64 : 64 ≤ k := by
    have hh : (64:ℝ) ≤ k := by linarith
    exact_mod_cast hh
  have htk : t ≤ k := by
    have hh := Nat.le_ceil ((1000000*65536:ℝ)*t*max 1 (t/r))
    dsimp [k]
    nlinarith [mul_nonneg htpos.le (sub_nonneg.mpr hy)]
  have hHord : (H.card : ℝ) ≤ n :=
    (by exact_mod_cast card_le_univ H : (H.card : ℝ) ≤ Fintype.card V).trans hord
  have hcardpos : 1 ≤ Fintype.card (Fin q × Fin N) := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    dsimp [N] at hN
    simpa only [one_mul] using Nat.mul_le_mul hq hN
  have hcard : Fintype.card (Fin q × Fin N) ≤ q*N := by simp
  have hsurv (v : V) : probability μ (fun x => v∈U x) ≤ 1/10000 := by
    have hh := unionRemainders_survival (κ := Fin q) hπ hπs E I v
    have hd := remainder_survival_bound (fun _ : Fin N => hπs) E I
      (by linarith : 1 ≤ r) (fun _ => hmarg) (by simpa [N] using hE) v
    have hb := (source_sparseness hp.1.le hr hru).2.2
    calc
      _ ≤ (q:ℝ)*probability (productMass (fun _ : Fin N => π))
          (fun x => v∈remainder E I x) := by simpa only [Fintype.card_fin] using hh
      _ ≤ (q:ℝ)*Real.exp (-((N:ℝ)/(4*r))) := by
        gcongr
        simpa only [Fintype.card_fin,neg_div] using hd
      _ ≤ _ := hb
  have hcomplement : probability μ complementBad ≤ 1/100 :=
    hT₃ t n r ht₃ hn hnt hrl hru V (Fin q × Fin N) (Finset V) G k H
      hk64 hrk htk hHord hH hcardpos hcard (fun _ => π) (fun _ => hπ)
      (fun _ => hπs) U hsurv (by
        intro A i x y hxy
        exact unionRemainders_card_bounded_changes E I (fun ω => (hI ω).2) A hxy)
  have hμ : ∀ x, 0 ≤ μ x := productMass_nonneg (fun _ => hπ)
  have hμs : ∑ x, μ x=1 := productMass_sum (fun _ => hπs)
  have hbad : probability μ (fun x => privateBad x ∨ complementBad x) < 1 := by
    have hh := probability_or_le hμ privateBad complementBad
    linarith
  obtain ⟨x,hxp,havoid⟩ := exists_positive_avoiding hμ hμs hbad
  have hpriv : ∀ i, r/8 < number (G.induce (↑(S x i) : Set V)) := by
    intro i
    by_contra hh
    exact havoid (Or.inl ⟨i,le_of_not_gt hh⟩)
  have hcomp : (∀ v∈H, k ≤ 2*((H\U x).filter (G.Adj v)).card) ∧
      KConnectedOn G (H\U x) (k/32) := by
    by_contra hh
    exact havoid (Or.inr hh)
  refine ⟨H,U x,S x,hH,?_,?_,hpriv,hcomp⟩
  · intro i j hij
    exact privateCopies_disjoint _ _ hij
  · intro i v hv
    have hw := (mem_sdiff.mp hv).1
    refine mem_inter.mpr ⟨(mem_inter.mp hw).2,?_⟩
    exact mem_biUnion.mpr ⟨i,mem_univ _,(mem_inter.mp hw).1⟩

end LinearListHadwiger.Sampling

namespace LinearListHadwiger

lemma HasCliqueMinor.restrict {V : Type} {G : SimpleGraph V} {a b : ℕ}
    (h : HasCliqueMinor G b) (hab : a ≤ b) : HasCliqueMinor G a := by
  obtain ⟨B,hB,hBB,hE⟩ := h
  let e : Fin a → Fin b := fun i => ⟨i.val,i.isLt.trans_le hab⟩
  have he : Function.Injective e := fun _ _ h => Fin.ext (congrArg (fun z : Fin b => z.val) h)
  exact ⟨B ∘ e,fun i => hB (e i),fun i j hij => hBB _ _ (fun h => hij (he h)),
    fun i j hij => hE _ _ (fun h => hij (he h))⟩

namespace Sampling
open Filter Finset Fractional
attribute [local instance] Classical.propDecidable

theorem eligible_thinning_or_fractional_counterexample :
    ∃ T : ℝ, ∀ (t : ℕ) (n r : ℝ), T ≤ (t:ℝ) → 1 ≤ n → n ≤ (t:ℝ)^(11/10:ℝ) →
      (t:ℝ)/Real.log t ≤ r → r ≤ 4*t →
      let N := ⌈192*r*Real.log (2*max 1 ((t:ℝ)/r))⌉₊
      ∀ (V : Type) [Fintype V] [DecidableEq V], ∀ G : SimpleGraph V,
      (Fintype.card V : ℝ) ≤ n → hadwigerNumber G < t → number G ≤ r →
      ∀ E : Fin N → Finset V,
      (∀ v, (N:ℝ)/2 ≤ (univ.filter (fun j => v∈E j)).card) →
      (∃ J : Fin N → Finset V, (∀ j, Stable G (J j)) ∧
        number (G.induce (↑(univ\univ.biUnion (fun j => J j∩E j)) : Set V)) ≤ r/2) ∨
      ∃ S : Finset V, 4*(hadwigerNumber (G.induce (↑S:Set V)):ℝ) <
        number (G.induce (↑S:Set V)) := by
  classical
  obtain ⟨T₀,hT₀⟩ := source_thinning_failure_structure
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp parameter_range_cutoff
  refine ⟨max (max T₀ T₁) 2,?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro V _ _ G hord hminor hf E hE
  by_contra hnone
  have hfail : ∀ J : Fin ⌈192*r*Real.log (2*max 1 ((t:ℝ)/r))⌉₊ → Finset V,
      (∀ j, Stable G (J j)) →
      r/2 < number (G.induce
        (↑(univ\univ.biUnion (fun j => J j∩E j)) : Set V)) := by
    intro J hJ
    by_contra hj
    exact hnone (Or.inl ⟨J,hJ,le_of_not_gt hj⟩)
  have hbound (S : Finset V) : number (G.induce (↑S:Set V)) ≤
      4*(hadwigerNumber (G.induce (↑S:Set V)):ℝ) :=
    le_of_not_gt (fun hs => hnone (Or.inr ⟨S,hs⟩))
  have ht₀ := ((le_max_left T₀ T₁).trans (le_max_left _ _)).trans ht
  have ht₁ := ((le_max_right T₀ T₁).trans (le_max_left _ _)).trans ht
  have ht₂ : (2:ℝ) ≤ t := (le_max_right _ _).trans ht
  have htpos : 0 < (t:ℝ) := by linarith
  have htNat : 1 ≤ t := by exact_mod_cast (show (1:ℝ) ≤ t by linarith)
  have hp := hT₁ (t:ℝ) ht₁
  obtain ⟨hr,hy,_,_,_⟩ := hp.2.2 r hrl hru
  let x := ⌊r/200⌋₊
  let b := ⌈(t:ℝ)/(x:ℝ)⌉₊
  let q := b^2
  let k := ⌈(1000000*65536:ℝ)*(t:ℝ)*max 1 ((t:ℝ)/r)⌉₊
  have hx : 1 ≤ x := (floor_parameter htpos hr hy (le_max_right _ _)).1
  have hxpos : 0 < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have htb : t ≤ b*x := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    exact (div_le_iff₀ hxpos).mp (Nat.le_ceil ((t:ℝ)/(x:ℝ)))
  obtain ⟨H,U,S,hH,hSS,hSU,hfS,hN,hC⟩ :=
    hT₀ (t:ℝ) n r ht₀ hn hnt hrl hru V G hord hf E hE hfail
  have hb := attachment_budget (γ := 65536) htpos hr hru hy
    (le_max_right 1 ((t:ℝ)/r)) (by norm_num)
  change r ≤ (k:ℝ) ∧ 64*(2*x*q) < k ∧ 65536*(2*x*q) ≤ k/32 at hb
  let e : (Fin b × Fin b) ≃ Fin q := Fintype.equivOfCardEq (by simp [q,pow_two])
  have hm (i : Fin q) : HasCliqueMinor (G.induce (↑(S i):Set V)) (2*x) := by
    apply (hasCliqueMinor_hadwigerNumber (G.induce (↑(S i):Set V))).restrict
    have hs := hbound (S i)
    have hf' := hfS i
    have hx' : (x:ℝ) ≤ r/200 := Nat.floor_le (by linarith)
    have hh : ((2*x:ℕ):ℝ) ≤ hadwigerNumber (G.induce (↑(S i):Set V)) := by
      push_cast
      nlinarith
    exact_mod_cast hh
  have hcl := Assembly.clique_from_block_models G htNat hx htb
    (fun z => S (e z)) (H\U)
    (fun i j hij => hSS _ _ (fun he => hij (e.injective he)))
    (fun i => disjoint_left.mpr (fun v hv hu =>
      (mem_sdiff.mp hu).2 (mem_inter.mp (hSU _ hv)).2))
    (fun i => hm (e i))
    (fun i v hv => by
      have hh := hN v (mem_inter.mp (hSU _ hv)).1
      change k ≤ 2*((H\U).filter (G.Adj v)).card at hh
      change 2*x*q ≤ ((H\U).filter (G.Adj v)).card
      omega)
    (Knitting.kConnected_mono hC hb.2.2)
  exact (not_lt_of_ge (cliqueMinor_le_hadwigerNumber hcl)) hminor

end Sampling
end LinearListHadwiger

end OAI
