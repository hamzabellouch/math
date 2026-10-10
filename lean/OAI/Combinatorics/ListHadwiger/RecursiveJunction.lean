import OAI.Combinatorics.ListHadwiger.RecursiveDistricts

namespace OAI

namespace LinearListHadwiger.Recursion
open SimpleGraph Finset Stage
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem junction_groups (G : SimpleGraph V) {a p : ℕ} (ha : 1≤a)
    (r : Fin a → V) (n : Fin (2*p) → V) (e : (Fin p × Bool) ≃ Fin (2*p)) (H D : Finset V) (F U : Set V)
    (hHD : Disjoint H D)
    (R : RoleRouting G r n F (↑H:Set V) D U)
    (M : RootedCliqueModel G R.fresh) (hMH : ∀ i, M.branch i⊆(↑H:Set V))
    (hc : KConnectedOn G D (65536*Fintype.card (Roles a (2*p)))) :
    ∃ C : (Fin a ⊕ Fin p) → Set V,
      (∀ i, (G.induce (C i)).Connected) ∧
      (∀ i j, i≠j → Disjoint (C i) (C j)) ∧
      (∀ i j, i≠j → ∃ v∈C (.inl i), ∃ w∈C (.inl j), G.Adj v w) ∧
      (∀ i, r i∈C (.inl i)) ∧
      (∀ q, n (e q)∈C (.inr q.1)) := by
  classical
  let owner : Roles a (2*p) → Fin a ⊕ Fin p :=
    Sum.elim Sum.inl (Sum.elim (fun j => Sum.inr (e.symm j).1) Sum.inl)
  let start := roleStart r n R.fresh
  let target (o : Roles a (2*p)) := (R.target o).val
  have htar : Function.Injective target := Subtype.val_injective.comp R.target_injective
  have hs : Function.Surjective owner := by
    intro i
    cases i with
    | inl i => exact ⟨.inl i,rfl⟩
    | inr i => exact ⟨.inr (.inl (e (i,false))),by simp [owner]⟩
  have hcpos : 1≤Fintype.card (Roles a (2*p)) := by simp only [Roles,Fintype.card_sum,Fintype.card_fin]; omega
  obtain ⟨E,hE,hEE,hED,htE⟩ := grouped_ends G D target htar (fun o => (R.target o).property)
    owner hs hcpos hc
  let B : Roles a (2*p) → Set V := Sum.elim (fun i => {r i}) (Sum.elim (fun j => {n j}) M.branch)
  have hB (o) : (G.induce (B o)).Connected := by
    rcases o with i|(j|i)
    · change (G.induce ({r i}:Set V)).Connected
      have : Nonempty ({r i}:Set V) := ⟨⟨r i,rfl⟩⟩
      exact Connected.of_subsingleton
    · change (G.induce ({n j}:Set V)).Connected
      have : Nonempty ({n j}:Set V) := ⟨⟨n j,rfl⟩⟩
      exact Connected.of_subsingleton
    · exact M.connected i
  have hxB (o) : start o∈B o := by
    rcases o with i|(j|i)
    · rfl
    · rfl
    · exact M.root_mem i
  have hBP (o q) (hne : owner o≠owner q) :
      Disjoint (B o) {v | v∈(R.route q).val.support} := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    rcases o with i|(j|i)
    · have he : v=r i := hv
      subst v
      have hneq : Sum.inl i≠q := fun h => hne (congrArg owner h)
      exact Set.disjoint_left.mp (R.disjoint _ _ hneq) (R.route (.inl i)).val.start_mem_support hw
    · have he : v=n j := hv
      subst v
      have hneq : Sum.inr (Sum.inl j)≠q := fun h => hne (congrArg owner h)
      exact Set.disjoint_left.mp (R.disjoint _ _ hneq) (R.route (.inr (.inl j))).val.start_mem_support hw
    · obtain ⟨j,rfl,hv'⟩ := R.new_only q v hw (hMH i hv)
      have hij : i≠j := by intro h; subst j; exact hne rfl
      exact Set.disjoint_left.mp (M.disjoint i j hij) hv (hv'.symm ▸ M.root_mem j)
  have hBB (o q) (hne : owner o≠owner q) : Disjoint (B o) (B q) := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    rcases q with j|(j|j)
    · have he : v=r j := hw
      exact Set.disjoint_left.mp (hBP o (.inl j) hne) hv (he.symm ▸ (R.route (.inl j)).val.start_mem_support)
    · have he : v=n j := hw
      exact Set.disjoint_left.mp (hBP o (.inr (.inl j)) hne) hv (he.symm ▸ (R.route (.inr (.inl j))).val.start_mem_support)
    · rcases o with i|(i|i)
      · have he : v=r i := hv
        exact Set.disjoint_left.mp (hBP (.inr (.inr j)) (.inl i) (Ne.symm hne)) hw
          (he.symm ▸ (R.route (.inl i)).val.start_mem_support)
      · have he : v=n i := hv
        exact Set.disjoint_left.mp (hBP (.inr (.inr j)) (.inr (.inl i)) (Ne.symm hne)) hw
          (he.symm ▸ (R.route (.inr (.inl i))).val.start_mem_support)
      · exact Set.disjoint_left.mp (M.disjoint i j (fun h => hne (congrArg Sum.inl h))) hv hw
  have hEP (i o) (hne : i≠owner o) : Disjoint (E i) {v | v∈(R.route o).val.support} := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    have he := R.target_only o v hw (hED i hv)
    exact Set.disjoint_left.mp (hEE i (owner o) hne) hv (he.symm ▸ htE o)
  have hEB (i o) (hne : i≠owner o) : Disjoint (E i) (B o) := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    rcases o with j|(j|j)
    · have he : v=r j := hw
      exact Set.disjoint_left.mp (hEP i (.inl j) hne) hv (he.symm ▸ (R.route (.inl j)).val.start_mem_support)
    · have he : v=n j := hw
      exact Set.disjoint_left.mp (hEP i (.inr (.inl j)) hne) hv (he.symm ▸ (R.route (.inr (.inl j))).val.start_mem_support)
    · exact Finset.disjoint_left.mp hHD (hMH j hw) (hED i hv)
  let C := extended E B owner start target R.route
  have hC (i) : (G.induce (C i)).Connected := extended_connected E B owner start target R.route
    hE hB hxB htE i
  have hCC : ∀ i j, i≠j → Disjoint (C i) (C j) :=
    extended_disjoint E B owner start target R.route hEE hBB hEB hEP hBP
      (fun o q hne => R.disjoint o q (fun h => hne (congrArg owner h)))
  have hBC (o) : B o⊆C (owner o) := fun _ hv => Or.inr ⟨o,rfl,Or.inl hv⟩
  refine ⟨C,hC,hCC,?_,fun i => hBC (.inl i) rfl,?_⟩
  · intro i j hij
    obtain ⟨v,hv,w,hw,he⟩ := M.adjacent i j hij
    exact ⟨v,hBC (.inr (.inr i)) hv,w,hBC (.inr (.inr j)) hw,he⟩
  · intro q
    have hmem := hBC (.inr (.inl (e q))) rfl
    simpa only [owner,Sum.elim_inr,Sum.elim_inl,e.symm_apply_apply] using hmem

end LinearListHadwiger.Recursion

namespace LinearListHadwiger.Recursion
open Finset Stage Footprint SmallList Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma outer_size_cutoff : ∃ T : ℕ, ∀ t : ℕ, T≤t →
    (t:ℝ)^(53/50:ℝ)+(t:ℝ)≤(t:ℝ)^(11/10:ℝ) := by
  have he : ∀ᶠ x : ℝ in atTop, 1≤x ∧ 2≤x^(1/25:ℝ) :=
    (eventually_ge_atTop 1).and ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/25)).eventually (eventually_ge_atTop 2))
  obtain ⟨S,hS⟩ := (eventually_atTop.mp he)
  refine ⟨⌈S⌉₊,fun t ht => ?_⟩
  obtain ⟨h1,h2⟩ := hS t ((Nat.le_ceil S).trans (by exact_mod_cast ht))
  have hle : (t:ℝ)≤(t:ℝ)^(53/50:ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (1:ℝ)≤53/50)
  have heq : (t:ℝ)^(11/10:ℝ)=(t:ℝ)^(53/50:ℝ)*(t:ℝ)^(1/25:ℝ) := by
    rw [←Real.rpow_add (by positivity : (0:ℝ)<t)]
    norm_num
  rw [heq]
  nlinarith [Real.rpow_nonneg (by positivity : (0:ℝ)≤t) (53/50:ℝ)]

theorem outer_region : ∃ A : ℕ, 1≤A ∧ ∃ T : ℕ, 1≤T ∧
    ∀ a : ℕ, 1≤a → T≤64*a → ∀ p : ℕ, p≤3*a →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (r : Fin a → V) (n : Fin (2*p) → V),
    Function.Injective r → Function.Injective n → (∀ i j, r i≠n j) →
    KConnectedOn G univ (30*a) → hadwigerNumber G<64*a →
    A*a<listChromaticNumber G →
    (∃ H D : Finset V, ∃ U : Set V,
      Nonempty (RoleRouting G r n (↑(univ.image r):Set V) (↑H:Set V) D U) ∧
      Disjoint H D ∧ KConnectedOn G H (K₀*(64*a)) ∧
      KConnectedOn G D (K₀*(64*a)) ∧
      listChromaticNumber G≤ell G H+(4*32768+42+5+6*K₀)*(64*a)) ∨
      FractionalObstruction G := by
  obtain ⟨D,hD,Td,hTd⟩ := districts_on K₀ (by norm_num [K₀])
  obtain ⟨Tx,hTx⟩ := outer_size_cutoff
  obtain ⟨Ta,hTa⟩ := additive_deletion_or_obstruction
  let c : ℕ := 4*32768+42+5
  let A := 128*D+10+64*(c+6*K₀)
  refine ⟨A,by dsimp [A]; omega,max 1 (max Td (max Tx Ta)),by omega,?_⟩
  intro a ha ht p hp V _ _ G r n hr hn hrn hc hm hl
  classical
  have htd : Td≤64*a := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htx : Tx≤64*a := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have hta : Ta≤64*a := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  let Z := oldSources r n
  have hz : Z.card≤7*a := by
    have h := card_union_le (univ.image r) (univ.image n)
    have h1 := card_image_le (s:=univ) (f:=r)
    have h2 := card_image_le (s:=univ) (f:=n)
    simp only [card_univ,Fintype.card_fin] at h1 h2
    change ((univ.image r)∪(univ.image n)).card≤7*a
    omega
  have hdel := ell_delete G univ Z
  rw [ell_univ] at hdel
  obtain ⟨J,hJS,hJc,hJs⟩ := hTd (64*a) htd V G (univ\Z) hm (by dsimp [A] at hl; nlinarith)
  have hZJ : Disjoint Z J := disjoint_sdiff_self_right.mono_right hJS
  have hk : 2*Z.card≤30*a := by omega
  have hJcard : 2*Z.card≤J.card := by have := hJc.1; dsimp [K₀] at this; omega
  obtain ⟨R,P,hRU,hRn,hRZ,hRJ,hPR⟩ := first_system univ univ Z J (Subset.refl _) (subset_univ _) (subset_univ _) hZJ
    (Knitting.kConnected_mono hc hk) hJcard
  let X := Z∪J
  let Y := R.used\X
  have hX : (X.card:ℝ)≤((64*a:ℕ):ℝ)^(11/10:ℝ) := by
    have hcard := card_union_le Z J
    have hle : (X.card:ℝ)≤(J.card:ℝ)+(64*a:ℕ) := by exact_mod_cast (by dsimp [X]; omega : X.card≤J.card+64*a)
    have hcut := hTx (64*a) htx
    linarith
  have hY : DegenerateOn G Y (42*(64*a)) := by
    intro B hBY hB
    obtain ⟨v,hv,hdeg⟩ := R.degenerate B (hBY.trans sdiff_subset) hB
    exact ⟨v,hv,hdeg.trans (by rw [hRn]; omega)⟩
  have hnY (v) (hv : v∉X∪Y) : (Y.filter (G.Adj v)).card≤42*(64*a) := by
    have hnot : v∉R.used := by
      intro hw
      by_cases hx : v∈X
      · exact hv (mem_union_left _ hx)
      · exact hv (mem_union_right _ (mem_sdiff.mpr ⟨hw,hx⟩))
    have hd : v∈R.domain := by rw [hRU]; exact mem_univ v
    exact (card_le_card (filter_subset_filter _ sdiff_subset)).trans
      ((R.used_neighbors v hd hnot).trans (by rw [hRn]; omega))
  rcases hTa (64*a) hta V G X Y 42 hm hX disjoint_sdiff_self_right hY hnY with hloss|hb
  swap
  · exact Or.inr hb
  have hlarge : 6*(K₀*(64*a))<ell G (univ\(X∪Y)) := by
    change listChromaticNumber G≤ell G (univ\(X∪Y))+c*(64*a) at hloss
    dsimp [A] at hl
    nlinarith
  obtain ⟨H,hHS,hHc,hHl⟩ := extract_on G (univ\(X∪Y)) (by dsimp [K₀]; omega) hlarge
  have hXH : Disjoint X H := by
    apply disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp (hHS hw)).2 (mem_union_left _ hv)
  have hRH : Disjoint R.used H := by
    apply disjoint_left.mpr
    intro v hv hw
    have hout := (mem_sdiff.mp (hHS hw)).2
    by_cases hx : v∈X
    · exact hout (mem_union_left _ hx)
    · exact hout (mem_union_right _ (mem_sdiff.mpr ⟨hv,hx⟩))
  have hZH : Disjoint Z H := hXH.mono_left (subset_union_left)
  have hJH : Disjoint J H := hXH.mono_left (subset_union_right)
  have hHsub : H⊆univ\Z := fun v hv => mem_sdiff.mpr ⟨mem_univ _,fun hz => disjoint_left.mp hZH hz hv⟩
  have hcc : KConnectedOn G (univ\Z) (2*a) := by
    exact Knitting.kConnected_mono (Knitting.delete_connected G hc (subset_univ Z) (by omega)) (by omega)
  obtain ⟨Q⟩ := Second.exists_in_region (univ\Z) (univ\Z) H J (2*a) (Subset.refl _) hHsub hJS hcc
    (by have := hHc.1; dsimp [K₀] at this; omega) (by have := hJc.1; dsimp [K₀] at this; omega)
  have hF : univ\(univ.image r\univ.image r)=(univ:Finset V) := by simp
  have hRu : R.domain=univ\(univ.image r\univ.image r) := by rwa [hF]
  obtain ⟨routing⟩ := combine_systems (univ.image r) H J r n hr hn hrn
    (fun i => mem_image.mpr ⟨i,mem_univ _,rfl⟩) hZH hZJ hJH.symm R hRu P hPR hRH Q
  refine Or.inl ⟨H,J,_,⟨routing⟩,hJH.symm,hHc,hJc,?_⟩
  change listChromaticNumber G≤ell G (univ\(X∪Y))+c*(64*a) at hloss
  dsimp [c] at hloss
  nlinarith

end LinearListHadwiger.Recursion

end OAI
