import OAI.Combinatorics.ListHadwiger.StageAdvance

namespace OAI

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable

lemma round_connectivity_level {t a : ℕ} (h : a≤t) : 65536*(2*t+a)≤K₀*t := by
  dsimp [K₀]
  omega

theorem advance_or_obstruction : ∃ S : ℕ, ch<S ∧ ∃ T : ℕ, 1≤T ∧
    ∀ t : ℕ, T≤t → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    hadwigerNumber G<t → 2*S*t≤listChromaticNumber G →
    Inseparable G (listChromaticNumber G) (S*t) →
    ∀ A : State G t (listChromaticNumber G), A.history.q<rounds t →
    ∀ a : ℕ, 1≤a → a≤t → a≤2*⌈(t:ℝ)/(Real.log t)^2⌉₊ →
    ∀ label : Fin a → Fin t,
    (∃ A' : State G t (listChromaticNumber G),
      A'.history.q=A.history.q+1 ∧ (∀ i, A.bag i⊆A'.bag i) ∧
      ∀ i j, i≠j → ∃ v∈A'.bag (label i), ∃ w∈A'.bag (label j), G.Adj v w) ∨
      FractionalObstruction G := by
  obtain ⟨D₀,hD₀,Td,hTd⟩ := two_districts K₀ (by decide)
  obtain ⟨Tl,hTl⟩ := History.list_loss_or_obstruction
  obtain ⟨Tw,hTw⟩ := districts_woven
  let S := ch+K₀+2*D₀+(4*32768+5)+10
  refine ⟨S,by dsimp [S]; omega,max 1 (max Td (max Tl Tw)),le_max_left _ _,?_⟩
  intro t ht V _ _ G hminor hlist hn A hq a ha hat haq label
  have ht1 : 1≤t := (le_max_left _ _).trans ht
  have htd : Td≤t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htl : Tl≤t := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have htw : Tw≤t := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  let F := A.history.footprint A.history.q
  let W := univ.image A.tip
  have hW : W.card=t := by simp only [W,card_image_of_injective _ A.tip_injective,card_univ,Fintype.card_fin]
  have hregion := A.region_list
  have hdelete := ell_delete G A.region W
  rw [hW] at hdelete
  have hdistrict : (2*D₀+4*32768+5)*t+2<ell G (A.region\W) := by
    dsimp [S,ch,cf,K₀] at hlist hregion
    nlinarith
  rcases hTd t htd V G (A.region\W) hminor hdistrict with
    ⟨J,hJS,D,hDS,hJD,hJc,hDc,hJsize,hDsize⟩|hbad
  swap
  · exact Or.inr hbad
  have hJF : Disjoint J F := A.live_disjoint.mono_left hJS
  have hDF : Disjoint D F := A.live_disjoint.mono_left hDS
  have hDFJ : Disjoint D (F∪J) := Finset.disjoint_union_right.mpr ⟨hDF,hJD.symm⟩
  have hJH : J⊆A.region := hJS.trans sdiff_subset
  have hDH : D⊆A.region := hDS.trans sdiff_subset
  obtain ⟨u,hu,huJ⟩ := choose_vertices (show a≤J.card from by
    have hh := hJc.1
    dsimp [K₀] at hh
    omega)
  let Z := oldSources A.tip u
  have hZcard : Z.card≤2*t := by
    have hh := card_union_le W (univ.image u)
    have hh' : (univ.image u).card≤a := by simpa using card_image_le (s:=univ) (f:=u)
    dsimp [Z,oldSources]
    dsimp [W] at hW hh
    omega
  have hZF : A.region⊆univ\(F\W) := by
    intro v hv
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    rintro hf
    have hw : v∈univ.image A.tip := A.intersection ▸ mem_inter.mpr ⟨hv,(mem_sdiff.mp hf).1⟩
    exact (mem_sdiff.mp hf).2 hw
  have hZH : Z⊆A.region := by
    intro v hv
    rcases (mem_oldSources _ _ v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact A.tip_region i
    · exact hJH (huJ j)
  have hZD : Disjoint Z D := by
    apply Finset.disjoint_left.mpr
    intro v hv hvD
    rcases (mem_oldSources _ _ v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact Finset.disjoint_left.mp hDF hvD (A.tip_footprint i)
    · exact Finset.disjoint_left.mp hJD (huJ j) hvD
  obtain ⟨R,P,hRU,hRn,hRS,hRE,hPR⟩ := first_system (univ\(F\W)) A.region Z D
    hZF hZH hDH hZD (Knitting.kConnected_mono A.region_conn (by dsimp [K₀]; omega))
    (by have hh := hDc.1; dsimp [K₀] at hh; omega)
  let C := firstRound A J D hJsize hDsize hJF hDFJ u huJ R hRU hRS hRE (by omega)
  have hCfinal : C.final=F∪J∪D∪R.used := by
    simp only [C,F,Round.final,firstRound,System.empty_used,union_empty]
  have hbound : (A.history.append C).q≤rounds t := by change A.history.q+1≤rounds t; omega
  rcases hTl t htl V G (A.history.append C) hminor hbound with hfoot|hbad
  swap
  · exact Or.inr hbad
  rw [History.append_final,hCfinal] at hfoot
  have hlarge : 6*((K₀+1)*t)<ell G (univ\(F∪J∪D∪R.used)) := by
    change listChromaticNumber G≤ell G (univ\(F∪J∪D∪R.used))+cf*t at hfoot
    dsimp [S,ch,cf,K₀] at hlist hfoot ⊢
    nlinarith
  obtain ⟨H',hH's,hH'c,hH'l⟩ := extract_on G (univ\(F∪J∪D∪R.used))
    (by dsimp [K₀]; omega : 1≤(K₀+1)*t) hlarge
  have hH'list : listChromaticNumber G≤ell G H'+(cf+6*(K₀+1))*t := by
    change listChromaticNumber G≤ell G (univ\(F∪J∪D∪R.used))+cf*t at hfoot
    dsimp [cf,K₀] at hfoot hH'l ⊢
    omega
  have hH'dis : Disjoint H' (F∪J∪D∪R.used) := Finset.disjoint_left.mpr
    (fun v hv hf => (mem_sdiff.mp (hH's hv)).2 hf)
  have hover : K₀*t≤(A.region∩H').card := overlap_of_inseparable hn A.region_list hH'list
    (by dsimp [S,ch,cf,K₀]; nlinarith)
    (by dsimp [S,ch,cf,K₀]; nlinarith)
  obtain ⟨Q⟩ := second_system A (by omega) J D H' hJH hDS hJD hDc u hat huJ hH'c
    (hH'dis.mono_right (fun v hv => by simp only [mem_union] at *; tauto)) hover
  let C' := completeRound C Q hH'dis
  have hC'final : C'.final=F∪J∪D∪R.used∪Q.record.used := rfl
  have hWoven := hTw t htw a ha haq V G J hJsize hJc
  obtain ⟨B',w',hB',hBB',hOld,hwB',hAdj,hInside,hw',hwQ⟩ := extend_with_systems G (t:=t) (a:=a)
    (by omega) F J H' D A.bag A.tip A.connected A.disjoint A.inside A.tip_mem A.tip_injective
    u hu huJ label hJF hDFJ R hRU P hPR hH'dis Q hWoven hat
    (Knitting.kConnected_mono hDc (round_connectivity_level hat))
  obtain ⟨hNewC,hNewL,hNewI⟩ := restore_region (by omega) H' C'.final Q.record.starts hH'c hH'list
    (completeRound_intersection C Q hH'dis) (Q.starts_card _ _ _) w' hw' hwQ
  let A' : State G t (listChromaticNumber G) := {
    history := A.history.append C'
    bag := B'
    tip := w'
    connected := hB'
    disjoint := hBB'
    inside := by intro i; rw [History.append_final,hC'final]; exact hInside i
    tip_mem := hwB'
    tip_injective := hw'
    region := H'\(Q.record.starts\univ.image w')
    region_conn := hNewC
    region_list := hNewL
    intersection := by rw [History.append_final]; exact hNewI }
  exact Or.inl ⟨A',rfl,hOld,hAdj⟩

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset Filter
attribute [local instance] Classical.propDecidable

def block (t m : ℕ) (b : Fin m) : Finset (Fin t) :=
  univ.filter (fun i => i.val % m=b.val)

lemma block_nonempty {t m : ℕ} (hmt : m≤t) (b : Fin m) : (block t m b).Nonempty := by
  refine ⟨⟨b.val,b.isLt.trans_le hmt⟩,?_⟩
  simp only [block,mem_filter,mem_univ,true_and]
  exact Nat.mod_eq_of_lt b.isLt

lemma block_card_le {t m q : ℕ} (hm : 0 < m) (ht : t≤q*m) (b : Fin m) :
    (block t m b).card≤q := by
  let f : ↥(block t m b) → Fin q := fun i => ⟨i.val.val/m,
    (Nat.div_lt_iff_lt_mul hm).mpr (i.val.isLt.trans_le ht)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hv := congrArg Fin.val hij
    change i.val.val/m=j.val.val/m at hv
    have hi : i.val.val%m=b.val := (mem_filter.mp i.property).2
    have hj : j.val.val%m=b.val := (mem_filter.mp j.property).2
    have hmod := Nat.mod_add_div i.val.val m
    have hmod' := Nat.mod_add_div j.val.val m
    rw [hi,hv] at hmod
    rw [hj] at hmod'
    apply Subtype.ext
    apply Fin.ext
    omega
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hinj

noncomputable def roundSet (t m : ℕ) : Sym2 (Fin m) → Finset (Fin t) :=
  Sym2.lift ⟨fun b c => block t m b∪block t m c,fun b c => union_comm (block t m b) (block t m c)⟩

lemma roundSet_nonempty {t m : ℕ} (hmt : m≤t) (r : Sym2 (Fin m)) :
    (roundSet t m r).Nonempty := by
  rcases Sym2.mk_surjective r with ⟨⟨b,c⟩,rfl⟩
  exact (block_nonempty hmt b).mono subset_union_left

lemma roundSet_card_le {t m q : ℕ} (hm : 0 < m) (ht : t≤q*m) (r : Sym2 (Fin m)) :
    (roundSet t m r).card≤2*q := by
  rcases Sym2.mk_surjective r with ⟨⟨b,c⟩,rfl⟩
  change (block t m b∪block t m c).card≤2*q
  have h := card_union_le (block t m b) (block t m c)
  have hb := block_card_le hm ht b
  have hc := block_card_le hm ht c
  omega

lemma roundSet_cover {t m : ℕ} (hm : 0 < m) (i j : Fin t) :
    ∃ r, i∈roundSet t m r ∧ j∈roundSet t m r := by
  refine ⟨s(⟨i.val%m,Nat.mod_lt _ hm⟩,⟨j.val%m,Nat.mod_lt _ hm⟩),?_,?_⟩
  · exact mem_union_left _ (by simp [block])
  · exact mem_union_right _ (by simp [block])

lemma sym2_fin_card (m : ℕ) : Fintype.card (Sym2 (Fin m))=m*(m+1)/2 := by
  rw [Sym2.card,Fintype.card_fin,Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm]

lemma schedule_parameter_cutoff : ∀ᶠ t : ℝ in atTop,
    1≤⌈(Real.log t)^2⌉₊ ∧ ⌈(Real.log t)^2⌉₊≤⌊t⌋₊ ∧
    t≤(⌈t/(Real.log t)^2⌉₊:ℝ)*⌈(Real.log t)^2⌉₊ := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (2:ℝ)
    (show (0:ℝ)<1 by norm_num)).bound (show (0:ℝ)<1/2 by norm_num)
  filter_upwards [eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),hlog] with t ht hl ho
  have ht0 : 0<t := by linarith
  have hl0 : 0<Real.log t := by linarith
  have hs : (Real.log t)^2≤t/2 := by
    have hh : (Real.log t)^2≤(1/2:ℝ)*t := by
      rw [←Real.rpow_natCast (Real.log t) 2]
      simpa only [Nat.cast_ofNat,Real.norm_eq_abs,Real.rpow_one,
        abs_of_nonneg (Real.rpow_nonneg hl0.le (2:ℝ)),abs_of_pos ht0] using ho
    linarith
  have hm := Nat.le_ceil ((Real.log t)^2)
  have hm1 : 1≤⌈(Real.log t)^2⌉₊ := by
    have hh : (1:ℝ)≤⌈(Real.log t)^2⌉₊ := by nlinarith
    exact_mod_cast hh
  have hfloor := Nat.lt_floor_add_one t
  have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log t))
  have hmf : (⌈(Real.log t)^2⌉₊:ℝ)≤⌊t⌋₊ := by linarith
  have hq := Nat.le_ceil (t/(Real.log t)^2)
  have hmul := mul_le_mul_of_nonneg_right hq (sq_nonneg (Real.log t))
  rw [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hl0))] at hmul
  have hmul' := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg ⌈t/(Real.log t)^2⌉₊)
  exact ⟨hm1,by exact_mod_cast hmf,hmul.trans hmul'⟩

theorem schedule_cutoff : ∃ T : ℕ, ∀ t : ℕ, T≤t →
    ∃ A : Fin (Footprint.rounds t) → Finset (Fin t),
      (∀ r, (A r).Nonempty) ∧
      (∀ r, (A r).card≤2*⌈(t:ℝ)/(Real.log t)^2⌉₊) ∧
      (∀ i j, ∃ r, i∈A r ∧ j∈A r) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp schedule_parameter_cutoff
  refine ⟨⌈T⌉₊,?_⟩
  intro t ht
  have htr : T≤(t:ℝ) := (Nat.le_ceil T).trans (by exact_mod_cast ht)
  obtain ⟨hm,hm',hq⟩ := hT t htr
  rw [Nat.floor_natCast] at hm'
  let m := ⌈(Real.log t)^2⌉₊
  let q := ⌈(t:ℝ)/(Real.log t)^2⌉₊
  have hqm : t≤q*m := by exact_mod_cast hq
  let e : Fin (Footprint.rounds t) ≃ Sym2 (Fin m) :=
    (Fintype.equivFinOfCardEq (show Fintype.card (Sym2 (Fin m))=Footprint.rounds t from
      sym2_fin_card m)).symm
  refine ⟨fun r => roundSet t m (e r),?_,?_,?_⟩
  · intro r; exact roundSet_nonempty hm' _
  · intro r; exact roundSet_card_le (by omega) hqm _
  · intro i j
    obtain ⟨r,hi,hj⟩ := roundSet_cover (m:=m) (by omega) i j
    exact ⟨e.symm r,by simpa using hi,by simpa using hj⟩

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable

theorem separability_or_obstruction : ∃ S : ℕ, 1≤S ∧ ∃ T : ℕ, 1≤T ∧
    ∀ t : ℕ, T≤t → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    hadwigerNumber G<t → 2*S*t≤listChromaticNumber G →
    (∃ X Y : Finset V, Disjoint X Y ∧
      listChromaticNumber G≤ell G X+S*t ∧ listChromaticNumber G≤ell G Y+S*t) ∨
      FractionalObstruction G := by
  obtain ⟨S,hS,Ta,hTa,hAdvance⟩ := advance_or_obstruction
  obtain ⟨Ts,hTs⟩ := schedule_cutoff
  refine ⟨S,by omega,max Ta Ts,hTa.trans (le_max_left _ _),?_⟩
  intro t ht V _ _ G hminor hlist
  have hta : Ta≤t := (le_max_left _ _).trans ht
  have hts : Ts≤t := (le_max_right _ _).trans ht
  have ht1 : 1≤t := hTa.trans hta
  by_cases hbad : FractionalObstruction G
  · exact Or.inr hbad
  by_cases hsep : ∃ X Y : Finset V, Disjoint X Y ∧
      listChromaticNumber G≤ell G X+S*t ∧ listChromaticNumber G≤ell G Y+S*t
  · exact Or.inl hsep
  have hn : Inseparable G (listChromaticNumber G) (S*t) := by
    intro X Y hd hx hy
    exact hsep ⟨X,Y,hd,hx,hy⟩
  have hinit : 6*(K₀*t)<listChromaticNumber G := by
    dsimp [ch,cf,K₀] at hS ⊢
    nlinarith
  obtain ⟨A₀,hA₀⟩ := State.initial (by omega) hinit
  obtain ⟨A,hA,hAs,hcover⟩ := hTs t hts
  have build : ∀ n : ℕ, n≤rounds t →
      ∃ X : State G t (listChromaticNumber G), X.history.q=n ∧
        ∀ r : Fin (rounds t), r.val<n → ∀ x∈A r, ∀ y∈A r, x≠y →
          ∃ v∈X.bag x, ∃ w∈X.bag y, G.Adj v w := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨A₀,hA₀,by intro r hr; omega⟩
    | succ n ih =>
      intro hnR
      obtain ⟨X,hX,hXadj⟩ := ih (by omega)
      let r : Fin (rounds t) := ⟨n,by omega⟩
      let a := (A r).card
      let e : Fin a ≃ ↥(A r) := (Fintype.equivFinOfCardEq (by simp [a])).symm
      let label : Fin a → Fin t := fun i => (e i).val
      have ha : 1≤a := card_pos.mpr (hA r)
      have hat : a≤t := by simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ (A r))
      rcases hAdvance t hta V G hminor hlist hn X (by rw [hX]; omega)
        a ha hat (hAs r) label with ⟨Y,hY,hretain,hnew⟩|hbad'
      swap
      · exact False.elim (hbad hbad')
      refine ⟨Y,by omega,?_⟩
      intro r' hr' x hx y hy hxy
      by_cases he : r'.val=n
      · have her : r'=r := Fin.ext he
        subst r'
        let ix := e.symm ⟨x,hx⟩
        let iy := e.symm ⟨y,hy⟩
        have hix : label ix=x := by simp [label,ix]
        have hiy : label iy=y := by simp [label,iy]
        have hne : ix≠iy := by intro he'; exact hxy (hix.symm.trans ((congrArg label he').trans hiy))
        simpa only [hix,hiy] using hnew ix iy hne
      · obtain ⟨v,hv,w,hw,hvw⟩ := hXadj r' (by omega) x hx y hy hxy
        exact ⟨v,hretain x hv,w,hretain y hw,hvw⟩
  obtain ⟨X,hX,hXadj⟩ := build (rounds t) le_rfl
  have hmodel : HasCliqueMinor G t := by
    refine ⟨X.bag,X.connected,X.disjoint,?_⟩
    intro i j hij
    obtain ⟨r,hi,hj⟩ := hcover i j
    exact hXadj r r.isLt i hi j hj hij
  exact False.elim (Nat.not_le_of_lt hminor (cliqueMinor_le_hadwigerNumber hmodel))

end LinearListHadwiger.Stage

end OAI
