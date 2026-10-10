import OAI.Combinatorics.ListHadwiger.SmallList

namespace OAI

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

theorem degenerate_of_phases {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (Y : Finset V) (phase : V → ℕ) (a b : ℕ)
    (hphase : ∀ i, DegenerateOn G (Y.filter (fun v => phase v = i)) a)
    (hback : ∀ v ∈ Y, (Y.filter (fun w => G.Adj v w ∧ phase w < phase v)).card ≤ b) :
    DegenerateOn G Y (a+b) := by
  intro T hT hn
  obtain ⟨u,hu,hmax⟩ := T.exists_max_image phase hn
  let P := T.filter (fun v => phase v = phase u)
  have hP : P ⊆ Y.filter (fun v => phase v = phase u) := by
    intro v hv
    exact mem_filter.mpr ⟨hT (mem_filter.mp hv).1, (mem_filter.mp hv).2⟩
  have hPn : P.Nonempty := ⟨u,mem_filter.mpr ⟨hu,rfl⟩⟩
  obtain ⟨v,hv,hdeg⟩ := hphase (phase u) P hP hPn
  have hvT := (mem_filter.mp hv).1
  have hpv := (mem_filter.mp hv).2
  have hsub : T.filter (G.Adj v) ⊆ (P.filter (G.Adj v)) ∪
      (Y.filter (fun w => G.Adj v w ∧ phase w < phase v)) := by
    intro w hw
    obtain ⟨hwT,hadj⟩ := mem_filter.mp hw
    have hle := hmax w hwT
    by_cases he : phase w = phase u
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hwT,he⟩,hadj⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hT hwT,hadj,by omega⟩)
  refine ⟨v,hvT,?_⟩
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add hdeg (hback v (hT hvT))))

theorem neighbors_in_collection {V J : Type} [DecidableEq V] [Fintype J]
    (G : SimpleGraph V) (B : J → Finset V) (v : V) (b d : ℕ)
    (hpath : ∀ j, ((B j).filter (G.Adj v)).card ≤ d)
    (hcount : (univ.filter (fun j => ∃ w ∈ B j, G.Adj v w)).card ≤ b) :
    ((univ.biUnion B).filter (G.Adj v)).card ≤ d*b := by
  classical
  let Jv := univ.filter (fun j => ∃ w ∈ B j, G.Adj v w)
  have he : (univ.biUnion B).filter (G.Adj v) =
      Jv.biUnion (fun j => (B j).filter (G.Adj v)) := by
    ext w
    simp only [mem_filter,mem_biUnion,mem_univ,true_and,Jv]
    constructor
    · rintro ⟨⟨j,hj⟩,hadj⟩
      exact ⟨j,⟨w,hj,hadj⟩,hj,hadj⟩
    · rintro ⟨j,_,hj,hadj⟩
      exact ⟨⟨j,hj⟩,hadj⟩
  rw [he]
  calc
    _ ≤ ∑ j ∈ Jv, ((B j).filter (G.Adj v)).card := card_biUnion_le
    _ ≤ ∑ _j ∈ Jv, d := sum_le_sum fun j _ => hpath j
    _ = d*Jv.card := by simp [mul_comm]
    _ ≤ d*b := Nat.mul_le_mul_left d hcount

theorem collection_incidence : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V J : Type) [Fintype V] [Fintype J] [DecidableEq V],
    ∀ (G : SimpleGraph V) (B : J → Finset V) (T : Finset V),
    hadwigerNumber G < t →
    (∀ j, (G.induce (↑(B j) : Set V)).Connected) →
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
    (∀ j, Disjoint T (B j)) →
    (∀ v ∈ T, 3202*t ≤ (univ.filter (fun j => ∃ w ∈ B j, G.Adj v w)).card) →
    (3202*t:ℝ)*T.card ≤ (t:ℝ)^(101/100:ℝ)*Fintype.card J := by
  classical
  obtain ⟨t₀,ht₀⟩ := Incidence.incidence_bound
  refine ⟨t₀,?_⟩
  intro t ht V J _ _ _ G B T hex hc hd hdis hlarge
  let C : J → Set V := fun j => ↑(B j)
  let H := BagContraction.graph G C
  let M := BagContraction.model G C hc (fun i j hij => by
    exact Set.disjoint_left.mpr (fun v hvi hvj => disjoint_left.mp (hd i j hij) hvi hvj))
  let A : Finset (BagContraction.Vertex C) := univ.image Sum.inr
  let f : ↥T → BagContraction.Vertex C := fun v => Sum.inl ⟨v.val,by
    intro j hj
    exact disjoint_left.mp (hdis j) v.property hj⟩
  have hf : Function.Injective f := by
    intro v w he
    exact Subtype.ext (congrArg (fun z : BagContraction.Vertex C =>
      match z with | Sum.inl x => x.val | Sum.inr _ => v.val) he)
  let T' := univ.image f
  have hAT : Disjoint A T' := by
    apply disjoint_left.mpr
    intro z hzA hzT
    obtain ⟨j,_,rfl⟩ := mem_image.mp hzA
    obtain ⟨v,_,hv⟩ := mem_image.mp hzT
    simp [f] at hv
  have hAc : A.card = Fintype.card J := by
    simp [A,card_image_of_injective _ Sum.inr_injective]
  have hTc : T'.card = T.card := by
    simp [T',card_image_of_injective _ hf]
  have hdegree : ∀ v : ↥T,
      (univ.filter (fun j => ∃ w ∈ B j, G.Adj v.val w)).card ≤
        (A.filter (H.Adj (f v))).card := by
    intro v
    let N := univ.filter (fun j => ∃ w ∈ B j, G.Adj v.val w)
    have hsub : N.image (Sum.inr : J → BagContraction.Vertex C) ⊆
        A.filter (H.Adj (f v)) := by
      intro z hz
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hz
      obtain ⟨w,hw,hadj⟩ := (mem_filter.mp hj).2
      refine mem_filter.mpr ⟨mem_image.mpr ⟨j,mem_univ _,rfl⟩,?_⟩
      exact ⟨by simp [f],
        v.val,rfl,w,hw,hadj⟩
    simpa only [card_image_of_injective _ Sum.inr_injective] using card_le_card hsub
  have hTlarge : ∀ z ∈ T', 3202*t ≤ (A.filter (H.Adj z)).card := by
    intro z hz
    obtain ⟨v,_,rfl⟩ := mem_image.mp hz
    exact (hlarge v.val v.property).trans (hdegree v)
  have hbound := ht₀ t ht (BagContraction.Vertex C) H
    (M.hadwiger_le.trans_lt hex) A T' hAT
  have he : T'.filter (fun z => 3202*t ≤ (A.filter (H.Adj z)).card) = T' :=
    filter_eq_self.mpr hTlarge
  rw [he,hAc] at hbound
  have hl : (3202*t:ℝ)*T'.card ≤ ∑ z ∈ T', ((A.filter (H.Adj z)).card : ℝ) := by
    calc
      _ = ∑ _z ∈ T', (3202*t:ℝ) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun z hz => by exact_mod_cast hTlarge z hz
  rw [hTc] at hl
  exact hl.trans hbound

theorem minimum_system_degenerate {V I J : Type} [DecidableEq V] [Fintype I]
    [DecidableEq I] (G : SimpleGraph V) (A : Finset V)
    (s : I → ↥(↑A : Set V)) (B : J → Set ↥(↑A : Set V))
    (D : BagRouting (G.induce (↑A : Set V)) s B) (hD : D.Minimal) :
    DegenerateOn G (D.usedFinset.image Subtype.val) (2*Fintype.card I) := by
  classical
  intro T hT hn
  let T' := D.usedFinset.filter (fun v => v.val ∈ T)
  have he : T'.image Subtype.val = T := by
    ext v
    constructor
    · rintro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hw).2
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp (hT hv)
      exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hv⟩,rfl⟩
  have hn' : T'.Nonempty := by
    obtain ⟨v,hv⟩ := hn
    rw [←he] at hv
    obtain ⟨w,hw,_⟩ := mem_image.mp hv
    exact ⟨w,hw⟩
  obtain ⟨v,hv,hd⟩ := hD.low_degree T' (filter_subset _ _) hn'
  refine ⟨v.val,(mem_filter.mp hv).2,?_⟩
  rw [←he,filter_image,card_image_of_injective _ Subtype.val_injective]
  exact hd

theorem minimum_system_path_neighbors {V I J : Type} [DecidableEq V] [Fintype I]
    [DecidableEq I] (G : SimpleGraph V) (A : Finset V)
    (s : I → ↥(↑A : Set V)) (B : J → Set ↥(↑A : Set V))
    (D : BagRouting (G.induce (↑A : Set V)) s B) (hD : D.Minimal)
    (i : I) (v : V) (hv : v ∈ A) (hout : v ∉ D.usedFinset.image Subtype.val) :
    (((D.paths i).2.val.support.toFinset.image Subtype.val).filter (G.Adj v)).card ≤ 3 := by
  classical
  let v' : ↥(↑A : Set V) := ⟨v,hv⟩
  have hv' : v' ∉ D.used := by
    intro hh
    exact hout (mem_image.mpr ⟨v',(D.mem_usedFinset v').mpr hh,rfl⟩)
  have hd := hD.path_neighbors_le_three i v' hv'
  rw [filter_image,card_image_of_injective _ Subtype.val_injective]
  exact hd

noncomputable def exceptional {V J : Type} [Fintype V] [Fintype J] [DecidableEq V]
    (G : SimpleGraph V) (B : J → Finset V) (F : Finset V) (t : ℕ) : Finset V :=
  univ.filter (fun v => v ∉ F ∧
    3202*t ≤ (univ.filter (fun j => ∃ w ∈ B j, G.Adj v w)).card)

theorem exceptional_card : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V J : Type) [Fintype V] [Fintype J] [DecidableEq V],
    ∀ (G : SimpleGraph V) (B : J → Finset V) (F : Finset V),
    hadwigerNumber G < t →
    (∀ j, (G.induce (↑(B j) : Set V)).Connected) →
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
    (∀ j, B j ⊆ F) →
    ((exceptional G B F t).card : ℝ) ≤ (t:ℝ)^(1/100:ℝ)*Fintype.card J := by
  classical
  obtain ⟨t₀,ht₀⟩ := collection_incidence
  refine ⟨max t₀ 1,?_⟩
  intro t ht V J _ _ _ G B F hex hc hd hBF
  let T := exceptional G B F t
  have hT := ht₀ t ((le_max_left _ _).trans ht) V J G B T hex hc hd
    (fun j => disjoint_left.mpr (fun v hv hvB => (mem_filter.mp hv).2.1 (hBF j hvB)))
    (fun v hv => (mem_filter.mp hv).2.2)
  have htnat : 1 ≤ t := (le_max_right _ _).trans ht
  have htpos : (0:ℝ) < t := by exact_mod_cast (Nat.zero_lt_of_lt htnat)
  have hp : (t:ℝ)^(101/100:ℝ) = (t:ℝ)^(1/100:ℝ)*t := by
    rw [←Real.rpow_add_one htpos.ne']
    norm_num
  rw [hp] at hT
  have hcnt : (0:ℝ) ≤ T.card := by positivity
  have hm : (t:ℝ)*T.card ≤ (3202*t:ℝ)*T.card := by nlinarith
  have hle := hm.trans hT
  nlinarith

theorem path_erase_start_connected {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {u v : V} (p : G.Path u v) (huv : u ≠ v) :
    (G.induce (↑(p.val.support.toFinset.erase u) : Set V)).Connected := by
  obtain ⟨p,hp⟩ := p
  cases p with
  | nil => exact (huv rfl).elim
  | @cons u w v huv' q =>
    have hu : u ∉ q.support := (List.nodup_cons.mp hp.support_nodup).1
    have he : ((SimpleGraph.Walk.cons huv' q).support.toFinset.erase u) = q.support.toFinset := by
      simp only [SimpleGraph.Walk.support_cons,List.toFinset_cons]
      exact erase_insert (by simpa using hu)
    have hs : (↑(q.support.toFinset) : Set V) = {x | x ∈ q.support} := by
      ext x
      simp
    rw [he,hs]
    exact q.connected_induce_support

theorem stripped_disjoint {V I J : Type} [DecidableEq V]
    {G : SimpleGraph V} {s : I → V} {B : J → Set V}
    (D : BagRouting G s B) (i j : I) (hij : i ≠ j) :
    Disjoint ((D.paths i).2.val.support.toFinset.erase (s i))
      ((D.paths j).2.val.support.toFinset.erase (s j)) := by
  apply disjoint_left.mpr
  intro v hv hw
  have hv' := mem_erase.mp hv
  have hw' := mem_erase.mp hw
  exact hv'.1 (D.overlap i j hij v (by simpa using hv'.2) (by simpa using hw'.2)).1

end LinearListHadwiger.Footprint

namespace LinearListHadwiger.Footprint
open Filter Real

noncomputable def rounds (t : ℝ) : ℕ := ⌈(Real.log t)^2⌉₊*(⌈(Real.log t)^2⌉₊+1)/2

lemma rounds_le_log {t : ℝ} (hlog : 1 ≤ Real.log t) :
    (rounds t : ℝ) ≤ 4*(Real.log t)^4 := by
  have hm : (⌈(Real.log t)^2⌉₊ : ℝ) ≤ 2*(Real.log t)^2 := by
    have hh := Nat.ceil_lt_add_one (sq_nonneg (Real.log t))
    nlinarith
  have hm0 : 1 ≤ ⌈(Real.log t)^2⌉₊ := by
    have hh := Nat.le_ceil ((Real.log t)^2)
    have : (1:ℝ) ≤ ⌈(Real.log t)^2⌉₊ := by nlinarith
    exact_mod_cast this
  have hround : rounds t ≤ ⌈(Real.log t)^2⌉₊^2 := by
    dsimp [rounds]
    apply Nat.div_le_of_le_mul
    nlinarith
  have hh : (rounds t : ℝ) ≤ (⌈(Real.log t)^2⌉₊ : ℝ)^2 := by exact_mod_cast hround
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ⌈(Real.log t)^2⌉₊) hm 2
  nlinarith

lemma exceptional_size_cutoff :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ 1 ≤ Real.log t ∧
      2*(rounds t:ℝ)*t^(106/100:ℝ)+(13*(rounds t:ℝ)+1)*t+
        6*(rounds t:ℝ)*((rounds t:ℝ)+1)*t^(101/100:ℝ) ≤ t^(11/10:ℝ) := by
  have hl := (isLittleO_log_rpow_rpow_atTop (8:ℝ)
    (show (0:ℝ)<4/100 by norm_num)).bound (show (0:ℝ)<1/181 by norm_num)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [eventually_ge_atTop (1:ℝ),hlog,hl] with t ht hlog hl
  have ht0 : 0<t := by linarith
  have hp : (Real.log t)^8 ≤ (1/181:ℝ)*t^(4/100:ℝ) := by
    simpa only [Real.norm_eq_abs, Real.rpow_ofNat,
      abs_of_nonneg (by positivity : 0 ≤ (Real.log t)^8),
      abs_of_nonneg (Real.rpow_nonneg ht0.le (4/100:ℝ))] using hl
  have ht1 : t ≤ t^(106/100:ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le ht (show (1:ℝ)≤106/100 by norm_num)
  have ht2 : t^(101/100:ℝ) ≤ t^(106/100:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  have h4 : 1 ≤ (Real.log t)^4 := one_le_pow₀ hlog
  have h48 : (Real.log t)^4 ≤ (Real.log t)^8 := pow_le_pow_right₀ hlog (by norm_num)
  have h8 : 1 ≤ (Real.log t)^8 := one_le_pow₀ hlog
  have hr := rounds_le_log hlog
  have hmid : 13*(rounds t:ℝ)+1 ≤ 53*(Real.log t)^8 := by nlinarith
  have hlast : 6*(rounds t:ℝ)*((rounds t:ℝ)+1) ≤ 120*(Real.log t)^8 := by
    have hnext : (rounds t:ℝ)+1 ≤ 5*(Real.log t)^4 := by linarith
    have hh := mul_le_mul hr hnext (by positivity : (0:ℝ)≤(rounds t:ℝ)+1)
      (by positivity : (0:ℝ)≤4*(Real.log t)^4)
    nlinarith
  refine ⟨ht,hlog,?_⟩
  calc
    _ ≤ 8*(Real.log t)^8*t^(106/100:ℝ)+53*(Real.log t)^8*t^(106/100:ℝ)+
        120*(Real.log t)^8*t^(106/100:ℝ) := by
      apply add_le_add (add_le_add ?_ ?_) ?_
      · exact mul_le_mul_of_nonneg_right (by linarith : 2*(rounds t:ℝ) ≤ 8*(Real.log t)^8)
          (by positivity)
      · exact mul_le_mul hmid ht1 ht0.le (by positivity)
      · exact mul_le_mul hlast ht2 (by positivity) (by positivity)
    _ = 181*(Real.log t)^8*t^(106/100:ℝ) := by ring
    _ ≤ t^(4/100:ℝ)*t^(106/100:ℝ) := by gcongr; linarith
    _ = t^(11/10:ℝ) := by rw [←Real.rpow_add ht0]; norm_num

end LinearListHadwiger.Footprint

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

structure System {V : Type} [DecidableEq V] (G : SimpleGraph V) where
  domain : Finset V
  n : ℕ
  source : Fin n → ↥(↑domain : Set V)
  target : Finset ↥(↑domain : Set V)
  routes : BagRouting (G.induce (↑domain : Set V)) source (fun v : ↥target => {v.val})
  minimal : routes.Minimal

namespace System
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}
noncomputable def path (S : System G) (i : Fin S.n) : Finset V :=
  (S.routes.paths i).2.val.support.toFinset.image Subtype.val
noncomputable def used (S : System G) : Finset V := S.routes.usedFinset.image Subtype.val
noncomputable def starts (S : System G) : Finset V := univ.image (fun i => (S.source i).val)
noncomputable def ends (S : System G) : Finset V :=
  univ.image (fun i => (S.routes.paths i).1.val)
noncomputable def stripped (S : System G) (i : Fin S.n) : Finset V :=
  S.path i \ {(S.source i).val}

lemma path_subset_domain (S : System G) (i : Fin S.n) : S.path i ⊆ S.domain := by
  intro v hv
  obtain ⟨w,_,rfl⟩ := mem_image.mp hv
  exact w.property

lemma mem_used (S : System G) (v : V) : v ∈ S.used ↔ ∃ i, v ∈ S.path i := by
  simp only [used,path,mem_image,BagRouting.usedFinset,mem_biUnion,mem_univ,true_and]
  aesop

lemma used_eq (S : System G) : S.used = univ.biUnion S.path := by
  ext v
  simp only [S.mem_used,mem_biUnion,mem_univ,true_and]

lemma path_subset_used (S : System G) (i : Fin S.n) : S.path i ⊆ S.used :=
  fun _ hv => (S.mem_used _).mpr ⟨i,hv⟩

lemma used_subset_domain (S : System G) : S.used ⊆ S.domain := by
  intro v hv
  obtain ⟨i,hi⟩ := (S.mem_used v).mp hv
  exact S.path_subset_domain i hi

lemma start_mem_path (S : System G) (i : Fin S.n) : (S.source i).val ∈ S.path i :=
  mem_image.mpr ⟨_,List.mem_toFinset.mpr (S.routes.paths i).2.val.start_mem_support,rfl⟩

lemma end_mem_path (S : System G) (i : Fin S.n) : (S.routes.paths i).1.val ∈ S.path i :=
  mem_image.mpr ⟨_,List.mem_toFinset.mpr (S.routes.paths i).2.val.end_mem_support,rfl⟩

lemma starts_card (S : System G) : S.starts.card ≤ S.n := by
  exact (card_image_le).trans (by simp)

lemma ends_card (S : System G) : S.ends.card ≤ S.n := by
  exact (card_image_le).trans (by simp)

lemma overlap (S : System G) {i j : Fin S.n} (hij : i ≠ j) {v : V}
    (hvi : v ∈ S.path i) (hvj : v ∈ S.path j) :
    v = (S.source i).val ∧ v = (S.source j).val := by
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hvi
  obtain ⟨w,hw,he⟩ := mem_image.mp hvj
  have he' : w=u := Subtype.ext he
  subst w
  have hh := S.routes.overlap i j hij u (List.mem_toFinset.mp hu) (List.mem_toFinset.mp hw)
  exact ⟨congrArg Subtype.val hh.1,congrArg Subtype.val hh.2⟩

lemma start_on_path (S : System G) (i : Fin S.n) {v : V}
    (hv : v ∈ S.path i) (hs : v ∈ S.starts) : v = (S.source i).val := by
  obtain ⟨j,_,rfl⟩ := mem_image.mp hs
  by_cases he : i=j
  · subst j; rfl
  · exact (S.overlap he hv (S.start_mem_path j)).1

lemma stripped_disjoint (S : System G) {i j : Fin S.n} (hij : i ≠ j) :
    Disjoint (S.stripped i) (S.stripped j) := by
  apply disjoint_left.mpr
  intro v hvi hvj
  exact (mem_sdiff.mp hvi).2 (mem_singleton.mpr
    (S.overlap hij (mem_sdiff.mp hvi).1 (mem_sdiff.mp hvj).1).1)

lemma paths_disjoint (S : System G) (hinj : Function.Injective S.source)
    {i j : Fin S.n} (hij : i ≠ j) : Disjoint (S.path i) (S.path j) := by
  apply disjoint_left.mpr
  intro v hv hw
  obtain ⟨hi,hj⟩ := S.overlap hij hv hw
  exact hij (hinj (Subtype.ext (hi.symm.trans hj)))

lemma degenerate (S : System G) : DegenerateOn G S.used (2*S.n) := by
  simpa only [used,Fintype.card_fin] using
    minimum_system_degenerate G S.domain S.source _ S.routes S.minimal

lemma path_neighbors (S : System G) (i : Fin S.n) (v : V)
    (hv : v ∈ S.domain) (hout : v ∉ S.used) :
    ((S.path i).filter (G.Adj v)).card ≤ 3 :=
  minimum_system_path_neighbors G S.domain S.source _ S.routes S.minimal i v hv hout

lemma used_neighbors (S : System G) (v : V) (hv : v ∈ S.domain) (hout : v ∉ S.used) :
    (S.used.filter (G.Adj v)).card ≤ 3*S.n := by
  rw [S.used_eq]
  exact neighbors_in_collection G S.path v S.n 3
    (fun i => S.path_neighbors i v hv hout) (by simpa using card_filter_le (univ : Finset (Fin S.n)) _)

lemma path_connected (S : System G) (i : Fin S.n) :
    (G.induce (↑(S.path i) : Set V)).Connected := by
  let f : G.induce (↑S.domain : Set V) →g G := ⟨Subtype.val,fun h => h⟩
  let p := (S.routes.paths i).2.val.map f
  have he : (↑(S.path i) : Set V) = {v | v ∈ p.support} := by
    ext v
    simp only [path,mem_coe,mem_image,List.mem_toFinset,Set.mem_ofPred_eq,p,
      SimpleGraph.Walk.support_map,List.mem_map]
    rfl
  rw [he]
  exact p.connected_induce_support

lemma stripped_connected (S : System G) (i : Fin S.n)
    (hne : (S.source i).val ≠ (S.routes.paths i).1.val) :
    (G.induce (↑(S.stripped i) : Set V)).Connected := by
  let f : G.induce (↑S.domain : Set V) →g G := ⟨Subtype.val,fun h => h⟩
  let p : G.Path (S.source i).val (S.routes.paths i).1.val :=
    ⟨(S.routes.paths i).2.val.map f,(S.routes.paths i).2.property.map Subtype.val_injective⟩
  have hp : S.path i = p.val.support.toFinset := by
    ext v
    simp only [path,mem_image,List.mem_toFinset,p,SimpleGraph.Walk.support_map,List.mem_map]
    rfl
  have he : S.stripped i = p.val.support.toFinset.erase (S.source i).val := by
    rw [stripped,hp,sdiff_singleton_eq_erase]
  rw [he]
  exact path_erase_start_connected p hne

end System
end LinearListHadwiger.Footprint

end OAI
