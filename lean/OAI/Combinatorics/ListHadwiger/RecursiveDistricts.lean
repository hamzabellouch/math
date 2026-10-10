import OAI.Combinatorics.ListHadwiger.RecursiveGeometry

namespace OAI

namespace LinearListHadwiger.Recursion
open Finset
attribute [local instance] Classical.propDecidable

def child (a : ℕ) : ℕ := 2*((a+2)/3)

def triBlock {a : ℕ} (i : Fin a) : Fin 3 := ⟨i.val%3,Nat.mod_lt _ (by decide)⟩

def district {a : ℕ} (o : Fin a × Fin 2) : Fin 3 := (triBlock o.1).succAbove o.2

def districtLabels (a : ℕ) (d : Fin 3) : Finset (Fin a) :=
  univ.filter (fun i => triBlock i≠d)

lemma district_labels_card (a : ℕ) (d : Fin 3) : (districtLabels a d).card≤child a := by
  have he : districtLabels a d=(univ.erase d).biUnion (Stage.block a 3) := by
    ext i
    simp only [districtLabels,mem_filter,mem_univ,true_and,mem_biUnion,mem_erase]
    constructor
    · intro hi
      refine ⟨triBlock i,⟨hi,trivial⟩,?_⟩
      exact mem_filter.mpr ⟨mem_univ _,rfl⟩
    · rintro ⟨b,⟨hbd,_⟩,hib⟩
      have hi : triBlock i=b := by
        apply Fin.ext
        exact (mem_filter.mp hib).2
      exact hi ▸ hbd
  rw [he]
  have hb (b : Fin 3) : (Stage.block a 3 b).card≤(a+2)/3 :=
    Stage.block_card_le (by decide) (by omega) b
  calc
    #((univ.erase d).biUnion (Stage.block a 3))≤∑b∈univ.erase d,(Stage.block a 3 b).card := card_biUnion_le
    _ ≤ ∑_b∈univ.erase d,(a+2)/3 := sum_le_sum (fun b _ => hb b)
    _ = child a := by simp [child]

lemma district_mem_labels {a : ℕ} (o : Fin a × Fin 2) :
    o.1∈districtLabels a (district o) := by
  exact mem_filter.mpr ⟨mem_univ _,Ne.symm (Fin.succAbove_ne _ _)⟩

lemma district_pair_coverage {a : ℕ} (i j : Fin a) :
    ∃ k l : Fin 2, district (i,k)=district (j,l) := by
  have third : ∀ i j : Fin 3, ∃ d, d≠i ∧ d≠j := by decide
  obtain ⟨d,hdi,hdj⟩ := third (triBlock i) (triBlock j)
  obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hdi
  obtain ⟨l,hl⟩ := Fin.exists_succAbove_eq hdj
  exact ⟨k,l,hk.trans hl.symm⟩

lemma district_same_injective {a : ℕ} (o p : Fin a × Fin 2)
    (hl : o.1=p.1) (hd : district o=district p) : o=p := by
  apply Prod.ext hl
  have he : (triBlock o.1).succAbove o.2=(triBlock o.1).succAbove p.2 := by
    simpa only [district,hl] using hd
  exact Fin.succAbove_right_injective he

lemma child_shrink {a : ℕ} (ha : 24<a) : 1≤child a ∧ child a<a ∧ 4*child a≤3*a := by
  dsimp [child]
  omega

lemma path_capacity (a : ℕ) : 2*a≤3*child a := by
  dsimp [child]
  omega

lemma district_indices (a : ℕ) :
    ∃ index : (Fin a × Fin 2) → Fin (child a),
      ∀ o p, district o=district p → index o=index p → o=p := by
  classical
  let f (d : Fin 3) : ↥(districtLabels a d) ↪ Fin (child a) :=
    (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (by simpa only [Fintype.card_coe] using district_labels_card a d))
  let index (o : Fin a × Fin 2) := f (district o) ⟨o.1,district_mem_labels o⟩
  refine ⟨index,?_⟩
  intro o p hd hi
  have key (d e : Fin 3) (i : ↥(districtLabels a d)) (j : ↥(districtLabels a e))
      (hde : d=e) (hij : f d i=f e j) : i.val=j.val := by
    subst e
    exact congrArg Subtype.val ((f d).injective hij)
  have hlabel : o.1=p.1 := key _ _ _ _ hd hi
  exact district_same_injective o p hlabel hd

end LinearListHadwiger.Recursion

namespace LinearListHadwiger.Recursion
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem three_district_model (G : SimpleGraph V) {a : ℕ} (ha : 1≤a)
    (S : Finset V) (r : Fin a → V) (hr : Function.Injective r) (hrS : ∀ i, r i∈S)
    (n : Fin a × Fin 2 → V) (hn : Function.Injective n)
    (hnS : ∀ o, n o∈S) (hnr : ∀ o i, n o≠r i)
    (hnadj : ∀ o, G.Adj (n o) (r o.1))
    (J : Fin 3 → Set V) (hJS : ∀ d, J d⊆(↑S:Set V))
    (hJr : ∀ d i, r i∉J d) (hJn : ∀ d o, n o∉J d)
    (hJJ : ∀ d e, d≠e → Disjoint (J d) (J e))
    (hJ : ∀ d, WovenOn G (J d) (child a) (3*child a))
    (u : Fin 3 → Fin (child a) → V) (hu : ∀ d, Function.Injective (u d))
    (huJ : ∀ d j, u d j∈J d)
    (hc : KConnectedOn G (S\univ.image r) (65536*(4*a))) :
    ∃ M : RootedCliqueModel G r, ∀ i, M.branch i⊆(↑S:Set V) := by
  classical
  obtain ⟨index,hindex⟩ := district_indices a
  let x (o : Fin a × Fin 2) := u (district o) (index o)
  have hx (o) : x o∈J (district o) := huJ _ _
  have hxi : Function.Injective x := by
    intro o p h
    have hd : district o=district p := by
      by_contra hne
      exact Set.disjoint_left.mp (hJJ _ _ hne) (hx o) (h ▸ hx p)
    have hi : index o=index p := (hu (district o)) (by simpa only [x,←hd] using h)
    exact hindex o p hd hi
  let z : (Fin a × Fin 2) × Bool → V := fun q => if q.2 then n q.1 else x q.1
  have hzi : Function.Injective z := by
    rintro ⟨o,b⟩ ⟨p,c⟩ h
    cases b <;> cases c
    · exact Prod.ext (hxi h) rfl
    · change x o=n p at h
      exact (hJn (district o) p (h ▸ hx o)).elim
    · change n o=x p at h
      exact (hJn (district p) o (h.symm ▸ hx p)).elim
    · exact Prod.ext (hn h) rfl
  have hzS (q) : z q∈S\univ.image r := by
    rcases q with ⟨o,b⟩
    cases b
    · refine mem_sdiff.mpr ⟨hJS _ (hx o),?_⟩
      rintro h
      obtain ⟨i,_,hi⟩ := mem_image.mp h
      exact hJr (district o) i (hi ▸ hx o)
    · refine mem_sdiff.mpr ⟨hnS o,?_⟩
      rintro h
      obtain ⟨i,_,hi⟩ := mem_image.mp h
      exact hnr o i hi.symm
  have hcard : Fintype.card (Fin a × Fin 2)=2*a := by simp [Nat.mul_comm]
  have hc' : KConnectedOn G (S\univ.image r) (65536*(2*Fintype.card (Fin a × Fin 2))) := by
    rw [hcard]; convert hc using 1; omega
  obtain ⟨P,hPS,hPP⟩ := paired_paths_on G (S\univ.image r) z hzi hzS (by rw [hcard]; omega) hc'
  change ∀ o, G.Path (x o) (n o) at P
  obtain ⟨M,hMJ,Q,hQQ,hQP,hQM⟩ := reroute_disjoint_districts J hJ hJJ u hu huJ x n P
    (by rw [hcard]; exact path_capacity a) hPP
  have hQS (o) (v) (hv : v∈(Q o).val.support) : v∈S\univ.image r := by
    by_cases hj : ∃ d, v∈J d
    · obtain ⟨d,hd⟩ := hj
      refine mem_sdiff.mpr ⟨hJS d hd,?_⟩
      rintro hm
      obtain ⟨i,_,hi⟩ := mem_image.mp hm
      exact hJr d i (hi ▸ hd)
    · exact hPS o v (hQP o v hv (by simpa only [not_exists] using hj))
  let C (o : Fin a × Fin 2) := (M (district o)).branch (index o)
  have hC (o) : (G.induce (C o)).Connected := (M _).connected _
  have hCx (o) : x o∈C o := (M _).root_mem _
  have hCJ (o) : C o⊆J (district o) := hMJ _ _
  have hCC (o p) (hne : o≠p) : Disjoint (C o) (C p) := by
    by_cases hd : district o=district p
    · have hi : index o≠index p := fun h => hne (hindex o p hd h)
      change Disjoint ((M (district o)).branch (index o)) ((M (district p)).branch (index p))
      rw [←hd]
      exact (M _).disjoint _ _ hi
    · exact (hJJ _ _ hd).mono (hCJ o) (hCJ p)
  have hPC (o p v) (hv : v∈(Q o).val.support) (hw : v∈C p) : v=x o ∧ v=x p :=
    hQM (district p) o (index p) v ⟨p,rfl⟩ hv hw
  have hRC (o i) : r i∉C o := fun hv => hJr _ i (hCJ o hv)
  have hRP (o i) : r i∉(Q o).val.support := fun hv =>
    (mem_sdiff.mp (hQS o (r i) hv)).2 (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
  have hpairs (i j : Fin a) (hij : i≠j) : ∃ o p : Fin a × Fin 2,
      o.1=i ∧ p.1=j ∧ ∃ v∈C o, ∃ w∈C p, G.Adj v w := by
    obtain ⟨k,l,hd⟩ := district_pair_coverage i j
    have hne : index (i,k)≠index (j,l) := fun h => hij (congrArg Prod.fst (hindex _ _ hd h))
    obtain ⟨v,hv,w,hw,he⟩ := (M (district (i,k))).adjacent _ _ hne
    refine ⟨(i,k),(j,l),rfl,rfl,v,hv,w,?_,he⟩
    change w∈(M (district (j,l))).branch (index (j,l))
    rw [←hd]
    exact hw
  obtain ⟨R,hR⟩ := rooted_from_bag_routes G r hr Prod.fst x n hxi C Q hC hCx hCC hQQ
    hPC hRC hRP hnadj hpairs
  refine ⟨R,?_⟩
  intro i v hv
  rw [hR] at hv
  rcases hv with hv | ⟨o,_,hv|hv⟩
  · exact hv ▸ hrS i
  · exact hJS _ (hCJ o hv)
  · exact (mem_sdiff.mp (hQS o v hv)).1

end LinearListHadwiger.Recursion

namespace LinearListHadwiger.Recursion
open Finset Stage SmallList
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem separability_on : ∃ S : ℕ, 1≤S ∧ ∃ T : ℕ, 1≤T ∧
    ∀ t : ℕ, T≤t → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (H : Finset V), hadwigerNumber G<t → 2*S*t≤ell G H →
    (∃ X⊆H, ∃ Y⊆H, Disjoint X Y ∧ ell G H≤ell G X+S*t ∧ ell G H≤ell G Y+S*t) ∨
      FractionalObstruction G := by
  obtain ⟨S,hS,T,hT,hs⟩ := separability_or_obstruction
  refine ⟨S,hS,T,hT,?_⟩
  intro t ht V _ _ G H hm hl
  rcases hs t ht (↑H:Set V) (G.induce (↑H:Set V))
    ((Knitting.model_induce G H).hadwiger_le.trans_lt hm) hl with ⟨X,Y,hd,hX,hY⟩|hb
  · left
    have himg (A : Finset (↑H:Set V)) : A.image Subtype.val⊆H := by
      rintro v hv
      obtain ⟨w,_,rfl⟩ := mem_image.mp hv
      exact w.property
    refine ⟨X.image Subtype.val,himg X,Y.image Subtype.val,himg Y,?_,?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro v hv hw
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
      obtain ⟨y,hy,he⟩ := mem_image.mp hw
      exact Finset.disjoint_left.mp hd hx (Subtype.val_injective he ▸ hy)
    · have he := ell_image G (Subtype.val : (↑H:Set V)→V) Subtype.val_injective X
      change ell (G.induce (↑H:Set V)) X=ell G (X.image Subtype.val) at he
      change ell G H≤ell (G.induce (↑H:Set V)) X+S*t at hX
      rwa [he] at hX
    · have he := ell_image G (Subtype.val : (↑H:Set V)→V) Subtype.val_injective Y
      change ell (G.induce (↑H:Set V)) Y=ell G (Y.image Subtype.val) at he
      change ell G H≤ell (G.induce (↑H:Set V)) Y+S*t at hY
      rwa [he] at hY
  · exact Or.inr (obstruction_induce G H hb)

theorem three_regions : ∃ S : ℕ, 1≤S ∧ ∃ T : ℕ, 1≤T ∧
    ∀ t : ℕ, T≤t → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (H : Finset V) (k R : ℕ), 1≤k → hadwigerNumber G<t →
    3*S*t≤ell G H → R+6*k+2*S*t<ell G H →
    (∃ J : Fin 3 → Finset V,
      (∀ d, J d⊆H) ∧ (∀ d e, d≠e → Disjoint (J d) (J e)) ∧
      (∀ d, KConnectedOn G (J d) k) ∧ (∀ d, R<ell G (J d))) ∨ FractionalObstruction G := by
  obtain ⟨S,hS,T,hT,hs⟩ := separability_on
  refine ⟨S,hS,T,hT,?_⟩
  intro t ht V _ _ G H k R hk hm hsep hlarge
  rcases hs t ht V G H hm (by nlinarith) with ⟨X,hXH,Y,hYH,hXY,hX,hY⟩|hb
  swap
  · exact Or.inr hb
  rcases hs t ht V G X hm (by nlinarith) with ⟨A,hAX,B,hBX,hAB,hA,hB⟩|hb
  swap
  · exact Or.inr hb
  obtain ⟨A',hA'A,hA'c,hA'l⟩ := extract_on G A hk (by nlinarith)
  obtain ⟨B',hB'B,hB'c,hB'l⟩ := extract_on G B hk (by nlinarith)
  obtain ⟨Y',hY'Y,hY'c,hY'l⟩ := extract_on G Y hk (by nlinarith)
  let J : Fin 3 → Finset V := ![A',B',Y']
  have hj (d : Fin 3) : J d⊆H ∧ KConnectedOn G (J d) k ∧ R<ell G (J d) := by
    fin_cases d
    · exact ⟨hA'A.trans (hAX.trans hXH),hA'c,by dsimp [J]; nlinarith⟩
    · exact ⟨hB'B.trans (hBX.trans hXH),hB'c,by dsimp [J]; nlinarith⟩
    · exact ⟨hY'Y.trans hYH,hY'c,by dsimp [J]; nlinarith⟩
  have hab : Disjoint A' B' := hAB.mono hA'A hB'B
  have hay : Disjoint A' Y' := hXY.mono (hA'A.trans hAX) hY'Y
  have hby : Disjoint B' Y' := hXY.mono (hB'B.trans hBX) hY'Y
  refine Or.inl ⟨J,fun d => (hj d).1,?_,fun d => (hj d).2.1,fun d => (hj d).2.2⟩
  intro d e hde
  fin_cases d <;> fin_cases e
  · exact (hde rfl).elim
  · exact hab
  · exact hay
  · exact hab.symm
  · exact (hde rfl).elim
  · exact hby
  · exact hay.symm
  · exact hby.symm
  · exact (hde rfl).elim

end LinearListHadwiger.Recursion

end OAI
