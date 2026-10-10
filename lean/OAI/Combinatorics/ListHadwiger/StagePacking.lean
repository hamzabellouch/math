import OAI.Combinatorics.ListHadwiger.RoleRouting

namespace OAI

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem extend_bags {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {t a : ℕ} (ht : 0<t)
    (F J H : Set V) (D : Finset V)
    (hFJ : Disjoint F J) (hFH : Disjoint F H) (hFD : Disjoint F (↑D : Set V))
    (hJH : Disjoint J H) (hJD : Disjoint J (↑D : Set V)) (hHD : Disjoint H (↑D : Set V))
    (B : Fin t → Set V) (w : Fin t → V)
    (hB : ∀ i, (G.induce (B i)).Connected)
    (hBB : ∀ i j, i≠j → Disjoint (B i) (B j))
    (hBF : ∀ i, B i⊆F) (hwB : ∀ i, w i∈B i)
    (u : Fin a → V) (M : RootedCliqueModel G u) (hMJ : ∀ j, M.branch j⊆J)
    (label : Fin a → Fin t) (w' : Fin t → V)
    (hw' : Function.Injective w') (hw'H : ∀ i, w' i∈H)
    (y : Roles t a → V) (hy : Function.Injective y) (hyD : ∀ p, y p∈D)
    (P : ∀ p, G.Path (roleStart w u w' p) (y p))
    (hPP : ∀ p q, p≠q → Disjoint {v | v∈(P p).val.support} {v | v∈(P q).val.support})
    (hPF : ∀ p v, v∈(P p).val.support → v∈F →
      ∃ i, p=Sum.inl i ∧ v=w i)
    (hPM : ∀ p j v, v∈(P p).val.support → v∈M.branch j → p=Sum.inr (Sum.inl j))
    (hPH : ∀ p v, v∈(P p).val.support → v∈H →
      ∃ i, p=Sum.inr (Sum.inr i) ∧ v=w' i)
    (hPD : ∀ p v, v∈(P p).val.support → v∈D → v=y p)
    (hDc : KConnectedOn G D (65536*(2*t+a)))
    (F' : Set V) (hFF' : F⊆F') (hJF' : J⊆F') (hDF' : (↑D : Set V)⊆F')
    (hPF' : ∀ p v, v∈(P p).val.support → v∈F') :
    ∃ B' : Fin t → Set V,
      (∀ i, (G.induce (B' i)).Connected) ∧
      (∀ i j, i≠j → Disjoint (B' i) (B' j)) ∧
      (∀ i, B i⊆B' i) ∧ (∀ i, w' i∈B' i) ∧
      (∀ j, M.branch j⊆B' (label j)) ∧ (∀ i, B' i⊆F') := by
  classical
  let owner := roleOwner label
  have hos : Function.Surjective owner := fun i => ⟨Sum.inl i,rfl⟩
  have hrc : Fintype.card (Roles t a)=2*t+a := by simp [Roles]; omega
  obtain ⟨E,hE,hEE,hED,hyE⟩ := grouped_ends G D y hy hyD owner hos
    (by rw [hrc]; omega) (by rw [hrc]; exact hDc)
  let C : Roles t a → Set V := Sum.elim B (Sum.elim M.branch (fun i => {w' i}))
  have hC : ∀ p, (G.induce (C p)).Connected := by
    rintro (i|j|i)
    · exact hB i
    · exact M.connected j
    · change (G.induce ({w' i} : Set V)).Connected
      exact SimpleGraph.Connected.of_subsingleton
  have hx : ∀ p, roleStart w u w' p∈C p := by
    rintro (i|j|i)
    · exact hwB i
    · exact M.root_mem j
    · exact Set.mem_singleton _
  have hCC : ∀ p q, p≠q → Disjoint (C p) (C q) := by
    rintro (i|j|i) (i'|j'|i') hne
    · exact hBB i i' (fun he => hne (congrArg Sum.inl he))
    · exact hFJ.mono (hBF i) (hMJ j')
    · exact hFH.mono (hBF i) (Set.singleton_subset_iff.mpr (hw'H i'))
    · exact hFJ.symm.mono (hMJ j) (hBF i')
    · exact M.disjoint j j' (fun he => hne (congrArg (Sum.inr ∘ Sum.inl) he))
    · exact hJH.mono (hMJ j) (Set.singleton_subset_iff.mpr (hw'H i'))
    · exact hFH.symm.mono (Set.singleton_subset_iff.mpr (hw'H i)) (hBF i')
    · exact hJH.symm.mono (Set.singleton_subset_iff.mpr (hw'H i)) (hMJ j')
    · apply Set.disjoint_singleton.mpr
      intro he
      exact hne (congrArg (Sum.inr ∘ Sum.inr) (hw' he))
  have hEC : ∀ i p, Disjoint (E i) (C p) := by
    intro i
    rintro (j|j|j)
    · exact hFD.symm.mono (hED i) (hBF j)
    · exact hJD.symm.mono (hED i) (hMJ j)
    · exact hHD.symm.mono (hED i) (Set.singleton_subset_iff.mpr (hw'H j))
  have hCP : ∀ p q, p≠q → Disjoint (C p) {v | v∈(P q).val.support} := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro v hv hvq
    rcases p with i | (j|i)
    · obtain ⟨j,hq,hv'⟩ := hPF q v hvq (hBF i hv)
      have hj : i=j := by
        by_contra hne
        exact Set.disjoint_left.mp (hBB i j hne) hv (hv'.symm ▸ hwB j)
      exact hpq (hj ▸ hq.symm)
    · exact hpq (hPM q j v hvq hv).symm
    · obtain ⟨j,hq,hv'⟩ := hPH q v hvq (by
        have he : v=w' i := hv
        exact he.symm ▸ hw'H i)
      have he : v=w' i := hv
      exact hpq (congrArg (Sum.inr ∘ Sum.inr) (hw' (he.symm.trans hv')) |>.trans hq.symm)
  have hEP : ∀ i p, i≠owner p → Disjoint (E i) {v | v∈(P p).val.support} := by
    intro i p hip
    apply Set.disjoint_left.mpr
    intro v hv hvp
    have he := hPD p v hvp (hED i hv)
    exact Set.disjoint_left.mp (hEE i (owner p) hip) hv (he.symm ▸ hyE p)
  let B' := extended E C owner (roleStart w u w') y P
  refine ⟨B',extended_connected E C owner _ _ P hE hC hx hyE,
    extended_disjoint E C owner _ _ P hEE
      (fun p q hpq => hCC p q (fun he => hpq (congrArg owner he)))
      (fun i p _ => hEC i p) hEP
      (fun p q hpq => hCP p q (fun he => hpq (congrArg owner he)))
      (fun p q hpq => hPP p q (fun he => hpq (congrArg owner he))),?_,?_,?_,?_⟩
  · intro i
    exact satellite_subset E C owner _ _ P (Sum.inl i)
  · intro i
    exact satellite_subset E C owner _ _ P (Sum.inr (Sum.inr i)) rfl
  · intro j
    exact satellite_subset E C owner _ _ P (Sum.inr (Sum.inl j))
  · apply extended_subset E C owner _ _ P (fun i => (hED i).trans hDF') _ hPF'
    rintro (i|j|i) v hv
    · exact hFF' (hBF i hv)
    · exact hJF' (hMJ j hv)
    · have he : v=w' i := hv
      exact he.symm ▸ hPF' (Sum.inr (Sum.inr i)) (w' i) (P _).val.start_mem_support

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset Footprint
attribute [local instance] Classical.propDecidable

theorem extend_with_systems {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {t a : ℕ} (ht : 0<t) (F J H D : Finset V)
    (B : Fin t → Set V) (w : Fin t → V)
    (hB : ∀ i, (G.induce (B i)).Connected)
    (hBB : ∀ i j, i≠j → Disjoint (B i) (B j))
    (hBF : ∀ i, B i⊆(↑F : Set V)) (hwB : ∀ i, w i∈B i)
    (hw : Function.Injective w)
    (u : Fin a → V) (hu : Function.Injective u) (huJ : ∀ j, u j∈J)
    (label : Fin a → Fin t)
    (hJF : Disjoint J F) (hDFJ : Disjoint D (F∪J))
    (R : System G) (hRU : R.domain=univ\(F\univ.image w))
    (P : DoublePacking G (oldSources w u) D)
    (hPR : ∀ i v, v∈(P.route i).val.support → v∈R.used)
    (hH : Disjoint H (F∪J∪D∪R.used))
    (Q : Second G (univ\(F∪univ.image u)) H D (2*t))
    (hJ : WovenOn G (↑J : Set V) a (3*t)) (ha : a≤t)
    (hDc : KConnectedOn G D (65536*(2*t+a))) :
    ∃ B' : Fin t → Set V, ∃ w' : Fin t → V,
      (∀ i, (G.induce (B' i)).Connected) ∧
      (∀ i j, i≠j → Disjoint (B' i) (B' j)) ∧
      (∀ i, B i⊆B' i) ∧ (∀ i, w' i∈B' i) ∧
      (∀ j j', j≠j' → ∃ v∈B' (label j), ∃ v'∈B' (label j'), G.Adj v v') ∧
      (∀ i, B' i⊆(↑(F∪J∪D∪R.used∪Q.record.used) : Set V)) ∧
      Function.Injective w' ∧ (∀ i, w' i∈Q.record.starts) := by
  classical
  have hHF : Disjoint H F := hH.mono_right (fun v hv => by simp [hv])
  have hHJ : Disjoint H J := hH.mono_right (fun v hv => by simp [hv])
  have hHD : Disjoint H D := hH.mono_right (fun v hv => by simp [hv])
  have hHR : Disjoint H R.used := hH.mono_right subset_union_right
  have hDF : Disjoint D F := hDFJ.mono_right subset_union_left
  have hDJ : Disjoint D J := hDFJ.mono_right subset_union_right
  have hwF (i) : w i∈F := hBF i (hwB i)
  have hwu : ∀ i j, w i≠u j := fun i j he =>
    Finset.disjoint_left.mp hJF (huJ j) (he ▸ hwF i)
  have hZH : Disjoint (oldSources w u) H := by
    apply Finset.disjoint_left.mpr
    intro v hv hvH
    rcases (mem_oldSources w u v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact Finset.disjoint_left.mp hHF hvH (hwF i)
    · exact Finset.disjoint_left.mp hHJ hvH (huJ j)
  have hZD : Disjoint (oldSources w u) D := by
    apply Finset.disjoint_left.mpr
    intro v hv hvD
    rcases (mem_oldSources w u v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact Finset.disjoint_left.mp hDF hvD (hwF i)
    · exact Finset.disjoint_left.mp hDJ hvD (huJ j)
  obtain ⟨L⟩ := combine_systems F H D w u hw hu hwu hwF hZH hZD hHD R hRU P hPR hHR.symm Q
  obtain ⟨M,hMJ,L',hLf,hML⟩ := L.weave (↑J : Set V) hJ hu huJ (by omega)
    (by exact_mod_cast hJF) (by exact_mod_cast hHJ.symm) (by exact_mod_cast hDJ.symm)
  have hFsubset : (↑F : Set V)⊆(↑(F∪J∪D∪R.used∪Q.record.used) : Set V) := by
    intro v hv; simp only [mem_coe,mem_union]; tauto
  have hJsubset : (↑J : Set V)⊆(↑(F∪J∪D∪R.used∪Q.record.used) : Set V) := by
    intro v hv; simp only [mem_coe,mem_union]; tauto
  have hDsubset : (↑D : Set V)⊆(↑(F∪J∪D∪R.used∪Q.record.used) : Set V) := by
    intro v hv; simp only [mem_coe,mem_union]; tauto
  have hLsubset : ∀ p v, v∈(L'.route p).val.support → v∈F∪J∪D∪R.used∪Q.record.used := by
    intro p v hv
    have hh := L'.inside p v hv
    simp only [Set.mem_union,mem_coe,mem_union] at hh ⊢
    tauto
  have htar : Function.Injective (fun p => (L'.target p).val) :=
    fun _ _ he => L'.target_injective (Subtype.ext he)
  obtain ⟨B',hB',hBB',hOld,hTips,hModels,hFin⟩ := extend_bags G ht
    (↑F : Set V) (↑J : Set V) (↑H : Set V) D
    (by exact_mod_cast hJF.symm) (by exact_mod_cast hHF.symm) (by exact_mod_cast hDF.symm)
    (by exact_mod_cast hHJ.symm) (by exact_mod_cast hDJ.symm) (by exact_mod_cast hHD)
    B w hB hBB hBF hwB u M hMJ label L'.fresh L'.fresh_injective L'.fresh_mem
    (fun p => (L'.target p).val) htar (fun p => (L'.target p).property)
    L'.route L'.disjoint L'.old_only hML L'.new_only L'.target_only hDc
    (↑(F∪J∪D∪R.used∪Q.record.used) : Set V) hFsubset hJsubset hDsubset hLsubset
  refine ⟨B',L'.fresh,hB',hBB',hOld,hTips,?_,hFin,L'.fresh_injective,?_⟩
  · intro j j' hj
    obtain ⟨v,hv,v',hv',hvv'⟩ := M.adjacent j j' hj
    exact ⟨v,hModels j hv,v',hModels j' hv',hvv'⟩
  · intro i
    rw [hLf]
    have hvH := L.fresh_mem i
    have hused := L.inside (Sum.inr (Sum.inr i)) (L.fresh i)
      (L.route (Sum.inr (Sum.inr i))).val.start_mem_support
    have hvQ : L.fresh i∈Q.record.used := by
      rcases mem_union.mp hused with hr|hq
      · exact False.elim (Finset.disjoint_left.mp hHR hvH hr)
      · exact hq
    rw [←Q.used_inter_region]
    exact mem_inter.mpr ⟨hvQ,hvH⟩

end LinearListHadwiger.Stage

end OAI
