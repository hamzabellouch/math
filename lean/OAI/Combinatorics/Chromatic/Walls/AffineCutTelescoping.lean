import Mathlib

namespace OAI

section
namespace ElementaryPositivity.AffineCut
noncomputable section

def beforeSide (u v t : ℝ) : Bool :=
  decide (0 < u+t*v ∨ (u+t*v=0 ∧ v<0))
def afterSide (u v t : ℝ) : Bool :=
  decide (0 < u+t*v ∨ (u+t*v=0 ∧ 0<v))

lemma sides_eq_of_ne (u v t : ℝ) (h : u+t*v≠0) :
    beforeSide u v t=decide (0<u+t*v) ∧
    afterSide u v t=decide (0<u+t*v) := by
  simp [beforeSide,afterSide,h]

lemma sides_at_zero (u v t : ℝ) (h : u+t*v=0) :
    beforeSide u v t=decide (v<0) ∧
    afterSide u v t=decide (0<v) := by
  simp [beforeSide,afterSide,h]

lemma gap_sides (u v lo hi : ℝ) (h : lo<hi) (hne : u≠0 ∨ v≠0)
    (hz : ∀t,lo<t → t<hi → u+t*v≠0) :
    afterSide u v lo=beforeSide u v hi := by
  have hstraddle : ¬(u+lo*v<0 ∧ 0<u+hi*v) := by
    rintro ⟨hl,hh⟩
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc h.le
      (show ContinuousOn (fun t : ℝ => u+t*v) (Set.Icc lo hi) by fun_prop)
      (show (0:ℝ)∈Set.Icc (u+lo*v) (u+hi*v) from ⟨hl.le,hh.le⟩)
    have hl' : lo<t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
    have hh' : t<hi := lt_of_le_of_ne ht.2 (by rintro rfl; linarith)
    exact hz t hl' hh' he
  have hstraddle' : ¬(u+hi*v<0 ∧ 0<u+lo*v) := by
    rintro ⟨hh,hl⟩
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' h.le
      (show ContinuousOn (fun t : ℝ => u+t*v) (Set.Icc lo hi) by fun_prop)
      (show (0:ℝ)∈Set.Icc (u+hi*v) (u+lo*v) from ⟨hh.le,hl.le⟩)
    have hl' : lo<t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
    have hh' : t<hi := lt_of_le_of_ne ht.2 (by rintro rfl; linarith)
    exact hz t hl' hh' he
  unfold afterSide beforeSide
  apply Bool.decide_congr
  rcases lt_trichotomy v 0 with hv | hv | hv
  · have hm : u+hi*v<u+lo*v := by nlinarith
    constructor
    · rintro (hl | ⟨hl,hv'⟩)
      · by_cases hh : 0<u+hi*v
        · exact Or.inl hh
        · exact Or.inr ⟨le_antisymm (le_of_not_gt hh)
            (not_lt.mp (fun H=>hstraddle' ⟨H,hl⟩)),hv⟩
      · linarith
    · rintro (hh | ⟨hh,_⟩) <;> exact Or.inl (by linarith)
  · subst v
    have hu : u≠0 := hne.resolve_right (by simp)
    simp
  · have hm : u+lo*v<u+hi*v := by nlinarith
    constructor
    · rintro (hl | ⟨hl,_⟩) <;> exact Or.inl (by linarith)
    · rintro (hh | ⟨hh,hv'⟩)
      · by_cases hl : 0<u+lo*v
        · exact Or.inl hl
        · exact Or.inr ⟨le_antisymm (le_of_not_gt hl)
            (not_lt.mp (fun H=>hstraddle ⟨H,hh⟩)),hv⟩
      · linarith

theorem telescope {A B : Type*} (u v : ℝ) (hne : u≠0 ∨ v≠0)
    (old : ℝ → A → A) (new : ℝ → B → B) (chart : Bool → A → B)
    (l : List ℝ) (hsort : l.Pairwise (· > ·)) (lo hi : ℝ) (hlohi : lo<hi)
    (hmem : ∀t∈l,lo<t ∧ t<hi)
    (hcut : ∀t,lo<t → t<hi → u+t*v=0 → t∈l)
    (hlocal : ∀t∈l,∀x,new t (chart (beforeSide u v t) x)=
      chart (afterSide u v t) (old t x)) (x : A) :
    l.foldr new (chart (afterSide u v lo) x)=
      chart (beforeSide u v hi) (l.foldr old x) := by
  induction l generalizing lo hi with
  | nil =>
    simp only [List.foldr_nil]
    rw [gap_sides u v lo hi hlohi hne]
    intro t hlt hth ht
    exact List.not_mem_nil (hcut t hlt hth ht)
  | cons a l ih =>
    obtain ⟨has,hsort⟩:=List.pairwise_cons.mp hsort
    obtain ⟨hla,hah⟩:=hmem a (by simp)
    have hlmem : ∀t∈l,lo<t ∧ t<a := by
      intro t ht
      exact ⟨(hmem t (by simp [ht])).1,has t ht⟩
    have hlcut : ∀t,lo<t → t<a → u+t*v=0 → t∈l := by
      intro t hlt hta ht
      have H:=hcut t hlt (hta.trans hah) ht
      rcases List.mem_cons.mp H with rfl | H
      · exact False.elim (lt_irrefl _ hta)
      · exact H
    have hg : afterSide u v a=beforeSide u v hi := by
      apply gap_sides u v a hi hah hne
      intro t hat hth ht
      have H:=hcut t (hla.trans hat) hth ht
      rcases List.mem_cons.mp H with rfl | H
      · exact lt_irrefl _ hat
      · exact (lt_asymm hat (has t H))
    simp only [List.foldr_cons]
    rw [ih hsort lo a hla hlmem hlcut (fun t ht=>hlocal t (by simp [ht])),
      hlocal a (by simp),hg]

lemma sort_strict (S : Finset ℝ) : (S.sort (· ≥ ·)).Pairwise (· > ·) := by
  have hn : (S.sort (· ≥ ·)).Pairwise (· ≠ ·) := S.sort_nodup _
  exact ((S.pairwise_sort (· ≥ ·)).and hn).imp (fun h=>lt_of_le_of_ne h.1 (Ne.symm h.2))

theorem telescope_sort {A B : Type*} (u v : ℝ) (hne : u≠0 ∨ v≠0)
    (old : ℝ → A → A) (new : ℝ → B → B) (chart : Bool → A → B)
    (S : Finset ℝ) (lo hi : ℝ) (hlohi : lo<hi)
    (hmem : ∀t∈S,lo<t ∧ t<hi)
    (hcut : ∀t,lo<t → t<hi → u+t*v=0 → t∈S)
    (hlocal : ∀t∈S,∀x,new t (chart (beforeSide u v t) x)=
      chart (afterSide u v t) (old t x)) (x : A) :
    (S.sort (· ≥ ·)).foldr new (chart (afterSide u v lo) x)=
      chart (beforeSide u v hi) ((S.sort (· ≥ ·)).foldr old x) := by
  exact telescope u v hne old new chart (S.sort (· ≥ ·)) (sort_strict S) lo hi hlohi
    (by simpa only [Finset.mem_sort] using hmem)
    (by simpa only [Finset.mem_sort] using hcut)
    (by simpa only [Finset.mem_sort] using hlocal) x
end
end ElementaryPositivity.AffineCut

end

end OAI
