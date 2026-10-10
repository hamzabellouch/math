import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.IncidencesDegrees
import OAI.Combinatorics.RamseyFive.Entropy.LogContractionDrop
import OAI.Combinatorics.RamseyFive.Marking.ChooseLevel

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

noncomputable def scanChoice (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) : Option (Fin 5) :=
  if Expensive (scanState a b q n) (a n) (b n) q then
    if h : chooseLevel (scanState a b q n) (finrank K (scanState a b q n (b n)))<5
      then some ⟨_,h⟩ else none
  else none

lemma scanChoice_isSome (hdim : finrank K V=5)
    (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (N : ℕ)
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N) : (scanChoice a b q n).isSome ↔
      Expensive (scanState a b q n) (a n) (b n) q := by
  have hl : chooseLevel (scanState a b q n) (finrank K (scanState a b q n (b n)))<5 :=
    (chooseLevel_le _ _).trans_lt (Nat.lt_succ_iff.mpr (scan_rank hdim a b q N hF hn))
  simp only [scanChoice,dite_eq_left hl]
  split_ifs <;> simp_all

theorem scanSet_card_bound (hdim : finrank K V=5)
    (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (hq : 0<q) (N : ℕ)
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i)) :
    ((scanSet a b q N).card:ℝ)≤800*q*Real.log (1+Fintype.card (ℙ K (Dual K V))) := by
  let S : ℕ → Fin 5 → Finset (ℙ K (Dual K V)) :=
    fun n j => upperSet (scanState a b q n) j.val
  have hm : ∀ n<N,∀ j,S (n+1) j⊆S n j := by
    intro n _ j y hy
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    exact (Submodule.finrank_mono (scanState_mono a b q n y)).trans (Finset.mem_filter.mp hy).2
  have hc : ∀ n<N,∀ j,scanChoice a b q n=some j →
      (S n j).Nonempty ∧ ((S (n+1) j).card:ℝ)≤(1-1/(80*q))*(S n j).card := by
    intro n hn j hj
    have he : Expensive (scanState a b q n) (a n) (b n) q :=
      (scanChoice_isSome hdim a b q N hF hn).mp (by rw [hj]; rfl)
    have hl : chooseLevel (scanState a b q n) (finrank K (scanState a b q n (b n)))<5 :=
      (chooseLevel_le _ _).trans_lt (Nat.lt_succ_iff.mpr (scan_rank hdim a b q N hF hn))
    have hjval : j.val=chooseLevel (scanState a b q n) (finrank K (scanState a b q n (b n))) := by
      have heq : j=⟨_,hl⟩ := by
        simpa only [scanChoice,ite_eq_left he,dite_eq_left hl,Option.some.injEq] using hj.symm
      exact congrArg Fin.val heq
    let W:=scanState a b q n
    let l:=chooseLevel W (finrank K (W (b n)))
    have hnon:=chooseLevel_nonempty W (b n)
    constructor
    · obtain ⟨y,hy⟩:=hnon
      refine ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
      rw [hjval]
      exact (Finset.mem_filter.mp hy).2.le
    · change ((upperSet (scanState a b q (n+1)) j.val).card:ℝ)≤
        (1-1/(80*q))*((upperSet (scanState a b q n) j.val).card:ℝ)
      rw [scanState_update a b q n he,hjval]
      exact expensive_contraction W (a n) (b n) l q hq
        (chooseLevel_sublevel W _ (scan_rank hdim a b q N hF hn)) he.2.le he.1.le
  have hb:=finite_scan_bound S (scanChoice a b q) N (1/(80*q)) (by positivity) hm hc
  have hfilter : ((Finset.range N).filter fun n => (scanChoice a b q n).isSome)=
      (Finset.range N).filter fun n => Expensive (state a b (scanSet a b q n)) (a n) (b n) q := by
    apply Finset.filter_congr
    intro n hn
    exact scanChoice_isSome hdim a b q N hF (Finset.mem_range.mp hn)
  have hzero (j : Fin 5) : S 0 j=Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro y
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    change finrank K (state a b ∅ y)≤j.val
    rw [state_empty]
    simp
  rw [hfilter,←scan_count] at hb
  simp only [hzero,Finset.card_univ] at hb
  have hsum : (∑ j:Fin 5,Real.log (1+(Fintype.card (ℙ K (Dual K V)):ℝ)))=
      5*Real.log (1+(Fintype.card (ℙ K (Dual K V)):ℝ)) := by simp
  rw [hsum] at hb
  have hid : (1/(80*q))/2=1/(160*q) := by ring
  rw [hid] at hb
  have hh:=mul_le_mul_of_nonneg_right hb (show 0≤160*q by positivity)
  have hz : 160*q≠0 := by positivity
  field_simp at hh
  nlinarith

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def popularDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r l : ℕ) : Finset (ℙ K V × ℙ K (Dual K V)) :=
  ((Finset.univ : Finset (ℙ K V)) ×ˢ (Finset.univ.filter fun b : ℙ K (Dual K V) =>
    finrank K (W b)=r ∧ ((levelSet W l).card:ℝ)/(16*Nat.card K)≤ memberships W (levelSet W l) b)).filter
    fun ab => ab.1.submodule≤(W ab.2).dualCoannihilator

noncomputable def poorDomain (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (r l : ℕ) : Finset (ℙ K V × ℙ K (Dual K V)) :=
  ((Finset.univ.filter fun a : ℙ K V =>
    (((levelSet W l).filter fun y => Incident a y).card:ℝ)≤((levelSet W l).card:ℝ)/(8*Nat.card K)) ×ˢ
      upperSet W r).filter fun ab => Incident ab.1 ab.2

theorem popularDomain_card (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r l : ℕ) (hlr : l≤r) (hr : r≤4)
    (hZ : (levelSet W l).Nonempty) :
    ((popularDomain W r l).card:ℝ)≤64*(Nat.card K:ℝ)^4 :=
  popular_joint_count hdim W r l hlr hr hZ _ (fun _ hb => (Finset.mem_filter.mp hb).2)

theorem poorDomain_card (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) (hr : r≤4) :
    ((poorDomain W r (chooseLevel W r)).card:ℝ)≤89*(Nat.card K:ℝ)^4 := by
  apply poor_joint_count hdim _ _ _ (fun a ha => (Finset.mem_filter.mp ha).2)
  exact (chooseLevel_large W r).trans (Nat.mul_le_mul_right _ (by omega))

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in

lemma scan_annihilator (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (N : ℕ)
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N) : (a n).submodule≤(scanState a b q n (b n)).dualCoannihilator := by
  rw [←Submodule.le_dualAnnihilator_iff_le_dualCoannihilator]
  apply iSup₂_le
  intro i hi
  split_ifs with hab
  · exact (incident_iff_dualAnnihilator _ _).mp
      (hF i n (Finset.mem_range.mp (scanSet_subset a b q n hi)) hn hab)
  · exact bot_le

omit [Finite K] [FiniteDimensional K V] in

theorem cheap_mem_domains (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (N : ℕ)
    (hflag : ∀ n<N,Incident (a n) (b n))
    (hF : ∀ i j,i<j → j<N → Incident (a i) (b j) → Incident (a j) (b i))
    {n : ℕ} (hn : n<N)
    (hc : ¬Expensive (scanState a b (Nat.card K) n) (a n) (b n) (Nat.card K)) :
    let W:=scanState a b (Nat.card K) n
    let r:=finrank K (W (b n))
    let l:=chooseLevel W r
    (a n,b n)∈popularDomain W r l ∨ (a n,b n)∈poorDomain W r l := by
  dsimp only
  let W:=scanState a b (Nat.card K) n
  let r:=finrank K (W (b n))
  let l:=chooseLevel W r
  change (a n,b n)∈popularDomain W r l ∨ (a n,b n)∈poorDomain W r l
  by_cases hp : ((levelSet W l).card:ℝ)/(16*Nat.card K)≤ memberships W (levelSet W l) (b n)
  · left
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,hp⟩⟩
    · exact scan_annihilator a b (Nat.card K) N hF hn
  · right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hflag n hn⟩
    · apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      apply le_of_not_gt
      intro hpoor
      apply hc
      exact ⟨lt_of_not_ge hp,hpoor⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_rfl⟩

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in

lemma state_congr_on (a a' : ι → ℙ K V) (b b' : ι → ℙ K (Dual K V))
    (E : Finset ι) (ha : ∀ i∈E,a i=a' i) (hb : ∀ i∈E,b i=b' i) :
    state a b E=state a' b' E := by
  funext y
  apply le_antisymm
  · apply iSup₂_le
    intro i hi
    rw [ha i hi,hb i hi]
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  · apply iSup₂_le
    intro i hi
    rw [←ha i hi,←hb i hi]
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

end SharpRamseyFive.Marking

end OAI
