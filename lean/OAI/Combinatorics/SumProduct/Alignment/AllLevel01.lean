import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice10
import OAI.Combinatorics.SumProduct.Alignment.TailCharacter01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators
namespace IntegerHyperplane
variable {n : ℕ}
lemma split_prefix_zero_iff (k : Fin (n+1) → ℤ) (p : Fin (n+1))
    (hp : k p≠0) (hlast : ∀ j : Fin (n+1),p<j → k j=0)
    (x : Fin (n+1) → ℝ) (t : ℕ) (hpt : p.val<t) :
    (∀ j : Fin (n+1),j.val<t → splitCoordinates k p x j=0) ↔
      ∀ j : Fin (n+1),j.val<t → x j=0 := by
  have htz : 0<t := by omega
  have hpR : (k p:ℝ)≠0 := by exact_mod_cast hp
  have hcut (j : Fin n) : (p.succAbove j).val<t ↔ j.val+1<t := by
    rw [succAbove_lt_cutoff]
    simp only [deletedCutoff,ite_eq_left hpt]
    omega
  constructor
  · intro hx j hj
    have hhead : form k x=0 := by
      have hh:=hx 0 htz
      change form k x/(k p:ℝ)=0 at hh
      exact (div_eq_zero_iff.mp hh).resolve_right hpR
    have hl:=congrFun (lift_remove k p hp x hhead) j
    rw [← hl]
    apply (lift_prefix_zero_iff k p hlast (p.removeNth x) t).mpr
    · intro a ha
      have hat : a.val+1<t := by simp only [deletedCutoff,ite_eq_left hpt] at ha; omega
      exact hx a.succ hat
    · exact hj
  · intro hx j hj
    revert hj
    refine Fin.cases ?_ (fun a => ?_) j <;> intro hj
    · change form k x/(k p:ℝ)=0
      have hf : form k x=0 := by
        change (∑ a,(k a:ℝ)*x a)=0
        apply Finset.sum_eq_zero
        intro a _
        by_cases hat : a.val<t
        · rw [hx a hat,mul_zero]
        · rw [hlast a (by change p.val<a.val; omega),Int.cast_zero,zero_mul]
      rw [hf,zero_div]
    · change x (p.succAbove a)=0
      exact hx _ ((hcut a).mpr hj)
end IntegerHyperplane

namespace TailCharacterRechart
open RationalLattice MalcevCharacters RationalTailCoordinates IntegerHyperplane
open BlockSplitCoordinates TailRefinementCharts RationalPolynomialMap
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r n : ℕ} (c : RealCoordinates G (r+(n+1)))
variable (k : Fin (n+1) → ℤ) (p : Fin (n+1)) (hp : k p≠0)

omit [IsTopologicalGroup G] in
lemma chart_early_zero_iff [IsTopologicalGroup G] (g : G) (s : ℕ) (hs : s≤r) :
    (∀ i : Fin (r+(n+1)),i.val<s → chartHomeomorph c k p hp g i=0) ↔
      ∀ i : Fin (r+(n+1)),i.val<s → c.coord g i=0 := by
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro hi
  rw [chart_prefix c k p hp g i (lt_of_lt_of_le hi hs)]

omit [IsTopologicalGroup G] in
lemma chart_late_zero_iff [IsTopologicalGroup G] (hlast : ∀ j : Fin (n+1),p<j → k j=0)
    (g : G) (s : ℕ) (hs : r+p.val<s) :
    (∀ i : Fin (r+(n+1)),i.val<s → chartHomeomorph c k p hp g i=0) ↔
      ∀ i : Fin (r+(n+1)),i.val<s → c.coord g i=0 := by
  have hpt : p.val<s-r := by omega
  have he := split_prefix_zero_iff k p hp hlast
    (fun j => c.coord g (embed r j)) (s-r) hpt
  have ht (a : Fin (n+1)) : chartHomeomorph c k p hp g (embed r a)=
      splitCoordinates k p (fun j => c.coord g (embed r j)) a := blockMap_embed _ _ _
  constructor
  · intro hx i hi
    by_cases hir : i.val<r
    · rw [← chart_prefix c k p hp g i hir]
      exact hx i hi
    · let a : Fin (n+1):=⟨i.val-r,by omega⟩
      have ha : i=embed r a := by apply Fin.ext; simp [a,embed]; omega
      rw [ha]
      apply he.mp
      · intro j hj
        rw [← ht]
        exact hx _ (by change r+j.val<s; omega)
      · dsimp [a]; omega
  · intro hx i hi
    by_cases hir : i.val<r
    · rw [chart_prefix c k p hp g i hir]
      exact hx i hi
    · let a : Fin (n+1):=⟨i.val-r,by omega⟩
      have ha : i=embed r a := by apply Fin.ext; simp [a,embed]; omega
      rw [ha,ht]
      apply he.mpr
      · intro j hj
        exact hx _ (by change r+j.val<s; omega)
      · dsimp [a]; omega

variable (H : Subgroup G)
variable (hH : ∀ g : G,g∈H ↔ ∀ i : Fin (r+(n+1)),i.val<r → c.coord g i=0)
variable (χ : H →* Multiplicative ℝ)
variable (hχ : ∀ x : H,(χ x).toAdd=form k ((tailCoordinates c H hH).coord x))

omit [IsTopologicalGroup G] in
lemma tail_of_mem [IsTopologicalGroup G] (g : H) : tail c H hH g.val=g := by
  apply Subtype.ext
  apply c.coord.injective
  funext i
  by_cases hi : i.val<r
  · rw [(hH _).mp (tail c H hH g.val).property i hi,(hH _).mp g.property i hi]
  · let a : Fin (n+1):=⟨i.val-r,by omega⟩
    have ha : i=embed r a := by apply Fin.ext; simp [a,embed]; omega
    rw [ha,tail_coord]

include hχ in
 

lemma chart_kernel (g : G) :
    g∈χ.ker.map H.subtype ↔
      ∀ i : Fin (r+(n+1)),i.val<r+1 → chartHomeomorph c k p hp g i=0 := by
  have hpR : (k p:ℝ)≠0 := by exact_mod_cast hp
  constructor
  · rintro ⟨x,hx,rfl⟩ i hi
    change chartHomeomorph c k p hp x.val i=0
    by_cases hir : i.val<r
    · rw [chart_prefix c k p hp x.val i hir]
      exact (hH _).mp x.property i hir
    · have he : i=embed r 0 := by apply Fin.ext; change i.val=r+0; omega
      rw [he,chart_head_character c k p hp H hH χ hχ,tail_of_mem]
      change χ x=1 at hx
      rw [hx]
      exact zero_div _
  · intro hx
    have hg : g∈H := (hH g).mpr (fun i hi => by
      rw [← chart_prefix c k p hp g i hi]
      exact hx i (by omega))
    refine ⟨⟨g,hg⟩,?_,rfl⟩
    change χ ⟨g,hg⟩=1
    apply Multiplicative.toAdd.injective
    have hh:=hx (embed r 0) (by change r+0<r+1; omega)
    rw [chart_head_character c k p hp H hH χ hχ] at hh
    have he : tail c H hH g=⟨g,hg⟩:=tail_of_mem c H hH ⟨g,hg⟩
    rw [he] at hh
    exact (div_eq_zero_iff.mp hh).resolve_right hpR

include hp hχ in
lemma pivot_lt_of_kills (K : Subgroup G) (s : ℕ)
    (hK : ∀ g : G,g∈K ↔ ∀ i : Fin (r+(n+1)),i.val<s → c.coord g i=0)
    (hkill : ∀ x : H,x.val∈K → χ x=1) : r+p.val<s := by
  classical
  by_contra hno
  let x : H:=axis (tailCoordinates c H hH) p 1
  have hx : x.val∈K := by
    apply (hK _).mpr
    intro i hi
    rw [show x.val=axis c (embed r p) 1 from axis_val c H hH p 1]
    have hine : i≠embed r p := by intro he; rw [he] at hi; change r+p.val<s at hi; omega
    simp [axis,hine]
  have hz:=congrArg Multiplicative.toAdd (hkill x hx)
  change (χ x).toAdd=0 at hz
  rw [hχ] at hz
  have he : form k ((tailCoordinates c H hH).coord x)=(k p:ℝ) := by
    dsimp [x,axis]
    simp [form,Pi.single_apply]
  rw [he] at hz
  exact hp (by exact_mod_cast hz)

include hH in
 

theorem exists_refined_integer_cover (hsk : SecondKind c) (Γ : Subgroup G)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (χ : H →* Multiplicative ℝ) (hcont : Continuous χ)
    (hz : ∀ x : H,x.val∈Γ → ∃ z : ℤ,(χ x).toAdd=z) (hne : χ≠1)
    (hconj : ∀ (g : G) (x : H),g⁻¹*x.val*g∈H)
    (hχconj : ∀ (g : G) (x : H),χ ⟨g⁻¹*x.val*g,hconj g x⟩=χ x) :
    ∃ Λ : Subgroup G,∃ e : RealCoordinates G (r+(n+1)),SecondKind e ∧
      (∀ g : G,g∈Λ ↔ ∀ i,∃ z : ℤ,e.coord g i=z) ∧
      Λ≤Γ ∧ (Λ.subgroupOf Γ).FiniteIndex ∧
      (∀ g : G,IsRational e g → IsRational c g) ∧
      (∀ g : G,g∈χ.ker.map H.subtype ↔
        ∀ i : Fin (r+(n+1)),i.val<r+1 → e.coord g i=0) ∧
      (∀ K : Subgroup G,∀ s : ℕ,s≤r →
        (∀ g : G,g∈K ↔ ∀ i : Fin (r+(n+1)),i.val<s → c.coord g i=0) →
        ∀ g : G,g∈K ↔ ∀ i : Fin (r+(n+1)),i.val<s → e.coord g i=0) ∧
      (∀ K : Subgroup G,∀ s : ℕ,
        (∀ g : G,g∈K ↔ ∀ i : Fin (r+(n+1)),i.val<s → c.coord g i=0) →
        (∀ x : H,x.val∈K → χ x=1) →
        r<s ∧ ∀ g : G,g∈K ↔ ∀ i : Fin (r+(n+1)),i.val<s → e.coord g i=0) := by
  obtain ⟨a,ha⟩:=integer_character_coordinates (tailCoordinates c H hH)
    (tail_secondKind c H hH hsk) χ (Γ.comap H.subtype)
    (tailCoordinates_lattice c H hH Γ hΓ) hcont hz
  have ha' : ∀ x : H,(χ x).toAdd=form a ((tailCoordinates c H hH).coord x) := by
    intro x
    rw [ha]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have ha0 : a≠0 := by
    intro he
    apply hne
    ext x
    apply Multiplicative.toAdd.injective
    change (χ x).toAdd=0
    rw [ha',he]
    simp [form]
  obtain ⟨q,hq,hlast⟩:=exists_last_nonzero a ha0
  let d:=tailCharacterCoordinates c a q hq hlast hsk H hH χ hconj hχconj ha'
  have hpoly : ∀ i,RationalPolynomialMap.IsPolynomial
      (fun x : Fin (r+(n+1)) → ℝ => c.coord (d.coord.symm x) i) :=
    inverse_polynomial c a q hq
  obtain ⟨Λ,e,hΛ,hle,hidx,hzero,hrat⟩:=exists_integer_sublattice_rational c d (MonoidHom.id G)
    hpoly Γ hΓ continuous_id Function.injective_id
  have hd (K : Subgroup G) (s : ℕ)
      (hK : ∀ g : G,g∈K ↔ ∀ i : Fin (r+(n+1)),i.val<s → d.coord g i=0) :
      ∀ g : G,g∈K ↔ ∀ i : Fin (r+(n+1)),i.val<s → (secondCoordinates e).coord g i=0 := by
    apply secondCoordinates_adapted e K s
    intro g
    rw [hK]
    exact forall_congr' (fun i => imp_congr_right (fun _ => (hzero g i).symm))
  refine ⟨Λ,secondCoordinates e,secondCoordinates_secondKind e,
    expCoordinates_lattice e Λ hΛ,hle,hidx,?_,?_,?_,?_⟩
  · intro g hg
    apply rationalHom_rational c d (MonoidHom.id G) hpoly
    exact (hrat g).mp ((secondCoordinates_rational e g).mp hg)
  · exact hd _ (r+1) (chart_kernel c a q hq H hH χ ha')
  · intro K s hs hK
    apply hd K s
    intro g
    exact (hK g).trans (chart_early_zero_iff c a q hq g s hs).symm
  · intro K s hK hkill
    have hqs:=pivot_lt_of_kills c a q hq H hH χ ha' K s hK hkill
    refine ⟨by omega,?_⟩
    apply hd K s
    intro g
    exact (hK g).trans (chart_late_zero_iff c a q hq hlast g s hqs).symm

end TailCharacterRechart

end
 
end

section
 

 

noncomputable section
open scoped commutatorElement
namespace AllLevelFactorization
open CubeFaces CubePolynomials NilpotentTaylor
variable {G : Type*} [Group G]

section Shrink
variable (H : Filtration G) (h01 : H.level 0=H.level 1)
variable (j : ℕ) (hj : 0<j) (K : Subgroup G)
variable (hK : K ≤ H.level j) (hnext : H.level (j+1) ≤ K)
variable (hbr : ∀ a b : ℕ, 0<a → 0<b → a+b=j → ⁅H.level a,H.level b⁆ ≤ K)

def shrinkLevel (k : ℕ) : Subgroup G := if max 1 k=j then K else H.level k

include hK in
lemma shrinkLevel_le (k : ℕ) : shrinkLevel H j K k ≤ H.level k := by
  unfold shrinkLevel
  split_ifs with hk
  · exact hK.trans (H.antitone (by omega))
  · exact le_rfl

include h01 hK in
lemma shrinkLevel_le_one : shrinkLevel H j K 0 ≤ H.level 1 := by
  rw [← h01]
  exact shrinkLevel_le H j K hK 0

include hj hK hnext in
lemma shrinkLevel_antitone : Antitone (shrinkLevel H j K) := by
  intro a b hab
  unfold shrinkLevel
  split_ifs with hb ha ha
  · exact le_rfl
  · exact hK.trans (H.antitone (by omega))
  · exact (H.antitone (by omega : j+1≤b)).trans hnext
  · exact H.antitone hab

include h01 hj hK hnext hbr in
lemma shrinkLevel_commutator (a b : ℕ) :
    ⁅shrinkLevel H j K a,shrinkLevel H j K b⁆ ≤ shrinkLevel H j K (a+b) := by
  by_cases ht : max 1 (a+b)=j
  · rw [show shrinkLevel H j K (a+b)=K from ite_eq_left ht]
    by_cases ha : a=0
    · subst a
      by_cases hb : b=0
      · subst b
        have hj1 : j=1 := by omega
        exact (Subgroup.commutator_mono (shrinkLevel_le_one H h01 j K hK)
          (shrinkLevel_le_one H h01 j K hK)).trans
          ((H.commutator_le 1 1).trans (by simpa [hj1] using hnext))
      · have hb' : b=j := by omega
        subst b
        exact (Subgroup.commutator_mono (shrinkLevel_le_one H h01 j K hK)
          (shrinkLevel_le H j K hK j)).trans
          ((H.commutator_le 1 j).trans (by simpa [Nat.add_comm] using hnext))
    · by_cases hb : b=0
      · subst b
        have ha' : a=j := by omega
        subst a
        exact (Subgroup.commutator_mono (shrinkLevel_le H j K hK j)
          (shrinkLevel_le_one H h01 j K hK)).trans ((H.commutator_le j 1).trans hnext)
      · exact (Subgroup.commutator_mono (shrinkLevel_le H j K hK a)
          (shrinkLevel_le H j K hK b)).trans (hbr a b (by omega) (by omega) (by omega))
  · rw [show shrinkLevel H j K (a+b)=H.level (a+b) from ite_eq_right ht]
    exact (Subgroup.commutator_mono (shrinkLevel_le H j K hK a)
      (shrinkLevel_le H j K hK b)).trans (H.commutator_le a b)

 

def shrink : Filtration G where
  level := shrinkLevel H j K
  antitone := shrinkLevel_antitone H j hj K hK hnext
  commutator_le := shrinkLevel_commutator H h01 j hj K hK hnext hbr

lemma shrink_zero_one :
    (shrink H h01 j hj K hK hnext hbr).level 0 =
      (shrink H h01 j hj K hK hnext hbr).level 1 := by
  simp only [shrink,shrinkLevel,max_self,Nat.max_eq_left (by omega : 0≤1)]
  split_ifs <;> first | rfl | exact h01

lemma shrink_at : (shrink H h01 j hj K hK hnext hbr).level j=K := by
  simp [shrink,shrinkLevel,Nat.max_eq_right hj]

lemma shrink_other {k : ℕ} (hk : 0<k) (hkj : k≠j) :
    (shrink H h01 j hj K hK hnext hbr).level k=H.level k := by
  simp [shrink,shrinkLevel,Nat.max_eq_right hk,hkj]

end Shrink

section LevelCharacter
variable (H : Filtration G) (h01 : H.level 0=H.level 1)
variable (j : ℕ) (hj : 0<j) (χ : H.level j →* Multiplicative ℝ)
variable (hnext : ∀ x : H.level j, x.val∈H.level (j+1) → χ x=1)
variable (hbr : ∀ a b : ℕ, 0<a → 0<b → a+b=j →
  ∀ x∈H.level a, ∀ y∈H.level b, ∀ hc : ⁅x,y⁆∈H.level j, χ ⟨⁅x,y⁆,hc⟩=1)

def levelKernel : Subgroup G := χ.ker.map (H.level j).subtype

lemma levelKernel_le : levelKernel H j χ ≤ H.level j := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

lemma mem_levelKernel (x : H.level j) : x.val∈levelKernel H j χ ↔ χ x=1 := by
  constructor
  · rintro ⟨y,hy,he⟩
    have : y=x := Subtype.ext he
    simpa only [this] using (show χ y=1 from hy)
  · intro hx
    exact ⟨x,hx,rfl⟩

include hnext in
lemma next_le_levelKernel : H.level (j+1) ≤ levelKernel H j χ := by
  intro x hx
  exact (mem_levelKernel H j χ ⟨x,H.antitone (by omega) hx⟩).mpr (hnext _ hx)

include hbr in
lemma brackets_le_levelKernel (a b : ℕ) (ha : 0<a) (hb : 0<b) (hab : a+b=j) :
    ⁅H.level a,H.level b⁆ ≤ levelKernel H j χ := by
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  have hc : ⁅x,y⁆∈H.level j := hab ▸ H.commutator_le a b (Subgroup.commutator_mem_commutator hx hy)
  exact (mem_levelKernel H j χ ⟨⁅x,y⁆,hc⟩).mpr (hbr a b ha hb hab x hx y hy hc)

 

def kernelFiltration : Filtration G :=
  shrink H h01 j hj (levelKernel H j χ) (levelKernel_le H j χ)
    (next_le_levelKernel H j χ hnext) (brackets_le_levelKernel H j χ hbr)

end LevelCharacter

section TaylorComparison

lemma word_node_cutoff (a : ℕ → G) {n d : ℕ} (hnd : n<d) :
    word a d (n:ℤ)=word a (n+1) (n:ℤ) := by
  induction d with
  | zero => omega
  | succ d ih =>
    by_cases hn : n=d
    · subst n; rfl
    · rw [word]
      simp only [Pi.mul_apply,Ring.choose_natCast,Nat.choose_eq_zero_of_lt (by omega : n<d),
        Nat.cast_zero,zpow_zero,mul_one]
      exact ih (by omega)

lemma word_node (a : ℕ → G) (n : ℕ) :
    word a (n+1) (n:ℤ)=word a n (n:ℤ)*a n := by
  simp [word,Ring.choose_natCast]

lemma coefficients_eq_of_initial {a b : ℕ → G} {d k : ℕ} (hkd : k≤d)
    (h : ∀ n<k, word a d (n:ℤ)=word b d (n:ℤ)) : ∀ n<k,a n=b n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn' : n<d := lt_of_lt_of_le hn hkd
    have hp : word a n=word b n := word_congr n (fun i hi => ih i hi (by omega))
    have he := h n hn
    rw [word_node_cutoff a hn',word_node_cutoff b hn',word_node,word_node,hp] at he
    exact mul_left_cancel he

 

theorem corrected_taylor_coefficients {a b : ℕ → G} {d j : ℕ} (hj : j<d)
    (u v : G)
    (h : ∀ n : ℤ, word b d n=(u^Ring.choose n j)⁻¹*word a d n*(v^Ring.choose n j)⁻¹) :
    (∀ i<j,b i=a i) ∧
      b j=(word a j (j:ℤ))⁻¹*u⁻¹*(word a j (j:ℤ))*a j*v⁻¹ := by
  have hlow : ∀ n<j,word b d (n:ℤ)=word a d (n:ℤ) := by
    intro n hn
    rw [h,Ring.choose_natCast,Nat.choose_eq_zero_of_lt hn]
    simp
  have hc := coefficients_eq_of_initial (Nat.le_of_lt hj) hlow
  refine ⟨hc,?_⟩
  have hp : word b j=word a j := word_congr j hc
  have he := h (j:ℤ)
  rw [word_node_cutoff b hj,word_node_cutoff a hj,word_node,word_node,hp] at he
  simp only [Ring.choose_natCast,Nat.choose_self,Nat.cast_one,zpow_one] at he
  calc b j = (word a j (j:ℤ))⁻¹*(word a j (j:ℤ)*b j) := by group
       _ = (word a j (j:ℤ))⁻¹*(u⁻¹*(word a j (j:ℤ)*a j)*v⁻¹) := by rw [he]
       _ = _ := by group

lemma word_mem_subgroup (K : Subgroup G) (a : ℕ → G) (d : ℕ)
    (ha : ∀ i<d,a i∈K) (z : ℤ) : word a d z∈K := by
  induction d with
  | zero => exact K.one_mem
  | succ d ih =>
    exact K.mul_mem (ih (fun i hi => ha i (by omega))) (K.zpow_mem (ha d (by omega)) _)

end TaylorComparison

section CharacterCorrection
variable (H : Filtration G) (j : ℕ) (χ : H.level j →* Multiplicative ℝ)
variable (hnext : ∀ x : H.level j, x.val∈H.level (j+1) → χ x=1)

lemma commutator_next {p x : G} (hp : p∈H.level 1) (hx : x∈H.level j) :
    ⁅p,x⁆∈H.level (j+1) := by
  simpa only [Nat.add_comm] using H.commutator_le 1 j (Subgroup.commutator_mem_commutator hp hx)

lemma conjugate_mem {p : G} (hp : p∈H.level 1) (x : H.level j) :
    p⁻¹*x.val*p∈H.level j := by
  have hc := commutator_next H j ((H.level 1).inv_mem hp) x.property
  have he : p⁻¹*x.val*p=⁅p⁻¹,x.val⁆*x.val := by simp [commutatorElement_def,mul_assoc]
  rw [he]
  exact (H.level j).mul_mem (H.antitone (by omega) hc) x.property

include hnext in
lemma character_conjugate {p : G} (hp : p∈H.level 1) (x : H.level j) :
    χ ⟨p⁻¹*x.val*p,conjugate_mem H j hp x⟩=χ x := by
  let z : H.level j := ⟨⁅p⁻¹,x.val⁆,
    H.antitone (by omega : j≤j+1) (commutator_next H j ((H.level 1).inv_mem hp) x.property)⟩
  have hz : χ z=1 := hnext z (commutator_next H j ((H.level 1).inv_mem hp) x.property)
  have he : (⟨p⁻¹*x.val*p,conjugate_mem H j hp x⟩ : H.level j)=z*x := by
    apply Subtype.ext
    simp [z,commutatorElement_def,mul_assoc]
  rw [he,map_mul,hz,one_mul]

include hnext in
lemma character_correction {p : G} (hp : p∈H.level 1) (u v a : H.level j)
    (hχ : (χ u).toAdd+(χ v).toAdd=(χ a).toAdd) :
    (p⁻¹*u.val⁻¹*p*a.val*v.val⁻¹)∈levelKernel H j χ := by
  let b : H.level j := ⟨p⁻¹*u.val⁻¹*p,conjugate_mem H j hp (u⁻¹)⟩*a*v⁻¹
  have hb : χ b=1 := by
    dsimp only [b]
    rw [map_mul,map_mul]
    have hc : χ ⟨p⁻¹*u.val⁻¹*p,conjugate_mem H j hp (u⁻¹)⟩=χ (u⁻¹) :=
      character_conjugate H j χ hnext hp (u⁻¹)
    rw [hc,map_inv,map_inv]
    change -(χ u).toAdd+(χ a).toAdd+ -(χ v).toAdd=0
    linarith
  exact (mem_levelKernel H j χ b).mpr hb

end CharacterCorrection

section OneStep
variable (H : Filtration G) (h01 : H.level 0=H.level 1)
variable (j : ℕ) (hj : 0<j) (χ : H.level j →* Multiplicative ℝ)
variable (hnext : ∀ x : H.level j, x.val∈H.level (j+1) → χ x=1)
variable (hbr : ∀ a b : ℕ, 0<a → 0<b → a+b=j →
  ∀ x∈H.level a, ∀ y∈H.level b, ∀ hc : ⁅x,y⁆∈H.level j, χ ⟨⁅x,y⁆,hc⟩=1)

 

theorem one_level_descent (d : ℕ) (hd : H.level d=⊥) (hjd : j<d)
    (a : ℕ → G) (ha : ∀ i<d,a i∈H.level i) (ha0 : a 0=1)
    (u v : H.level j)
    (hχ : (χ u).toAdd+(χ v).toAdd=(χ ⟨a j,ha j hjd⟩).toAdd) :
    ∃ b : ℕ → G,
      (∀ i<d,b i∈(kernelFiltration H h01 j hj χ hnext hbr).level i) ∧
      (∀ i<j,b i=a i) ∧
      (∀ z : ℤ, (u.val^Ring.choose z j)⁻¹*word a d z*(v.val^Ring.choose z j)⁻¹=word b d z) := by
  let f : ℤ → G := fun z => (u.val^Ring.choose z j)⁻¹*word a d z*(v.val^Ring.choose z j)⁻¹
  have hu : (fun z : ℤ => u.val^Ring.choose z j)∈polynomials H 0 :=
    binomial_mem j 0 u.val (by simp)
  have hv : (fun z : ℤ => v.val^Ring.choose z j)∈polynomials H 0 :=
    binomial_mem j 0 v.val (by simp)
  have hf : f∈polynomials H 0 :=
    (polynomials H 0).mul_mem
      ((polynomials H 0).mul_mem ((polynomials H 0).inv_mem hu)
        (word_mem a d (by simpa using ha))) ((polynomials H 0).inv_mem hv)
  obtain ⟨b,hb,he⟩ := exists_taylor (H:=H) (k:=0) (d:=d) (by simpa using hd) hf
  have he' : ∀ z : ℤ, word b d z=(u.val^Ring.choose z j)⁻¹*word a d z*(v.val^Ring.choose z j)⁻¹ :=
    fun z => (congrFun he z).symm
  obtain ⟨hlow,hjcoef⟩ := corrected_taylor_coefficients hjd u.val v.val he'
  have hp : word a j (j:ℤ)∈H.level 1 := by
    apply word_mem_subgroup
    intro i hi
    by_cases hi0 : i=0
    · subst i; rw [ha0]; exact (H.level 1).one_mem
    · exact H.antitone (by omega : 1 ≤ i) (ha i (by omega))
  have hkernel : b j∈levelKernel H j χ := by
    rw [hjcoef]
    exact character_correction H j χ hnext hp u v ⟨a j,ha j hjd⟩ hχ
  refine ⟨b,?_,hlow,fun z => congrFun he z⟩
  intro i hi
  change b i∈shrinkLevel H j (levelKernel H j χ) i
  unfold shrinkLevel
  split_ifs with hij
  · by_cases hi0 : i=0
    · subst i
      rw [hlow 0 hj,ha0]
      exact (levelKernel H j χ).one_mem
    · have : i=j := by omega
      simpa only [this] using hkernel
  · simpa using hb i hi

include h01 hj hnext hbr in
 
theorem corrected_polynomial (d : ℕ) (hd : H.level d=⊥) (hjd : j<d)
    (a : ℕ → G) (ha : ∀ i<d,a i∈H.level i) (ha0 : a 0=1)
    (u v : H.level j)
    (hχ : (χ u).toAdd+(χ v).toAdd=(χ ⟨a j,ha j hjd⟩).toAdd) :
    (fun z : ℤ => (u.val^Ring.choose z j)⁻¹*word a d z*(v.val^Ring.choose z j)⁻¹)∈
      polynomials (kernelFiltration H h01 j hj χ hnext hbr) 0 := by
  obtain ⟨b,hb,_,he⟩ := one_level_descent H h01 j hj χ hnext hbr d hd hjd a ha ha0 u v hχ
  rw [show (fun z : ℤ => (u.val^Ring.choose z j)⁻¹*word a d z*(v.val^Ring.choose z j)⁻¹)=word b d from funext he]
  exact word_mem b d (by simpa using hb)

end OneStep

end AllLevelFactorization

end
end
end
end

end OAI
