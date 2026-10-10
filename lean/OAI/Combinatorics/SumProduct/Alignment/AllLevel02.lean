import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped commutatorElement
end
 
end

section
 

 

noncomputable section
open scoped BigOperators commutatorElement
namespace AllLevelGeometry
open RationalLattice MalcevCharacters RationalTailCoordinates CubeFaces AllLevelFactorization
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)

omit [IsTopologicalGroup G] in
lemma cutoff_le_of_subgroup_le [IsTopologicalGroup G] (A B : Subgroup G) (r s : ℕ) (hr : r≤n)
    (hA : ∀ g : G,g∈A ↔ ∀ i : Fin n,i.val<r → c.coord g i=0)
    (hB : ∀ g : G,g∈B ↔ ∀ i : Fin n,i.val<s → c.coord g i=0)
    (hAB : B≤A) : r ≤ s := by
  by_contra hn
  have hsn : s<n := by omega
  let i : Fin n:=⟨s,hsn⟩
  let g:=axis c i 1
  have hg : g∈B := by
    apply (hB g).mpr
    intro k hk
    change c.coord (axis c i 1) k=0
    rw [coord_axis]
    apply Pi.single_eq_of_ne
    exact (show k ≠ i from by
      intro h
      have hh := congrArg Fin.val h
      dsimp [i] at hh
      omega)
  have hz:=(hA g).mp (hAB hg) i (by dsimp [i]; omega)
  change c.coord (axis c i 1) i=0 at hz
  simp only [coord_axis, Pi.single_eq_same] at hz
  norm_num at hz

lemma top_cutoff_zero (r : ℕ) (hr : r≤n)
    (htop : ∀ g : G,∀ i : Fin n,i.val<r → c.coord g i=0) : r=0 := by
  have hh:=cutoff_le_of_subgroup_le c ⊤ ⊤ r 0 hr
    (by intro g; simp only [Subgroup.mem_top, true_iff]; exact htop g)
    (by intro g; simp) le_rfl
  omega

omit [IsTopologicalGroup G] in
lemma cutoff_lt_of_character [IsTopologicalGroup G] {H : Subgroup G} (r : ℕ) (hr : r≤n)
    (hH : ∀ g : G,g∈H ↔ ∀ i : Fin n,i.val<r → c.coord g i=0)
    (χ : H →* Multiplicative ℝ) (hne : χ≠1) : r<n := by
  by_contra hn
  have he : r=n := by omega
  apply hne
  ext x
  have hx : x=1 := by
    apply Subtype.ext
    apply c.coord.injective
    funext i
    change c.coord x.val i=c.coord 1 i
    rw [(hH _).mp x.property i (by omega),c.one_coord]
  simp [hx]

variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable (r : ℕ → ℕ) (hr : ∀ k,r k≤n)
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,i.val<r k → c.coord g i=0)

include hr hH in
lemma cutoffs_monotone : Monotone r := by
  intro a b hab
  exact cutoff_le_of_subgroup_le c (H.level a) (H.level b) (r a) (r b) (hr a)
    (hH a) (hH b) (H.antitone hab)

include h0 hr hH in
lemma cutoff_zero : r 0=0 :=
  top_cutoff_zero c (r 0) (hr 0) (fun g=> (hH 0 g).mp (h0 ▸ Subgroup.mem_top g))

include h1 hr hH in
lemma cutoff_one : r 1=0 :=
  top_cutoff_zero c (r 1) (hr 1) (fun g=> (hH 1 g).mp (h1 ▸ Subgroup.mem_top g))

variable (j : ℕ) (hj : 0<j) (χ : H.level j →* Multiplicative ℝ)
variable (hnext : ∀ x : H.level j,x.val∈H.level (j+1) → χ x=1)
variable (hbr : ∀ a b : ℕ,0<a → 0<b → a+b=j →
  ∀ x∈H.level a,∀ y∈H.level b,∀ hc : ⁅x,y⁆∈H.level j,χ ⟨⁅x,y⁆,hc⟩=1)

def newCutoff (k : ℕ) : ℕ := if max 1 k=j then r j+1 else r k

include hr in
lemma newCutoff_le (hjr : r j<n) (k : ℕ) : newCutoff r j k≤n := by
  unfold newCutoff
  split_ifs <;> first | omega | exact hr k

include h0 h1 hr hH hj hnext hbr in
 

theorem refined_chart (hsk : SecondKind c) (Γ : Subgroup G)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (hcont : Continuous χ) (hz : ∀ x : H.level j,x.val∈Γ → ∃ z : ℤ,(χ x).toAdd=z)
    (hne : χ≠1) :
    ∃ Λ : Subgroup G,∃ e : RealCoordinates G n,SecondKind e ∧
      (∀ g : G,g∈Λ ↔ ∀ i,∃ z : ℤ,e.coord g i=z) ∧
      Λ≤Γ ∧ (Λ.subgroupOf Γ).FiniteIndex ∧
      (∀ g : G,IsRational e g → IsRational c g) ∧
      (∀ k,newCutoff r j k≤n) ∧
      (∀ k (g : G),g∈(kernelFiltration H (h0.trans h1.symm) j hj χ hnext hbr).level k ↔
        ∀ i : Fin n,i.val<newCutoff r j k → e.coord g i=0) := by
  have hjr:=cutoff_lt_of_character c (r j) (hr j) (hH j) χ hne
  obtain ⟨q,hn⟩ : ∃ q,n=r j+(q+1) := ⟨n-r j-1,by omega⟩
  subst n
  obtain ⟨Λ,e,hsk',hΛ,hle,hidx,hrat,hker,hearly,hlate⟩:=
    TailCharacterRechart.exists_refined_integer_cover c (H.level j) (hH j)
      hsk Γ hΓ χ hcont hz hne
      (fun g=>conjugate_mem H j (h1 ▸ Subgroup.mem_top g))
      (fun g x=>character_conjugate H j χ hnext (h1 ▸ Subgroup.mem_top g) x)
  refine ⟨Λ,e,hsk',hΛ,hle,hidx,hrat,newCutoff_le r hr j hjr,?_⟩
  intro k g
  change g∈shrinkLevel H j (levelKernel H j χ) k ↔ _
  unfold shrinkLevel newCutoff
  split_ifs with hk
  · exact hker g
  · by_cases hkj : k<j
    · exact hearly (H.level k) (r k) (cutoffs_monotone c H r hr hH hkj.le) (hH k) g
    · have hjk : j<k := by
        by_contra hn
        have hke : k=j := by omega
        exact hk (by simp [hke,Nat.max_eq_right hj])
      exact (hlate (H.level k) (r k) (hH k)
        (fun x hx=>hnext x (H.antitone (by omega) hx))).2 g

 
def rank (n s : ℕ) (r : ℕ → ℕ) : ℕ := Finset.univ.sum (fun i : Fin s => n - r (i.val + 1))

lemma rank_strict_drop (n s : ℕ) (r : ℕ → ℕ) (j : ℕ)
    (hj : 0<j) (hjs : j ≤ s) (hjr : r j<n) :
    rank n s (newCutoff r j) < rank n s r := by
  unfold rank
  apply Finset.sum_lt_sum
  · intro i _
    by_cases he : i.val + 1 = j
    · simp only [newCutoff, he, Nat.max_eq_right hj, ite_true]
      omega
    · simp only [newCutoff, Nat.max_eq_right (by omega : 1 ≤ i.val + 1), ite_eq_right he, le_refl]
  · let i : Fin s:=⟨j-1,by omega⟩
    refine ⟨i,Finset.mem_univ _,?_⟩
    have he : i.val+1=j := by dsimp [i]; omega
    simp only [he,newCutoff,Nat.max_eq_right hj,ite_true]
    omega

lemma rank_restrict (n s : ℕ) (r : ℕ → ℕ) (hr : ∀ k,1≤r k) :
    rank n s (fun k=>r k-1)=rank (1+n) s r := by
  unfold rank
  apply Finset.sum_congr rfl
  intro i _
  change n - (r (i.val + 1) - 1) = (1 + n) - r (i.val + 1)
  have := hr (i.val + 1)
  omega

 

def comapFiltration {K : Type*} [Group K] (F : K →* G) (H : Filtration G) : Filtration K where
  level k:=(H.level k).comap F
  antitone:=fun _ _ hab=>Subgroup.comap_mono (H.antitone hab)
  commutator_le a b:=by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    change F ⁅x,y⁆∈H.level (a+b)
    rw [map_commutatorElement]
    exact H.commutator_le a b (Subgroup.commutator_mem_commutator hx hy)

section Restrict
variable {q : ℕ} (d : RealCoordinates G (1+q)) (K : Subgroup G)
variable (hK : ∀ g : G,g∈K ↔ ∀ i : Fin (1+q),i.val<1 → d.coord g i=0)
variable (F : Filtration G) (t : ℕ → ℕ) (ht : ∀ k,1≤t k)
variable (hF : ∀ k (g : G),g∈F.level k ↔
  ∀ i : Fin (1+q),i.val<t k → d.coord g i=0)

include ht hF in
 

omit [IsTopologicalGroup G] in
lemma restricted_chart [IsTopologicalGroup G] (k : ℕ) (x : K) :
    x∈(comapFiltration K.subtype F).level k ↔
      ∀ i : Fin q,i.val<t k-1 → (tailCoordinates d K hK).coord x i=0 := by
  change x.val∈F.level k ↔ _
  rw [hF]
  constructor
  · intro hx i hi
    change d.coord x.val (embed 1 i)=0
    apply hx
    change 1+i.val<t k
    calc
      1+i.val < 1+(t k-1) := Nat.add_lt_add_left hi 1
      _ = t k := (Nat.add_comm _ _).trans (Nat.sub_add_cancel (ht k))
  · intro hx i hi
    by_cases hi0 : i.val<1
    · exact (hK _).mp x.property i hi0
    · let a : Fin q:=⟨i.val-1,by omega⟩
      have he : i=embed 1 a := by apply Fin.ext; change i.val=1+(i.val-1); omega
      rw [he]
      exact hx a (by dsimp [a]; omega)

include hK in
omit [IsTopologicalGroup G] in
lemma restricted_rational [IsTopologicalGroup G] (x : K) (hx : IsRational (tailCoordinates d K hK) x) :
    IsRational d x.val := by
  intro i
  by_cases hi : i.val<1
  · exact ⟨0,by simpa using ((hK _).mp x.property i hi).symm⟩
  · let a : Fin q:=⟨i.val-1,by omega⟩
    have he : i=embed 1 a := by apply Fin.ext; change i.val=1+(i.val-1); omega
    rw [he]
    exact hx a

end Restrict

section GeneralRestrict
variable {a q : ℕ} (d : RealCoordinates G (a+q)) (K : Subgroup G)
variable (hK : ∀ g : G,g∈K ↔ ∀ i : Fin (a+q),i.val<a → d.coord g i=0)
variable (F : Filtration G) (t : ℕ → ℕ)
variable (hF : ∀ k (g : G),g∈F.level k ↔
  ∀ i : Fin (a+q),i.val<t k → d.coord g i=0)
include hF in
omit [IsTopologicalGroup G] in
lemma restricted_chart_general [IsTopologicalGroup G] (k : ℕ) (x : K) :
    x∈(comapFiltration K.subtype F).level k ↔
      ∀ i : Fin q,i.val<t k-a → (tailCoordinates d K hK).coord x i=0 := by
  change x.val∈F.level k ↔ _
  rw [hF]
  constructor
  · intro hx i hi
    change d.coord x.val (embed a i)=0
    apply hx
    change a+i.val<t k
    omega
  · intro hx i hi
    by_cases hi0 : i.val<a
    · exact (hK _).mp x.property i hi0
    · let b : Fin q:=⟨i.val-a,by omega⟩
      have he : i=embed a b := by apply Fin.ext; change i.val=a+(i.val-a); omega
      rw [he]
      exact hx b (by dsimp [b]; omega)

include hK in
omit [IsTopologicalGroup G] in
lemma restricted_rational_general [IsTopologicalGroup G] (x : K) (hx : IsRational (tailCoordinates d K hK) x) :
    IsRational d x.val := by
  intro i
  by_cases hi : i.val<a
  · exact ⟨0,by simpa using ((hK _).mp x.property i hi).symm⟩
  · let b : Fin q:=⟨i.val-a,by omega⟩
    have he : i=embed a b := by apply Fin.ext; change i.val=a+(i.val-a); omega
    rw [he]
    exact hx b
end GeneralRestrict

lemma rank_restrict_general (a n s : ℕ) (r : ℕ → ℕ) (hr : ∀ k,a≤r k) :
    rank n s (fun k=>r k-a)=rank (a+n) s r := by
  unfold rank
  apply Finset.sum_congr rfl
  intro i _
  change n - (r (i.val + 1) - a) = (a + n) - r (i.val + 1)
  have := hr (i.val + 1)
  omega

include h0 h1 hr hH hj hnext hbr in
 

theorem restricted_refinement (hsk : SecondKind c) (Γ : Subgroup G)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (hcont : Continuous χ) (hz : ∀ x : H.level j,x.val∈Γ → ∃ z : ℤ,(χ x).toAdd=z)
    (hne : χ≠1) (s : ℕ) (hjs : j ≤ s) :
    let F:=kernelFiltration H (h0.trans h1.symm) j hj χ hnext hbr
    let K:=F.level 1
    ∃ q : ℕ,∃ d : RealCoordinates K q,∃ Δ : Subgroup K,∃ t : ℕ → ℕ,
      SecondKind d ∧
      (∀ x : K,x∈Δ ↔ ∀ i,∃ z : ℤ,d.coord x i=z) ∧
      (∀ x : K,x∈Δ → x.val∈Γ) ∧
      (∀ x : K,IsRational d x → IsRational c x.val) ∧
      (∀ k,t k≤q) ∧
      (∀ k (x : K),x∈(comapFiltration K.subtype F).level k ↔
        ∀ i : Fin q,i.val<t k → d.coord x i=0) ∧
      rank q s t < rank n s r := by
  dsimp only
  let F:=kernelFiltration H (h0.trans h1.symm) j hj χ hnext hbr
  let K:=F.level 1
  let t:=newCutoff r j
  obtain ⟨Λ,e,hsk',hΛ,hle,hidx,hrat,ht,he⟩:=
    refined_chart c H h0 h1 r hr hH j hj χ hnext hbr hsk Γ hΓ hcont hz hne
  have ht0 : t 0=t 1 := by
    have h0r:=cutoff_zero c H h0 r hr hH
    have h1r:=cutoff_one c H h1 r hr hH
    simp [t,newCutoff,h0r,h1r]
  have htmono : Monotone t := cutoffs_monotone e F t ht he
  have htlo (k : ℕ) : t 1≤t k := by
    by_cases hk : k=0
    · subst k; exact ht0.ge
    · exact htmono (by omega)
  have hrank:=rank_strict_drop n s r j hj hjs
    (cutoff_lt_of_character c _ (hr j) (hH j) χ hne)
  obtain ⟨q,hn⟩ : ∃ q,n=t 1+q := ⟨n-t 1,by have hb : t 1 ≤ n := ht 1; omega⟩
  subst n
  have hK : ∀ g : G,g∈K ↔ ∀ i : Fin (t 1+q),i.val<t 1 → e.coord g i=0 := he 1
  let d:=tailCoordinates e K hK
  refine ⟨q,d,Λ.comap K.subtype,fun k=>t k-t 1,tail_secondKind e K hK hsk',
    tailCoordinates_lattice e K hK Λ hΛ,?_,?_,?_,?_,?_⟩
  · intro x hx; exact hle hx
  · intro x hx
    exact hrat x.val (restricted_rational_general e K hK x hx)
  · intro k
    change t k - t 1 ≤ q
    have hb : t k ≤ t 1 + q := ht k
    omega
  · exact restricted_chart_general e K hK F t he
  · rw [rank_restrict_general (t 1) q s t htlo]
    exact hrank

end AllLevelGeometry

end
end
end
end

end OAI
