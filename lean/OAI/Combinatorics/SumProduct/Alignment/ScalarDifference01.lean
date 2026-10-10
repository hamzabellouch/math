import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubePolynomials01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators Topology commutatorElement
end
end
 

 
section

noncomputable section
open scoped commutatorElement
namespace CubeMaxFiltration
open CubeFaces
variable {G ι : Type*} [Group G] [DecidableEq ι]

 

def level (H : Filtration G) (I : Finset ι) (k : ℕ) : Subgroup (Finset ι→G) :=
  ⨆ D : Finset ι, ⨆ (_ : D⊆I), (H.level (max k D.card)).map (face D)

lemma face_mem (H : Filtration G) {I D : Finset ι} {k : ℕ}
    (hD : D⊆I) {g : G} (hg : g∈H.level (max k D.card)) : face D g∈level H I k :=
  (le_iSup_of_le D (le_iSup_of_le hD le_rfl) :
    (H.level (max k D.card)).map (face D) ≤ level H I k) ⟨g,hg,rfl⟩

lemma antitone (H : Filtration G) (I : Finset ι) : Antitone (level H I) := by
  intro i j hij
  refine iSup_le fun D => iSup_le fun hD => ?_
  rintro f ⟨g,hg,rfl⟩
  exact face_mem H hD (H.antitone (max_le_max hij le_rfl) hg)

@[simp] lemma level_zero (H : Filtration G) (I : Finset ι) : level H I 0=cube H I 0 := by
  simp [level,cube]

lemma level_one (H : Filtration G) (I : Finset ι) (h01 : H.level 0=H.level 1) :
    level H I 1=cube H I 0 := by
  have hh (D : Finset ι) : H.level (max 1 D.card)=H.level D.card := by
    by_cases hD : D.card=0
    · simp [hD,←h01]
    · rw [max_eq_right (by omega)]
  simp only [level,cube,hh,Nat.add_zero]

lemma max_union_degree (i j : ℕ) (D E : Finset ι) :
    max (i+j) (D∪E).card ≤ max i D.card+max j E.card := by
  have := Finset.card_union_le D E
  omega

lemma normalizes (H : Filtration G) (I : Finset ι) (k : ℕ) :
    level H I 0 ≤ Subgroup.normalizer (level H I k) := by
  refine iSup_le fun D => iSup_le fun hD => ?_
  rintro f ⟨g,hg,rfl⟩
  have hc (g : G) (hg : g∈H.level (max 0 D.card)) :
      ∀ z∈level H I k, face D g*z*(face D g)⁻¹∈level H I k := by
    have hle : level H I k ≤ (level H I k).comap (MulAut.conj (face D g)).toMonoidHom := by
      refine iSup_le fun E => iSup_le fun hE => ?_
      rintro f ⟨h,hh,rfl⟩
      change face D g*face E h*(face D g)⁻¹∈level H I k
      have hdeg := max_union_degree 0 k D E
      simp only [Nat.zero_add] at hdeg
      have hcomm : ⁅face D g,face E h⁆∈level H I k := by
        rw [face_commutator]
        exact face_mem H (Finset.union_subset hD hE)
          (H.antitone hdeg (H.commutator_le _ _ (Subgroup.commutator_mem_commutator hg hh)))
      have heq : face D g*face E h*(face D g)⁻¹=⁅face D g,face E h⁆*face E h := by
        simp [commutatorElement_def,mul_assoc]
      rw [heq]
      exact (level H I k).mul_mem hcomm (face_mem H hE hh)
    exact fun z hz => hle hz
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hc g hg z
  · intro hz
    have hh := hc g⁻¹ ((H.level _).inv_mem hg) _ hz
    simpa [map_inv,mul_assoc] using hh

lemma face_commutator_mem (H : Filtration G) (I : Finset ι) {i j : ℕ}
    {D : Finset ι} (hD : D⊆I) {g : G} (hg : g∈H.level (max i D.card))
    {f : Finset ι→G} (hf : f∈level H I j) : ⁅face D g,f⁆∈level H I (i+j) := by
  have hle : level H I j ≤ commModulo (level H I (i+j)) (face D g) := by
    refine iSup_le fun E => iSup_le fun hE => ?_
    rintro f ⟨h,hh,rfl⟩
    constructor
    · exact normalizes H I _ (antitone H I (Nat.zero_le j) (face_mem H hE hh))
    · rw [face_commutator]
      exact face_mem H (Finset.union_subset hD hE)
        (H.antitone (max_union_degree i j D E)
          (H.commutator_le _ _ (Subgroup.commutator_mem_commutator hg hh)))
  exact (hle hf).2

lemma commutator_mem (H : Filtration G) (I : Finset ι) {i j : ℕ}
    {f g : Finset ι→G} (hf : f∈level H I i) (hg : g∈level H I j) :
    ⁅f,g⁆∈level H I (i+j) := by
  have hle : level H I i ≤ commModulo (level H I (i+j)) g := by
    refine iSup_le fun D => iSup_le fun hD => ?_
    rintro f ⟨a,ha,rfl⟩
    constructor
    · exact normalizes H I _ (antitone H I (Nat.zero_le i) (face_mem H hD ha))
    · have hh := face_commutator_mem H I hD ha hg
      have hinv := (level H I (i+j)).inv_mem hh
      simpa [commutatorElement_def,mul_assoc] using hinv
  have hinv := (level H I (i+j)).inv_mem (hle hf).2
  simpa [commutatorElement_def,mul_assoc] using hinv

 
def ambient (H : Filtration G) (I : Finset ι) : Filtration (Finset ι→G) where
  level := level H I
  antitone := antitone H I
  commutator_le _ _ := Subgroup.commutator_le.mpr (fun _ hf _ hg => commutator_mem H I hf hg)

 
def filtration (H : Filtration G) (I : Finset ι) : Filtration (cube H I 0) where
  level k := (level H I k).comap (cube H I 0).subtype
  antitone := fun _ _ hij => Subgroup.comap_mono (antitone H I hij)
  commutator_le i j := by
    apply Subgroup.commutator_le.mpr
    intro f hf g hg
    exact commutator_mem H I hf hg

@[simp] lemma filtration_zero (H : Filtration G) (I : Finset ι) :
    (filtration H I).level 0=⊤ := by
  ext f
  simp [filtration]

lemma filtration_one (H : Filtration G) (I : Finset ι) (h01 : H.level 0=H.level 1) :
    (filtration H I).level 1=⊤ := by
  ext f
  simp [filtration,level_one H I h01]

lemma level_bot (H : Filtration G) (I : Finset ι) {s : ℕ} (hs : H.level s=⊥) :
    level H I s=⊥ := by
  apply le_antisymm _ bot_le
  refine iSup_le fun D => iSup_le fun hD => ?_
  have hh : H.level (max s D.card)=⊥ := le_antisymm (hs ▸ H.antitone (le_max_left _ _)) bot_le
  rw [hh,Subgroup.map_bot]

lemma filtration_bot (H : Filtration G) (I : Finset ι) {s : ℕ} (hs : H.level s=⊥) :
    (filtration H I).level s=⊥ := by
  ext f
  simp only [filtration,Subgroup.mem_comap,level_bot H I hs,Subgroup.mem_bot]
  exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩

 

lemma taylor_face_mem (H : Filtration G) (I : Finset ι) {D : Finset ι}
    (hD : D⊆I) {k l : ℕ} (hkl : k≤l) (hDl : D.card≤l) {a : G} (ha : a∈H.level l) :
    face D a∈level H I k :=
  face_mem H hD (H.antitone (max_le hkl hDl) ha)

end CubeMaxFiltration
end
end
 

 
section

noncomputable section
open scoped BigOperators
namespace ScalarDifferenceDegree
variable {A R : Type*} [AddCommGroup A] [CommRing R]

def diff (h : A) (f : A→R) : A→R := fun x => f (x+h)-f x

def DegreeAtMost : ℕ→(A→R)→Prop
  | 0,f => ∀ x y,f x=f y
  | d+1,f => ∀ h,DegreeAtMost d (diff h f)

lemma constant (d : ℕ) (r : R) : DegreeAtMost d (fun _ : A => r) := by
  induction d generalizing r with
  | zero => intro x y; rfl
  | succ d ih =>
    intro h
    change DegreeAtMost d (diff h (fun _ : A => r))
    have he : diff h (fun _ : A => r)=(fun _ => 0) := by ext x; exact sub_self r
    rw [he]
    exact ih 0

lemma add (d : ℕ) {f g : A→R} (hf : DegreeAtMost d f) (hg : DegreeAtMost d g) :
    DegreeAtMost d (fun x => f x+g x) := by
  induction d generalizing f g with
  | zero => intro x y; change f x+g x=f y+g y; rw [hf x y,hg x y]
  | succ d ih =>
    intro h
    have he : diff h (fun x => f x+g x)=fun x => diff h f x+diff h g x := by
      ext x; simp only [diff]; ring
    rw [he]
    exact ih (hf h) (hg h)

lemma mul_const (d : ℕ) {f : A→R} (hf : DegreeAtMost d f) (r : R) :
    DegreeAtMost d (fun x => f x*r) := by
  induction d generalizing f with
  | zero => intro x y; change f x*r=f y*r; rw [hf x y]
  | succ d ih =>
    intro h
    have he : diff h (fun x => f x*r)=fun x => diff h f x*r := by
      ext x; simp only [diff]; ring
    rw [he]
    exact ih (hf h)

lemma mono_step (d : ℕ) {f : A→R} (hf : DegreeAtMost d f) : DegreeAtMost (d+1) f := by
  induction d generalizing f with
  | zero => intro h x y; simp [diff,hf (x+h) x,hf (y+h) y]
  | succ d ih => intro h; exact ih (hf h)

lemma mono {d e : ℕ} (hde : d≤e) {f : A→R} (hf : DegreeAtMost d f) : DegreeAtMost e f := by
  induction e,hde using Nat.le_induction with
  | base => exact hf
  | succ e he ih => exact mono_step e ih

lemma shift (d : ℕ) {f : A→R} (hf : DegreeAtMost d f) (t : A) :
    DegreeAtMost d (fun x => f (x+t)) := by
  induction d generalizing f with
  | zero => intro x y; exact hf _ _
  | succ d ih =>
    intro h
    have he : diff h (fun x => f (x+t))=fun x => diff h f (x+t) := by
      ext x; simp [diff,add_comm,add_left_comm]
    rw [he]
    exact ih (hf h)

lemma mul (d e : ℕ) {f g : A→R} (hf : DegreeAtMost d f) (hg : DegreeAtMost e g) :
    DegreeAtMost (d+e) (fun x => f x*g x) := by
  induction d generalizing e f g with
  | zero =>
    have he : (fun x => f x*g x)=(fun x => g x*f 0) := by ext x; rw [hf x 0,mul_comm]
    rw [he,Nat.zero_add]
    exact mul_const e hg _
  | succ d ih =>
    induction e generalizing f g with
    | zero =>
      have he : (fun x => f x*g x)=(fun x => f x*g 0) := by ext x; rw [hg x 0]
      rw [he,Nat.add_zero]
      exact mul_const (d+1) hf _
    | succ e ihe =>
      rw [show (d+1)+(e+1)=(d+(e+1))+1 by omega]
      intro h
      have he : diff h (fun x => f x*g x)=
          fun x => diff h f x*g (x+h)+f x*diff h g x := by
        ext x; simp only [diff]; ring
      rw [he]
      apply add
      · exact ih (e+1) (hf h) (shift (e+1) hg h)
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ihe hf (hg h)

lemma pow (d n : ℕ) {f : A→R} (hf : DegreeAtMost d f) :
    DegreeAtMost (d*n) (fun x => f x^n) := by
  induction n with
  | zero => simpa using constant 0 (1:R)
  | succ n ih =>
    simpa only [Nat.mul_succ,pow_succ] using mul (d*n) d ih hf

lemma sum {T : Type*} (S : Finset T) (d : ℕ) (f : T→A→R)
    (hf : ∀ t∈S,DegreeAtMost d (f t)) : DegreeAtMost d (fun x => ∑ t∈S,f t x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using constant d (0:R)
  | @insert t S ht ih =>
    simp only [Finset.sum_insert ht]
    exact add d (hf t (Finset.mem_insert_self _ _)) (ih (fun u hu => hf u (Finset.mem_insert_of_mem hu)))

lemma prod {T : Type*} (S : Finset T) (d : T→ℕ) (f : T→A→R)
    (hf : ∀ t∈S,DegreeAtMost (d t) (f t)) :
    DegreeAtMost (∑ t∈S,d t) (fun x => ∏ t∈S,f t x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using constant 0 (1:R)
  | @insert t S ht ih =>
    simp only [Finset.sum_insert ht,Finset.prod_insert ht]
    exact mul _ _ (hf t (Finset.mem_insert_self _ _)) (ih (fun u hu => hf u (Finset.mem_insert_of_mem hu)))

lemma hom (φ : A→+R) : DegreeAtMost 1 φ := by
  intro h
  have hh : diff h φ=fun _ => φ h := by ext x; simp [diff]
  rw [hh]
  exact constant 0 _

lemma eval_monomial {σ : Type*} [Fintype σ] (e : σ→₀ℕ) (r : ℝ) :
    DegreeAtMost (e.sum (fun _ n => n)) (fun x : σ→ℝ => MvPolynomial.eval x (MvPolynomial.monomial e r)) := by
  classical
  have hcoord (i : σ) : DegreeAtMost 1 (fun x : σ→ℝ => x i) := hom ({ toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl } : (σ→ℝ)→+ℝ)
  have hh := prod Finset.univ (fun i => e i) (fun i (x : σ→ℝ) => x i^(e i))
    (fun i _ => by simpa using pow 1 (e i) (hcoord i))
  have he : e.sum (fun _ n => n)=∑ i : σ,e i := Finsupp.sum_fintype _ _ (by simp)
  rw [he]
  have hp (x : σ→ℝ) : e.prod (fun i k => x i^k)=∏ i,x i^(e i) :=
    Finsupp.prod_fintype _ _ (by intro i; simp)
  simp_rw [MvPolynomial.eval_monomial,hp]
  simpa only [mul_comm] using mul_const _ hh r

 

lemma eval_polynomial {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) {d : ℕ}
    (hp : p.totalDegree≤d) : DegreeAtMost d (fun x : σ→ℝ => MvPolynomial.eval x p) := by
  classical
  have he (x : σ→ℝ) : MvPolynomial.eval x p=
      ∑ e∈p.support,MvPolynomial.eval x (MvPolynomial.monomial e (p.coeff e)) := by
    simpa only [map_sum] using congrArg (MvPolynomial.eval x) (MvPolynomial.as_sum p)
  simp_rw [he]
  apply sum
  intro e he
  exact mono ((MvPolynomial.le_totalDegree he).trans hp) (eval_monomial e _)

def iterDiff : List A→(A→R)→(A→R)
  | [],f => f
  | h::hs,f => iterDiff hs (diff h f)

lemma iterDiff_zero_function (hs : List A) : iterDiff hs (fun _ : A => (0:R))=0 := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    have he : diff h (fun _ : A => (0:R))=0 := by ext x; exact sub_self 0
    simpa only [iterDiff,he,Pi.zero_def] using ih

lemma iterDiff_zero {d : ℕ} {f : A→R} (hf : DegreeAtMost d f)
    (hs : List A) (hhs : d<hs.length) : iterDiff hs f=0 := by
  induction d generalizing hs f with
  | zero =>
    cases hs with
    | nil => simp at hhs
    | cons h hs =>
      have he : diff h f=0 := by ext x; exact sub_eq_zero.mpr (hf (x+h) x)
      simpa only [iterDiff,he,Pi.zero_def] using iterDiff_zero_function hs
  | succ d ih =>
    cases hs with
    | nil => simp at hhs
    | cons h hs => exact ih (hf h) hs (by simpa using hhs)

 

theorem polynomial_power {K : Type*} [Group K] (H : CubeFaces.Filtration K)
    (φ : Multiplicative ℝ→*K) (d : ℕ) (hφ : ∀ r,φ (Multiplicative.ofAdd r)∈H.level d)
    {f : A→ℝ} (hf : DegreeAtMost d f) :
    LeibmanSquare.Polynomial H 0 (fun x => φ (Multiplicative.ofAdd (f x))) := by
  have hm (hs : List A) (f : A→ℝ) :
      LeibmanSquare.iterDiff hs (fun x => φ (Multiplicative.ofAdd (f x)))=
        fun x => φ (Multiplicative.ofAdd (iterDiff hs f x)) := by
    induction hs generalizing f with
    | nil => rfl
    | cons h hs ih =>
      have he : LeibmanSquare.diff h (fun x => φ (Multiplicative.ofAdd (f x)))=
          fun x => φ (Multiplicative.ofAdd (diff h f x)) := by
        ext x
        change (φ (Multiplicative.ofAdd (f x)))⁻¹*φ (Multiplicative.ofAdd (f (x+h)))=
          φ (Multiplicative.ofAdd (f (x+h)-f x))
        rw [←map_inv,←map_mul]
        congr 1
        change Multiplicative.ofAdd (-f x+f (x+h))=Multiplicative.ofAdd (f (x+h)-f x)
        congr 1
        ring
      rw [LeibmanSquare.iterDiff,he,ih]
      rfl
  intro hs x
  rw [hm]
  by_cases hd : hs.length≤d
  · exact H.antitone (by simpa using hd) (hφ _)
  · rw [iterDiff_zero hf hs (lt_of_not_ge hd)]
    simp

end ScalarDifferenceDegree

end
end
end
end
end

end OAI
