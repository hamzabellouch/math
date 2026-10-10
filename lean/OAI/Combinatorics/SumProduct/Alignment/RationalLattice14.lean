import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.WeightedPolynomial02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

noncomputable section
namespace RationalLattice
open WeightedPolynomial MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (H : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)

include hsk hH in
lemma log_multiplication_weighted (i : Fin n) :
    IsWeighted (Sum.elim w w) (w i) (fun x=>canonicalLog c
      (canonicalExp c (fun j=>x (Sum.inl j))*canonicalExp c (fun j=>x (Sum.inr j))) i) := by
  have he (j : Fin n ⊕ Fin n) : IsWeighted (Sum.elim w w) ((Sum.elim w w) j)
      (fun x=>Sum.elim (fun k=>c.coord (canonicalExp c (fun l=>x (Sum.inl l))) k)
        (fun k=>c.coord (canonicalExp c (fun l=>x (Sum.inr l))) k) j) := by
    cases j with
    | inl j =>
      exact IsWeighted.comp (canonicalExp_weighted c hsk H w hH j)
        (fun k=>IsWeighted.coordinate (Sum.elim w w) (Sum.inl k))
    | inr j =>
      exact IsWeighted.comp (canonicalExp_weighted c hsk H w hH j)
        (fun k=>IsWeighted.coordinate (Sum.elim w w) (Sum.inr k))
  have hm (j : Fin n) := IsWeighted.comp (multiplication_weighted c hsk H w hH j) he
  simp only [Sum.elim_inl,Sum.elim_inr,Homeomorph.symm_apply_apply] at hm
  have hl:=IsWeighted.comp (canonicalLog_weighted c hsk H w hH i) hm
  simpa only [Homeomorph.symm_apply_apply] using hl

include hsk hH in
 

theorem log_left_displacement_weighted (hw : ∀ i,0 < w i) (a : G) (i : Fin n) :
    IsWeighted w (w i-1) (fun y=>canonicalLog c (a*canonicalExp c y) i-y i) := by
  obtain ⟨p,hp,he⟩:=log_multiplication_weighted c hsk H w hH i
  let q:=p-MvPolynomial.X (Sum.inr i)
  have hq : Bounded (Sum.elim w w) (w i) q := hp.sub (bounded_X (Sum.inr i))
  have hz (y : Fin n → ℝ) : MvPolynomial.eval (Sum.elim (fun _ : Fin n=>0) y) q=0 := by
    simp only [q,map_sub,MvPolynomial.eval_X,Sum.elim_inr]
    have h:=he (Sum.elim (fun _ : Fin n=>0) y)
    change canonicalLog c (canonicalExp c 0*canonicalExp c y) i=_ at h
    simp only [canonicalExp_zero,one_mul,canonicalLog_exp] at h
    rw [← h,sub_self]
  let Q:=MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun j=>MvPolynomial.C (canonicalLog c a j)) (fun j=>MvPolynomial.X j)) q
  refine ⟨Q,fixed_left_spends_weight w w hw q hq hz (canonicalLog c a),?_⟩
  intro y
  change _=MvPolynomial.eval y (MvPolynomial.eval₂ MvPolynomial.C _ q)
  rw [← MvPolynomial.eval_assoc]
  have hv : (MvPolynomial.eval y ∘ Sum.elim
      (fun j=>MvPolynomial.C (canonicalLog c a j)) (fun j=>MvPolynomial.X j))=
      Sum.elim (canonicalLog c a) y := by funext j; cases j <;> simp
  rw [hv]
  simp only [q,map_sub,MvPolynomial.eval_X,Sum.elim_inr]
  rw [← he]
  simp only [Sum.elim_inl,Sum.elim_inr,canonicalExp_log]

end RationalLattice
end
 
end

section
 

noncomputable section
namespace RationalLattice
open WeightedPolynomial MalcevCharacters MalcevWeightedCoordinates
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)

omit [IsTopologicalGroup G] in
lemma canonicalLog_congr_prefix (g h : G) (k : ℕ)
    (he : ∀ j : Fin n,j.val < k → c.coord g j=c.coord h j) :
    ∀ j : Fin n,j.val < k → canonicalLog c g j=canonicalLog c h j := by
  intro j hj
  have hh:=canonicalLog_sub_of_prefix_eq c g h j (fun l hl=>he l (lt_trans hl hj))
  rw [he j hj,sub_self,sub_eq_zero] at hh
  exact hh

omit [IsTopologicalGroup G] in
lemma canonicalLog_mul_prefix (g h : G) (k : ℕ)
    (hh : ∀ j : Fin n,j.val < k → c.coord h j=0) :
    ∀ j : Fin n,j.val < k → canonicalLog c (g*h) j=canonicalLog c g j := by
  apply canonicalLog_congr_prefix
  intro j hj
  rw [coord_mul_of_right_zero c _ _ j (fun l hl=>hh l (lt_trans hl hj)),hh j hj,add_zero]

variable (H : CubeFaces.Filtration G) (w : Fin n → ℕ) (hmono : Monotone w)
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)
include hmono hH in
omit [IsTopologicalGroup G] in
lemma mem_level_iff_log (k : ℕ) (g : G) :
    g∈H.level k ↔ ∀ i : Fin n,w i < k → canonicalLog c g i=0 := by
  obtain ⟨r,hr,he⟩:=exists_weight_cutoff w hmono k
  rw [hH]
  simp only [he]
  exact (canonicalLog_prefix_zero_iff c g r).symm

include hmono hH in
omit [IsTopologicalGroup G] in
lemma canonicalExp_mem_level_iff (k : ℕ) (x : Fin n → ℝ) :
    canonicalExp c x∈H.level k ↔ ∀ i : Fin n,w i < k → x i=0 := by
  rw [mem_level_iff_log c H w hmono hH,canonicalLog_exp]

include hmono hH in
omit [IsTopologicalGroup G] in
lemma canonicalLog_mul_level (k : ℕ) (g h : G) (hh : h∈H.level k) :
    ∀ j : Fin n,w j < k → canonicalLog c (g*h) j=canonicalLog c g j := by
  obtain ⟨r,hr,he⟩:=exists_weight_cutoff w hmono k
  have hz : ∀ j : Fin n,j.val < r → c.coord h j=0 :=
    fun j hj=>(hH k h).mp hh j ((he j).mpr hj)
  exact fun j hj=>canonicalLog_mul_prefix c g h r hz j ((he j).mp hj)

include hmono hH in
 

theorem logHomLinear_lowers_of_displacement (hsk : SecondKind c) (F : G →* G)
    (hF : Continuous F) (k : ℕ)
    (hd : ∀ g∈H.level k,g⁻¹*F g∈H.level (k+1))
    (x : Fin n → ℝ) (hx : ∀ j : Fin n,w j < k → x j=0) :
    ∀ j : Fin n,w j < k+1 → (logHomLinear c c F x-x) j=0 := by
  have hg : canonicalExp c x∈H.level k := (canonicalExp_mem_level_iff c H w hmono hH _ _).mpr hx
  have he:=canonicalLog_mul_level c H w hmono hH (k+1) (canonicalExp c x)
    ((canonicalExp c x)⁻¹*F (canonicalExp c x)) (hd _ hg)
  simp only [mul_inv_cancel_left,canonicalLog_exp] at he
  intro j hj
  rw [logHomLinear_apply c c hsk F hF]
  exact sub_eq_zero.mpr (he j hj)

end RationalLattice
end
 
end

section
 

noncomputable section
open scoped BigOperators
namespace WeightedPolynomial
open MvPolynomial
variable {σ τ : Type*}

lemma IsWeighted.smul {w : σ → ℕ} {d : ℕ} {f : (σ → ℝ) → ℝ}
    (hf : IsWeighted w d f) (a : ℝ) : IsWeighted w d (fun x=>a*f x) := by
  obtain ⟨p,hp,he⟩:=hf
  refine ⟨C a*p,?_,by simp [he]⟩
  simpa only [Nat.zero_add] using (bounded_C (w:=w) (d:=0) a).mul hp
lemma IsWeighted.sum {ι : Type*} (s : Finset ι) {w : σ → ℕ} {d : ℕ}
    {f : ι → (σ → ℝ) → ℝ} (hf : ∀ i∈s,IsWeighted w d (f i)) :
    IsWeighted w d (fun x=>∑ i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsWeighted.const w d 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))

lemma IsWeighted.linear [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (d : ℕ)
    (A : (σ → ℝ) →ₗ[ℝ] ℝ)
    (hA : ∀ j,d < w j → A (Pi.single j 1)=0) : IsWeighted w d A := by
  have hs : IsWeighted w d (fun x=>∑ j : σ,A (Pi.single j 1)*x j) := by
    apply IsWeighted.sum
    intro j hj
    by_cases hd : w j ≤ d
    · exact ((IsWeighted.coordinate w j).mono hd).smul _
    · simp only [hA j (Nat.lt_of_not_ge hd),zero_mul]
      exact IsWeighted.const w d 0
  have he (x : σ → ℝ) : A x=∑ j : σ,A (Pi.single j 1)*x j := by
    have hx : x=∑ j : σ,x j • Pi.single j 1 := by
      ext i
      simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
    nth_rw 1 [hx]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_smul,smul_eq_mul,mul_comm]
  obtain ⟨p,hp,hq⟩:=hs
  exact ⟨p,hp,fun x=>(he x).trans (hq x)⟩

end WeightedPolynomial
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace WeightedPolynomial
open MvPolynomial
variable {α β : Type*}

lemma eval_kill_inl (p : MvPolynomial (α ⊕ β) ℝ) (x : α → ℝ) :
    eval x (p.killCompl Sum.inl_injective)=eval (Sum.elim x (fun _ : β=>0)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    cases i with
    | inr i => simp [map_mul,killCompl]
    | inl i =>
      have he : killCompl (R:=ℝ) (Sum.inl_injective (β:=β)) (X (Sum.inl i))=X i := by
        rw [← rename_X,killCompl_rename_app]
      simp [map_mul,hp,he]

lemma exists_right_of_vanishing (p : MvPolynomial (α ⊕ β) ℝ)
    (hz : ∀ x,eval (Sum.elim x (fun _ : β=>0)) p=0)
    (m : (α ⊕ β) →₀ ℕ) (hm : p.coeff m≠0) : ∃ b : β,m (Sum.inr b)≠0 := by
  classical
  by_contra hh
  push Not at hh
  have hs : ↑m.support ⊆ Set.range (@Sum.inl α β) := by
    intro j hj
    cases j with
    | inr b => exact False.elim ((Finsupp.mem_support_iff.mp hj) (hh b))
    | inl a => exact ⟨a,rfl⟩
  have hk : p.killCompl Sum.inl_injective=0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero,eval_kill_inl,hz]
  have hc:=congrArg (fun poly : MvPolynomial α ℝ=>
    poly.coeff (m.comapDomain (@Sum.inl α β) Sum.inl_injective.injOn)) hk
  rw [coeff_killCompl,m.mapDomain_comapDomain _ Sum.inl_injective hs,
    AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at hc
  exact hm hc

lemma weight_lt_of_other {σ : Type*} (w : σ → ℕ) (m : σ →₀ ℕ)
    (i j : σ) (hne : i≠j) (hi : m i≠0) (hj : m j≠0) (hwj : 0<w j) :
    w i < Finsupp.weight w m := by
  classical
  have hs : {i,j}⊆m.support := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl <;> exact Finsupp.mem_support_iff.mpr (by assumption)
  have hsum:=Finset.sum_le_sum_of_subset hs (f:=fun a=>m a*w a)
  simp only [Finset.sum_insert (show i∉({j}:Finset σ) by simpa using hne),Finset.sum_singleton] at hsum
  have hmi : w i ≤ m i*w i:=by nlinarith [Nat.pos_of_ne_zero hi]
  have hmj : 0 < m j * w j:=Nat.mul_pos (Nat.pos_of_ne_zero hj) hwj
  simpa only [Finsupp.weight_apply,Finsupp.sum,smul_eq_mul] using
    (lt_of_lt_of_le (by omega : w i < m i*w i+m j*w j) hsum)

lemma mixed_weight_strict {wa : α → ℕ} {wb : β → ℕ} {d : ℕ}
    (hwa : ∀ a,0<wa a) (hwb : ∀ b,0<wb b)
    (p : MvPolynomial (α ⊕ β) ℝ) (hp : Bounded (Sum.elim wa wb) d p)
    (hl : ∀ y,eval (Sum.elim (fun _ : α=>0) y) p=0)
    (hr : ∀ x,eval (Sum.elim x (fun _ : β=>0)) p=0)
    {m : (α ⊕ β) →₀ ℕ} {j : α ⊕ β} (hj : j∈m.support) (hm : p.coeff m≠0) :
    (Sum.elim wa wb) j<d := by
  have hlt : (Sum.elim wa wb) j<Finsupp.weight (Sum.elim wa wb) m := by
    cases j with
    | inl a =>
      obtain ⟨b,hb⟩:=exists_right_of_vanishing p hr m hm
      exact weight_lt_of_other _ m (Sum.inl a) (Sum.inr b) (by simp)
        (Finsupp.mem_support_iff.mp hj) hb (hwb b)
    | inr b =>
      obtain ⟨a,ha⟩:=exists_left_of_vanishing p hl m hm
      exact weight_lt_of_other _ m (Sum.inr b) (Sum.inl a) (by simp)
        (Finsupp.mem_support_iff.mp hj) ha (hwa a)
  exact lt_of_lt_of_le hlt (hp m hm)

 

theorem mixed_eval_congr {wa : α → ℕ} {wb : β → ℕ} {d : ℕ}
    (hwa : ∀ a,0<wa a) (hwb : ∀ b,0<wb b)
    (p : MvPolynomial (α ⊕ β) ℝ) (hp : Bounded (Sum.elim wa wb) d p)
    (hl : ∀ y,eval (Sum.elim (fun _ : α=>0) y) p=0)
    (hr : ∀ x,eval (Sum.elim x (fun _ : β=>0)) p=0)
    (x y : (α ⊕ β) → ℝ)
    (hxy : ∀ j,(Sum.elim wa wb) j<d → x j=y j) : eval x p=eval y p := by
  apply eval₂_congr
  intro j m hj hm
  exact hxy j (mixed_weight_strict hwa hwb p hp hl hr hj hm)

end WeightedPolynomial

end
end
end

end OAI
