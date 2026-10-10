import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.EventMass

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι→Type*} [∀i,Fintype (β i)]

noncomputable def piLaw (p : ∀i,Law (β i)) : Law (∀i,β i) where
  mass x := ∏i,p i (x i)
  nonneg x := Finset.prod_nonneg fun i _=>(p i).nonneg _
  sum_one := by rw [←Fintype.prod_sum];simp only [(p _).sum_one,Finset.prod_const_one]

lemma piLaw_prod (p : ∀i,Law (β i)) (f : ∀i,β i→ℝ) :
    (∑x,piLaw p x*(∏i,f i (x i)))=∏i,∑a,p i a*f i a := by
  simp only [piLaw,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a=>p i a*f i a)).symm

lemma piLaw_eval_expectation (p : ∀i,Law (β i)) (i : ι) (f : β i→ℝ) :
    (∑x,piLaw p x*f (x i))=∑a,p i a*f a := by
  let g : ∀j,β j→ℝ := fun j a=>if h : j=i then f (h ▸ a) else 1
  have hx (x : ∀j,β j) : (∏j,g j (x j))=f (x i) := by
    have he : (fun j=>g j (x j))=Function.update (fun _=>1) i (f (x i)) := by
      funext j
      by_cases hj : j=i
      · subst j;simp [g]
      · simp [g,hj]
    rw [he,Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hs : (fun j=>∑a,p j a*g j a)=Function.update (fun _=>1) i (∑a,p i a*f a) := by
    funext j
    by_cases hj : j=i
    · subst j;simp [g]
    · simp [g,hj,(p j).sum_one]
  have hh := piLaw_prod p g
  simp_rw [hx] at hh
  rw [hs,Finset.prod_update_of_mem (Finset.mem_univ i)] at hh
  simpa using hh

lemma piLaw_eval (p : ∀i,Law (β i)) (i : ι) : map (piLaw p) (fun x=>x i)=p i := by
  apply Law.ext
  funext a
  have hm := piLaw_eval_expectation p i (fun b=>if b=a then 1 else 0)
  simpa only [map,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hm
end

open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

lemma entropy_le_cross_subprob (p : Law α) (r : α→ℝ)
    (hr : ∀a,0<r a) (hs : ∑a,r a≤1) :
    entropy p ≤ -∑a,p a*Real.log (r a) := by
  have hh := Finset.sum_le_sum (fun a (_ : a∈Finset.univ)=>
    point_log_ratio (p a) (r a) (p.nonneg _) (hr _).le (fun _=>hr _))
  have he : (∑a,p a*Real.log (p a/r a))=
      (∑a,p a*Real.log (p a))-(∑a,p a*Real.log (r a)) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hz : p a=0
    · simp [hz]
    · rw [Real.log_div hz (hr _).ne'];ring
  rw [Finset.sum_sub_distrib,p.sum_one,he] at hh
  dsimp only [entropy]
  linarith

lemma finite_geometric_mass (z : α→ℕ) (hz : Function.Injective z)
    (r : ℝ) (hr : 0≤r) (hr1 : r≤1) :
    (∑a,(1-r)*r^(z a))≤1 := by
  let S := Finset.univ.image z
  let N := S.sup id+1
  have hsub : S⊆Finset.range N := by
    intro n hn
    apply Finset.mem_range.mpr
    have := Finset.le_sup (f:=id) hn
    dsimp only [id] at this
    dsimp only [N]
    omega
  have he (m : ℕ) : (∑n∈Finset.range m,(1-r)*r^n)=1-r^m := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ,ih,pow_succ];ring
  have hi : (∑a,(1-r)*r^(z a))=∑n∈S,(1-r)*r^n := by
    dsimp only [S]
    rw [Finset.sum_image]
    exact fun a _ b _ h=>hz h
  rw [hi]
  calc
    _ ≤ ∑n∈Finset.range N,(1-r)*r^n := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _=>mul_nonneg (sub_nonneg.mpr hr1) (pow_nonneg hr _))
    _ = 1-r^N := he N
    _ ≤ 1 := by linarith [pow_nonneg hr N]

theorem integer_entropy (p : Law α) (z : α→ℕ) (hz : Function.Injective z)
    (M : ℝ) (hM : 0<M) (hm : (∑a,p a*(z a:ℝ))≤M) :
    entropy p≤Real.log (M+1)+1 := by
  let r := M/(M+1)
  have hMp : 0<M+1 := by linarith
  have hr : 0<r := div_pos hM hMp
  have hr1 : r<1 := (div_lt_one hMp).mpr (by linarith)
  have hs := finite_geometric_mass z hz r hr.le hr1.le
  have hh := entropy_le_cross_subprob p (fun a=>(1-r)*r^(z a))
    (fun a=>mul_pos (sub_pos.mpr hr1) (pow_pos hr _)) hs
  have he : (∑a,p a*Real.log ((1-r)*r^(z a)))=
      Real.log (1-r)+(∑a,p a*(z a:ℝ))*Real.log r := by
    simp only [Real.log_mul (sub_pos.mpr hr1).ne' (pow_ne_zero _ hr.ne'),Real.log_pow]
    simp only [mul_add,Finset.sum_add_distrib,←mul_assoc,←Finset.sum_mul,p.sum_one,one_mul]
  rw [he] at hh
  have hlogr : Real.log r≤0 := Real.log_nonpos hr.le hr1.le
  have hm' := mul_le_mul_of_nonpos_right hm hlogr
  have h1 : 1-r=1/(M+1) := by dsimp only [r];field_simp;ring
  have hl1 : Real.log (1-r)= -Real.log (M+1) := by
    rw [h1,Real.log_div one_ne_zero hMp.ne',Real.log_one,zero_sub]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hMp hM)
  have hlr : Real.log ((M+1)/M)= -Real.log r := by
    rw [Real.log_div hMp.ne' hM.ne']
    dsimp only [r]
    rw [Real.log_div hM.ne' hMp.ne']
    ring
  rw [hlr] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hM.le
  have heq : M*((M+1)/M-1)=1 := by field_simp;ring
  rw [heq] at hmul
  rw [hl1] at hh
  nlinarith

noncomputable def atomLevel (p : Law α) (a : α) : ℕ := ⌊-Real.log (p a)⌋₊
noncomputable def levelRange (p : Law α) : Finset ℕ := Finset.univ.image (atomLevel p)
abbrev Level (p : Law α) := ↥(levelRange p)
noncomputable def levelIndex (p : Law α) (a : α) : Level p :=
  ⟨atomLevel p a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩
noncomputable def levelLaw (p : Law α) : Law (Level p) := map p (levelIndex p)
noncomputable def levelCell (p : Law α) (n : Level p) : Finset α :=
  Finset.univ.filter (fun a=>0<p a ∧ atomLevel p a=n.val)

lemma mem_levelCell (p : Law α) (n : Level p) (a : α) :
    a∈levelCell p n ↔ 0<p a ∧ atomLevel p a=n.val := by simp [levelCell]

lemma atomLevel_le (p : Law α) (a : α) : (atomLevel p a:ℝ)≤ -Real.log (p a) := by
  exact Nat.floor_le (neg_nonneg.mpr (Real.log_nonpos (p.nonneg _) (mass_le_one p a)))

lemma atomLevel_lt (p : Law α) (a : α) : -Real.log (p a)<(atomLevel p a:ℝ)+1 :=
  Nat.lt_floor_add_one _

lemma level_mean_le_entropy (p : Law α) :
    (∑n : Level p,levelLaw p n*(n.val:ℝ))≤entropy p := by
  unfold levelLaw
  rw [sum_map]
  calc
    _ ≤ ∑a,p a*(-Real.log (p a)) := Finset.sum_le_sum fun a _=>
      mul_le_mul_of_nonneg_left (atomLevel_le p a) (p.nonneg _)
    _ = entropy p := by simp [entropy,mul_neg]

theorem endpoint_level_entropy (p : Law α) (M : ℝ) (hM : 0<M)
    (hp : entropy p≤M) : entropy (levelLaw p)≤Real.log (M+1)+1 :=
  integer_entropy (levelLaw p) Subtype.val Subtype.val_injective M hM
    ((level_mean_le_entropy p).trans hp)

lemma level_mass (p : Law α) (n : Level p) :
    levelLaw p n=∑a∈levelCell p n,p a := by
  simp only [levelLaw,map,levelCell,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : p a=0
  · simp [hp]
  · have hp0 : 0<p a := lt_of_le_of_ne (p.nonneg _) (Ne.symm hp)
    simp only [hp0,true_and]
    have he : levelIndex p a=n ↔ atomLevel p a=n.val := Subtype.ext_iff
    by_cases h : atomLevel p a=n.val <;> simp [he,h]

lemma same_level_ratio (p : Law α) (n : Level p) {a b : α}
    (ha : a∈levelCell p n) (hb : b∈levelCell p n) :
    p b≤Real.exp 1*p a := by
  obtain ⟨ha0,hae⟩ := (mem_levelCell p n a).mp ha
  obtain ⟨hb0,hbe⟩ := (mem_levelCell p n b).mp hb
  have h₁ := atomLevel_le p b
  have h₂ := atomLevel_lt p a
  rw [hae] at h₂
  rw [hbe] at h₁
  have hl : Real.log (p b)≤1+Real.log (p a) := by linarith
  have he := Real.exp_le_exp.mpr hl
  simpa only [Real.exp_add,Real.exp_log ha0,Real.exp_log hb0] using he

lemma level_mass_bound (p : Law α) (n : Level p) {a : α}
    (ha : a∈levelCell p n) :
    levelLaw p n≤(levelCell p n).card*Real.exp 1*p a := by
  rw [level_mass]
  calc
    _ ≤ ∑b∈levelCell p n,Real.exp 1*p a :=
      Finset.sum_le_sum (fun b hb=>same_level_ratio p n ha hb)
    _ = _ := by simp [mul_assoc]

noncomputable def conditionOn (p : Law α) (E : Finset α) (hE : 0<eventMass p E) : Law α where
  mass a := if a∈E then p a/eventMass p E else 0
  nonneg a := by
    split
    · exact div_nonneg (p.nonneg _) hE.le
    · exact le_refl 0
  sum_one := by rw [←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,
    ←Finset.sum_div];exact div_self hE.ne'

lemma conditionOn_apply (p : Law α) (E : Finset α) (hE : 0<eventMass p E) (a : α) :
    conditionOn p E hE a=if a∈E then p a/eventMass p E else 0 := rfl

theorem good_level_domination (p : Law α) (Good : Finset α) (E : Finset (Level p))
    (hE : (1:ℝ)/2≤eventMass (levelLaw p) E)
    (hhalf : ∀n∈E,(levelCell p n).card≤2*(levelCell p n∩Good).card) (a : α) :
    let c := conditionOn (levelLaw p) E (by linarith : 0<eventMass (levelLaw p) E)
    (∑n : Level p,c n*(if a∈levelCell p n∩Good then 1/((levelCell p n∩Good).card:ℝ) else 0))
      ≤4*Real.exp 1*p a := by
  dsimp only
  have hZ : 0<eventMass (levelLaw p) E := by linarith
  have hpa := p.nonneg a
  calc
    _ ≤ ∑n : Level p,if levelIndex p a=n then 4*Real.exp 1*p a else 0 := by
      apply Finset.sum_le_sum
      intro n _
      rw [conditionOn_apply]
      by_cases hn : n∈E
      · rw [ite_eq_left hn]
        by_cases ha : a∈levelCell p n∩Good
        · rw [ite_eq_left ha]
          have ham := (Finset.mem_inter.mp ha).1
          have he : levelIndex p a=n := Subtype.ext ((mem_levelCell p n a).mp ham).2
          rw [ite_eq_left he]
          have hcard : (0:ℝ)<(levelCell p n∩Good).card := by
            exact_mod_cast Finset.card_pos.mpr ⟨a,ha⟩
          have hm := level_mass_bound p n ham
          have hh : ((levelCell p n).card:ℝ)≤2*(levelCell p n∩Good).card := by exact_mod_cast hhalf n hn
          have h₁ := mul_le_mul_of_nonneg_right hh (mul_nonneg (Real.exp_pos 1).le (p.nonneg a))
          have h₂ := mul_le_mul_of_nonneg_right hE
            (by positivity : (0:ℝ)≤4*Real.exp 1*p a*(levelCell p n∩Good).card)
          rw [div_mul_div_comm,mul_one]
          apply (div_le_iff₀ (mul_pos hZ hcard)).mpr
          nlinarith
        · rw [ite_eq_right ha,mul_zero]
          split <;> positivity
      · rw [ite_eq_right hn,zero_mul]
        split <;> positivity
    _ = _ := by simp

end SharpRamseyFive.FiniteEntropy

end OAI
