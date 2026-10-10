import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Map

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

noncomputable def eventMass (p : Law α) (E : Finset α) : ℝ := ∑ a ∈ E,p a

lemma eventMass_nonneg (p : Law α) (E : Finset α) : 0≤eventMass p E :=
  Finset.sum_nonneg fun a _ => p.nonneg a

lemma eventMass_le_one (p : Law α) (E : Finset α) : eventMass p E≤1 := by
  rw [←p.sum_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => p.nonneg a)

lemma rejection_mass (p : Law α) (E : Finset α) :
    (∑ a,if a∈E then 0 else p a)=1-eventMass p E := by
  have h : (∑ a,if a∈E then p a else 0)+(∑ a,if a∈E then 0 else p a)=1 := by
    rw [←Finset.sum_add_distrib]
    convert p.sum_one using 1
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have he : (∑ a,if a∈E then p a else 0)=eventMass p E := by
    classical
    simp [eventMass]
  linarith

noncomputable def iid (p : Law α) (ι : Type*) [Fintype ι] [DecidableEq ι] : Law (ι → α) where
  mass x := ∏ i,p (x i)
  nonneg x := Finset.prod_nonneg fun i _ => p.nonneg (x i)
  sum_one := by
    classical
    rw [←Fintype.prod_sum]
    simp only [p.sum_one,Finset.prod_const_one]

lemma iid_cons (p : Law α) {n : ℕ} (a : α) (x : Fin n → α) :
    iid p (Fin (n+1)) (Fin.cons a x)=p a*iid p (Fin n) x := by
  simp [iid,Fin.prod_univ_succ]

noncomputable def firstAccepted (E : Finset α) : {n : ℕ} → (Fin n → α) → Option α
  | 0,_ => none
  | _+1,x => if x 0∈E then some (x 0) else firstAccepted E (fun i => x i.succ)

omit [Fintype α] in
lemma firstAccepted_cons (E : Finset α) {n : ℕ} (a : α) (x : Fin n → α) :
    firstAccepted E (Fin.cons a x)=if a∈E then some a else firstAccepted E x := by
  simp only [firstAccepted,Fin.cons_zero,Fin.cons_succ]

lemma sum_iid_succ (p : Law α) (n : ℕ) (f : (Fin (n+1) → α) → ℝ) :
    (∑ x,iid p (Fin (n+1)) x*f x)=
      ∑ a,∑ x,p a*iid p (Fin n) x*f (Fin.cons a x) := by
  have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => α))
    (fun z => p z.1*iid p (Fin n) z.2*f (Fin.cons z.1 z.2))
    (fun x => iid p (Fin (n+1)) x*f x) (by
      intro z
      change _ = iid p (Fin (n+1)) (Fin.cons z.1 z.2)*f (Fin.cons z.1 z.2)
      rw [iid_cons])
  simpa only [Fintype.sum_prod_type] using h.symm

lemma first_integrand (p : Law α) (E : Finset α) (n : ℕ) (y : Option α)
  (a : α) (x : Fin n → α) :
    p a*iid p (Fin n) x*(if firstAccepted E (Fin.cons a x)=y then 1 else 0) =
    (if a∈E ∧ some a=y then p a else 0)*iid p (Fin n) x+
    (if a∈E then 0 else p a)*
      (if firstAccepted E x=y then iid p (Fin n) x else 0) := by
  rw [firstAccepted_cons]
  by_cases ha : a∈E
  · by_cases hy : some a=y <;> simp [ha,hy]
  · by_cases hy : firstAccepted E x=y <;> simp [ha,hy]

lemma first_law_succ (p : Law α) (E : Finset α) (n : ℕ) (y : Option α) :
    map (iid p (Fin (n+1))) (firstAccepted E (n := n+1)) y =
      (∑ a,if a∈E ∧ some a=y then p a else 0)+
      (1-eventMass p E)*map (iid p (Fin n)) (firstAccepted E (n := n)) y := by
  have h := sum_iid_succ p n (fun x => if firstAccepted E x=y then 1 else 0)
  calc
    _ = ∑ x,iid p (Fin (n+1)) x*(if firstAccepted E x=y then 1 else 0) := by
      simp only [map,mul_ite,mul_one,mul_zero]
      congr 2
      funext x
      congr 1
    _ = ∑ a,∑ x,p a*iid p (Fin n) x*
        (if firstAccepted E (Fin.cons a x)=y then 1 else 0) := h
    _ = _ := by
      simp only [first_integrand,Finset.sum_add_distrib,←Finset.mul_sum,(iid p (Fin n)).sum_one,
        mul_one,←Finset.sum_mul,rejection_mass,map]
      congr 3
      funext x
      congr 1

lemma first_law_zero_none (p : Law α) (E : Finset α) :
    map (iid p (Fin 0)) (firstAccepted E (n := 0)) none=1 := by
  simp [map,firstAccepted,iid]

lemma first_law_zero_some (p : Law α) (E : Finset α) (a : α) :
    map (iid p (Fin 0)) (firstAccepted E (n := 0)) (some a)=0 := by
  simp [map,firstAccepted]

lemma first_law_none (p : Law α) (E : Finset α) (n : ℕ) :
    map (iid p (Fin n)) (firstAccepted E (n := n)) none=(1-eventMass p E)^n := by
  induction n with
  | zero => simpa using first_law_zero_none p E
  | succ n hn =>
    rw [first_law_succ,hn,pow_succ]
    simp only [Option.some_ne_none,and_false,ite_false,Finset.sum_const_zero,zero_add]
    ring

lemma first_law_some (p : Law α) (E : Finset α) (n : ℕ) (a : α) :
    map (iid p (Fin n)) (firstAccepted E (n := n)) (some a)=
      (if a∈E then p a else 0)*(∑ i∈Finset.range n,(1-eventMass p E)^i) := by
  induction n with
  | zero => simpa using first_law_zero_some p E a
  | succ n hn =>
    rw [first_law_succ,hn]
    have he : (∑ b,if b∈E ∧ some b=some a then p b else 0)=if a∈E then p a else 0 := by
      classical
      simp only [Option.some.injEq]
      simp only [and_comm,ite_and]
      simp
    rw [he,Finset.sum_range_succ']
    simp only [pow_succ',←Finset.mul_sum,pow_zero]
    ring

lemma acceptance_geom_sum (p : Law α) (E : Finset α) (n : ℕ) :
    eventMass p E*(∑ i∈Finset.range n,(1-eventMass p E)^i)=1-(1-eventMass p E)^n := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ,mul_add,hn,pow_succ]
    ring

theorem first_success_law (p : Law α) (E : Finset α) (n : ℕ) (hn : 0<n)
    (hE : 0<eventMass p E) (a : α) :
    map (iid p (Fin n)) (firstAccepted E (n := n)) (some a) /
      (1-map (iid p (Fin n)) (firstAccepted E (n := n)) none)=
      (if a∈E then p a/eventMass p E else 0) := by
  have hq : 0≤1-eventMass p E := sub_nonneg.mpr (eventMass_le_one p E)
  have hq1 : 1-eventMass p E<1 := by linarith
  have hp : (1-eventMass p E)^n<1 := pow_lt_one₀ hq hq1 (Nat.ne_of_gt hn)
  have hd : 1-(1-eventMass p E)^n≠0 := by linarith
  rw [first_law_some,first_law_none]
  by_cases ha : a∈E
  · rw [ite_eq_left ha,ite_eq_left ha]
    have hg := acceptance_geom_sum p E n
    apply (div_eq_div_iff hd (ne_of_gt hE)).mpr
    nlinarith [congrArg (fun z : ℝ => p a*z) hg]
  · simp [ha]

theorem first_success_density (p : Law α) (E : Finset α) (n : ℕ) (hn : 0<n)
    (hE : 0<eventMass p E) (a : α) :
    map (iid p (Fin n)) (firstAccepted E (n := n)) (some a) /
      (1-map (iid p (Fin n)) (firstAccepted E (n := n)) none)≤p a/eventMass p E := by
  rw [first_success_law p E n hn hE]
  split_ifs
  · exact le_rfl
  · exact div_nonneg (p.nonneg a) hE.le

end SharpRamseyFive.FiniteEntropy

end OAI
