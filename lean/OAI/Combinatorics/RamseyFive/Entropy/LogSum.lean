import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Map

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

theorem log_sum (f g : α → ℝ) (hf : ∀ a,0≤f a) (hg : ∀ a,0≤g a)
    (hac : ∀ a,0<f a → 0<g a) :
    (∑ a,f a)*Real.log ((∑ a,f a)/(∑ a,g a)) ≤ ∑ a,f a*Real.log (f a/g a) := by
  let F := ∑ a,f a
  let G := ∑ a,g a
  have hF0 : 0≤F := Finset.sum_nonneg fun a _ => hf a
  by_cases hFz : F=0
  · have hzero (a : α) : f a=0 := by
      have hle : f a≤F := Finset.single_le_sum (fun b _ => hf b) (Finset.mem_univ a)
      exact le_antisymm (hle.trans_eq hFz) (hf a)
    simp only [hzero,Finset.sum_const_zero,zero_mul]
    exact le_rfl
  have hF : 0<F := lt_of_le_of_ne hF0 (Ne.symm hFz)
  have hG : 0<G := by
    have hex : ∃ a,0<f a := by
      by_contra! hn
      have hnon : F≤0 := Finset.sum_nonpos fun a _ => hn a
      exact (not_le_of_gt hF) hnon
    obtain ⟨a,ha⟩ := hex
    exact (hac a ha).trans_le (Finset.single_le_sum (fun b _ => hg b) (Finset.mem_univ a))
  let p : Law α :=
    { mass := fun a => f a/F
      nonneg := fun a => div_nonneg (hf a) hF.le
      sum_one := by rw [←Finset.sum_div]; exact div_self hFz }
  let q : Law α :=
    { mass := fun a => g a/G
      nonneg := fun a => div_nonneg (hg a) hG.le
      sum_one := by rw [←Finset.sum_div]; exact div_self (ne_of_gt hG) }
  have hD : 0≤divergence p q := by
    apply divergence_nonneg p q
    intro a ha
    exact div_pos (hac a ((div_pos_iff_of_pos_right hF).mp ha)) hG
  have he (a : α) : f a*Real.log (f a/g a) =
      f a*Real.log (F/G)+F*(p a*Real.log (p a/q a)) := by
    by_cases hz : f a=0
    · simp [p,hz]
    · have hfp : 0<f a := lt_of_le_of_ne (hf a) (Ne.symm hz)
      have hgp := hac a hfp
      dsimp [p,q]
      rw [Real.log_div hz (ne_of_gt hgp),Real.log_div hFz (ne_of_gt hG),
        Real.log_div (ne_of_gt (div_pos hfp hF)) (ne_of_gt (div_pos hgp hG)),
        Real.log_div hz hFz,Real.log_div (ne_of_gt hgp) (ne_of_gt hG)]
      field_simp
      ring
  calc
    _ ≤ F*Real.log (F/G)+F*divergence p q := le_add_of_nonneg_right (mul_nonneg hF.le hD)
    _ = _ := by
      simp only [he,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,divergence,F]

theorem divergence_map_le (p q : Law α) (hac : ∀ a,0<p a → 0<q a) (f : α → β) :
    divergence (map p f) (map q f) ≤ divergence p q := by
  have hpoint (b : β) := log_sum
    (fun a => if f a=b then p a else 0)
    (fun a => if f a=b then q a else 0)
    (fun a => by split_ifs; exact p.nonneg a; exact le_rfl)
    (fun a => by split_ifs; exact q.nonneg a; exact le_rfl)
    (fun a ha => by
      split_ifs at ha ⊢ with h
      · exact hac a ha
      · exact (lt_irrefl _ ha).elim)
  have hs := Finset.sum_le_sum (fun b (_ : b∈Finset.univ) => hpoint b)
  change divergence (map p f) (map q f) ≤ _ at hs
  apply hs.trans_eq
  rw [Finset.sum_comm]
  unfold divergence
  apply Finset.sum_congr rfl
  intro a _
  have hterm (b : β) : (if f a=b then p a else 0)*Real.log
      ((if f a=b then p a else 0)/(if f a=b then q a else 0)) =
      if f a=b then p a*Real.log (p a/q a) else 0 := by
    split_ifs <;> simp
  simp only [hterm]
  classical
  simp

lemma map_product {γ δ : Type*} [Fintype γ] [Fintype δ]
    (p : Law α) (q : Law β) (f : α → γ) (g : β → δ) :
    map (product p q) (fun z => (f z.1,g z.2)) = product (map p f) (map q g) := by
  apply Law.ext
  funext z
  simp only [map,product,Fintype.sum_prod_type]
  have he (a : α) (b : β) :
      (if (f a,g b)=z then p a*q b else 0) =
        (if f a=z.1 then p a else 0)*(if g b=z.2 then q b else 0) := by
    rcases z with ⟨c,d⟩
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  simp only [he,←Finset.mul_sum,←Finset.sum_mul]

lemma map_first (p : Law (α × β)) : map p Prod.fst=first p := by
  apply Law.ext
  funext a
  simp only [map,first,Fintype.sum_prod_type]
  classical
  rw [Finset.sum_comm]
  simp

lemma map_second (p : Law (α × β)) : map p Prod.snd=second p := by
  apply Law.ext
  funext b
  simp only [map,second,Fintype.sum_prod_type]
  classical
  simp

theorem mutual_information_map_le {γ δ : Type*} [Fintype γ] [Fintype δ]
    (p : Law (α × β)) (f : α → γ) (g : β → δ) :
    entropy (map (first p) f)+entropy (map (second p) g)-
      entropy (map p (fun z => (f z.1,g z.2))) ≤
    entropy (first p)+entropy (second p)-entropy p := by
  have h := divergence_map_le p (product (first p) (second p)) (ac_product p)
    (fun z => (f z.1,g z.2))
  rw [map_product] at h
  have h1 : first (map p (fun z => (f z.1,g z.2)))=map (first p) f := by
    change first (pair p (f ∘ Prod.fst) (g ∘ Prod.snd))=_
    rw [first_pair,←map_comp,map_first]
  have h2 : second (map p (fun z => (f z.1,g z.2)))=map (second p) g := by
    change second (pair p (f ∘ Prod.fst) (g ∘ Prod.snd))=_
    rw [second_pair,←map_comp,map_second]
  rw [←h1,←h2,mutual_information,mutual_information] at h
  rw [h1,h2] at h
  exact h

end

open scoped BigOperators Classical
variable {α β γ ι : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

noncomputable def mapSnd (p : Law (α × β)) (f : β → γ) : Law (α × γ) :=
  map p (fun z => (z.1,f z.2))

lemma mapSnd_mass (p : Law (α × β)) (f : β → γ) (a : α) (c : γ) :
    mapSnd p f (a,c) = ∑ b,if f b=c then p (a,b) else 0 := by
  simp only [mapSnd,map,Fintype.sum_prod_type,Prod.mk.injEq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : f b=c <;> simp [h]

lemma first_mapSnd (p : Law (α × β)) (f : β → γ) : first (mapSnd p f)=first p := by
  change first (pair p Prod.fst (f ∘ Prod.snd))=_
  rw [first_pair,map_first]

lemma second_mapSnd (p : Law (α × β)) (f : β → γ) : second (mapSnd p f)=map (second p) f := by
  change second (pair p Prod.fst (f ∘ Prod.snd))=_
  rw [second_pair,←map_comp,map_second]

lemma fiber_mapSnd (p : Law (α × β)) (f : β → γ) (a : α) :
    fiber (mapSnd p f) a = map (fiber p a) f := by
  by_cases h : 0 < first p a
  · apply Law.ext
    funext c
    simp only [fiber,first_mapSnd,dite_eq_left h]
    change mapSnd p f (a,c)/first p a=∑ b,if f b=c then p (a,b)/first p a else 0
    rw [mapSnd_mass,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp
  · simp only [fiber,first_mapSnd,dite_eq_right h,second_mapSnd]

noncomputable def totalCorrelation (p : Law (ι → β)) : ℝ :=
  (∑ i,entropy (map p (fun x => x i)))-entropy p

noncomputable def information (p : Law (α × β)) : ℝ :=
  entropy (first p)+entropy (second p)-entropy p

lemma information_nonneg (p : Law (α × β)) : 0 ≤ information p := by
  dsimp [information]
  linarith [entropy_subadditive p]

lemma information_conditional (p : Law (α × β)) :
    information p = entropy (second p)-∑ a,first p a*entropy (fiber p a) := by
  dsimp [information]
  rw [entropy_chain]
  ring

theorem total_correlation_drop (p : Law (α × (ι → β))) :
    (entropy (first p)+(∑ i,entropy (map (second p) (fun x => x i)))-entropy p)-
      (∑ a,first p a*totalCorrelation (fiber p a)) =
      ∑ i,information (mapSnd p (fun x => x i)) := by
  have hI (i : ι) : information (mapSnd p (fun x => x i)) =
      entropy (map (second p) (fun x => x i))-
      ∑ a,first p a*entropy (map (fiber p a) (fun x => x i)) := by
    rw [information_conditional,second_mapSnd,first_mapSnd]
    simp only [fiber_mapSnd]
  simp only [hI,totalCorrelation,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a i => first p a*entropy (map (fiber p a) (fun x => x i)))]
  rw [entropy_chain]
  ring

lemma information_observation_le (p : Law (α × β)) (f : α → γ) :
    information (map p (fun z => (f z.1,z.2))) ≤ information p := by
  have hh := mutual_information_map_le p f id
  have h1 : first (map p (fun z => (f z.1,z.2)))=map (first p) f := by
    change first (pair p (f ∘ Prod.fst) (id ∘ Prod.snd))=_
    rw [first_pair]
    rw [←map_comp,map_first]
  have h2 : second (map p (fun z => (f z.1,z.2)))=second p := by
    change second (pair p (f ∘ Prod.fst) Prod.snd)=_
    rw [second_pair,map_second]
  simpa only [information,h1,h2,map_id,id_eq] using hh

noncomputable def independent (p : ι → Law β) : Law (ι → β) where
  mass x := ∏ i,p i (x i)
  nonneg x := Finset.prod_nonneg fun i _ => (p i).nonneg _
  sum_one := by
    rw [←Fintype.prod_sum]
    simp only [Law.sum_one,Finset.prod_const_one]

lemma map_eval_mass_pos (p : Law (ι → β)) (x : ι → β) (hx : 0<p x) (i : ι) :
    0 < map p (fun z => z i) (x i) := by
  apply hx.trans_le
  change p x≤∑ z,if z i=x i then p z else 0
  have hh := Finset.single_le_sum (s := Finset.univ) (a := x)
    (f := fun z => if z i=x i then p z else 0) (fun z _ => by split_ifs; exact p.nonneg _; rfl)
    (Finset.mem_univ x)
  simpa using hh

theorem totalCorrelation_nonneg (p : Law (ι → β)) : 0≤totalCorrelation p := by
  let q : Law (ι → β) := independent (fun i => map p (fun z => z i))
  have hac (x : ι → β) (hx : 0<p x) : 0<q x :=
    Finset.prod_pos (fun i _ => map_eval_mass_pos p x hx i)
  have hd := divergence_nonneg p q hac
  have hpq (x : ι → β) : p x*Real.log (p x/q x) =
      p x*Real.log (p x)-∑ i,p x*Real.log (map p (fun z => z i) (x i)) := by
    by_cases h : p x=0
    · simp only [h,zero_mul,Finset.sum_const_zero,sub_zero]
    · have hx : 0<p x := lt_of_le_of_ne (p.nonneg x) (Ne.symm h)
      rw [Real.log_div h (ne_of_gt (hac x hx))]
      have he : Real.log (q x)=∑ i,Real.log (map p (fun z => z i) (x i)) := by
        apply Real.log_prod
        intro i _
        exact ne_of_gt (map_eval_mass_pos p x hx i)
      rw [he,mul_sub,Finset.mul_sum]
  have he : divergence p q=totalCorrelation p := by
    simp only [divergence,hpq,Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    have hm (i : ι) : (∑ x,p x*Real.log (map p (fun z => z i) (x i))) =
        -entropy (map p (fun z => z i)) := by
      rw [←sum_map p (fun z => z i) (fun b => Real.log (map p (fun z => z i) b))]
      simp only [entropy,neg_neg]
    simp only [hm,Finset.sum_neg_distrib,totalCorrelation,entropy]
    ring
  rwa [he] at hd

end SharpRamseyFive.FiniteEntropy

end OAI
