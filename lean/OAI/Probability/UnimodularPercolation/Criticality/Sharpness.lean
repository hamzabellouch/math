import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.Sprinkling

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteRusso
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

 
noncomputable def bernoulliPolynomial (s : Finset E) (f : Finset E → ℝ) (p : ℝ) : ℝ :=
  ∑ t ∈ s.powerset, f t * p ^ t.card * (1-p) ^ (s.card-t.card)

@[simp] theorem bernoulliPolynomial_empty (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial ∅ f p = f ∅ := by simp [bernoulliPolynomial]

theorem bernoulliPolynomial_congr (s : Finset E) {f g : Finset E → ℝ}
    (h : ∀ t ⊆ s, f t = g t) (p : ℝ) :
    bernoulliPolynomial s f p = bernoulliPolynomial s g p := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (Finset.mem_powerset.mp ht)]

theorem bernoulliPolynomial_sub (s : Finset E) (f g : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => f t-g t) p =
      bernoulliPolynomial s f p - bernoulliPolynomial s g p := by
  simp only [bernoulliPolynomial, sub_mul, Finset.sum_sub_distrib]

theorem bernoulliPolynomial_insert (s : Finset E) (e : E) (he : e ∉ s)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (insert e s) f p =
      (1-p)*bernoulliPolynomial s f p + p*bernoulliPolynomial s (fun t => f (insert e t)) p := by
  have hd : Disjoint s.powerset (s.powerset.image (insert e)) := by
    apply Finset.disjoint_left.mpr
    intro t ht himg
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp himg
    exact he ((Finset.mem_powerset.mp ht) (by simp))
  have hinj : Set.InjOn (insert e) (↑s.powerset : Set (Finset E)) := by
    intro t ht r hr h
    have ht' : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    have hr' : e ∉ r := fun h => he (Finset.mem_powerset.mp hr h)
    have hh := congrArg (fun t : Finset E => t.erase e) h
    simpa [ht', hr'] using hh
  simp only [bernoulliPolynomial, Finset.powerset_insert, Finset.sum_union hd,
    Finset.sum_image hinj, Finset.mul_sum, Finset.card_insert_of_notMem he]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp ht)
    have hexp : s.card+1-t.card = (s.card-t.card)+1 := by omega
    rw [hexp, pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro t ht
    have het : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    simp only [Finset.card_insert_of_notMem het, Nat.add_sub_add_right, pow_succ]
    ring

 
theorem hasDerivAt_bernoulliPolynomial (s : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    HasDerivAt (bernoulliPolynomial s f)
      (∑ e ∈ s, bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p) p := by
  induction s using Finset.induction_on generalizing f with
  | empty =>
    convert hasDerivAt_const p (f ∅) using 1 <;> try rfl
    · funext q
      exact bernoulliPolynomial_empty f q
  | @insert e s he ih =>
    have hd := (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul (ih f)).add
      ((hasDerivAt_id p).mul (ih (fun t => f (insert e t))))
    have hf : bernoulliPolynomial (insert e s) f =
        fun q => (1-q)*bernoulliPolynomial s f q +
          q*bernoulliPolynomial s (fun t => f (insert e t)) q :=
      funext fun q => bernoulliPolynomial_insert s e he f q
    rw [hf]
    convert hd using 1 <;> try rfl
    have hs : ∑ a ∈ s, bernoulliPolynomial ((insert e s).erase a)
          (fun t => f (insert a t)-f t) p =
        (1-p)*(∑ a ∈ s, bernoulliPolynomial (s.erase a) (fun t => f (insert a t)-f t) p) +
        p*(∑ a ∈ s, bernoulliPolynomial (s.erase a)
          (fun t => f (insert e (insert a t))-f (insert e t)) p) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have hae : e ≠ a := (ne_of_mem_of_not_mem ha he).symm
      rw [Finset.erase_insert_of_ne hae, bernoulliPolynomial_insert _ e
        (fun hh => he (Finset.mem_of_mem_erase hh))]
      congr 2
      apply bernoulliPolynomial_congr
      intro t _
      rw [Finset.insert_comm e a]
    simp only [Finset.sum_insert he, Finset.erase_insert he, zero_sub, neg_one_mul,
      one_mul, Pi.sub_apply, id_eq]
    rw [hs, bernoulliPolynomial_sub]
    ring

@[simp] theorem bernoulliPolynomial_zero (s : Finset E) (p : ℝ) :
    bernoulliPolynomial s (fun _ => 0) p = 0 := by simp [bernoulliPolynomial]

theorem bernoulliPolynomial_const (s : Finset E) (c p : ℝ) :
    bernoulliPolynomial s (fun _ => c) p = c := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih => rw [bernoulliPolynomial_insert s e he]; simp only [ih]; ring

theorem bernoulliPolynomial_nonneg (s : Finset E) (f : Finset E → ℝ) (p : ℝ)
    (hp : p ∈ Set.Icc (0:ℝ) 1) (hf : ∀ t ⊆ s, 0 ≤ f t) :
    0 ≤ bernoulliPolynomial s f p := by
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (mul_nonneg (hf t (Finset.mem_powerset.mp ht))
    (pow_nonneg hp.1 _)) (pow_nonneg (sub_nonneg.mpr hp.2) _)

theorem bernoulliPolynomial_mono (s : Finset E) (f g : Finset E → ℝ) (p : ℝ)
    (hp : p ∈ Set.Icc (0:ℝ) 1) (hfg : ∀ t ⊆ s, f t ≤ g t) :
    bernoulliPolynomial s f p ≤ bernoulliPolynomial s g p := by
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hfg t (Finset.mem_powerset.mp ht)) (pow_nonneg hp.1 _))
    (pow_nonneg (sub_nonneg.mpr hp.2) _)

 
theorem bernoulliPolynomial_union (s t : Finset E) (hdis : Disjoint s t)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (s ∪ t) f p =
      bernoulliPolynomial s (fun a => bernoulliPolynomial t (fun b => f (a ∪ b)) p) p := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert e s he ih =>
    have hed : e ∉ t := (Finset.disjoint_insert_left.mp hdis).1
    have hst : Disjoint s t := (Finset.disjoint_insert_left.mp hdis).2
    rw [Finset.insert_union, bernoulliPolynomial_insert _ e (by simp [he, hed]),
      bernoulliPolynomial_insert s e he, ih hst, ih hst]
    congr 2
    apply bernoulliPolynomial_congr
    intro a _
    apply bernoulliPolynomial_congr
    intro b _
    rw [Finset.insert_union]

 

theorem bernoulliPolynomial_closed_difference (s : Finset E) (e : E) (he : e ∈ s)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => if e ∈ t then 0 else f (insert e t)-f t) p =
      (1-p)*bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p := by
  have hes : e ∉ s.erase e := Finset.notMem_erase e s
  conv_lhs => rw [← Finset.insert_erase he]
  rw [bernoulliPolynomial_insert _ e hes]
  have hc : bernoulliPolynomial (s.erase e)
      (fun t => if e ∈ t then 0 else f (insert e t)-f t) p =
      bernoulliPolynomial (s.erase e) (fun t => f (insert e t)-f t) p := by
    apply bernoulliPolynomial_congr
    intro t ht
    simp [show e ∉ t from fun h => hes (ht h)]
  rw [hc]
  simp

theorem closed_difference_russo (s : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    (1-p)*deriv (bernoulliPolynomial s f) p =
      ∑ e ∈ s, bernoulliPolynomial s
        (fun t => if e ∈ t then 0 else f (insert e t)-f t) p := by
  rw [(hasDerivAt_bernoulliPolynomial s f p).deriv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact (bernoulliPolynomial_closed_difference s e he f p).symm

 
noncomputable def finiteEventPolynomial (s : Finset E) (A : Set (Set E)) (p : ℝ) : ℝ :=
  bernoulliPolynomial s (fun t => if (t : Set E) ∈ A then 1 else 0) p

theorem finiteEventPolynomial_eq (s : Finset E) (A : Set (Set E)) (p : unitInterval) :
    finiteEventPolynomial s A (p : ℝ) = finiteProbability p s A := by
  unfold finiteEventPolynomial bernoulliPolynomial finiteProbability
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : (t : Set E) ∈ A <;> simp [ht]

 
def closedPivotal (A : Set (Set E)) (e : E) : Set (Set E) :=
  {ω | e ∉ ω ∧ ω ∉ A ∧ insert e ω ∈ A}

theorem closedPivotal_difference (A : Set (Set E)) (hA : IsUpperSet A) (e : E)
    (t : Finset E) :
    (if (t : Set E) ∈ closedPivotal A e then (1:ℝ) else 0) =
    (if e ∈ t then 0 else
      (if ((insert e t : Finset E) : Set E) ∈ A then (1:ℝ) else 0) -
      (if (t : Set E) ∈ A then 1 else 0)) := by
  by_cases he : e ∈ t
  · simp [closedPivotal, he]
  · by_cases ha : (t : Set E) ∈ A
    · have hi : insert e (t : Set E) ∈ A := hA (Set.subset_insert e _) ha
      simp [closedPivotal, he, ha, hi]
    · by_cases hi : insert e (t : Set E) ∈ A <;> simp [closedPivotal, he, ha, hi]

 
theorem finite_russo_closed (s : Finset E) (A : Set (Set E)) (hA : IsUpperSet A)
    (p : unitInterval) :
    (1-(p:ℝ))*deriv (finiteEventPolynomial s A) (p:ℝ) =
      ∑ e ∈ s, finiteProbability p s (closedPivotal A e) := by
  rw [show finiteEventPolynomial s A =
    bernoulliPolynomial s (fun t => if (t : Set E) ∈ A then 1 else 0) from rfl,
    closed_difference_russo]
  apply Finset.sum_congr rfl
  intro e _
  rw [← finiteEventPolynomial_eq]
  apply bernoulliPolynomial_congr
  intro t _
  exact (closedPivotal_difference A hA e t).symm

 

theorem finite_russo_closed_law [Fintype E] (A : Set (Set E)) (hA : IsUpperSet A)
    (p : unitInterval) :
    (1-(p:ℝ))*deriv (finiteEventPolynomial Finset.univ A) (p:ℝ) =
      ∑ e : E, (law p).real (closedPivotal A e) := by
  simpa only [finiteProbability_univ] using finite_russo_closed Finset.univ A hA p

end FiniteRusso

section ExteriorExposure
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

 
theorem conn_insert_iff (G : BondGraph V E) (ω : Set E) (e : E) (a b x y : V)
    (he : G e = s(a,b)) :
    Conn G (insert e ω) x y ↔ Conn G ω x y ∨
      (Conn G ω x a ∧ Conn G ω b y) ∨ (Conn G ω x b ∧ Conn G ω a y) := by
  constructor
  · intro hh
    induction hh with
    | refl => exact Or.inl (conn_refl G ω x)
    | @tail u v huv huv' ih =>
      obtain ⟨f,hf,hfuv⟩ := huv'
      rcases Set.mem_insert_iff.mp hf with rfl | hf
      · have hp : s(a,b) = s(u,v) := he.symm.trans hfuv
        rcases Sym2.eq_iff.mp hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rcases ih with h | ⟨hxa,hba⟩ | ⟨hxb,haa⟩
          · exact Or.inr (Or.inl ⟨h,conn_refl G ω b⟩)
          · exact Or.inr (Or.inl ⟨hxa,conn_refl G ω b⟩)
          · exact Or.inl hxb
        · rcases ih with h | ⟨hxa,hbb⟩ | ⟨hxb,hab⟩
          · exact Or.inr (Or.inr ⟨h,conn_refl G ω a⟩)
          · exact Or.inl hxa
          · exact Or.inr (Or.inr ⟨hxb,conn_refl G ω a⟩)
      · have huvω : Conn G ω u v := .single ⟨f,hf,hfuv⟩
        rcases ih with h | ⟨hxa,hbu⟩ | ⟨hxb,hau⟩
        · exact Or.inl (h.trans huvω)
        · exact Or.inr (Or.inl ⟨hxa,hbu.trans huvω⟩)
        · exact Or.inr (Or.inr ⟨hxb,hau.trans huvω⟩)
  · intro hh
    have hm : ω ⊆ insert e ω := Set.subset_insert e ω
    have hab : Conn G (insert e ω) a b := .single ⟨e,Set.mem_insert e ω,he⟩
    rcases hh with h | ⟨hxa,hby⟩ | ⟨hxb,hay⟩
    · exact conn_mono G hm h
    · exact (conn_mono G hm hxa).trans (hab.trans (conn_mono G hm hby))
    · exact (conn_mono G hm hxb).trans ((conn_symm G _ hab).trans (conn_mono G hm hay))

 
def internalEdges (G : BondGraph V E) (S : Set V) : Set E :=
  {e | ∀ x ∈ G e, x ∈ S}

@[simp] theorem mem_internalEdges_of_ends (G : BondGraph V E) (S : Set V)
    (e : E) (a b : V) (he : G e = s(a,b)) :
    e ∈ internalEdges G S ↔ a ∈ S ∧ b ∈ S := by
  simp [internalEdges, he]

 
def unexposed (G : BondGraph V E) (Λ : Set V) (ω : Set E) : Set V :=
  {x | ∀ y, Conn G ω x y → y ∈ Λ}

theorem unexposed_subset (G : BondGraph V E) (Λ : Set V) (ω : Set E) :
    unexposed G Λ ω ⊆ Λ := fun x hx => hx x (conn_refl G ω x)

theorem mem_unexposed_of_conn (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∈ unexposed G Λ ω) (hxy : Conn G ω x y) :
    y ∈ unexposed G Λ ω := by
  intro z hyz
  exact hx z (hxy.trans hyz)

 
theorem conn_restrict_unexposed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∈ unexposed G Λ ω) (hxy : Conn G ω x y) :
    Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x y := by
  induction hxy with
  | refl => exact conn_refl _ _ _
  | @tail y z hxy hyz ih =>
    obtain ⟨e,he,hends⟩ := hyz
    have hy : y ∈ unexposed G Λ ω := mem_unexposed_of_conn G Λ ω hx hxy
    have hz : z ∈ unexposed G Λ ω := mem_unexposed_of_conn G Λ ω hy (.single ⟨e,he,hends⟩)
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e y z hends).mpr ⟨hy,hz⟩⟩,hends⟩

 
theorem unexposed_boundary_closed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {e : E} {a b : V} (he : G e = s(a,b))
    (ha : a ∈ unexposed G Λ ω) (hb : b ∉ unexposed G Λ ω) : e ∉ ω := by
  intro ho
  exact hb (mem_unexposed_of_conn G Λ ω ha (.single ⟨e,ho,he⟩))

 

theorem unexposed_insert_crossing (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {e : E} {a b x : V} (he : G e = s(a,b))
    (hx : x ∈ unexposed G Λ ω) (_ha : a ∈ unexposed G Λ ω)
    (hb : b ∉ unexposed G Λ ω) :
    x ∉ unexposed G Λ (insert e ω) ↔
      Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x a := by
  classical
  constructor
  · intro hn
    obtain ⟨y,hxy,hy⟩ := by simpa [unexposed, not_forall, Classical.not_imp] using hn
    rcases (conn_insert_iff G ω e a b x y he).mp hxy with h | h | h
    · exact (hy (hx y h)).elim
    · exact conn_restrict_unexposed G Λ ω hx h.1
    · exact (hb (mem_unexposed_of_conn G Λ ω hx h.1)).elim
  · intro hxa hn
    have hxa' : Conn G ω x a := conn_mono G Set.inter_subset_left hxa
    apply hb
    intro y hby
    exact hn y ((conn_insert_iff G ω e a b x y he).mpr (Or.inr (Or.inl ⟨hxa',hby⟩)))

 
theorem not_mem_unexposed_of_conn (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∉ unexposed G Λ ω) (hxy : Conn G ω x y) :
    y ∉ unexposed G Λ ω := by
  intro hy
  exact hx (mem_unexposed_of_conn G Λ ω hy (conn_symm G ω hxy))

 
theorem conn_sdiff_internal_unexposed (G : BondGraph V E) (Λ : Set V) (ω : Set E)
    {x y : V} (hx : x ∉ unexposed G Λ ω) (hxy : Conn G ω x y) :
    Conn G (ω \ internalEdges G (unexposed G Λ ω)) x y := by
  induction hxy with
  | refl => exact conn_refl _ _ _
  | @tail y z hxy hyz ih =>
    obtain ⟨e,he,hends⟩ := hyz
    have hy : y ∉ unexposed G Λ ω := not_mem_unexposed_of_conn G Λ ω hx hxy
    exact ih.tail ⟨e,⟨he,fun hi => hy ((mem_internalEdges_of_ends G _ e y z hends).mp hi).1⟩,hends⟩

 
theorem unexposed_sdiff_internal (G : BondGraph V E) (Λ : Set V) (ω : Set E) :
    unexposed G Λ (ω \ internalEdges G (unexposed G Λ ω)) = unexposed G Λ ω := by
  ext x
  constructor
  · intro hx
    by_contra hn
    apply hn
    intro y hxy
    exact hx y (conn_sdiff_internal_unexposed G Λ ω hn hxy)
  · intro hx y hxy
    exact hx y (conn_mono G Set.sdiff_subset hxy)

 
theorem unexposed_union_internal (G : BondGraph V E) (Λ : Set V) (ω η : Set E)
    (hη : η ⊆ internalEdges G (unexposed G Λ ω)) :
    unexposed G Λ (ω ∪ η) = unexposed G Λ ω := by
  ext x
  constructor
  · intro hx y hxy
    exact hx y (conn_mono G Set.subset_union_left hxy)
  · intro hx y hxy
    suffices hy : y ∈ unexposed G Λ ω from unexposed_subset G Λ ω hy
    induction hxy with
    | refl => exact hx
    | @tail y z hxy hyz ih =>
      obtain ⟨e,hωe,he⟩ := hyz
      rcases hωe with ho | hηe
      · exact mem_unexposed_of_conn G Λ ω ih (.single ⟨e,ho,he⟩)
      · exact ((mem_internalEdges_of_ends G _ e y z he).mp (hη hηe)).2

 
theorem unexposed_union_eq_iff (G : BondGraph V E) (Λ S : Set V) (a b : Set E)
    (ha : a ⊆ internalEdges G S) (hb : Disjoint b (internalEdges G S)) :
    unexposed G Λ (a ∪ b) = S ↔ unexposed G Λ b = S := by
  constructor
  · intro h
    have he : (a ∪ b) \ internalEdges G S = b := by
      ext e
      constructor
      · rintro ⟨he,hn⟩
        exact he.resolve_left (fun he => hn (ha he))
      · intro he
        exact ⟨Or.inr he,fun hi => Set.disjoint_left.mp hb he hi⟩
    simpa only [h, he] using unexposed_sdiff_internal G Λ (a ∪ b)
  · intro h
    have he := unexposed_union_internal G Λ b a (h ▸ ha)
    simpa only [Set.union_comm b a,h] using he

 
def escapeEvent (G : BondGraph V E) (Λ : Set V) (x : V) : Set (Set E) :=
  {ω | x ∉ unexposed G Λ ω}

theorem escapeEvent_isUpperSet (G : BondGraph V E) (Λ : Set V) (x : V) :
    IsUpperSet (escapeEvent G Λ x) := by
  intro ω η hωη hx hη
  apply hx
  intro y hxy
  exact hη y (conn_mono G hωη hxy)

 
theorem escape_closed_pivotal_iff (G : BondGraph V E) (Λ : Set V)
    (ω : Set E) (x : V) (e : E) :
    (e ∉ ω ∧ ω ∉ escapeEvent G Λ x ∧ insert e ω ∈ escapeEvent G Λ x) ↔
      x ∈ unexposed G Λ ω ∧ ∃ a b,
        G e = s(a,b) ∧ a ∈ unexposed G Λ ω ∧ b ∉ unexposed G Λ ω ∧
        Conn G (ω ∩ internalEdges G (unexposed G Λ ω)) x a := by
  classical
  constructor
  · rintro ⟨_,hx,hn⟩
    have hx' : x ∈ unexposed G Λ ω := by simpa [escapeEvent] using hx
    refine ⟨hx',?_⟩
    obtain ⟨⟨a,b⟩,he'⟩ := Sym2.mk_surjective (G e)
    have he : G e = s(a,b) := he'.symm
    obtain ⟨y,hxy,hy⟩ := by simpa [escapeEvent,unexposed,not_forall,Classical.not_imp] using hn
    rcases (conn_insert_iff G ω e a b x y he).mp hxy with h | h | h
    · exact (hy (hx' y h)).elim
    · exact ⟨a,b,he,mem_unexposed_of_conn G Λ ω hx' h.1,
        fun hb => hy (hb y h.2),conn_restrict_unexposed G Λ ω hx' h.1⟩
    · exact ⟨b,a,he.trans (Sym2.eq_swap ..),mem_unexposed_of_conn G Λ ω hx' h.1,
        fun ha => hy (ha y h.2),conn_restrict_unexposed G Λ ω hx' h.1⟩
  · rintro ⟨hx,a,b,he,ha,hb,hxa⟩
    exact ⟨unexposed_boundary_closed G Λ ω he ha hb,by simpa [escapeEvent] using hx,
      (unexposed_insert_crossing G Λ ω he hx ha hb).mpr hxa⟩

attribute [local instance] Classical.decEq

 theorem bernoulliPolynomial_add (s : Finset E) (f g : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => f t+g t) p =
      bernoulliPolynomial s f p + bernoulliPolynomial s g p := by
  simp only [bernoulliPolynomial, add_mul, Finset.sum_add_distrib]

 theorem bernoulliPolynomial_mul_const (s : Finset E) (f : Finset E → ℝ) (c p : ℝ) :
    bernoulliPolynomial s (fun t => f t*c) p = bernoulliPolynomial s f p*c := by
  simp only [bernoulliPolynomial, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  ring

 theorem bernoulliPolynomial_const_mul (s : Finset E) (f : Finset E → ℝ) (c p : ℝ) :
    bernoulliPolynomial s (fun t => c*f t) p = c*bernoulliPolynomial s f p := by
  simpa only [mul_comm c] using bernoulliPolynomial_mul_const s f c p

 theorem bernoulliPolynomial_sum {ι : Type*} (s : Finset E) (I : Finset ι)
    (f : ι → Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial s (fun t => ∑ i ∈ I, f i t) p =
      ∑ i ∈ I, bernoulliPolynomial s (f i) p := by
  classical
  simp only [bernoulliPolynomial, Finset.sum_mul]
  exact Finset.sum_comm

 
theorem bernoulliPolynomial_blocks (s t : Finset E) (hdis : Disjoint s t)
    (f g : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (s ∪ t) (fun a => f (a ∩ s)*g (a ∩ t)) p =
      bernoulliPolynomial s f p * bernoulliPolynomial t g p := by
  rw [bernoulliPolynomial_union s t hdis]
  trans bernoulliPolynomial s (fun a => f a*bernoulliPolynomial t g p) p
  · apply bernoulliPolynomial_congr
    intro a ha
    rw [← bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_congr
    intro b hb
    have has : a ∩ s = a := Finset.inter_eq_left.mpr ha
    have hbt : b ∩ t = b := Finset.inter_eq_left.mpr hb
    have hbs : b ∩ s = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
      (hdis.symm.mono_left hb)
    have hat : a ∩ t = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
      (hdis.mono_left ha)
    simp [Finset.union_inter_distrib_right,has,hbt,hbs,hat]
  · exact bernoulliPolynomial_mul_const s f _ p

 

theorem bernoulliPolynomial_exposure (G : BondGraph V E) (Λ S : Set V)
    (s t : Finset E) (hs : (s : Set E) ⊆ internalEdges G S)
    (ht : Disjoint (t : Set E) (internalEdges G S)) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial (s ∪ t)
      (fun a => (if unexposed G Λ (a : Set E) = S then (1:ℝ) else 0) * f (a ∩ s)) p =
    bernoulliPolynomial t (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p *
      bernoulliPolynomial s f p := by
  have hdis : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Set.disjoint_left.mp ht hf (hs he)
  rw [bernoulliPolynomial_union s t hdis]
  trans bernoulliPolynomial s (fun a =>
    bernoulliPolynomial t (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p * f a) p
  · apply bernoulliPolynomial_congr
    intro a ha
    rw [← bernoulliPolynomial_mul_const]
    apply bernoulliPolynomial_congr
    intro b hb
    have hab : unexposed G Λ ((a ∪ b : Finset E) : Set E) = S ↔
        unexposed G Λ (b : Set E) = S := by
      rw [Finset.coe_union]
      exact unexposed_union_eq_iff G Λ S _ _ (fun _ he => hs (ha he))
        (ht.mono_left (by exact_mod_cast hb))
    have hbs : b ∩ s = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp (hdis.symm.mono_left hb)
    rw [Finset.union_inter_distrib_right,Finset.inter_eq_left.mpr ha,hbs,Finset.union_empty]
    simp only [hab]
  · exact bernoulliPolynomial_const_mul s f _ p

 
noncomputable def unexposedRegion (G : BondGraph V E) (Λ : Finset V) (ω : Set E) : Finset V :=
  ((Set.toFinite (Λ : Set V)).subset (unexposed_subset G (Λ : Set V) ω)).toFinset

@[simp] theorem coe_unexposedRegion (G : BondGraph V E) (Λ : Finset V) (ω : Set E) :
    (unexposedRegion G Λ ω : Set V) = unexposed G (Λ : Set V) ω := by
  simp [unexposedRegion]

theorem unexposedRegion_subset (G : BondGraph V E) (Λ : Finset V) (ω : Set E) :
    unexposedRegion G Λ ω ⊆ Λ := by
  intro x hx
  apply unexposed_subset G (Λ : Set V) ω
  simpa only [← coe_unexposedRegion,Finset.mem_coe] using hx

 
theorem bernoulliPolynomial_partition_region (G : BondGraph V E) (Λ : Finset V)
    (F : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial F f p = ∑ S ∈ Λ.powerset,
      bernoulliPolynomial F
        (fun t => if unexposed G (Λ : Set V) (t : Set E) = (S : Set V) then f t else 0) p := by
  rw [← bernoulliPolynomial_sum]
  apply bernoulliPolynomial_congr
  intro t _
  symm
  rw [Finset.sum_eq_single (unexposedRegion G Λ (t : Set E))]
  · simp
  · intro S _ hne
    have hh : unexposed G (Λ : Set V) (t : Set E) ≠ (S : Set V) := by
      intro he
      apply hne
      apply Finset.coe_injective
      exact he.symm.trans (coe_unexposedRegion G Λ (t : Set E)).symm
    simp [hh]
  · intro hn
    exact (hn (Finset.mem_powerset.mpr (unexposedRegion_subset G Λ (t : Set E)))).elim

 
noncomputable def internalSupport (G : BondGraph V E) (S : Set V) (F : Finset E) : Finset E :=
  F.filter (fun e => e ∈ internalEdges G S)

 theorem internalSupport_subset (G : BondGraph V E) (S : Set V) (F : Finset E) :
    internalSupport G S F ⊆ F := Finset.filter_subset _ _

 theorem internalSupport_union_sdiff (G : BondGraph V E) (S : Set V) (F : Finset E) :
    internalSupport G S F ∪ (F \ internalSupport G S F) = F :=
  Finset.union_sdiff_of_subset (internalSupport_subset G S F)

 theorem coe_inter_internalSupport (G : BondGraph V E) (S : Set V) (F t : Finset E)
    (ht : t ⊆ F) : ((t ∩ internalSupport G S F : Finset E) : Set E) =
      (t : Set E) ∩ internalEdges G S := by
  ext e
  simp only [Finset.mem_coe,Finset.mem_inter,internalSupport,Finset.mem_filter,Set.mem_inter_iff]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,ht h.1,h.2⟩⟩

 
noncomputable def regionProbability (G : BondGraph V E) (Λ S : Set V)
    (F : Finset E) (p : ℝ) : ℝ :=
  bernoulliPolynomial F (fun t => if unexposed G Λ (t : Set E) = S then 1 else 0) p

 theorem regionProbability_nonneg (G : BondGraph V E) (Λ S : Set V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ regionProbability G Λ S F p := by
  apply bernoulliPolynomial_nonneg _ _ _ hp
  intro t _
  split_ifs <;> norm_num

 
theorem bernoulliPolynomial_exposure_factor (G : BondGraph V E) (Λ S : Set V)
    (F : Finset E) (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial F
      (fun t => (if unexposed G Λ (t : Set E) = S then (1:ℝ) else 0) *
        f (t ∩ internalSupport G S F)) p =
      regionProbability G Λ S F p * bernoulliPolynomial (internalSupport G S F) f p := by
  let s := internalSupport G S F
  let t := F \ s
  have hs : (s : Set E) ⊆ internalEdges G S := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have ht : Disjoint (t : Set E) (internalEdges G S) := by
    apply Set.disjoint_left.mpr
    intro e he hi
    have he' := Finset.mem_sdiff.mp he
    exact he'.2 (Finset.mem_filter.mpr ⟨he'.1,hi⟩)
  have he : s ∪ t = F := internalSupport_union_sdiff G S F
  have hq : bernoulliPolynomial t
      (fun b => if unexposed G Λ (b : Set E) = S then (1:ℝ) else 0) p =
      regionProbability G Λ S F p := by
    simpa only [he,mul_one,bernoulliPolynomial_const,regionProbability] using
      (bernoulliPolynomial_exposure G Λ S s t hs ht (fun _ => 1) p).symm
  simpa only [he,hq] using bernoulliPolynomial_exposure G Λ S s t hs ht f p

 
def crossingReach (G : BondGraph V E) (S : Set V) (x : V) (ω : Set E) (e : E) : Prop :=
  ∃ a b, G e = s(a,b) ∧ a ∈ S ∧ b ∉ S ∧ Conn G ω x a

noncomputable def crossingCount (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) (ω : Set E) : ℝ :=
  ∑ e ∈ F, if crossingReach G S x ω e then (1:ℝ) else 0

 
noncomputable def boundaryExpectation (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) (p : ℝ) : ℝ :=
  bernoulliPolynomial (internalSupport G S F)
    (fun t => crossingCount G S x F (t : Set E)) p

noncomputable def closedEscapeCount (G : BondGraph V E) (Λ : Set V) (x : V)
    (F : Finset E) (ω : Set E) : ℝ :=
  ∑ e ∈ F, if ω ∈ closedPivotal (escapeEvent G Λ x) e then (1:ℝ) else 0

theorem finite_escape_russo (G : BondGraph V E) (Λ : Set V) (x : V)
    (F : Finset E) (p : ℝ) :
    (1-p)*deriv (finiteEventPolynomial F (escapeEvent G Λ x)) p =
      bernoulliPolynomial F (fun t => closedEscapeCount G Λ x F (t : Set E)) p := by
  unfold finiteEventPolynomial
  rw [closed_difference_russo]
  unfold closedEscapeCount
  rw [bernoulliPolynomial_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply bernoulliPolynomial_congr
  intro t _
  exact (closedPivotal_difference _ (escapeEvent_isUpperSet G Λ x) e t).symm

 
theorem closedEscapeCount_expectation (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) :
    bernoulliPolynomial F (fun t => closedEscapeCount G Λ x F (t : Set E)) p =
      ∑ S ∈ Λ.powerset, if x ∈ S then
        regionProbability G Λ S F p * boundaryExpectation G S x F p else 0 := by
  rw [bernoulliPolynomial_partition_region G Λ F]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    unfold boundaryExpectation
    rw [← bernoulliPolynomial_exposure_factor G Λ S F
      (fun t => crossingCount G S x F (t : Set E)) p]
    apply bernoulliPolynomial_congr
    intro t ht
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V)
    · simp only [hreg,ite_true,one_mul]
      apply Finset.sum_congr rfl
      intro e _
      have hc : (t : Set E) ∈ closedPivotal (escapeEvent G Λ x) e ↔
          crossingReach G S x ((t ∩ internalSupport G S F : Finset E) : Set E) e := by
        simpa only [closedPivotal,Set.mem_ofPred_eq,hreg,Finset.mem_coe,hx,true_and,
          coe_inter_internalSupport G S F t ht,crossingReach] using
          escape_closed_pivotal_iff G Λ (t : Set E) x e
      exact if_congr hc rfl rfl
    · simp [hreg]
  · rw [ite_eq_right hx,← bernoulliPolynomial_zero F p]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V)
    · simp only [hreg,ite_true]
      apply Finset.sum_eq_zero
      intro e _
      have hn : (t : Set E) ∉ closedPivotal (escapeEvent G Λ x) e := by
        intro he
        have hh := ((escape_closed_pivotal_iff G Λ (t : Set E) x e).mp he).1
        apply hx
        simpa only [hreg,Finset.mem_coe] using hh
      simp [hn]
    · simp [hreg]

 
theorem finite_escape_complement (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) :
    1-finiteEventPolynomial F (escapeEvent G Λ x) p =
      ∑ S ∈ Λ.powerset, if x ∈ S then regionProbability G Λ S F p else 0 := by
  have he : 1-finiteEventPolynomial F (escapeEvent G Λ x) p =
      bernoulliPolynomial F
        (fun t => if x ∈ unexposed G (Λ : Set V) (t : Set E) then (1:ℝ) else 0) p := by
    change 1-bernoulliPolynomial F (fun t => if (t : Set E) ∈ escapeEvent G Λ x then 1 else 0) p = _
    rw [show (1:ℝ) = bernoulliPolynomial F (fun _ => 1) p from (bernoulliPolynomial_const F 1 p).symm]
    rw [← bernoulliPolynomial_sub]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hx : x ∈ unexposed G (Λ : Set V) (t : Set E) <;> simp [escapeEvent,hx,bernoulliPolynomial_const]
  rw [he,bernoulliPolynomial_partition_region G Λ F]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V) <;> simp [hreg,hx]
  · rw [ite_eq_right hx,← bernoulliPolynomial_zero F p]
    apply bernoulliPolynomial_congr
    intro t _
    by_cases hreg : unexposed G (Λ : Set V) (t : Set E) = (S : Set V) <;> simp [hreg,hx]

 

theorem finite_escape_differential_lower (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hcost : ∀ S ⊆ Λ, x ∈ S → 1 ≤ p*boundaryExpectation G (S : Set V) x F p) :
    1-finiteEventPolynomial F (escapeEvent G Λ x) p ≤
      p*(1-p)*deriv (finiteEventPolynomial F (escapeEvent G Λ x)) p := by
  rw [mul_assoc,finite_escape_russo,closedEscapeCount_expectation,finite_escape_complement,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  by_cases hx : x ∈ S
  · simp only [ite_eq_left hx]
    have hq := regionProbability_nonneg G Λ S F p hp
    calc
      regionProbability G Λ S F p ≤
          regionProbability G Λ S F p * (p*boundaryExpectation G S x F p) :=
        le_mul_of_one_le_right hq (hcost S (Finset.mem_powerset.mp hS) hx)
      _ = p*(regionProbability G Λ S F p * boundaryExpectation G S x F p) := by ring
  · simp [hx]

 theorem bernoulliPolynomial_monotoneOn (F : Finset E) (f : Finset E → ℝ)
    (hf : ∀ a b, a ⊆ b → f a ≤ f b) :
    MonotoneOn (bernoulliPolynomial F f) (Set.Icc (0:ℝ) 1) := by
  have hd : Differentiable ℝ (bernoulliPolynomial F f) :=
    fun q => (hasDerivAt_bernoulliPolynomial F f q).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hd.continuous.continuousOn hd.differentiableOn
  intro q hq
  have hq' : q ∈ Set.Icc (0:ℝ) 1 := interior_subset hq
  rw [(hasDerivAt_bernoulliPolynomial F f q).deriv]
  apply Finset.sum_nonneg
  intro e _
  apply bernoulliPolynomial_nonneg _ _ _ hq'
  intro t _
  exact sub_nonneg.mpr (hf t (insert e t) (Finset.subset_insert e t))

 theorem crossingCount_mono (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) {ω η : Set E} (h : ω ⊆ η) :
    crossingCount G S x F ω ≤ crossingCount G S x F η := by
  apply Finset.sum_le_sum
  intro e _
  have hh : crossingReach G S x ω e → crossingReach G S x η e := by
    rintro ⟨a,b,he,ha,hb,hc⟩
    exact ⟨a,b,he,ha,hb,conn_mono G h hc⟩
  by_cases hω : crossingReach G S x ω e
  · simp [hω,hh hω]
  · simp only [ite_eq_right hω]
    split_ifs <;> norm_num

 theorem boundaryExpectation_nonneg (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ boundaryExpectation G S x F p := by
  apply bernoulliPolynomial_nonneg _ _ _ hp
  intro t _
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> norm_num

 theorem boundaryExpectation_monotoneOn (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) : MonotoneOn (boundaryExpectation G S x F) (Set.Icc (0:ℝ) 1) := by
  apply bernoulliPolynomial_monotoneOn
  intro a b hab
  exact crossingCount_mono G S x F (by exact_mod_cast hab)

 theorem boundaryCost_monotoneOn (G : BondGraph V E) (S : Set V) (x : V)
    (F : Finset E) : MonotoneOn (fun p => p*boundaryExpectation G S x F p)
      (Set.Icc (0:ℝ) 1) := by
  intro p hp q hq hpq
  exact mul_le_mul hpq (boundaryExpectation_monotoneOn G S x F hp hq hpq)
    (boundaryExpectation_nonneg G S x F p hp) hq.1

 theorem finiteEventPolynomial_mem_Icc (F : Finset E) (A : Set (Set E))
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    finiteEventPolynomial F A p ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · apply bernoulliPolynomial_nonneg _ _ _ hp
    intro t _
    split_ifs <;> norm_num
  · calc
      finiteEventPolynomial F A p ≤ bernoulliPolynomial F (fun _ => 1) p := by
        apply bernoulliPolynomial_mono _ _ _ _ hp
        intro t _
        split_ifs <;> norm_num
      _ = 1 := bernoulliPolynomial_const F 1 p

 

theorem differential_escape_growth {f : ℝ → ℝ} {r p : ℝ}
    (hr : 0 < r) (hrp : r ≤ p) (hp : p < 1)
    (hf : Differentiable ℝ f) (hbound : ∀ q ∈ Set.Icc r p, f q ∈ Set.Icc (0:ℝ) 1)
    (hineq : ∀ q ∈ Set.Icc r p, 1-f q ≤ q*(1-q)*deriv f q) :
    1-Real.exp (r-p) ≤ f p := by
  have hd (q : ℝ) : HasDerivAt (fun u => Real.exp u*(1-f u))
      (Real.exp q*(1-f q)+Real.exp q*(0-deriv f q)) q :=
    (Real.hasDerivAt_exp q).mul ((hasDerivAt_const q 1).sub (hf q).hasDerivAt)
  have hanti : AntitoneOn (fun q => Real.exp q*(1-f q)) (Set.Icc r p) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc r p)
      (Real.continuous_exp.mul (continuous_const.sub hf.continuous)).continuousOn
      (fun q _ => (hd q).hasDerivWithinAt)
    intro q hq
    have hqi : q ∈ Set.Icc r p := interior_subset hq
    have hq0 : 0 < q := hr.trans_le hqi.1
    have hq1 : q < 1 := hqi.2.trans_lt hp
    have hcoef : 0 < q*(1-q) := mul_pos hq0 (sub_pos.mpr hq1)
    have hder : 0 ≤ deriv f q := nonneg_of_mul_nonneg_right
      ((sub_nonneg.mpr (hbound q hqi).2).trans (hineq q hqi)) hcoef
    have hc : q*(1-q) ≤ 1 := by nlinarith [sq_nonneg q]
    have hsmall : 1-f q ≤ deriv f q := (hineq q hqi).trans
      (mul_le_of_le_one_left hder hc)
    have hn := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos q).le
      (show 1-f q-deriv f q ≤ 0 by linarith)
    nlinarith only [hn]
  have hle := hanti (show r ∈ Set.Icc r p from ⟨le_rfl,hrp⟩)
    (show p ∈ Set.Icc r p from ⟨hrp,le_rfl⟩) hrp
  have he : Real.exp p*(1-f p) ≤ Real.exp r := by
    calc
      Real.exp p*(1-f p) ≤ Real.exp r*(1-f r) := hle
      _ ≤ Real.exp r := mul_le_of_le_one_right (Real.exp_pos r).le
        (by linarith [(hbound r ⟨le_rfl,hrp⟩).1])
  have hfin : 1-f p ≤ Real.exp (r-p) := by
    rw [Real.exp_sub]
    apply (le_div_iff₀ (Real.exp_pos p)).mpr
    simpa only [mul_comm] using he
  linarith

 

theorem finite_escape_probability_lower (G : BondGraph V E) (Λ : Finset V) (x : V)
    (F : Finset E) (r p : ℝ) (hr : 0 < r) (hrp : r < p) (hp : p < 1)
    (hcost : ∀ S ⊆ Λ, x ∈ S → 1 ≤ r*boundaryExpectation G (S : Set V) x F r) :
    0 < 1-Real.exp (r-p) ∧
      1-Real.exp (r-p) ≤ finiteEventPolynomial F (escapeEvent G Λ x) p := by
  have hrI : r ∈ Set.Icc (0:ℝ) 1 := ⟨hr.le,(hrp.trans hp).le⟩
  have hqI (q : ℝ) (hq : q ∈ Set.Icc r p) : q ∈ Set.Icc (0:ℝ) 1 :=
    ⟨hr.le.trans hq.1,hq.2.trans hp.le⟩
  refine ⟨sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr hrp)),?_⟩
  apply differential_escape_growth hr hrp.le hp
  · intro q
    exact (hasDerivAt_bernoulliPolynomial F _ q).differentiableAt
  · intro q hq
    exact finiteEventPolynomial_mem_Icc F _ q (hqI q hq)
  · intro q hq
    apply finite_escape_differential_lower G Λ x F q (hqI q hq)
    intro S hS hx
    exact (hcost S hS hx).trans (boundaryCost_monotoneOn G S x F hrI (hqI q hq) hq.1)

end ExteriorExposure

section SharpnessBridge
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology

theorem bernoulliPolynomial_map {F : Type*} (f : E ↪ F) (s : Finset E)
    (h : Finset F → ℝ) (p : ℝ) :
    bernoulliPolynomial (s.map f) h p =
      bernoulliPolynomial s (fun t => h (t.map f)) p := by
  induction s using Finset.induction_on generalizing h with
  | empty => simp
  | @insert e s he ih =>
    rw [Finset.map_insert,bernoulliPolynomial_insert _ (f e) (by simpa using he),
      bernoulliPolynomial_insert s e he,ih,ih]
    simp only [Finset.map_insert]

theorem finiteEventPolynomial_restrict (F : Finset E) (A : Set (Set E)) (p : unitInterval) :
    finiteEventPolynomial F A (p : ℝ) = (law p).real {ω | ω ∩ (F : Set E) ∈ A} := by
  let f : (F : Set E) ↪ E := ⟨Subtype.val,Subtype.val_injective⟩
  have hm : (Finset.univ : Finset (F : Set E)).map f = F := by
    ext e
    simp [f]
  have he : finiteEventPolynomial F A (p : ℝ) =
      finiteEventPolynomial (Finset.univ : Finset (F : Set E))
        {η | f '' η ∈ A} (p : ℝ) := by
    unfold finiteEventPolynomial
    calc
      bernoulliPolynomial F (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ) =
        bernoulliPolynomial (Finset.univ.map f) (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ) :=
          congrArg (fun H => bernoulliPolynomial H (fun t => if (t : Set E) ∈ A then 1 else 0) (p : ℝ)) hm.symm
      _ = _ := by
        rw [bernoulliPolynomial_map]
        apply bernoulliPolynomial_congr
        intro t _
        simp only [Finset.coe_map]
        rfl
  rw [he,finiteEventPolynomial_eq,finiteProbability_univ,← law_map_restrict p (F : Set E),
    measureReal_def,Measure.map_apply (measurable_set_restrict _) .of_discrete]
  congr 2
  ext ω
  have hh : f '' (Subtype.val ⁻¹' ω : Set (F : Set E)) = ω ∩ (F : Set E) := by
    ext e
    simp [f,and_comm]
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,hh]

theorem bernoulliPolynomial_restrict (F H : Finset E) (hFH : F ⊆ H)
    (f : Finset E → ℝ) (p : ℝ) :
    bernoulliPolynomial H (fun t => f (t ∩ F)) p = bernoulliPolynomial F f p := by
  rw [← Finset.union_sdiff_of_subset hFH,bernoulliPolynomial_union _ _ Finset.disjoint_sdiff]
  trans bernoulliPolynomial F (fun a => f a) p
  · apply bernoulliPolynomial_congr
    intro a ha
    trans bernoulliPolynomial (H \ F) (fun _ => f a) p
    · apply bernoulliPolynomial_congr
      intro b hb
      have hdis : Disjoint b F := (Finset.disjoint_sdiff.symm).mono_left hb
      rw [Finset.union_inter_distrib_right,Finset.inter_eq_left.mpr ha,
        Finset.disjoint_iff_inter_eq_empty.mp hdis,Finset.union_empty]
    · exact bernoulliPolynomial_const _ _ _
  · rfl

 
noncomputable def incidentSupport (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) : Finset E := Λ.biUnion (fun x => (hloc x).toFinset)

@[simp] theorem mem_incidentSupport (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (e : E) : e ∈ incidentSupport G hloc Λ ↔ ∃ x ∈ Λ, x ∈ G e := by
  simp [incidentSupport]

theorem incidentSupport_mono (G : BondGraph V E) (hloc : LocallyFinite G)
    {S Λ : Finset V} (hS : S ⊆ Λ) : incidentSupport G hloc S ⊆ incidentSupport G hloc Λ := by
  intro e he
  obtain ⟨x,hx,hxe⟩ := (mem_incidentSupport G hloc S e).mp he
  exact (mem_incidentSupport G hloc Λ e).mpr ⟨x,hS hx,hxe⟩

 
theorem escapeEvent_restrict_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) (ω : Set E) :
    ω ∩ (incidentSupport G hloc Λ : Set E) ∈ escapeEvent G Λ x ↔
      ω ∈ escapeEvent G Λ x := by
  constructor
  · exact escapeEvent_isUpperSet G Λ x Set.inter_subset_left
  · intro hx
    by_contra hn
    have hx' : x ∈ unexposed G Λ (ω ∩ (incidentSupport G hloc Λ : Set E)) := by
      simpa only [escapeEvent,Set.mem_ofPred_eq,not_not] using hn
    apply hx
    intro y hxy
    have hc : Conn G (ω ∩ (incidentSupport G hloc Λ : Set E)) x y := by
      induction hxy with
      | refl => exact conn_refl _ _ _
      | @tail a b hxa hab ih =>
        obtain ⟨e,he,heab⟩ := hab
        have ha : a ∈ Λ := hx' a ih
        have hF : e ∈ incidentSupport G hloc Λ :=
          (mem_incidentSupport G hloc Λ e).mpr ⟨a,ha,by simp [heab]⟩
        exact ih.tail ⟨e,⟨he,hF⟩,heab⟩
    exact hx' y hc

theorem finite_escape_eq_law (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) (p : unitInterval) :
    finiteEventPolynomial (incidentSupport G hloc Λ) (escapeEvent G Λ x) (p : ℝ) =
      (law p).real (escapeEvent G Λ x) := by
  rw [finiteEventPolynomial_restrict]
  congr 1
  ext ω
  exact escapeEvent_restrict_incident G hloc Λ x ω

theorem internal_edge_mem_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) {e : E} (he : e ∈ internalEdges G (S : Set V)) :
    e ∈ incidentSupport G hloc S := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective (G e)
  have ha : a ∈ G e := by rw [← hab]; simp
  exact (mem_incidentSupport G hloc S e).mpr ⟨a,he a ha,ha⟩

theorem internalSupport_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) :
    internalSupport G S F = internalSupport G S (incidentSupport G hloc S) := by
  ext e
  simp only [internalSupport,Finset.mem_filter]
  exact ⟨fun h => ⟨internal_edge_mem_incident G hloc S h.2,h.2⟩,
    fun h => ⟨hF h.1,h.2⟩⟩

theorem crossingCount_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) (ω : Set E) :
    crossingCount G S x F ω = crossingCount G S x (incidentSupport G hloc S) ω := by
  symm
  apply Finset.sum_subset hF
  intro e _ he
  have hn : ¬ crossingReach G S x ω e := by
    rintro ⟨a,b,hab,ha,_,_⟩
    exact he ((mem_incidentSupport G hloc S e).mpr ⟨a,ha,by simp [hab]⟩)
  simp [hn]

theorem boundaryExpectation_eq_of_incident_subset (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (F : Finset E) (hF : incidentSupport G hloc S ⊆ F) (p : ℝ) :
    boundaryExpectation G S x F p =
      boundaryExpectation G S x (incidentSupport G hloc S) p := by
  unfold boundaryExpectation
  rw [internalSupport_eq_of_incident_subset G hloc S F hF]
  apply bernoulliPolynomial_congr
  intro t _
  exact crossingCount_eq_of_incident_subset G hloc S x F hF t

 
noncomputable def boundaryCost (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (p : ℝ) : ℝ :=
  p*boundaryExpectation G S x (incidentSupport G hloc S) p

theorem measurableSet_escapeEvent (G : BondGraph V E) (hloc : LocallyFinite G)
    (Λ : Finset V) (x : V) : MeasurableSet (escapeEvent G Λ x) := by
  let F := incidentSupport G hloc Λ
  have he : escapeEvent G Λ x =
      (fun ω => (Subtype.val ⁻¹' ω : Set (F : Set E))) ⁻¹'
        {η | Subtype.val '' η ∈ escapeEvent G Λ x} := by
    ext ω
    have hh : Subtype.val '' (Subtype.val ⁻¹' ω : Set (F : Set E)) = ω ∩ (F : Set E) := by
      ext e
      simp [and_comm]
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,hh]
    exact (escapeEvent_restrict_incident G hloc Λ x ω).symm
  rw [he]
  exact MeasurableSet.preimage .of_discrete (measurable_set_restrict _)

theorem escapeEvent_antitone_domain (G : BondGraph V E) {S Λ : Set V} (hS : S ⊆ Λ)
    (x : V) : escapeEvent G Λ x ⊆ escapeEvent G S x := by
  intro ω hω hn
  apply hω
  intro y hxy
  exact hS (hn y hxy)

noncomputable def vertexExhaustion [Encodable V] (n : ℕ) : Finset V :=
  (Finset.range n).preimage Encodable.encode Encodable.encode_injective.injOn

theorem vertexExhaustion_mono [Encodable V] :
    Monotone (vertexExhaustion : ℕ → Finset V) := by
  intro m n h x hx
  simp only [vertexExhaustion,Finset.mem_preimage,Finset.mem_range] at hx ⊢
  exact hx.trans_le h

theorem subset_vertexExhaustion [Encodable V] (S : Finset V) :
    ∃ n, S ⊆ vertexExhaustion n := by
  refine ⟨S.sup Encodable.encode+1,?_⟩
  intro x hx
  simp only [vertexExhaustion,Finset.mem_preimage,Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup hx)

theorem infinite_cluster_eq_iInter_escape [Encodable V] (G : BondGraph V E) (x : V) :
    {ω | (cluster G ω x).Infinite} = ⋂ n, escapeEvent G (vertexExhaustion (V := V) n : Set V) x := by
  ext ω
  simp only [Set.mem_ofPred_eq,Set.mem_iInter]
  constructor
  · intro hi n hn
    exact hi ((vertexExhaustion n).finite_toSet.subset (by
      intro y hy; exact hn y hy))
  · intro he hf
    obtain ⟨n,hn⟩ := subset_vertexExhaustion hf.toFinset
    apply he n
    intro y hy
    exact hn (hf.mem_toFinset.mpr hy)

 
theorem infinite_cluster_probability_ge_of_escape [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (p : unitInterval) (c : ℝ)
    (hc : ∀ Λ : Finset V, c ≤ (law p).real (escapeEvent G Λ x)) :
    c ≤ (law p).real {ω | (cluster G ω x).Infinite} := by
  let := Encodable.ofCountable V
  rw [infinite_cluster_eq_iInter_escape]
  have hm : Antitone (fun n => escapeEvent G (vertexExhaustion (V := V) n : Set V) x) := by
    intro m n h
    exact escapeEvent_antitone_domain G (by exact_mod_cast vertexExhaustion_mono h) x
  have ht := tendsto_measure_iInter_atTop (μ := law p)
    (fun n => (measurableSet_escapeEvent G hloc (vertexExhaustion n) x).nullMeasurableSet)
    hm ⟨0,measure_ne_top _ _⟩
  have hr := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  exact ge_of_tendsto hr (Eventually.of_forall (fun n => hc (vertexExhaustion n)))

 

theorem infinite_cluster_probability_pos_of_bad_cost [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (r p : unitInterval)
    (hr : 0 < r) (hrp : r < p) (hp : p < 1)
    (hcost : ∀ S : Finset V, x ∈ S → 1 ≤ boundaryCost G hloc S x (r : ℝ)) :
    0 < (law p).real {ω | (cluster G ω x).Infinite} := by
  have hc : 0 < 1-Real.exp ((r:ℝ)-(p:ℝ)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr hrp))
  apply hc.trans_le
  apply infinite_cluster_probability_ge_of_escape G hloc x p
  intro Λ
  rw [← finite_escape_eq_law G hloc Λ x p]
  apply (finite_escape_probability_lower G Λ x (incidentSupport G hloc Λ)
    (r:ℝ) (p:ℝ) hr hrp hp ?_).2
  intro S hS hx
  rw [boundaryExpectation_eq_of_incident_subset G hloc S x _ (incidentSupport_mono G hloc hS)]
  exact hcost S hx

theorem pc_le_of_infinite_cluster_probability_pos (G : BondGraph V E)
    (x : V) (p : unitInterval) (hp : 0 < (law p).real {ω | (cluster G ω x).Infinite}) :
    pc G ≤ p := by
  apply sInf_le
  have hh : 0 < law p {ω | (cluster G ω x).Infinite} := (ENNReal.toReal_pos_iff.mp hp).1
  apply hh.trans_le
  apply measure_mono
  intro ω hω
  exact ⟨cluster G ω x,hω,x,rfl⟩

 
theorem exists_subcritical_testSet [Countable V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (p : unitInterval) (hp : p < pc G) (x : V) :
    ∃ S : Finset V, x ∈ S ∧ boundaryCost G hloc S x (p:ℝ) < 1 := by
  by_cases hz : p = 0
  · exact ⟨{x},by simp,by simp [hz,boundaryCost]⟩
  · have hp0 : 0 < p := bot_lt_iff_ne_bot.mpr hz
    by_contra! hn
    obtain ⟨q,hpq,hqc⟩ := exists_between hp
    have hq1 : q < 1 := hqc.trans_le (show pc G ≤ 1 from (pc G).2.2)
    have hs := infinite_cluster_probability_pos_of_bad_cost G hloc x p q hp0 hpq hq1 hn
    exact (not_le_of_gt hqc) (pc_le_of_infinite_cluster_probability_pos G x q hs)

theorem internalEdges_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (e : E) :
    b e ∈ internalEdges G (a '' S) ↔ e ∈ internalEdges G S := by
  constructor
  · intro he x hx
    have hh := he (a x) (by rw [h e]; exact Sym2.mem_map.mpr ⟨x,hx,rfl⟩)
    simpa using hh
  · intro he y hy
    rw [h e,Sym2.mem_map] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact Set.mem_image_of_mem a (he x hx)

theorem crossingReach_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (ω : Set E) (e : E) :
    crossingReach G (a '' S) (a x) (b '' ω) (b e) ↔ crossingReach G S x ω e := by
  constructor
  · rintro ⟨c,d,he,hc,hd,hconn⟩
    have he' : G e = s(a.symm c,a.symm d) := by
      have hh := congrArg (Sym2.map a.symm) he
      rw [h e,Sym2.map_map,Equiv.symm_comp_self,Sym2.map_id,Sym2.map_mk] at hh
      exact hh
    refine ⟨a.symm c,a.symm d,he',?_,?_,?_⟩
    · simpa using hc
    · simpa using hd
    · have hh := (conn_aut_iff G h (b '' ω) x (a.symm c)).mpr (by simpa using hconn)
      simpa only [Set.preimage_image_eq _ b.injective] using hh
  · rintro ⟨c,d,he,hc,hd,hconn⟩
    refine ⟨a c,a d,?_,by simpa using hc,by simpa using hd,conn_aut G h hconn⟩
    rw [h e,he,Sym2.map_mk]

theorem internalSupport_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (F : Finset E) :
    internalSupport G (a '' S) (F.map b.toEmbedding) =
      (internalSupport G S F).map b.toEmbedding := by
  ext e
  obtain ⟨d,rfl⟩ := b.surjective e
  simp [internalSupport,internalEdges_aut_iff G h]

theorem crossingCount_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (F : Finset E) (ω : Set E) :
    crossingCount G (a '' S) (a x) (F.map b.toEmbedding) (b '' ω) =
      crossingCount G S x F ω := by
  simp only [crossingCount,Finset.sum_map,Equiv.toEmbedding_apply,crossingReach_aut_iff G h]

theorem boundaryExpectation_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (S : Set V) (x : V) (F : Finset E) (p : ℝ) :
    boundaryExpectation G (a '' S) (a x) (F.map b.toEmbedding) p =
      boundaryExpectation G S x F p := by
  unfold boundaryExpectation
  rw [internalSupport_aut G h,bernoulliPolynomial_map]
  apply bernoulliPolynomial_congr
  intro t _
  simp only [Finset.coe_map,Equiv.coe_toEmbedding]
  exact crossingCount_aut G h S x F t

theorem incidentSupport_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (S : Finset V) :
    incidentSupport G hloc (S.map a.toEmbedding) =
      (incidentSupport G hloc S).map b.toEmbedding := by
  ext e
  obtain ⟨d,rfl⟩ := b.surjective e
  simp only [mem_incidentSupport,Finset.mem_map,Equiv.toEmbedding_apply,
    b.injective.eq_iff,exists_eq_right]
  constructor
  · rintro ⟨x,⟨y,hy,rfl⟩,hx⟩
    rw [h d,Sym2.mem_map] at hx
    obtain ⟨z,hz,hzy⟩ := hx
    have hz' : z = y := a.injective hzy
    exact ⟨y,hy,hz' ▸ hz⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨a x,⟨x,hx,rfl⟩,by rw [h d]; exact Sym2.mem_map.mpr ⟨x,he,rfl⟩⟩

theorem boundaryCost_aut (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (S : Finset V) (x : V) (p : ℝ) :
    boundaryCost G hloc (S.map a.toEmbedding) (a x) p = boundaryCost G hloc S x p := by
  unfold boundaryCost
  rw [incidentSupport_aut G hloc h,Finset.coe_map]
  exact congrArg (p*·) (boundaryExpectation_aut G h S x (incidentSupport G hloc S) p)

 

theorem exists_uniform_subcritical_testSets [Countable V] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) :
    ∃ (L : ℕ) (a : ℝ), 0 ≤ a ∧ a < 1 ∧ ∀ x, ∃ S : Finset V,
      x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p:ℝ) ≤ a := by
  obtain ⟨O,hO⟩ := hqt
  choose S hmem hcost using exists_subcritical_testSet G hloc p hp
  have hOn : O.Nonempty := by
    obtain ⟨o,ho,_⟩ := hO (Classical.arbitrary V)
    exact ⟨o,ho⟩
  let L := O.sup (fun x => (S x).card)
  let a := max 0 (O.sup' hOn (fun x => boundaryCost G hloc (S x) x (p:ℝ)))
  refine ⟨L,a,le_max_left _ _,?_,?_⟩
  · apply max_lt zero_lt_one
    exact (Finset.sup'_lt_iff hOn).mpr (fun x _ => hcost x)
  · intro x
    obtain ⟨o,ho,α,β,hαβ,rfl⟩ := hO x
    refine ⟨(S o).map α.toEmbedding,?_,?_,?_⟩
    · simp only [Finset.mem_map,Equiv.toEmbedding_apply]
      exact ⟨o,hmem o,rfl⟩
    · simpa only [Finset.card_map] using Finset.le_sup (f := fun x => (S x).card) ho
    · rw [boundaryCost_aut G hloc hαβ]
      exact (Finset.le_sup' (f := fun x => boundaryCost G hloc (S x) x (p:ℝ)) ho).trans
        (le_max_right _ _)

end SharpnessBridge

section SharpnessSusceptibility
open Filter Topology
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def domainTwoPoint (G : BondGraph V E) (S : Set V) (p : unitInterval)
    (x y : V) : ℝ := (law p).real {ω | Conn G (ω ∩ internalEdges G S) x y}

theorem conn_internal_endpoint (G : BondGraph V E) (S : Set V) {ω : Set E} {x y : V}
    (hx : x ∈ S) (h : Conn G (ω ∩ internalEdges G S) x y) : y ∈ S := by
  induction h with
  | refl => exact hx
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact ((mem_internalEdges_of_ends G S e a b heq).mp he.2).2

def CutExists (G : BondGraph V E) (S : Set V) (e : E) : Prop :=
  ∃ a b, G e = s(a,b) ∧ a ∈ S ∧ b ∉ S

noncomputable def cutInside [Nonempty V] (G : BondGraph V E) (S : Set V) (e : E) : V :=
  if h : CutExists G S e then h.choose else Classical.arbitrary V

noncomputable def cutOutside [Nonempty V] (G : BondGraph V E) (S : Set V) (e : E) : V :=
  if h : CutExists G S e then h.choose_spec.choose else Classical.arbitrary V

theorem cut_spec [Nonempty V] (G : BondGraph V E) (S : Set V) {e : E}
    (he : CutExists G S e) :
    G e = s(cutInside G S e,cutOutside G S e) ∧
      cutInside G S e ∈ S ∧ cutOutside G S e ∉ S := by
  simpa only [cutInside,cutOutside,dite_eq_left he] using he.choose_spec.choose_spec

theorem cut_unique [Nonempty V] (G : BondGraph V E) (S : Set V) {e : E} {a b : V}
    (he : G e = s(a,b)) (ha : a ∈ S) (hb : b ∉ S) :
    a = cutInside G S e ∧ b = cutOutside G S e := by
  have hc := cut_spec G S (e := e) ⟨a,b,he,ha,hb⟩
  have hh := Sym2.eq_iff.mp (he.symm.trans hc.1)
  rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact ⟨h₁,h₂⟩
  · exact (hc.2.2 (h₁ ▸ ha)).elim

theorem crossingReach_cut [Nonempty V] (G : BondGraph V E) (S : Set V)
    (x : V) (ω : Set E) (e : E) :
    crossingReach G S x ω e ↔ CutExists G S e ∧ Conn G ω x (cutInside G S e) := by
  constructor
  · rintro ⟨a,b,he,ha,hb,h⟩
    exact ⟨⟨a,b,he,ha,hb⟩,(cut_unique G S he ha hb).1 ▸ h⟩
  · rintro ⟨he,h⟩
    have hs := cut_spec G S he
    exact ⟨_,_,hs.1,hs.2.1,hs.2.2,h⟩

theorem crossingReach_upper (G : BondGraph V E) (S : Set V) (x : V) (e : E) :
    IsUpperSet {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  rintro ω η h ⟨a,b,he,ha,hb,hconn⟩
  exact ⟨a,b,he,ha,hb,conn_mono G (Set.inter_subset_inter_left _ h) hconn⟩

theorem finiteWitness_crossingReach (G : BondGraph V E) (S : Set V) (x : V) (e : E) :
    FiniteWitness {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  rintro ω ⟨a,b,he,ha,hb,hconn⟩
  obtain ⟨t,ht,hc⟩ := finiteWitness_inter {η | Conn G η x a} (finiteWitness_conn G x a)
    (internalEdges G S) ω hconn
  exact ⟨t,ht,a,b,he,ha,hb,hc⟩

 
theorem conn_first_exit [Nonempty V] (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (U : Set E) {ω : Set E} {x y : V} (hx : x ∈ S)
    (hxy : Conn G (ω ∩ U) x y) :
    y ∈ S ∨ ∃ e ∈ incidentSupport G hloc S,
      ω ∈ DisjointOccurrence {η | crossingReach G S x (η ∩ internalEdges G S) e}
        (DisjointOccurrence {η | e ∈ η} {η | Conn G (η ∩ U) (cutOutside G S e) y}) := by
  obtain ⟨l,hl,hn,ho⟩ := conn_exists_bond_trail G hxy
  rcases hl.first_outside (internalEdges G S) with hall |
      ⟨a,b,e,l₁,l₂,heq,h₁,he,h₂,hfirst,hnot⟩
  · exact Or.inl (conn_internal_endpoint G S hx (hl.conn fun e he => ⟨(ho e he).1,hall e he⟩))
  · subst l
    have hnod := List.nodup_append.mp hn
    have hen : e ∉ l₂ := (List.nodup_cons.mp hnod.2.1).1
    have ha : a ∈ S := conn_internal_endpoint G S hx
      (h₁.conn (ω := ω ∩ internalEdges G S) fun d hd =>
        ⟨(ho d (List.mem_append_left _ hd)).1,hfirst d hd⟩)
    have hb : b ∉ S := fun hb => hnot ((mem_internalEdges_of_ends G S e a b he).mpr ⟨ha,hb⟩)
    have hbe := (cut_unique G S he ha hb).2
    refine Or.inr ⟨e,(mem_incidentSupport G hloc S e).mpr ⟨a,ha,by simp [he]⟩,
      l₁.toFinset,(e::l₂).toFinset,?_,?_,?_,?_,?_⟩
    · intro d hd
      exact (ho d (List.mem_append_left _ (List.mem_toFinset.mp hd))).1
    · intro d hd
      exact (ho d (List.mem_append_right _ (List.mem_toFinset.mp hd))).1
    · apply Finset.disjoint_left.mpr
      intro d hd hd'
      exact hnod.2.2 d (List.mem_toFinset.mp hd) d (List.mem_toFinset.mp hd') rfl
    · exact ⟨a,b,he,ha,hb,h₁.conn (fun d hd => ⟨by simpa using hd,hfirst d hd⟩)⟩
    · refine ⟨{e},l₂.toFinset,by simp,by simp,by simpa using hen,by simp,?_⟩
      rw [← hbe]
      exact h₂.conn fun d hd => ⟨by simpa using hd,
        (ho d (List.mem_append_right _ (List.mem_cons_of_mem e hd))).2⟩

 
theorem boundaryExpectation_eq_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (x : V) (p : unitInterval) :
    boundaryExpectation G S x (incidentSupport G hloc S) (p:ℝ) =
      ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} := by
  have hI : (internalSupport G S (incidentSupport G hloc S) : Set E) = internalEdges G S := by
    ext e
    simp only [Finset.mem_coe,internalSupport,Finset.mem_filter]
    exact ⟨And.right,fun he => ⟨internal_edge_mem_incident G hloc S he,he⟩⟩
  unfold boundaryExpectation crossingCount bernoulliPolynomial
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  change finiteEventPolynomial (internalSupport G S (incidentSupport G hloc S))
    {ω | crossingReach G S x ω e} (p:ℝ) = _
  rw [finiteEventPolynomial_restrict,hI]
  rfl

 
theorem domainTwoPoint_first_exit [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (S : Finset V) (Λ : Set V) (p : unitInterval)
    (x y : V) (hx : x ∈ S) :
    domainTwoPoint G Λ p x y ≤ (if y ∈ S then (1:ℝ) else 0) +
      ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
          (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y := by
  by_cases hy : y ∈ S
  · have hnon : 0 ≤ ∑ e ∈ incidentSupport G hloc S,
        (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
          (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y := by
      apply Finset.sum_nonneg
      intro e _
      exact mul_nonneg (mul_nonneg (measureReal_nonneg) p.2.1) measureReal_nonneg
    simpa only [ite_eq_left hy,domainTwoPoint] using (measureReal_le_one (μ := law p)
      (s := {ω | Conn G (ω ∩ internalEdges G Λ) x y})).trans (le_add_of_nonneg_right hnon)
  · simp only [ite_eq_right hy,zero_add]
    let A := fun e => {ω | crossingReach G S x (ω ∩ internalEdges G S) e}
    let B := fun e => {ω | Conn G (ω ∩ internalEdges G Λ) (cutOutside G S e) y}
    let F := incidentSupport G hloc S
    let C := fun e => DisjointOccurrence (A e) (DisjointOccurrence {ω | e ∈ ω} (B e))
    have hsub : {ω | Conn G (ω ∩ internalEdges G Λ) x y} ⊆ ⋃ e ∈ F, C e := by
      intro ω hω
      rcases conn_first_exit G hloc S (internalEdges G Λ) hx hω with h | ⟨e,he,h⟩
      · exact (hy h).elim
      · exact Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨he,h⟩⟩
    calc
      domainTwoPoint G Λ p x y ≤ (law p).real (⋃ e ∈ F, C e) := measureReal_mono (μ := law p) hsub (measure_ne_top _ _)
      _ ≤ ∑ e ∈ F, (law p).real (C e) := measureReal_biUnion_finset_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro e _
        have hB : IsUpperSet (B e) := fun _ _ h hc =>
          conn_mono G (Set.inter_subset_inter_left _ h) hc
        have hfB : FiniteWitness (B e) := finiteWitness_inter _
          (finiteWitness_conn G _ _) (internalEdges G Λ)
        have hb := bk p (A e) (DisjointOccurrence {ω | e ∈ ω} (B e))
          (crossingReach_upper G S x e) (disjointOccurrence_upper _ _)
          (finiteWitness_crossingReach G S x e) (finiteWitness_disjointOccurrence _ _)
        have hb' := bk p {ω | e ∈ ω} (B e) (fun _ _ h he => h he) hB (finiteWitness_edge e) hfB
        have heq : (law p).real {ω : Set E | e ∈ ω} = (p:ℝ) := by
          simpa using finite_open_probability p {e}
        rw [heq] at hb'
        calc
          (law p).real (C e) ≤ (law p).real (A e) * (law p).real
              (DisjointOccurrence {ω | e ∈ ω} (B e)) := hb
          _ ≤ (law p).real (A e) * ((p:ℝ) * (law p).real (B e)) :=
            mul_le_mul_of_nonneg_left hb' measureReal_nonneg
          _ = _ := (mul_assoc _ _ _).symm

theorem conn_internal_eq_or_mem (G : BondGraph V E) (S : Set V) {ω : Set E} {x y : V}
    (h : Conn G (ω ∩ internalEdges G S) x y) : x = y ∨ x ∈ S ∧ y ∈ S := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    have he' := (mem_internalEdges_of_ends G S e a b heq).mp he.2
    right
    exact ⟨ih.elim (fun h => h.symm ▸ he'.1) And.left,he'.2⟩

theorem domainTwoPoint_zero_of_outside (G : BondGraph V E) (S : Set V) (p : unitInterval)
    {x y : V} (hx : x ∉ S) (hy : y ∈ S) : domainTwoPoint G S p x y = 0 := by
  have he : {ω | Conn G (ω ∩ internalEdges G S) x y} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω h
    rcases conn_internal_eq_or_mem G S h with rfl | h
    · exact hx hy
    · exact hx h.1
  simp only [domainTwoPoint,he,measureReal_empty]

theorem domainRow_le_boundaryCost [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (S Λ : Finset V) (p : unitInterval) (x : V) (hx : x ∈ S)
    (H : ℝ) (hH : ∀ z, ∑ y ∈ Λ, domainTwoPoint G Λ p z y ≤ H) :
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤ S.card + boundaryCost G hloc S x (p:ℝ) * H := by
  have hind : (∑ y ∈ Λ, if y ∈ S then (1:ℝ) else 0) ≤ (S.card:ℝ) := by
    simp only [← Finset.sum_filter]
    simpa using (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card
      (show Λ.filter (fun y => y ∈ S) ⊆ S from fun y hy => (Finset.mem_filter.mp hy).2))
  calc
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤
        ∑ y ∈ Λ, ((if y ∈ S then (1:ℝ) else 0) +
          ∑ e ∈ incidentSupport G hloc S,
            (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
              (p:ℝ) * domainTwoPoint G Λ p (cutOutside G S e) y) :=
      Finset.sum_le_sum fun y _ => domainTwoPoint_first_exit G hloc S Λ p x y hx
    _ = (∑ y ∈ Λ, if y ∈ S then (1:ℝ) else 0) +
        ∑ e ∈ incidentSupport G hloc S,
          (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} *
            (p:ℝ) * ∑ y ∈ Λ, domainTwoPoint G Λ p (cutOutside G S e) y := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [← Finset.mul_sum]
    _ ≤ S.card + ∑ e ∈ incidentSupport G hloc S,
          (law p).real {ω | crossingReach G S x (ω ∩ internalEdges G S) e} * (p:ℝ) * H := by
      apply add_le_add hind
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (hH _) (mul_nonneg measureReal_nonneg p.2.1)
    _ = S.card + boundaryCost G hloc S x (p:ℝ) * H := by
      unfold boundaryCost
      rw [boundaryExpectation_eq_sum]
      simp only [← Finset.sum_mul]
      ring

theorem domainRow_uniform_bound [Countable E] [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (p : unitInterval) (L : ℕ) (a : ℝ) (ha : a < 1)
    (htest : ∀ x, ∃ S : Finset V, x ∈ S ∧ S.card ≤ L ∧ boundaryCost G hloc S x (p:ℝ) ≤ a)
    (Λ : Finset V) (x : V) :
    (∑ y ∈ Λ, domainTwoPoint G Λ p x y) ≤ (L:ℝ)/(1-a) := by
  by_cases hΛ : Λ.Nonempty
  · let row := fun z => ∑ y ∈ Λ, domainTwoPoint G Λ p z y
    obtain ⟨z,hz,hmax⟩ := Λ.exists_max_image row hΛ
    have hnon : 0 ≤ row z := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
    have hH : ∀ w, row w ≤ row z := by
      intro w
      by_cases hw : w ∈ Λ
      · exact hmax w hw
      · have he : row w = 0 := by
          apply Finset.sum_eq_zero
          intro y hy
          exact domainTwoPoint_zero_of_outside G Λ p hw hy
        rwa [he]
    obtain ⟨S,hS,hcard,hcost⟩ := htest z
    have h := domainRow_le_boundaryCost G hloc S Λ p z hS (row z) hH
    have hL : (S.card:ℝ) ≤ (L:ℝ) := Nat.cast_le.mpr hcard
    have hc := mul_le_mul_of_nonneg_right hcost hnon
    have hrow : row z ≤ (L:ℝ)/(1-a) := (le_div_iff₀ (sub_pos.mpr ha)).mpr (by nlinarith)
    exact (hH x).trans hrow
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hΛ,Finset.sum_empty]
    exact div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr ha).le

theorem internalEdges_mono (G : BondGraph V E) {S T : Set V} (h : S ⊆ T) :
    internalEdges G S ⊆ internalEdges G T := fun _ he x hx => h (he x hx)

theorem exists_internal_vertexExhaustion [Encodable V] (G : BondGraph V E) (e : E) :
    ∃ n, e ∈ internalEdges G (vertexExhaustion (V := V) n : Set V) := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective (G e)
  obtain ⟨n,hn⟩ := subset_vertexExhaustion ({a,b} : Finset V)
  refine ⟨n,?_⟩
  rw [mem_internalEdges_of_ends G _ e a b hab.symm]
  exact ⟨hn (by simp),hn (by simp)⟩

theorem conn_domain_exhaustion [Encodable V] (G : BondGraph V E) {ω : Set E} {x y : V}
    (h : Conn G ω x y) :
    ∃ n, Conn G (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y := by
  induction h with
  | refl => exact ⟨0,conn_refl _ _ _⟩
  | @tail a b hxa hab ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨e,he,heq⟩ := hab
    obtain ⟨m,hm⟩ := exists_internal_vertexExhaustion G e
    refine ⟨max n m,?_⟩
    have hnm := internalEdges_mono G (show (vertexExhaustion (V := V) n : Set V) ⊆
        (vertexExhaustion (V := V) (max n m) : Set V) from vertexExhaustion_mono (le_max_left n m))
    have hmm := internalEdges_mono G (show (vertexExhaustion (V := V) m : Set V) ⊆
        (vertexExhaustion (V := V) (max n m) : Set V) from vertexExhaustion_mono (le_max_right n m))
    exact (conn_mono G (Set.inter_subset_inter_right _ hnm) hn).tail ⟨e,⟨he,hmm hm⟩,heq⟩

theorem tendsto_domainTwoPoint [Encodable V] (G : BondGraph V E) (p : unitInterval) (x y : V) :
    Tendsto (fun n => domainTwoPoint G (vertexExhaustion (V := V) n : Set V) p x y)
      atTop (𝓝 (twoPoint G p x y)) := by
  have hm : Monotone (fun n => {ω | Conn G
      (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y}) := by
    intro m n h ω hc
    exact conn_mono G (Set.inter_subset_inter_right _ (internalEdges_mono G
      (show (vertexExhaustion (V := V) m : Set V) ⊆ (vertexExhaustion (V := V) n : Set V) from
        vertexExhaustion_mono h))) hc
  have he : (⋃ n, {ω | Conn G (ω ∩ internalEdges G (vertexExhaustion (V := V) n : Set V)) x y}) =
      {ω | Conn G ω x y} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    exact ⟨fun ⟨n,h⟩ => conn_mono G Set.inter_subset_left h,conn_domain_exhaustion G⟩
  have h := tendsto_measure_iUnion_atTop (μ := law p) hm
  rw [he] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

 
theorem subcritical_row_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x (F : Finset V), ∑ y ∈ F, twoPoint G p x y ≤ C := by
  let : Encodable V := Encodable.ofCountable V
  obtain ⟨L,a,_,ha,htest⟩ := exists_uniform_subcritical_testSets G hloc hqt p hp
  refine ⟨(L:ℝ)/(1-a),div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr ha).le,?_⟩
  intro x F
  apply le_of_tendsto (tendsto_finsetSum F (fun y _ => tendsto_domainTwoPoint G p x y))
  obtain ⟨N,hN⟩ := subset_vertexExhaustion F
  filter_upwards [eventually_ge_atTop N] with n hn
  have hFn : F ⊆ vertexExhaustion n := hN.trans (vertexExhaustion_mono hn)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hFn (fun _ _ _ => measureReal_nonneg)).trans
    (domainRow_uniform_bound G hloc p L a ha htest (vertexExhaustion n) x)

 
theorem operatorBounded_of_lt_pc [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) : OperatorBounded G p := by
  obtain ⟨C,hC,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  obtain ⟨A,_,hA⟩ := exists_operator_of_row_column_bound (twoPoint G p) C hC
    (twoPoint_nonneg G p) hrow (fun y F => by
      simpa only [twoPoint_symm G p] using hrow y F)
  exact ⟨A,hA⟩

end SharpnessSusceptibility

end Percolation

end OAI
