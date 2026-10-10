import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.ExposureBudget

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical
namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
theorem divergence_map_le (p q : Law α) (hab : p.AbsolutelyContinuous q) (f : α → β) :
    divergence (p.map f) (q.map f) ≤ divergence p q := by
  unfold divergence
  calc
    _ ≤ ∑ b, ∑ a with f a = b, p.mass a*Real.log (p.mass a/q.mass a) := by
      apply sum_le_sum
      intro b hb
      exact log_sum (univ.filter (fun a => f a = b)) p.mass q.mass
        (fun a ha => p.nonneg a) (fun a ha => q.nonneg a) (fun a ha => hab a)
    _ = _ := sum_fiberwise univ f _

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

@[ext] theorem Law.ext {p q : Law α} (h : ∀ a, p.mass a = q.mass a) : p = q := by
  cases p with | mk p hp hpt =>
  cases q with | mk q hq hqt =>
  have hh : p = q := funext h
  subst q
  rfl

@[simp] theorem Law.map_id (p : Law α) : p.map id = p := by
  ext a
  simp [Law.map, sum_filter]

@[simp] theorem Law.map_map (p : Law α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (g ∘ f) := by
  ext c
  change (∑ b with g b = c, (p.map f).mass b) = ∑ a with g (f a) = c, p.mass a
  have h := p.sum_map f (fun b => if g b = c then 1 else 0)
  simpa [mul_ite, sum_filter] using h

@[simp] theorem Law.map_fst (p : Law (α × β)) : p.map Prod.fst = p.fst := by
  ext a
  simp only [Law.map, Law.fst, sum_filter, Fintype.sum_prod_type]
  rw [sum_comm]
  simp

@[simp] theorem Law.map_snd (p : Law (α × β)) : p.map Prod.snd = p.snd := by
  ext b
  simp [Law.map, Law.snd, sum_filter, Fintype.sum_prod_type]

theorem Law.prod_map (p : Law α) (q : Law β) (f : α → γ) (g : β → δ) :
    (p.prod q).map (fun z => (f z.1,g z.2)) = (p.map f).prod (q.map g) := by
  ext z
  rcases z with ⟨c,d⟩
  simp only [Law.map, Law.prod, Prod.mk.injEq, Fintype.sum_prod_type, sum_filter]
  rw [sum_mul_sum]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  split_ifs <;> simp_all

@[simp] theorem Law.fst_map_pair (p : Law (α × β)) (f : α → γ) (g : β → δ) :
    (p.map (fun z => (f z.1,g z.2))).fst = p.fst.map f := by
  rw [← Law.map_fst, Law.map_map, ← Law.map_fst, Law.map_map]
  rfl

@[simp] theorem Law.snd_map_pair (p : Law (α × β)) (f : α → γ) (g : β → δ) :
    (p.map (fun z => (f z.1,g z.2))).snd = p.snd.map g := by
  rw [← Law.map_snd, Law.map_map, ← Law.map_snd, Law.map_map]
  rfl

theorem mutualInfo_map_le (p : Law (α × β)) (f : α → γ) (g : β → δ) :
    mutualInfo (p.map (fun z => (f z.1,g z.2))) ≤ mutualInfo p := by
  rw [mutualInfo_eq_divergence, Law.fst_map_pair, Law.snd_map_pair,
    mutualInfo_eq_divergence, ← Law.prod_map]
  exact divergence_map_le _ _ p.absContinuous_prod _

theorem entropy_map_eq_of_leftInverse (p : Law α) (f : α → β) (g : β → α)
    (h : Function.LeftInverse g f) : entropy (p.map f) = entropy p := by
  apply le_antisymm (entropy_map_le p f)
  have hh := entropy_map_le (p.map f) g
  have he : g ∘ f = id := funext h
  simpa only [Law.map_map, he, Law.map_id] using hh

theorem entropy_pair_self (p : Law α) (f : α → β) :
    entropy (p.map (fun a => (a,f a))) = entropy p :=
  entropy_map_eq_of_leftInverse p _ Prod.fst (fun _a => rfl)

@[simp] theorem Law.fst_map_self (p : Law α) (f : α → β) :
    (p.map (fun a => (a,f a))).fst = p := by
  rw [← Law.map_fst, Law.map_map]
  exact p.map_id

@[simp] theorem Law.snd_map_self (p : Law α) (f : α → β) :
    (p.map (fun a => (a,f a))).snd = p.map f := by
  rw [← Law.map_snd, Law.map_map]
  rfl

noncomputable def Law.cond (p : Law α) (f : α → β) (b : β) : Law α :=
  (p.map (fun a => (a,f a))).condFst b

theorem Law.cond_mass (p : Law α) (f : α → β) (b : β)
    (hb : (p.map f).mass b ≠ 0) (a : α) :
    (p.cond f b).mass a = (if f a = b then p.mass a else 0)/(p.map f).mass b := by
  unfold Law.cond
  rw [Law.condFst_mass _ _ (by simpa using hb)]
  rw [Law.snd_map_self]
  congr 1
  simp [Law.map, sum_filter, ite_and]

theorem Law.cond_map_weight (p : Law α) (f : α → β) (g : α → γ) (b : β) (c : γ) :
    (p.map f).mass b * ((p.cond f b).map g).mass c =
    (p.map (fun a => (g a,f a))).mass (c,b) := by
  by_cases hb : (p.map f).mass b = 0
  · rw [hb,zero_mul]
    have hh := (p.map (fun a => (g a,f a))).le_snd c b
    have he : (p.map (fun a => (g a,f a))).snd = p.map f := by
      rw [← Law.map_snd, Law.map_map]; rfl
    rw [he,hb] at hh
    exact (le_antisymm hh ((p.map _).nonneg _)).symm
  change (p.map f).mass b*(∑ a with g a = c, (p.cond f b).mass a) = _
  simp_rw [p.cond_mass f b hb]
  rw [← sum_div, mul_div_cancel₀ _ hb]
  simp only [Law.map, Prod.mk.injEq, sum_filter]
  apply sum_congr rfl
  intro a ha
  split_ifs <;> simp_all

theorem entropy_cond_chain (p : Law α) (f : α → β) (g : α → γ) :
    entropy (p.map (fun a => (g a,f a))) = entropy (p.map f)+
      ∑ b, (p.map f).mass b*entropy ((p.cond f b).map g) := by
  let q := p.map (fun a => (g a,f a))
  have he : q.snd = p.map f := by rw [← Law.map_snd, Law.map_map]; rfl
  have hm (b : β) : (p.map f).mass b*entropy (q.condFst b) =
      (p.map f).mass b*entropy ((p.cond f b).map g) := by
    by_cases hb : (p.map f).mass b = 0
    · simp [hb]
    congr 1
    congr 1
    ext c
    apply (mul_left_cancel₀ hb)
    rw [← he, q.snd_mul_condFst, he, p.cond_map_weight]
  rw [entropy_chain, he]
  congr 1
  exact sum_congr rfl fun b hb => hm b

theorem entropy_cond_self (p : Law α) (f : α → β) :
    entropy p = entropy (p.map f)+∑ b, (p.map f).mass b*entropy (p.cond f b) := by
  simpa only [id_eq, Law.map_id, entropy_pair_self] using entropy_cond_chain p f id

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def Law.pi (p : ι → Law β) : Law (ι → β) where
  mass x := ∏ i, (p i).mass (x i)
  nonneg x := prod_nonneg fun i hi => (p i).nonneg (x i)
  total := by
    have h := prod_univ_sum (fun _ : ι => (univ : Finset β)) (fun i b => (p i).mass b)
    simpa only [Fintype.piFinset_univ, Law.total, prod_const_one] using h.symm

noncomputable def Law.marginal (p : Law (ι → β)) (i : ι) : Law β :=
  p.map (fun x => x i)

noncomputable def totalCorrelation (p : Law (ι → β)) : ℝ :=
  (∑ i, entropy (p.marginal i))-entropy p

theorem Law.absContinuous_pi (p : Law (ι → β)) :
    p.AbsolutelyContinuous (Law.pi p.marginal) := by
  intro x hz
  change (∏ i, (p.marginal i).mass (x i)) = 0 at hz
  obtain ⟨i,hi⟩ := (prod_eq_zero_iff).mp hz
  have hh : p.mass x ≤ (p.marginal i).mass (x i) := p.le_map (fun y => y i) x
  exact le_antisymm (hi.2 ▸ hh) (p.nonneg _)

theorem totalCorrelation_eq_divergence (p : Law (ι → β)) :
    totalCorrelation p = divergence p (Law.pi p.marginal) := by
  have pointwise (x : ι → β) :
      p.mass x*Real.log (p.mass x/(∏ i, (p.marginal i).mass (x i))) =
      p.mass x*Real.log (p.mass x)-∑ i, p.mass x*Real.log ((p.marginal i).mass (x i)) := by
    by_cases hz : p.mass x = 0
    · simp [hz]
    have hp : 0 < p.mass x := lt_of_le_of_ne (p.nonneg x) (Ne.symm hz)
    have hm (i : ι) : 0 < (p.marginal i).mass (x i) := hp.trans_le (p.le_map _ x)
    rw [Real.log_div hz (prod_ne_zero_iff.mpr fun i hi => (hm i).ne'),
      Real.log_prod (fun i hi => (hm i).ne'),mul_sub,mul_sum]
  have hs : ∑ x, ∑ i, p.mass x*Real.log ((p.marginal i).mass (x i)) =
      ∑ i, ∑ b, (p.marginal i).mass b*Real.log ((p.marginal i).mass b) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    exact (p.sum_map (fun x => x i) (fun b => Real.log ((p.marginal i).mass b))).symm
  unfold divergence
  change _ = ∑ x, p.mass x*Real.log (p.mass x/(∏ i, (p.marginal i).mass (x i)))
  simp_rw [pointwise]
  rw [sum_sub_distrib,hs]
  unfold totalCorrelation entropy
  rw [sum_neg_distrib]
  ring

theorem totalCorrelation_nonneg (p : Law (ι → β)) : 0 ≤ totalCorrelation p := by
  rw [totalCorrelation_eq_divergence]
  exact divergence_nonneg _ _ p.absContinuous_pi

theorem entropy_subadditive_pi (p : Law (ι → β)) :
    entropy p ≤ ∑ i, entropy (p.marginal i) := by
  have h := totalCorrelation_nonneg p
  unfold totalCorrelation at h
  linarith

theorem Law.map_mass_injective (p : Law α) (f : α → β) (hf : Function.Injective f) (a : α) :
    (p.map f).mass (f a) = p.mass a := by
  change (∑ x with f x = f a, p.mass x) = p.mass a
  simp only [hf.eq_iff]
  simp [sum_filter]

theorem entropy_map_eq_of_injective (p : Law α) (f : α → β) (hf : Function.Injective f) :
    entropy (p.map f) = entropy p := by
  rw [entropy_map]
  simp only [p.map_mass_injective f hf]
  rfl

noncomputable def Law.restrict (p : Law (ι → β)) (S : Finset ι) : Law (S → β) :=
  p.map (fun x i => x i)

theorem entropy_restrict_chain (p : Law (ι → β)) (E : Finset ι) :
    entropy p = entropy (p.restrict E)+
      ∑ e, (p.restrict E).mass e*entropy ((p.cond (fun x (i:E) => x i) e).restrict Eᶜ) := by
  have hx : Function.Injective (fun x : ι → β =>
      ((fun i : ↥(Eᶜ) => x i),(fun i : E => x i))) := by
    intro x y h
    funext i
    by_cases hi : i ∈ E
    · exact congr_fun (congrArg Prod.snd h) ⟨i,hi⟩
    · exact congr_fun (congrArg Prod.fst h) ⟨i,by simpa using hi⟩
  have h := entropy_cond_chain p (fun x (i:E) => x i) (fun x (i:↥(Eᶜ)) => x i)
  rwa [entropy_map_eq_of_injective p _ hx] at h

theorem entropy_marginal_cond (p : Law (ι → β)) (E : Finset ι) (i : ι) :
    (∑ e, (p.restrict E).mass e*entropy ((p.cond (fun x (j:E) => x j) e).marginal i)) =
      entropy (p.marginal i)-mutualInfo (p.map (fun x => (x i,fun j:E => x j))) := by
  have he : (p.map (fun x => (x i,fun j:E => x j))).fst = p.marginal i := by
    rw [← Law.map_fst, Law.map_map]; rfl
  have hs : (p.map (fun x => (x i,fun j:E => x j))).snd = p.restrict E := by
    rw [← Law.map_snd, Law.map_map]; rfl
  have h := entropy_cond_chain p (fun x (j:E) => x j) (fun x => x i)
  unfold mutualInfo
  rw [he,hs,h]
  change _ = entropy (p.marginal i)-(entropy (p.marginal i)+entropy (p.restrict E)-
    (entropy (p.restrict E)+∑ e, (p.restrict E).mass e*entropy ((p.cond (fun x (j:E) => x j) e).marginal i)))
  ring

@[simp] theorem Law.marginal_restrict (p : Law (ι → β)) (S : Finset ι) (i : S) :
    (p.restrict S).marginal i = p.marginal i := by
  unfold Law.marginal Law.restrict
  rw [Law.map_map]
  rfl

theorem totalCorrelation_drop (p : Law (ι → β)) (E : Finset ι) :
    totalCorrelation p-
      (∑ e, (p.restrict E).mass e*
        totalCorrelation ((p.cond (fun x (i:E) => x i) e).restrict Eᶜ)) =
    totalCorrelation (p.restrict E)+
      ∑ i ∈ Eᶜ, mutualInfo (p.map (fun x => (x i,fun j:E => x j))) := by
  have hc := entropy_restrict_chain p E
  have hm : ∑ e, (p.restrict E).mass e *
      (∑ i : ↥(Eᶜ), entropy (((p.cond (fun x (i:E) => x i) e).restrict Eᶜ).marginal i)) =
      ∑ i ∈ Eᶜ, (entropy (p.marginal i)-mutualInfo (p.map (fun x => (x i,fun j:E => x j)))) := by
    simp only [Law.marginal_restrict,mul_sum]
    rw [sum_comm]
    simp_rw [entropy_marginal_cond]
    exact (sum_subtype (Eᶜ) (fun _ => Iff.rfl) (fun i => entropy (p.marginal i)-mutualInfo (p.map (fun x => (x i,fun j:E => x j))))).symm
  unfold totalCorrelation
  simp only [mul_sub,sum_sub_distrib]
  rw [hm]
  have he : (∑ i : E, entropy ((p.restrict E).marginal i)) =
      ∑ i ∈ E, entropy (p.marginal i) := by
    simp only [Law.marginal_restrict]
    exact (sum_subtype E (fun _ => Iff.rfl) (fun i => entropy (p.marginal i))).symm
  rw [he,sum_sub_distrib]
  have hsum := sum_add_sum_compl E (fun i => entropy (p.marginal i))
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {B X : Type*} [Fintype B] [Fintype X] [DecidableEq B]

theorem fresh_draw_identity (b : B) (g : X→(B→X)→ℝ)
    (hdep : ∀ j f x, g j (Function.update f b x)=g j f) :
    (Fintype.card X:ℝ)*(∑ f : B→X, g (f b) f)=
      ∑ f : B→X, ∑ j, g j f := by
  classical
  let e := Equiv.funSplitAt b X
  have hi (x : X) (r : {z : B // z≠b}→X) : e.symm (x,r) b=x := by
    simp [e,Equiv.funSplitAt,Equiv.piSplitAt]
  have hu (x j : X) (r : {z : B // z≠b}→X) :
      Function.update (e.symm (x,r)) b j=e.symm (j,r) := by
    funext z
    by_cases hz : z=b
    · subst z
      simp [hi]
    · simp [e,Equiv.funSplitAt,Equiv.piSplitAt,hz]
  have hg (x j : X) (r : {z : B // z≠b}→X) : g j (e.symm (x,r))=g j (e.symm (j,r)) := by
    rw [←hu x j r]
    exact (hdep j (e.symm (x,r)) j).symm
  rw [←e.symm.sum_comp (fun f => g (f b) f),←e.symm.sum_comp (fun f => ∑ j, g j f)]
  simp only [Fintype.sum_prod_type,hi]
  trans (∑ _x : X, ∑ j : X, ∑ r : {z : B // z≠b}→X, g j (e.symm (j,r)))
  · simp only [sum_const,nsmul_eq_mul,card_univ]
  · apply sum_congr rfl
    intro x _
    rw [sum_comm]
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro j _
    exact (hg x j r).symm

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

noncomputable def pairInformation (p : Law (ι → β)) (i j : ι) : NNReal :=
  ⟨mutualInfo (p.map (fun x => (x i,x j))),mutualInfo_nonneg _⟩

noncomputable def exposedInformation (p : Law (ι → β)) (i : ι) (E : Finset ι) : NNReal :=
  ⟨mutualInfo (p.map (fun x => (x i,fun j : E => x j))),mutualInfo_nonneg _⟩

noncomputable def maximumInformation (p : Law (ι → β)) (i : ι) (J : Finset ι) : NNReal :=
  J.sup (pairInformation p i)

lemma pairInformation_le_exposed (p : Law (ι → β)) (i : ι) (E : Finset ι)
    {j : ι} (hj : j∈E) : pairInformation p i j ≤ exposedInformation p i E := by
  change mutualInfo (p.map (fun x => (x i,x j))) ≤
    mutualInfo (p.map (fun x => (x i,fun z : E => x z)))
  have H := mutualInfo_map_le (p.map (fun x => (x i,fun z : E => x z)))
    id (fun z : E → β => z ⟨j,hj⟩)
  simpa only [Law.map_map,Function.comp_def,id_eq] using H

lemma maximumInformation_le_exposed (p : Law (ι → β)) (i : ι) (E J : Finset ι)
    (hJ : J⊆E) : maximumInformation p i J ≤ exposedInformation p i E := by
  apply Finset.sup_le
  intro j hj
  exact pairInformation_le_exposed p i E (hJ hj)

theorem maximum_exposure_drop (p : Law (ι → β)) (E : Finset ι)
    (J : ι → Finset ι) (hJ : ∀ i, J i⊆E) :
    (∑ i, (maximumInformation p i (J i):ℝ)) ≤
      totalCorrelation p-
        (∑ e, (p.restrict E).mass e*
          totalCorrelation ((p.cond (fun x (j:E) => x j) e).restrict Eᶜ))+
      ∑ i∈E, (maximumInformation p i (J i):ℝ) := by
  have H := totalCorrelation_drop p E
  have hn := totalCorrelation_nonneg (p.restrict E)
  have hle : (∑ i∈Eᶜ, (maximumInformation p i (J i):ℝ)) ≤
      ∑ i∈Eᶜ, mutualInfo (p.map (fun x => (x i,fun j:E => x j))) := by
    apply sum_le_sum
    intro i _
    exact maximumInformation_le_exposed p i E (J i) (hJ i)
  have hs := sum_add_sum_compl E (fun i => (maximumInformation p i (J i):ℝ))
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {ι β B X : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
  [Fintype B] [Fintype X] [DecidableEq B]

noncomputable def freshRepresentatives (e : B×X ↪ ι) (f : B→X) : Finset ι :=
  univ.image (fun b => e (b,f b))

noncomputable def otherRepresentatives (e : B×X ↪ ι) (own : ι→Option B)
    (f : B→X) (i : ι) : Finset ι :=
  (univ.filter (fun b => some b≠own i)).image (fun b => e (b,f b))

omit [Fintype ι] [Fintype X] in
lemma otherRepresentatives_sub (e : B×X ↪ ι) (own : ι→Option B)
    (f : B→X) (i : ι) : otherRepresentatives e own f i⊆freshRepresentatives e f := by
  exact image_subset_image (filter_subset _ _)

omit [Fintype ι] [Fintype X] in
lemma otherRepresentatives_update (e : B×X ↪ ι) (own : ι→Option B)
    (hown : ∀ b x, own (e (b,x))=some b) (b : B) (x y : X) (f : B→X) :
    otherRepresentatives e own (Function.update f b y) (e (b,x))=
      otherRepresentatives e own f (e (b,x)) := by
  unfold otherRepresentatives
  rw [hown]
  apply image_congr
  intro c hc
  have hn : c≠b := by simpa using (mem_filter.mp hc).2
  simp only [Function.update_of_ne hn]

theorem selected_maximum_absorption (p : Law (ι→β)) (e : B×X ↪ ι)
    (own : ι→Option B) (hown : ∀ b x, own (e (b,x))=some b) :
    (Fintype.card X:ℝ)*
      (∑ f : B→X, ∑ i∈freshRepresentatives e f,
        (maximumInformation p i (otherRepresentatives e own f i):ℝ)) ≤
      ∑ f : B→X, ∑ i, (maximumInformation p i (otherRepresentatives e own f i):ℝ) := by
  let M (f : B→X) (i : ι) : ℝ := maximumInformation p i (otherRepresentatives e own f i)
  have hsel (f : B→X) : (∑ i∈freshRepresentatives e f,M f i)=∑ b,M f (e (b,f b)) := by
    apply sum_image
    intro b _ c _ he
    exact (Prod.mk.inj (e.injective he)).1
  change (Fintype.card X:ℝ)*(∑ f, ∑ i∈freshRepresentatives e f,M f i)≤∑ f,∑ i,M f i
  simp_rw [hsel]
  rw [sum_comm,mul_sum]
  have hb (b : B) : (Fintype.card X:ℝ)*(∑ f : B→X,M f (e (b,f b)))=
      ∑ f : B→X,∑ x : X, M f (e (b,x)) := by
    apply fresh_draw_identity b (fun x f => M f (e (b,x)))
    intro x f y
    dsimp [M]
    rw [otherRepresentatives_update e own hown]
  simp_rw [hb]
  rw [sum_comm]
  apply sum_le_sum
  intro f _
  have h : (∑ z∈univ.map e, M f z) ≤ ∑ i, M f i := by
    apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro i _ _
    exact (maximumInformation p i _).property
  simpa only [sum_map,Fintype.sum_prod_type] using h

theorem fresh_round_drop (p : Law (ι→β)) (e : B×X ↪ ι)
    (own : ι→Option B) (hown : ∀ b x, own (e (b,x))=some b)
    (hX : 0<Fintype.card X) :
    (1-1/(Fintype.card X:ℝ))*
      (∑ f : B→X, ∑ i, (maximumInformation p i (otherRepresentatives e own f i):ℝ)) ≤
      ∑ f : B→X, (totalCorrelation p-
        ∑ z, (p.restrict (freshRepresentatives e f)).mass z*
          totalCorrelation ((p.cond (fun x (j:freshRepresentatives e f) => x j) z).restrict
            (freshRepresentatives e f)ᶜ)) := by
  have H := sum_le_sum (fun f (_ : f∈(univ : Finset (B→X))) =>
    maximum_exposure_drop p (freshRepresentatives e f) (otherRepresentatives e own f)
      (otherRepresentatives_sub e own f))
  rw [sum_add_distrib] at H
  have hs := selected_maximum_absorption p e own hown
  have hn : 0<(Fintype.card X:ℝ) := by exact_mod_cast hX
  let A : ℝ := ∑ f : B→X, ∑ i, (maximumInformation p i (otherRepresentatives e own f i):ℝ)
  let S : ℝ := ∑ f : B→X, ∑ i∈freshRepresentatives e f,
    (maximumInformation p i (otherRepresentatives e own f i):ℝ)
  have hh : S≤A/(Fintype.card X:ℝ) := by
    apply (le_div_iff₀ hn).mpr
    change S*(Fintype.card X:ℝ)≤A
    change (Fintype.card X:ℝ)*S≤A at hs
    nlinarith
  change A≤_+S at H
  change (1-1/(Fintype.card X:ℝ))*A≤_
  have he : (1-1/(Fintype.card X:ℝ))*A=A-A/(Fintype.card X:ℝ) := by ring
  rw [he]
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
open Finset
open scoped Classical
noncomputable section
variable {B β ι : Type*} [Fintype B] [Fintype β] [Fintype ι] [DecidableEq ι] [DecidableEq B]

end
end SharpLogRamsey.Selection
end

end OAI
