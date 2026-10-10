import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma measurePreserving_split_schedule (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ =>
      ((fun r (i : {i // p i}) => ω r i),(fun r (i : {i // ¬p i}) => ω r i)))
      (scheduleMeasure rate R)
      ((scheduleMeasure (fun i : {i // p i} => rate i) R).prod
        (scheduleMeasure (fun i : {i // ¬p i} => rate i) R)) := by
  have h1 := measurePreserving_pi (fun _ : Fin R => batchMeasure rate)
    (fun _ : Fin R => (batchMeasure (fun i : {i // p i} => rate i)).prod
      (batchMeasure (fun i : {i // ¬p i} => rate i)))
    (fun _ => measurePreserving_piEquivPiSubtypeProd (fun i => poissonMeasure (rate i)) p)
  exact (measurePreserving_arrowProdEquivProdArrow ({i // p i}→ℕ) ({i // ¬p i}→ℕ)
    (Fin R) (fun _ => batchMeasure (fun i : {i // p i} => rate i))
      (fun _ => batchMeasure (fun i : {i // ¬p i} => rate i))).comp h1

omit [DecidableEq ι] in
lemma integral_split_schedule (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    {R : ℕ} (F : (Fin R→{i // p i}→ℕ)→(Fin R→{i // ¬p i}→ℕ)→ℝ)
    (M : ℝ) (hM : ∀ u v,|F u v|≤M) :
    (∫ ω,F (fun r i => ω r i) (fun r i => ω r i) ∂scheduleMeasure rate R) =
      ∫ u,∫ v,F u v ∂scheduleMeasure (fun i : {i // ¬p i} => rate i) R
        ∂scheduleMeasure (fun i : {i // p i} => rate i) R := by
  let μ := scheduleMeasure (fun i : {i // p i} => rate i) R
  let ν := scheduleMeasure (fun i : {i // ¬p i} => rate i) R
  let G : (Fin R→{i // p i}→ℕ)×(Fin R→{i // ¬p i}→ℕ)→ℝ := fun z => F z.1 z.2
  have hG : Integrable G (μ.prod ν) := by
    apply Integrable.of_bound (measurable_of_countable G).aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hM z.1 z.2
  calc
    _ = ∫ z,G z ∂μ.prod ν :=
      (measurePreserving_split_schedule rate p R).hasLaw.integral_comp
        (measurable_of_countable G).aestronglyMeasurable
    _ = _ := integral_prod G hG

omit [DecidableEq ι] in
lemma integral_split_schedule_le (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    {R : ℕ} (F : (Fin R→{i // p i}→ℕ)→(Fin R→{i // ¬p i}→ℕ)→ℝ)
    (M B : ℝ) (hM : ∀ u v,|F u v|≤M)
    (hB : ∀ u,(∫ v,F u v ∂scheduleMeasure (fun i : {i // ¬p i} => rate i) R)≤B) :
    (∫ ω,F (fun r i => ω r i) (fun r i => ω r i) ∂scheduleMeasure rate R)≤B := by
  rw [integral_split_schedule rate p F M hM]
  have hG : Integrable (fun z : (Fin R→{i // p i}→ℕ)×(Fin R→{i // ¬p i}→ℕ) => F z.1 z.2)
      ((scheduleMeasure (fun i : {i // p i} => rate i) R).prod
        (scheduleMeasure (fun i : {i // ¬p i} => rate i) R)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hM z.1 z.2
  calc
    _ ≤ ∫ _u : Fin R→{i // p i}→ℕ,B ∂scheduleMeasure (fun i : {i // p i} => rate i) R :=
      integral_mono hG.integral_prod_left (integrable_const B) hB
    _ = B := by simp

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.ScoreAcceptance
open scoped BigOperators Classical
variable {V H : Type*} [DecidableEq V] [DecidableEq H]

noncomputable def empty (s : Finset V) (ω : V → ℕ) : Bool :=
  decide (∀ x∈s,ω x=0)

lemma empty_union (s t : Finset V) (ω : V → ℕ) :
    empty (s ∪ t) ω = (empty s ω && empty t ω) := by
  simp [empty,or_imp,forall_and]

noncomputable def factor (own outside : Bool) (b : ℝ) : ℝ :=
  (if own then 1 else 0)*((if outside then 1 else 0)-b)

lemma abs_factor_le_one (a c : Bool) (b : ℝ) (hb : b∈Set.Icc (0:ℝ) 1) :
    |factor a c b| ≤ 1 := by
  rcases hb with ⟨hb0,hb1⟩
  cases a <;> cases c <;> simp [factor,abs_of_nonneg,sub_nonneg.mpr hb1,hb0,hb1]

lemma abs_factor_of_nonempty (a c : Bool) (b : ℝ) (hb : 0≤b)
    (h : (a && c)=false) : |factor a c b| ≤ b := by
  cases a <;> cases c <;> simp_all [factor,abs_of_nonneg]

noncomputable def term {R : ℕ} (S O A : Finset V) (b : ℝ) (ω : Fin R → V → ℕ) : ℝ :=
  ∏ r,factor (empty (O ∩ A) (ω r)) (empty ((S \ O) ∩ A) (ω r)) b

noncomputable def allEmpty {R : ℕ} (S A : Finset V) (ω : Fin R → V → ℕ) : Prop :=
  ∀ r,empty (S ∩ A) (ω r)=true

lemma own_split (S O A : Finset V) (hO : O⊆S) :
    (O ∩ A) ∪ ((S \ O) ∩ A) = S ∩ A := by
  ext x
  simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
  constructor
  · rintro (h|h)
    · exact ⟨hO h.1,h.2⟩
    · exact ⟨h.1.1,h.2⟩
  · rintro ⟨hs,ha⟩
    by_cases hx : x∈O
    · exact Or.inl ⟨hx,ha⟩
    · exact Or.inr ⟨⟨hs,hx⟩,ha⟩

lemma term_empty {R : ℕ} (S O A : Finset V) (hO : O⊆S) (b : ℝ)
    (ω : Fin R → V → ℕ) (h : allEmpty S A ω) : term S O A b ω=(1-b)^R := by
  have hf (r : Fin R) : factor (empty (O ∩ A) (ω r))
      (empty ((S \ O) ∩ A) (ω r)) b=1-b := by
    have hr := h r
    rw [←own_split S O A hO,empty_union] at hr
    have hh : empty (O ∩ A) (ω r)=true ∧ empty ((S \ O) ∩ A) (ω r)=true := by
      simpa using hr
    obtain ⟨h1,h2⟩ := hh
    simp [factor,h1,h2]
  simp only [term,hf,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma term_nonempty {R : ℕ} (S O A : Finset V) (hO : O⊆S) (b : ℝ)
    (hb : b∈Set.Icc (0:ℝ) 1) (ω : Fin R → V → ℕ) (h : ¬allEmpty S A ω) :
    |term S O A b ω| ≤ b := by
  obtain ⟨r,hr⟩ : ∃ r,empty (S ∩ A) (ω r)≠true := not_forall.mp h
  have hr' : (empty (O ∩ A) (ω r) && empty ((S \ O) ∩ A) (ω r))=false := by
    rw [←empty_union,own_split S O A hO]
    exact Bool.eq_false_iff.mpr hr
  unfold term
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ s : Fin R,if s=r then b else 1 := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro s _
      by_cases hs : s=r
      · subst s
        simp only [ite_true]
        exact abs_factor_of_nonempty _ _ b hb.1 hr'
      · simp only [ite_eq_right hs]
        exact abs_factor_le_one _ _ b hb
    _ = b := by simp

noncomputable def emptyFamily {R : ℕ} (E : Finset H) (planes : H → Finset V)
    (S : Finset V) (ω : Fin R → V → ℕ) : Finset H :=
  E.filter fun h => allEmpty S (planes h) ω

omit [DecidableEq H] in

theorem exceptional_error {R : ℕ} (E : Finset H) (planes : H → Finset V)
    (S O : Finset V) (hO : O⊆S) (b : ℝ) (hb : b∈Set.Icc (0:ℝ) 1)
    (ω : Fin R → V → ℕ) :
    |(∑ h∈E,term S O (planes h) b ω)-
      (1-b)^R*(emptyFamily E planes S ω).card| ≤ b*E.card := by
  have he : (1-b)^R*(emptyFamily E planes S ω).card =
      ∑ h∈E,if allEmpty S (planes h) ω then (1-b)^R else 0 := by
    rw [←Finset.sum_filter]
    simp [emptyFamily,mul_comm]
  rw [he,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ h∈E,|term S O (planes h) b ω-
        (if allEmpty S (planes h) ω then (1-b)^R else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _h∈E,b := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hz : allEmpty S (planes h) ω
      · simp only [ite_eq_left hz,term_empty S O (planes h) hO b ω hz,sub_self,abs_zero]
        exact hb.1
      · simp only [ite_eq_right hz,sub_zero]
        exact term_nonempty S O (planes h) hO b hb ω hz
    _ = _ := by simp [mul_comm]

lemma training_separation (zq c zx err typ : ℝ) (hz : 0<zq)
    (hc : 0≤c ∧ c≤1) (hx : 0≤zx ∧ zx≤zq/10)
    (herr : |err|≤zq/100) (htyp : |typ|≤zq/10) :
    c*zx+err+typ < zq/2 := by
  have hm : c*zx≤zx := mul_le_of_le_one_left hx.1 hc.2
  have he := (le_abs_self err).trans herr
  have ht := (le_abs_self typ).trans htyp
  linarith

lemma ambient_separation (zq c zx err typ : ℝ) (hz : 0<zq)
    (hc : 9/10≤c) (hx : (4/5)*zq≤zx)
    (herr : |err|≤zq/100) (htyp : |typ|≤zq/10) :
    zq/2 < c*zx+err+typ := by
  have hx0 : 0≤zx := by linarith
  have hm : (9/10)*((4/5)*zq)≤c*zx :=
    mul_le_mul hc hx (by positivity) (by linarith)
  have he := (neg_abs_le err).trans' (neg_le_neg herr)
  have ht := (neg_abs_le typ).trans' (neg_le_neg htyp)
  linarith

noncomputable def accepted (U sampled : Finset V) (A : V → ℝ) (threshold : ℝ) :=
  U.filter fun x => x∈sampled ∨ A x<threshold

lemma capture (U S sampled bad : Finset V) (hS : S⊆U) (A : V → ℝ) (threshold : ℝ)
    (hgood : ∀ x∈S\bad,x∉sampled → A x<threshold) :
    S.card-bad.card ≤ ((accepted U sampled A threshold) ∩ S).card := by
  have hs : S\bad ⊆ accepted U sampled A threshold ∩ S := by
    intro x hx
    have hxS := (Finset.mem_sdiff.mp hx).1
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hS hxS,?_⟩,hxS⟩
    by_cases hxs : x∈sampled
    · exact Or.inl hxs
    · exact Or.inr (hgood x hx hxs)
  exact (Finset.le_card_sdiff _ _).trans (Finset.card_le_card hs)

lemma size_bound (U sampled bad : Finset V) (A : V → ℝ) (threshold : ℝ)
    (hgood : ∀ x∈U\bad,x∉sampled → threshold≤A x) :
    (accepted U sampled A threshold).card ≤ sampled.card+bad.card := by
  apply (Finset.card_le_card (show accepted U sampled A threshold ⊆ sampled∪bad from ?_)).trans
    (Finset.card_union_le _ _)
  intro x hx
  obtain ⟨hxU,hs|hA⟩ := Finset.mem_filter.mp hx
  · exact Finset.mem_union_left _ hs
  · by_contra hn
    have hs : x∉sampled := fun h => hn (Finset.mem_union_left _ h)
    have hb : x∉bad := fun h => hn (Finset.mem_union_right _ h)
    exact (not_lt_of_ge (hgood x (Finset.mem_sdiff.mpr ⟨hxU,hb⟩) hs)) hA

end SharpRamseyFive.ScoreAcceptance

end OAI
