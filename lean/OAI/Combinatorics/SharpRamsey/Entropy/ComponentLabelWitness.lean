import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.ExternalMass

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable (label : D → Option C) (R : ℕ)
variable (color : V → C) (s : V → Finset D) (b : ℝ) (own : V → Fin R → Bool)
omit [Fintype D] [DecidableEq V] in
lemma componentLabel_witness (weight : D → ℝ≥0) (t : ℝ) (d : D)
    (c : (strongGraph weight s t).ConnectedComponent)
    (hc : componentLabel weight s t d = some c) :
    ∃ v, d ∈ s v ∧ (strongGraph weight s t).connectedComponentMk v = c := by
  unfold componentLabel at hc
  split_ifs at hc with h h'
  exact ⟨h.choose, h.choose_spec, Option.some.inj hc⟩
omit [DecidableEq V] in

lemma simple_inside_univ (weight : D → ℝ≥0) (t : ℝ) (v : V)
    (hsingle : ∀ u, (strongGraph weight s t).connectedComponentMk u =
      (strongGraph weight s t).connectedComponentMk v → u = v) :
    inside (componentLabel weight s t) ((strongGraph weight s t).connectedComponentMk v)
      (s v) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro d
  obtain ⟨u, hu, hc⟩ := componentLabel_witness s weight t d.val _ d.property
  have he := hsingle u hc
  simpa [inside, he] using hu

omit [DecidableEq D] [Fintype C] in
lemma blockTrunc_eq_indicator (J : ℕ) (c : C) (x : Block label R (some c) → ℕ) :
    blockTrunc label R J (some c) x =
      (overloaded Finset.univ J)ᶜ.indicator (fun _ => (1 : ℝ)) (unblock label R c x) := by
  by_cases he : unblock label R c x ∈ overloaded Finset.univ J
  · simp only [Set.indicator_of_notMem (show unblock label R c x ∉
      (overloaded Finset.univ J)ᶜ by simpa using he)]
    obtain ⟨d, _, hd⟩ := he
    apply Finset.prod_eq_zero (Finset.mem_univ d)
    change lineTrunc R J (fun r => x ⟨(r,d), d.property⟩) = 0
    have hn : ¬ (Finset.univ.filter (fun r => x ⟨(r,d), d.property⟩ ≠ 0)).card < J := by
      exact not_lt.mpr hd
    simp only [lineTrunc, ite_eq_right hn]
  · rw [Set.indicator_of_mem (show unblock label R c x ∈
      (overloaded Finset.univ J)ᶜ by simpa using he)]
    apply Finset.prod_eq_one
    intro d _
    change lineTrunc R J (fun r => x ⟨(r,d), d.property⟩) = 1
    have hd : (Finset.univ.filter (fun r => x ⟨(r,d), d.property⟩ ≠ 0)).card < J := by
      by_contra hn
      exact he ⟨d, Finset.mem_univ _, not_lt.mp hn⟩
    simp only [lineTrunc, ite_eq_left hd]

omit [DecidableEq V] in
omit [Fintype C] in
lemma componentFactor_eq_single (J : ℕ) (c : C) (v : {v : V // color v = c})
    (hsingle : ∀ u, color u = c → u = v.val)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    (hin : inside label c (s v) = Finset.univ)
    (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ) :
    componentFactor label R color s b own J c z x =
      (overloaded (inside label c (s v)) J)ᶜ.indicator
        (maskedTerm (inside label c (s v)) b (own v) (touched label R c (s v) z))
        (unblock label R c x) := by
  have hp : (∏ u : {v : V // color v = c}, scoreTerm (s u) b (own u) (fill label R c z x)) =
      scoreTerm (s v) b (own v) (fill label R c z x) := by
    apply Finset.prod_eq_single v
    · intro u _ huv
      exfalso
      exact huv (Subtype.ext (hsingle u u.property))
    · simp
  rw [componentFactor, hp, scoreTerm_eq_masked label R c (s v) b (own v) hcompat,
    blockTrunc_eq_indicator label R J c, hin]
  by_cases he : unblock label R c x ∈ (overloaded Finset.univ J)ᶜ <;> simp [he]
omit [DecidableEq V] in
omit [Fintype C] in

lemma simple_component_integral (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c})
    (hsingle : ∀ u, color u = c → u = v.val)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    (hin : inside label c (s v) = Finset.univ) (z : Block label R none → ℕ) :
    (∫ x, componentFactor label R color s b own J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)) =
      ∫ w, (overloaded (inside label c (s v)) J)ᶜ.indicator
        (maskedTerm (inside label c (s v)) b (own v) (touched label R c (s v) z)) w
        ∂scheduleMeasure (fun d : IntDir label c => rate d) R := by
  simp_rw [componentFactor_eq_single label R color s b own J c v hsingle hcompat hin]
  exact (measurePreserving_unblock label R rate c).integral_comp
    (unblockEquiv label R c).measurableEmbedding _
omit [DecidableEq V] in
omit [Fintype C] in

lemma simple_component_attenuation (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c})
    (hsingle : ∀ u, color u = c → u = v.val)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    (hin : inside label c (s v) = Finset.univ) (z : Block label R none → ℕ)
    {L base delta alpha : ℝ} (hL : 10000 ≤ L)
    (hmass : mass (fun d : IntDir label c => rate d) (inside label c (s v)) =
      L * (base + delta - alpha))
    (hint : (37 / 50 : ℝ) ≤ base + delta - alpha) (hbase : (37 / 50 : ℝ) ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {N K : ℕ}
    (hN : N ≤ (untouchedBatches (touched label R c (s v) z)).card) (hK : K ≤ N) :
    |∫ x, componentFactor label R color s (Real.exp (-L * base)) own J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)| ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) *
        (|delta| ^ N + alpha ^ K +
          ∑ d ∈ inside label c (s v), ((R : ℝ) * (rate d : ℝ)) ^ J) := by
  rw [simple_component_integral label R color s _ own rate J c v hsingle hcompat hin z]
  exact simple_singleton_truncated _ _ J (own v) (touched label R c (s v) z)
    hL hmass hint hbase ha hd hN hK
omit [Fintype C] in

lemma nonsimple_component_attenuation (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c}) (z : Block label R none → ℕ)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    {L lam base : ℝ} (hL : 10000 ≤ L)
    (hmass : mass (fun d : IntDir label c => rate d) (inside label c (s v)) = L * lam)
    (hlam : (37 / 50 : ℝ) ≤ lam) (hbase : (37 / 50 : ℝ) ≤ base) :
    (∫ x, |componentFactor label R color s (Real.exp (-L * base)) own J c z x|
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)) ≤
        Real.exp (-(7 / 10 : ℝ) * (L * R)) := by
  apply (component_integral_abs_le label R color s own rate J c v z hcompat
    (show 0 ≤ L by linarith) (by norm_num : (0 : ℝ) ≤ 37 / 50) hmass hlam hbase).trans
  have he : (2 : ℝ) ≤ Real.exp ((1 / 25 : ℝ) * L) := by
    have := Real.add_one_le_exp ((1 / 25 : ℝ) * L)
    linarith
  have hmul := mul_le_mul_of_nonneg_right he (Real.exp_pos (-L * (37 / 50 : ℝ))).le
  rw [← Real.exp_add] at hmul
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-L * (37 / 50 : ℝ))) hmul R
  rw [← Real.exp_nat_mul] at hpow
  convert hpow using 1 ; congr 1 ; ring

end SharpRamseyFive.TupleComponents

namespace SharpRamseyFive.TupleMultiplicity
open scoped BigOperators
open Classical
variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

abbrev RepresentativeMap (V : Type*) := {r : V → V // ∀ v, r (r v) = r v}
abbrev Representatives (r : RepresentativeMap V) := {v : V // r.val v = v}

noncomputable def chosen (f : V → H) (v : V) : V :=
  Classical.choose (show ∃ w, f w = f v from ⟨v, rfl⟩)

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
lemma chosen_spec (f : V → H) (v : V) : f (chosen f v) = f v :=
  Classical.choose_spec (show ∃ w, f w = f v from ⟨v, rfl⟩)

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
lemma chosen_eq (f : V → H) {v w : V} (h : f v = f w) :
    chosen f v = chosen f w := by
  unfold chosen
  congr 1
  funext x
  rw [h]
omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in

lemma chosen_idempotent (f : V → H) : ∀ v, chosen f (chosen f v) = chosen f v := by
  intro v
  exact chosen_eq f (chosen_spec f v)

noncomputable def representatives (f : V → H) : RepresentativeMap V :=
  ⟨chosen f, chosen_idempotent f⟩

noncomputable def assignment (f : V → H) : Representatives (representatives f) ↪ H where
  toFun v := f v
  inj' := by
    intro v w h
    apply Subtype.ext
    have := chosen_eq f h
    change chosen f v.val = chosen f w.val at this
    simpa only [show chosen f v.val = v.val from v.property,
      show chosen f w.val = w.val from w.property] using this

noncomputable def decode (r : RepresentativeMap V) (h : Representatives r ↪ H) : V → H :=
  fun v => h ⟨r.val v, r.property v⟩
omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in

lemma decode_assignment (f : V → H) :
    decode (representatives f) (assignment f) = f := by
  funext v
  exact chosen_spec f v

noncomputable def encode (f : V → H) :
    (r : RepresentativeMap V) × (Representatives r ↪ H) :=
  ⟨representatives f, assignment f⟩
omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in

lemma encode_injective : Function.Injective (encode (V := V) (H := H)) := by
  intro f g h
  have := congrArg (fun z : (r : RepresentativeMap V) × (Representatives r ↪ H) =>
    decode z.1 z.2) h
  simpa only [encode, decode_assignment] using this

lemma representativeMap_card_le :
    Fintype.card (RepresentativeMap V) ≤ Fintype.card V ^ Fintype.card V := by
  calc
    _ ≤ Fintype.card (V → V) := Fintype.card_subtype_le _
    _ = _ := by simp

lemma representatives_card_le (r : RepresentativeMap V) :
    Fintype.card (Representatives r) ≤ Fintype.card V := Fintype.card_subtype_le _

theorem sum_tuples_le_representative_assignments (F : (V → H) → ℝ)
    (hF : ∀ f, 0 ≤ F f) :
    (∑ f : V → H, F f) ≤
      ∑ r : RepresentativeMap V, ∑ h : Representatives r ↪ H, F (decode r h) := by
  rw [← Fintype.sum_sigma (fun z : (r : RepresentativeMap V) × (Representatives r ↪ H) =>
    F (decode z.1 z.2))]
  let e := encode (V := V) (H := H)
  let G := fun z : (r : RepresentativeMap V) × (Representatives r ↪ H) => F (decode z.1 z.2)
  have he : (∑ f : V → H, F f) = ∑ z ∈ Finset.univ.image e, G z := by
    rw [Finset.sum_image (fun _ _ _ _ h => encode_injective h)]
    apply Finset.sum_congr rfl
    intro f _
    simp only [G, encode, decode_assignment]
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => hF _)

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in

lemma range_decode (r : RepresentativeMap V) (h : Representatives r ↪ H) :
    Set.range (decode r h) = Set.range h := by
  ext a
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨⟨r.val v,r.property v⟩,rfl⟩
  · rintro ⟨v,rfl⟩
    refine ⟨v, ?_⟩
    apply congrArg h
    exact Subtype.ext v.property

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
lemma fiber_decode (r : RepresentativeMap V) (h : Representatives r ↪ H)
    (v : V) (w : Representatives r) : decode r h v = h w ↔ r.val v = w.val := by
  constructor
  · intro he
    exact congrArg Subtype.val (h.injective he)
  · intro he
    exact congrArg h (Subtype.ext he)
end SharpRamseyFive.TupleMultiplicity

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
omit [DecidableEq V] in

lemma mass_inside_eq (weight rate : D → ℝ≥0) (s : V → Finset D) (t : ℝ) (v : V) :
    mass (fun d : IntDir (componentLabel weight s t)
      ((strongGraph weight s t).connectedComponentMk v) => rate d)
      (inside (componentLabel weight s t) _ (s v)) =
      mass rate (internalPart weight s t v) := by
  unfold mass
  apply Finset.sum_bij (fun d _ => d.val)
  · intro d hd
    exact (internalPart_iff_label weight s t v d.val).mpr
      ⟨(Finset.mem_filter.mp hd).2, d.property⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro d hd
    obtain ⟨hm, hl⟩ := (internalPart_iff_label weight s t v d).mp hd
    exact ⟨⟨d,hl⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩,rfl⟩
  · intro d _
    rfl

omit [Fintype D] [DecidableEq D] in
lemma mass_scaled (L : ℝ≥0) (weight : D → ℝ≥0) (S : Finset D) :
    mass (fun d => L * weight d) S = (L : ℝ) * mass weight S := by
  simp only [mass, NNReal.coe_mul, Finset.mul_sum]

lemma source_inside_mass_lower (weight : D → ℝ≥0) (s : V → Finset D)
    {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (hs : ∀ v, (3 / 4 : ℝ) ≤ mass weight (s v)) (v : V) :
    (37 / 50 : ℝ) ≤ mass (fun d : IntDir (componentLabel weight s (1 / (100 * p)))
      ((strongGraph weight s (1 / (100 * p))).connectedComponentMk v) => weight d)
      (inside (componentLabel weight s (1 / (100 * p))) _ (s v)) := by
  rw [mass_inside_eq]
  exact source_internal_mass_lower weight s hp hc hs v

omit [Fintype D] [Fintype V] in

lemma repeats_same_component (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    {v w : V} (he : s v = s w) (hm : t < mass weight (s v)) :
    (strongGraph weight s t).connectedComponentMk v =
      (strongGraph weight s t).connectedComponentMk w := by
  by_cases hvw : v = w
  · exact congrArg _ hvw
  · apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    exact ⟨hvw, by simpa only [← he, Finset.inter_self] using hm⟩

variable (label : D → Option C) (R : ℕ) (color : V → C)
  (s : V → Finset D) (own : V → Fin R → Bool)

def hitBatches {R : ℕ} (mask : Fin R → Bool) : Finset (Fin R) :=
  Finset.univ.filter (fun r => mask r = true)

def BAD {R : ℕ} (mask : Fin R → Bool) : Prop := R / 2 ≤ (hitBatches mask).card

lemma batches_partition {R : ℕ} (mask : Fin R → Bool) :
    (hitBatches mask).card + (untouchedBatches mask).card = R := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun r : Fin R => mask r = true)
  simpa only [hitBatches, untouchedBatches, Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] using h

lemma untouched_of_not_bad {R : ℕ} (mask : Fin R → Bool) (h : ¬ BAD mask) :
    R / 2 ≤ (untouchedBatches mask).card := by
  have hp := batches_partition mask
  simp only [BAD, not_le] at h
  omega

omit [Fintype C] in

theorem simple_component_designations_raw (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c})
    (hsingle : ∀ u, color u = c → u = v.val)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    (hin : inside label c (s v) = Finset.univ) (z : Block label R none → ℕ)
    {L base delta alpha : ℝ} (hL : 10000 ≤ L)
    (hmass : mass (fun d : IntDir label c => rate d) (inside label c (s v)) =
      L * (base + delta - alpha))
    (hint : (37 / 50 : ℝ) ≤ base + delta - alpha) (hbase : (37 / 50 : ℝ) ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {K : ℕ} (hK : K ≤ R / 2) :
    |∫ x, componentFactor label R color s (Real.exp (-L * base)) own J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)| ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) *
        (|delta| ^ (R / 2) + alpha ^ K +
          ∑ d ∈ inside label c (s v), ((R : ℝ) * (rate d : ℝ)) ^ J +
            if BAD (touched label R c (s v) z) then 1 else 0) := by
  by_cases hg : ¬ BAD (touched label R c (s v) z)
  · simp only [ite_eq_right hg, add_zero]
    exact simple_component_attenuation label R color s own rate J c v hsingle hcompat hin z
      hL hmass hint hbase ha hd (untouched_of_not_bad _ hg) hK
  · simp only [not_not] at hg
    simp only [ite_eq_left hg]
    have hn := nonsimple_component_attenuation label R color s own rate J c v z
      hcompat hL hmass hint hbase
    have hat : Real.exp (-(7 / 10 : ℝ) * (L * R)) ≤
        Real.exp (-(17 / 25 : ℝ) * (L * R)) := by
      apply Real.exp_le_exp.mpr
      have hLR : 0 ≤ L * (R : ℝ) := mul_nonneg (by linarith) (by positivity)
      nlinarith
    calc
      _ ≤ ∫ x, |componentFactor label R color s (Real.exp (-L * base)) own J c z x|
          ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2) := abs_integral_le_integral_abs
      _ ≤ _ := hn
      _ ≤ Real.exp (-(17 / 25 : ℝ) * (L * R)) := hat
      _ ≤ _ := by
        apply le_mul_of_one_le_right (Real.exp_pos _).le
        have he : 0 ≤ ∑ d ∈ inside label c (s v), ((R : ℝ) * (rate d : ℝ)) ^ J := by positivity
        have haK : 0 ≤ alpha ^ K := pow_nonneg ha K
        have hdN : 0 ≤ |delta| ^ (R / 2) := by positivity
        linarith
omit [Fintype C] in

theorem simple_component_designations (rate : D → ℝ≥0) (J : ℕ)
    (c : C) (v : {v : V // color v = c})
    (hsingle : ∀ u, color u = c → u = v.val)
    (hcompat : ∀ d ∈ s v, label d = none ∨ label d = some c)
    (hin : inside label c (s v) = Finset.univ) (z : Block label R none → ℕ)
    {L base delta alpha : ℝ} (hL : 10000 ≤ L)
    (hmass : mass (fun d : IntDir label c => rate d) (inside label c (s v)) =
      L * (base + delta - alpha))
    (hint : (37 / 50 : ℝ) ≤ base + delta - alpha) (hbase : (37 / 50 : ℝ) ≤ base)
    (ha : 0 ≤ alpha) (hd : |delta| + alpha ≤ 1) {K : ℕ} (hK : K ≤ R / 2) :
    |∫ x, componentFactor label R color s (Real.exp (-L * base)) own J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)| ≤
      Real.exp (-(17 / 25 : ℝ) * (L * R)) *
        (|delta| ^ (R / 2) + alpha ^ K +
          (if R < J then 0 else
            ∑ d ∈ inside label c (s v), ((R : ℝ) * (rate d : ℝ)) ^ J) +
            if BAD (touched label R c (s v) z) then 1 else 0) := by
  by_cases hRJ : R < J
  · simp only [ite_eq_left hRJ, add_zero]
    by_cases hg : ¬ BAD (touched label R c (s v) z)
    · simp only [ite_eq_right hg, add_zero]
      rw [simple_component_integral label R color s _ own rate J c v hsingle hcompat hin z]
      simp_rw [overloaded_eq_empty _ hRJ, Set.compl_empty, Set.indicator_univ]
      exact simple_singleton_attenuation _ _ (own v) (touched label R c (s v) z)
        hL hmass hint hbase ha hd (untouched_of_not_bad _ hg) hK
    · simp only [not_not] at hg
      simp only [ite_eq_left hg]
      have hn := nonsimple_component_attenuation label R color s own rate J c v z
        hcompat hL hmass hint hbase
      have hat : Real.exp (-(7 / 10 : ℝ) * (L * R)) ≤
          Real.exp (-(17 / 25 : ℝ) * (L * R)) := by
        apply Real.exp_le_exp.mpr
        have hLR : 0 ≤ L * (R : ℝ) := mul_nonneg (by linarith) (by positivity)
        nlinarith
      calc
        _ ≤ ∫ x, |componentFactor label R color s (Real.exp (-L * base)) own J c z x|
            ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2) := abs_integral_le_integral_abs
        _ ≤ _ := hn
        _ ≤ Real.exp (-(17 / 25 : ℝ) * (L * R)) := hat
        _ ≤ _ := by
          apply le_mul_of_one_le_right (Real.exp_pos _).le
          have haK : 0 ≤ alpha ^ K := pow_nonneg ha K
          have hdN : 0 ≤ |delta| ^ (R / 2) := by positivity
          linarith
  · simpa only [ite_eq_right hRJ] using
      simple_component_designations_raw label R color s own rate J c v hsingle
        hcompat hin z hL hmass hint hbase ha hd hK

end SharpRamseyFive.TupleComponents

namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open Classical
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]
variable (R : ℕ) (s : H → Finset D) (b : ℝ) (own : H → Fin R → Bool)

noncomputable def allTrunc (J : ℕ) (ω : Fin R × D → ℕ) : ℝ :=
  ∏ d : D, lineTrunc R J (fun r => ω (r,d))

omit [DecidableEq D] in
lemma allTrunc_range (J : ℕ) (ω : Fin R × D → ℕ) :
    allTrunc R J ω ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg (fun _ _ => (lineTrunc_range R J _).1)
  · exact Finset.prod_le_one₀ (fun _ _ => (lineTrunc_range R J _).1)
      (fun _ _ => (lineTrunc_range R J _).2)

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] [DecidableEq D] in
lemma scoreTerm_abs_le (hb : b ∈ Set.Icc (0 : ℝ) 1) (h : H) (ω : Fin R × D → ℕ) :
    |scoreTerm (s h) b (own h) (fun r d => ω (r,d))| ≤ 1 := by
  simpa only [maskedTerm, maskedFactor, Bool.false_eq_true, ↓reduceIte, scoreTerm]
    using abs_maskedTerm_le_one (s h) hb (own h) (fun _ => false) (fun r d => ω (r,d))
omit [Fintype H] [DecidableEq H] in
omit [DecidableEq D] in

lemma truncated_tuple_abs_le (J : ℕ) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    {V : Type} [Fintype V] (f : V → H) (ω : Fin R × D → ℕ) :
    |allTrunc R J ω * ∏ v, scoreTerm (s (f v)) b (own (f v)) (fun r d => ω (r,d))| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (allTrunc_range R J ω).1, Finset.abs_prod]
  exact (mul_le_of_le_one_left (by positivity) (allTrunc_range R J ω).2).trans
    (Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun _ _ => scoreTerm_abs_le R s b own hb _ ω))

end SharpRamseyFive.HighMoment
end

end OAI
