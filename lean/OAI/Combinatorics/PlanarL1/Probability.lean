import Mathlib

namespace OAI

section

namespace PlanarL1.FiniteRandom

attribute [local instance] Classical.propDecidable

noncomputable def event {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : Finset Ω := by
  classical
  exact Finset.univ.filter P

lemma mem_event {Ω : Type*} [Fintype Ω] (P : Ω → Prop) (w : Ω) : w ∈ event P ↔ P w := by
  classical
  simp [event]

noncomputable def prob {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact ((event P).card : ℝ) / Fintype.card Ω

lemma prob_nonneg {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : 0 ≤ prob P := by
  unfold prob
  positivity

lemma prob_eq_sum {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    prob P = (∑ w, if P w then (1 : ℝ) else 0) / Fintype.card Ω := by
  classical
  simp [prob, event, Finset.sum_boole]

lemma prob_mono {Ω : Type*} [Fintype Ω] {P Q : Ω → Prop} (h : ∀ w, P w → Q w) :
    prob P ≤ prob Q := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show event P ⊆ event Q from
    fun w hw => (mem_event Q w).mpr (h w ((mem_event P w).mp hw)))

lemma prob_equiv {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (e : Ω ≃ Λ) (P : Λ → Prop) :
    prob (fun w => P (e w)) = prob P := by
  classical
  rw [prob_eq_sum, prob_eq_sum, Fintype.card_congr e]
  exact congrArg (fun z : ℝ => z / Fintype.card Λ)
    (e.sum_comp (fun z : Λ => if P z then (1 : ℝ) else 0))

lemma prob_prod {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] (P : Ω × Λ → Prop) :
    prob P = (∑ w : Ω, prob (fun z : Λ => P (w,z))) / Fintype.card Ω := by
  classical
  simp only [prob_eq_sum, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.sum_div]
  ring

lemma prob_prod_bound {Ω Λ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Λ]
    (P : Ω × Λ → Prop) {b : ℝ} (h : ∀ w, prob (fun z : Λ => P (w,z)) ≤ b) :
    prob P ≤ b := by
  rw [prob_prod]
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).mpr
  calc
    ∑ w : Ω, prob (fun z : Λ => P (w,z)) ≤ ∑ _w : Ω, b := Finset.sum_le_sum (fun w _ => h w)
    _ = b * Fintype.card Ω := by simp [mul_comm]

lemma prob_union_bound {Ω ι : Type*} [Fintype Ω] (S : Finset ι) (P : ι → Ω → Prop) :
    prob (fun w => ∃ i ∈ S, P i w) ≤ ∑ i ∈ S, prob (P i) := by
  classical
  unfold prob
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have he : event (fun w => ∃ i ∈ S, P i w) =
      S.biUnion (fun i => event (P i)) := by
    ext w
    simp [mem_event]
  rw [he]
  exact_mod_cast (Finset.card_biUnion_le :
    (S.biUnion (fun i => event (P i))).card ≤
      ∑ i ∈ S, (event (P i)).card)

/-- Cardinality of a grid subset is controlled by the span of its indices. -/
lemma grid_card_span (s : Finset ℕ) {a b : ℕ} (h : ∀ i ∈ s, a ≤ i ∧ i ≤ b) :
    s.card ≤ b + 1 - a := by
  have hs : s ⊆ Finset.Icc a b := fun i hi => Finset.mem_Icc.mpr (h i hi)
  simpa using Finset.card_le_card hs

/-- An interval of radius t meets at most 2t/step+1 equally spaced points.
This argument is exact and includes both endpoints of the grid. -/
lemma grid_count (m : ℕ) {step t : ℝ} (hstep : 0 < step) (ht : 0 ≤ t) (c : ℝ) :
    ((event (fun i : Fin (m + 1) => |c + step * i.val| ≤ t)).card : ℝ) * step ≤
      2 * t + step := by
  classical
  let A := event (fun i : Fin (m + 1) => |c + step * i.val| ≤ t)
  by_cases hA : A.Nonempty
  · let a := A.min' hA
    let b := A.max' hA
    have ha : a ∈ A := A.min'_mem hA
    have hb : b ∈ A := A.max'_mem hA
    have hab : a.val ≤ b.val := A.min'_le b hb
    have hsub : A.image Fin.val ⊆ Finset.Icc a.val b.val := by
      rintro i hi
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_Icc.mpr ⟨A.min'_le z hz, A.le_max' z hz⟩
    have hcard : A.card ≤ b.val + 1 - a.val := by
      have hc := Finset.card_le_card hsub
      simpa only [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] using hc
    have hcard' : (A.card : ℝ) ≤ (b.val : ℝ) - a.val + 1 := by
      have he : b.val + 1 - a.val + a.val = b.val + 1 := Nat.sub_add_cancel (by omega)
      have hh : (b.val + 1 - a.val : ℕ) + a.val ≤ b.val + 1 := he.le
      have hi : A.card + a.val ≤ b.val + 1 := by omega
      have hir : (A.card : ℝ) + a.val ≤ (b.val : ℝ) + 1 := by exact_mod_cast hi
      linarith
    have ham : |c + step * a.val| ≤ t := (mem_event _ a).mp ha
    have hbm : |c + step * b.val| ≤ t := (mem_event _ b).mp hb
    have ha' := (abs_le.mp ham).1
    have hb' := (abs_le.mp hbm).2
    have hm := mul_le_mul_of_nonneg_right hcard' hstep.le
    change (A.card : ℝ) * step ≤ 2 * t + step
    nlinarith
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change (A.card : ℝ) * step ≤ 2 * t + step
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    linarith

/-- Uniform endpoint grid estimate in the normalization used by the paper. -/
lemma grid_probability (m : ℕ) (hm : 0 < m) {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t) (c : ℝ) :
    prob (fun i : Fin (m + 1) => |c + q / m * i.val| ≤ t) ≤ (2 * t + q / m) / q := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < q / m := div_pos hq hm'
  have hcount := grid_count m hs ht c
  have hc : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  unfold prob
  rw [Fintype.card_fin]
  apply (div_le_iff₀ hc).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hq).mpr
  have hn : (0 : ℝ) ≤ (event (fun i : Fin (m + 1) => |c + q / m * i.val| ≤ t)).card :=
    Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_right hcount hm'.le
  have hmul : q / (m : ℝ) * m = q := div_mul_cancel₀ q (ne_of_gt hm')
  rw [mul_assoc, hmul] at hh
  push_cast
  nlinarith

end PlanarL1.FiniteRandom

namespace PlanarL1.FiniteRandom

attribute [local instance] Classical.propDecidable

/-- Independent uniform grid coordinates can be exposed one at a time by an
actual equivalence of finite sample spaces. -/
lemma coordinate_probability {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (m : ℕ) (hm : 0 < m) {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t)
    (F : (I → Fin (m + 1)) → ℝ)
    (hF : ∀ α : I → Fin (m + 1), ∃ c : ℝ,
      (∀ r : Fin (m + 1), F (Function.update α i r) = c + q / m * r.val) ∨
      (∀ r : Fin (m + 1), F (Function.update α i r) = c - q / m * r.val)) :
    prob (fun α => |F α| ≤ t) ≤ (2 * t + q / m) / q := by
  classical
  let e : (I → Fin (m + 1)) ≃ ({j : I // j ≠ i} → Fin (m + 1)) × Fin (m + 1) :=
    (Equiv.funSplitAt i (Fin (m + 1))).trans (Equiv.prodComm _ _)
  have he := prob_equiv e.symm (fun α => |F α| ≤ t)
  rw [← he]
  apply prob_prod_bound
  intro rest
  let α : I → Fin (m + 1) := e.symm (rest, 0)
  have hu (r : Fin (m + 1)) : e.symm (rest,r) = Function.update α i r := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, α, Equiv.funSplitAt_symm_apply]
    · simp [e, α, Equiv.funSplitAt_symm_apply, hj]
  obtain ⟨c, hc⟩ := hF α
  rcases hc with hc | hc
  · have hp := prob_mono (fun r (hr : |F (e.symm (rest,r))| ≤ t) =>
      (show |c + q / m * r.val| ≤ t by simpa only [hu r, hc r] using hr))
    exact hp.trans (grid_probability m hm hq ht c)
  · have hp := prob_mono (fun r (hr : |F (e.symm (rest,r))| ≤ t) =>
      (show |-c + q / m * r.val| ≤ t by
        rw [hu r, hc r] at hr
        rw [show -c + q / m * r.val = -(c - q / m * r.val) by ring, abs_neg]
        exact hr))
    exact hp.trans (grid_probability m hm hq ht (-c))

lemma prob_false {Ω : Type*} [Fintype Ω] : prob (fun _ : Ω => False) = 0 := by
  simp [prob, event]

lemma prob_pair_bound {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (S : Finset ι) (P : ι → ι → Ω → Prop) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → prob (P i j) ≤ b) :
    prob (fun w => ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ P i j w) ≤ (S.card : ℝ)^2 * b := by
  classical
  have he : (fun w => ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ P i j w) =
      (fun w => ∃ ij ∈ S ×ˢ S, ij.1 ≠ ij.2 ∧ P ij.1 ij.2 w) := by
    funext w
    simp only [Finset.mem_product, Prod.exists]
    aesop
  rw [he]
  calc
    prob (fun w => ∃ ij ∈ S ×ˢ S, ij.1 ≠ ij.2 ∧ P ij.1 ij.2 w) ≤
        ∑ ij ∈ S ×ˢ S, prob (fun w => ij.1 ≠ ij.2 ∧ P ij.1 ij.2 w) := prob_union_bound _ _
    _ ≤ ∑ _ij ∈ S ×ˢ S, b := by
      apply Finset.sum_le_sum
      intro ij hij
      by_cases heq : ij.1 = ij.2
      · have hz : prob (fun w => ij.1 ≠ ij.2 ∧ P ij.1 ij.2 w) = 0 := by
          simpa only [heq, ne_eq, not_true_eq_false, false_and] using (prob_false (Ω := Ω))
        rw [hz]
        exact hb
      · exact (prob_mono (fun _ hw => hw.2)).trans
          (h ij.1 (Finset.mem_product.mp hij).1 ij.2 (Finset.mem_product.mp hij).2 heq)
    _ = (S.card : ℝ)^2 * b := by simp [pow_two]

end PlanarL1.FiniteRandom

end

section

namespace PlanarL1.FiniteRandom
lemma prob_prod_bound_left {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [Nonempty Λ]
    (P : Ω × Λ → Prop) {b : ℝ} (h : ∀ z, prob (fun w : Ω => P (w,z)) ≤ b) :
    prob P ≤ b := by
  rw [← prob_equiv (Equiv.prodComm Λ Ω) P]
  exact prob_prod_bound _ h
end PlanarL1.FiniteRandom


end

section

namespace PlanarL1.FiniteRandom

/-- Expose one independent finite coordinate, retaining every other coordinate.
This is the conditional probability step used between distinct seed groups. -/
lemma prob_update_bound {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] [Nonempty Ω] (i : I) (P : (I → Ω) → Prop) {b : ℝ}
    (h : ∀ α, prob (fun r : Ω => P (Function.update α i r)) ≤ b) :
    prob P ≤ b := by
  classical
  let e : (I → Ω) ≃ ({j : I // j ≠ i} → Ω) × Ω :=
    (Equiv.funSplitAt i Ω).trans (Equiv.prodComm _ _)
  rw [← prob_equiv e.symm P]
  apply prob_prod_bound
  intro rest
  let α : I → Ω := e.symm (rest, Classical.arbitrary Ω)
  have hu (r : Ω) : e.symm (rest,r) = Function.update α i r := by
    funext j
    by_cases hj : j=i
    · subst j; simp [e,α,Equiv.funSplitAt_symm_apply]
    · simp [e,α,Equiv.funSplitAt_symm_apply,hj]
  simpa only [hu] using h α

end PlanarL1.FiniteRandom


end

section

namespace PlanarL1.FiniteRandom
attribute [local instance] Classical.propDecidable

lemma prob_singleton {Ω : Type*} [Fintype Ω] (x : Ω) :
    prob (fun ω => ω=x) = 1/(Fintype.card Ω : ℝ) := by
  classical
  have he : event (fun ω : Ω => ω=x)={x} := by
    ext ω
    simp only [mem_event,Finset.mem_singleton]
  rw [prob,he]
  simp

/-- Exact probability of any finite prescribed set of independent fair coins.
Unprescribed coins are unrestricted, so their number does not affect the bound. -/
lemma prob_prescribed {I : Type*} [Fintype I] (S : Finset I) (b : I → Bool) :
    prob (fun ω : I → Bool => ∀ i ∈ S, ω i=b i) = 1/(2:ℝ)^S.card := by
  classical
  let e : (I → Bool) ≃ ({i : I // i ∉ S} → Bool) × ({i : I // i ∈ S} → Bool) :=
    (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)).trans (Equiv.prodComm _ _)
  let f : {i : I // i ∈ S} → Bool := fun i => b i
  have he (ω : ({i : I // i ∉ S} → Bool) × ({i : I // i ∈ S} → Bool)) :
      (∀ i ∈ S, e.symm ω i=b i) ↔ ω.2=f := by
    constructor
    · intro h
      funext i
      simpa [e,f,Equiv.piEquivPiSubtypeProd] using h i i.property
    · intro h i hi
      simpa [e,f,Equiv.piEquivPiSubtypeProd,hi] using congrFun h ⟨i,hi⟩
  rw [← prob_equiv e.symm (fun ω : I → Bool => ∀ i ∈ S, ω i=b i)]
  simp_rw [he]
  rw [prob_prod]
  simp_rw [prob_singleton]
  have hc : (Fintype.card ({i : I // i ∉ S} → Bool) : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ hc]
  simp

lemma prob_two_coins {I : Type*} [Fintype I] (i j : I) (hij : i ≠ j) (a b : Bool) :
    prob (fun ω : I → Bool => ω i=a ∧ ω j=b) = (1:ℝ)/4 := by
  classical
  have h := prob_prescribed ({i,j} : Finset I) (Function.update (fun _ => b) i a)
  have hp (ω : I → Bool) : (∀ k ∈ ({i,j} : Finset I),
      ω k=Function.update (fun _ => b) i a k) ↔ ω i=a ∧ ω j=b := by
    simp [Function.update,Ne.symm hij]
  have hc : ({i,j} : Finset I).card=2 := by simp [hij]
  simpa only [hp,hc,pow_two,show (2:ℝ)*2=4 by norm_num] using h

/-- Any event forced by at most k independently prescribed group/cell coins
has probability at least 2⁻ᵏ. -/
lemma prob_at_least_prescription {I : Type*} [Fintype I]
    (S : Finset I) (b : I → Bool) (P : (I → Bool) → Prop) {k : ℕ}
    (hk : S.card ≤ k) (h : ∀ ω, (∀ i ∈ S, ω i=b i) → P ω) :
    1/(2:ℝ)^k ≤ prob P := by
  calc
    _ ≤ 1/(2:ℝ)^S.card := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) hk
    _ = prob (fun ω : I → Bool => ∀ i ∈ S, ω i=b i) := (prob_prescribed S b).symm
    _ ≤ prob P := prob_mono h

end PlanarL1.FiniteRandom



end

end OAI
