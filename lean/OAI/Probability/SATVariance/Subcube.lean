import OAI.Probability.SATVariance.HallSatisfiability

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace RandomKSAT

def subcube (u b : ℕ) : Finset (Assignment u) :=
  Finset.univ.filter fun a => ∀ v : Fin u, (v : ℕ) < b → a v = false

lemma mem_subcube {u b : ℕ} {a : Assignment u} :
    a ∈ subcube u b ↔ ∀ v : Fin u, (v : ℕ) < b → a v = false := by
  simp [subcube]

lemma subcube_nonempty (u b : ℕ) : (subcube u b).Nonempty := by
  exact ⟨fun _ => false, mem_subcube.mpr (by simp)⟩

lemma subcube_sat_of_disjoint.{u_1} {u b k : ℕ} {ι : Type u_1} [Fintype ι]
    (cs : ι → Clause u k)
    (hkill : ∀ i, ¬ Kills (subcube u b) (cs i))
    (hdisj : ∀ i j, i ≠ j → ∀ v : Fin u, b ≤ (v : ℕ) →
      v ∈ (cs i).1.1 → v ∉ (cs j).1.1) :
    ∃ a ∈ subcube u b, ∀ i, Satisfies (cs i) a := by
  have hw : ∀ i, ∃ a ∈ subcube u b, Satisfies (cs i) a := by
    intro i
    simpa only [Kills, not_forall, exists_prop, not_not] using hkill i
  choose a ha hv using hw
  choose v hv using hv
  let x : Assignment u := fun w =>
    if h : b ≤ (w : ℕ) ∧ ∃ i, w ∈ (cs i).1.1 then
      a h.2.choose w else false
  refine ⟨x, mem_subcube.mpr ?_, ?_⟩
  · intro w hw
    simp [x, show ¬ b ≤ (w : ℕ) by omega]
  · intro i
    refine ⟨v i, ?_⟩
    by_cases hb : (v i : Fin u).val < b
    · have hfalse := mem_subcube.mp (ha i) (v i) hb
      have hv' := hv i
      rw [hfalse] at hv'
      simpa [x, show ¬ b ≤ (v i : Fin u).val by omega] using hv'
    · have hh : b ≤ (v i : Fin u).val ∧ ∃ j, (v i : Fin u) ∈ (cs j).1.1 :=
        ⟨by omega, i, (v i).property⟩
      have he : hh.2.choose = i := by
        by_contra hn
        exact hdisj i hh.2.choose (Ne.symm hn) (v i) hh.1 (v i).property hh.2.choose_spec
      simp only [x, dite_eq_left hh]
      rw [he]
      exact hv i

lemma frozen_subcube (u b : ℕ) :
    frozen (subcube u b) = Finset.univ.filter (fun v : Fin u => (v : ℕ) < b) := by
  ext v
  simp only [frozen, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hn
    let a : Assignment u := fun w => if w = v then true else false
    have ha : a ∈ subcube u b := by
      apply mem_subcube.mpr
      intro w hw
      have hwv : w ≠ v := by rintro rfl; exact hn hw
      simp [a, hwv]
    have h0 : (fun _ : Fin u => false) ∈ subcube u b := mem_subcube.mpr (by simp)
    have hh := h _ h0 a ha
    simp [a] at hh
  · intro hv a ha c hc
    exact (mem_subcube.mp ha v hv).trans (mem_subcube.mp hc v hv).symm

lemma frozen_subcube_card {u b : ℕ} (hbu : b ≤ u) :
    (frozen (subcube u b)).card = b := by
  let e : {v : Fin u // (v : ℕ) < b} ≃ Fin b :=
    { toFun := fun v => ⟨v.1.val, v.2⟩
      invFun := fun v => ⟨⟨v.val, v.isLt.trans_le hbu⟩, v.isLt⟩
      left_inv := by intro v; rfl
      right_inv := by intro v; rfl }
  rw [frozen_subcube]
  simpa only [Fintype.card_subtype, Fintype.card_fin] using Fintype.card_congr e

lemma subcube_one {u b s : ℕ} (hbu : b ≤ u) (hsu : s ≤ u) :
    blockKill u s (subcube u b) 1 = killRatio u b s := by
  rw [blockKill_one hsu (subcube_nonempty u b), frozen_subcube_card hbu]

lemma subcube_killing_indicator {u b k t : ℕ} (cs : Fin t → Clause u k) :
    (if ¬ (residual (subcube u b) cs).Nonempty then (1 : ℝ) else 0) ≤
      (∑ i, if Kills (subcube u b) (cs i) then (1 : ℝ) else 0) +
      ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ v : Fin u,
        if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0 := by
  by_cases hs : (residual (subcube u b) cs).Nonempty
  · rw [ite_eq_right (not_not.mpr hs)]
    positivity
  rw [ite_eq_left hs]
  have hex : (∃ i, Kills (subcube u b) (cs i)) ∨
      ∃ i j, i ≠ j ∧ ∃ v : Fin u, v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 := by
    by_contra hn
    push Not at hn
    have hh := subcube_sat_of_disjoint cs hn.1 (by
      intro i j hij v _ hv
      exact hn.2 i j hij v hv)
    obtain ⟨a, ha, hcs⟩ := hh
    exact hs ⟨a, by simp only [residual, Finset.mem_filter]; exact ⟨ha, hcs⟩⟩
  rcases hex with ⟨i, hi⟩ | ⟨i, j, hij, v, hv, hw⟩
  · have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin t)))
      (f := fun j => if Kills (subcube u b) (cs j) then (1 : ℝ) else 0)
      (fun _ _ => by positivity) (Finset.mem_univ i)
    simp only [ite_eq_left hi] at h
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · have h1 := Finset.single_le_sum (s := (Finset.univ : Finset (Fin u)))
      (f := fun w => if w ∈ (cs i).1.1 ∧ w ∈ (cs j).1.1 then (1 : ℝ) else 0)
      (fun _ _ => by positivity) (Finset.mem_univ v)
    rw [ite_eq_left ⟨hv,hw⟩] at h1
    have h2 := Finset.single_le_sum (s := Finset.univ.erase i)
      (f := fun j => ∑ v : Fin u,
        if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0)
      (fun _ _ => by positivity) (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)
    have h3 := Finset.single_le_sum (s := (Finset.univ : Finset (Fin t)))
      (f := fun i => ∑ j ∈ Finset.univ.erase i, ∑ v : Fin u,
        if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0)
      (fun _ _ => by positivity) (Finset.mem_univ i)
    exact (h1.trans (h2.trans h3)).trans (le_add_of_nonneg_left (by positivity))

lemma favg_pi_pair.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Nonempty α] (i j : ι) (hij : i ≠ j) (f : α → ℝ) :
    favg (fun cs : ι → α => f (cs i) * f (cs j)) = (favg f)^2 := by
  simpa [hij] using favg_pi_on ({i,j} : Finset ι) f

lemma support_probability {u k : ℕ} (hu : 0 < u) (hku : k ≤ u) (v : Fin u) :
    favg (fun c : Clause u k => if v ∈ c.1.1 then (1 : ℝ) else 0) = (k : ℝ)/u := by
  have h := support_probability_scaled hku v
  exact (eq_div_iff (by positivity)).mpr (by linarith)

lemma overlap_favg {u k t : ℕ} (hu : 0 < u) (hku : k ≤ u)
    (i j : Fin t) (hij : i ≠ j) :
    favg (fun cs : Fin t → Clause u k => ∑ v : Fin u,
      if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0) = (k : ℝ)^2/u := by
  let := clause_nonempty u k hku
  rw [favg_sum]
  have hh (v : Fin u) :
      favg (fun cs : Fin t → Clause u k =>
        if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0) = ((k : ℝ)/u)^2 := by
    have he (cs : Fin t → Clause u k) :
        (if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0) =
        (if v ∈ (cs i).1.1 then (1 : ℝ) else 0) *
          (if v ∈ (cs j).1.1 then (1 : ℝ) else 0) := by
      split_ifs <;> simp_all
    simp only [he]
    rw [favg_pi_pair i j hij (fun c : Clause u k => if v ∈ c.1.1 then (1 : ℝ) else 0),
      support_probability hu hku v]
  simp only [hh, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma blockKill_favg {u k t : ℕ} (hku : k ≤ u) (S : Finset (Assignment u)) :
    blockKill u k S t =
      favg (fun cs : Fin t → Clause u k => if ¬(residual S cs).Nonempty then (1 : ℝ) else 0) := by
  let := clause_nonempty u k hku
  rw [blockKill_iterate hku, clauseStep_iterate_avg]
  have he : (fun cs : Fin t → Clause u k => if ¬(residual S cs).Nonempty then (1 : ℝ) else 0) =
      (fun cs => 1 - alive u (residual S cs)) := by
    funext cs
    simp only [alive]
    split_ifs <;> simp_all
  rw [he, favg_sub, favg_const]

lemma subcube_block_upper {u b k : ℕ} (hu : 0 < u) (hbu : b ≤ u) (hku : k ≤ u)
    (t : ℕ) :
    blockKill u k (subcube u b) t ≤
      (t : ℝ) * killRatio u b k + (t : ℝ)^2 * (k : ℝ)^2 / u := by
  let := clause_nonempty u k hku
  rw [blockKill_favg hku]
  have hh := favg_mono (subcube_killing_indicator (u := u) (b := b) (k := k) (t := t))
  apply hh.trans
  rw [favg_add, favg_sum, favg_sum]
  have hsingle (i : Fin t) :
      favg (fun cs : Fin t → Clause u k => if Kills (subcube u b) (cs i) then (1 : ℝ) else 0) =
        killRatio u b k := by
    rw [favg_pi_eval i (fun c : Clause u k => if Kills (subcube u b) c then (1 : ℝ) else 0)]
    have hp := clauseLaw_kills_toReal (subcube_nonempty u b) (s := k)
    rw [clauseLaw, uniformOn_real, frozen_subcube_card hbu] at hp
    exact hp
  simp only [hsingle, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply add_le_add le_rfl
  have hpair (i : Fin t) :
      favg (fun cs : Fin t → Clause u k => ∑ j ∈ Finset.univ.erase i, ∑ v : Fin u,
        if v ∈ (cs i).1.1 ∧ v ∈ (cs j).1.1 then (1 : ℝ) else 0) ≤
        (t : ℝ) * ((k : ℝ)^2/u) := by
    rw [favg_sum]
    calc
      _ = ∑ _j ∈ Finset.univ.erase i, (k : ℝ)^2/u := by
        apply Finset.sum_congr rfl
        intro j hj
        exact overlap_favg hu hku i j (Ne.symm (Finset.mem_erase.mp hj).1)
      _ ≤ ∑ _j : Fin t, (k : ℝ)^2/u :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by intros; positivity)
      _ = _ := by simp
  calc
    _ ≤ ∑ _i : Fin t, (t : ℝ) * ((k : ℝ)^2/u) := Finset.sum_le_sum fun i _ => hpair i
    _ = _ := by simp; ring

lemma bernoulli_quadratic {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (t : ℕ) :
    (t : ℝ)*h - (t : ℝ)^2*h^2 ≤ 1 - (1-h)^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr h1)
    have h3 := mul_nonneg (sq_nonneg (t : ℝ)) (pow_nonneg h0 3)
    have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) t) (sq_nonneg h)
    rw [pow_succ (1-h) t]
    push_cast
    nlinarith [sq_nonneg h]

lemma subcube_block_lower {u b k : ℕ} (hbu : b ≤ u) (hku : k ≤ u) (t : ℕ) :
    (t : ℝ) * killRatio u b k - (t : ℝ)^2 * (killRatio u b k)^2 ≤
      blockKill u k (subcube u b) t := by
  have hh := blockKill_individual hku (subcube_nonempty u b) t
  rw [frozen_subcube_card hbu] at hh
  apply (bernoulli_quadratic (killRatio_nonneg u b k) ?_ t).trans hh
  rw [← subcube_one hbu hku]
  exact blockKill_le_one hku _ _

end RandomKSAT

end

end OAI
