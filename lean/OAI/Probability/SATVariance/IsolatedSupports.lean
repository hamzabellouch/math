import OAI.Probability.SATVariance.InsertionVariance

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma avoidance_probability_lower {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n)
    (c : Clause n k) :
    1-(k:ℝ)^2/n ≤ favg (fun d : Clause n k => if Disjoint c.1.1 d.1.1 then (1:ℝ) else 0) := by
  let := clause_nonempty n k hkn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hp (v : Fin n) : favg (fun d : Clause n k => if v ∈ d.1.1 then (1:ℝ) else 0) = (k:ℝ)/n := by
    apply (eq_div_iff hn0).mpr
    nlinarith [support_probability_scaled hkn v]
  calc
    _ = favg (fun d : Clause n k => 1-∑ v ∈ c.1.1, if v ∈ d.1.1 then (1:ℝ) else 0) := by
      rw [favg_sub,favg_const,favg_sum]
      simp only [hp,Finset.sum_const,c.1.2,nsmul_eq_mul]
      ring
    _ ≤ _ := favg_mono (fun d => by
      by_cases h : Disjoint c.1.1 d.1.1
      · rw [ite_eq_left h]
        have hs : (∑ v ∈ c.1.1, if v ∈ d.1.1 then (1:ℝ) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          simp [Finset.disjoint_left.mp h hv]
        rw [hs]
        norm_num
      · rw [ite_eq_right h]
        obtain ⟨v,hv,hd⟩ := Finset.not_disjoint_iff.mp h
        have hh := Finset.single_le_sum (f := fun v : Fin n => if v ∈ d.1.1 then (1:ℝ) else 0)
          (fun _ _ => by positivity) hv
        rw [ite_eq_left hd] at hh
        linarith)

lemma log_one_sub_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
    -2*x ≤ Real.log (1-x) := by
  have hp : 0 < 1-x := by linarith
  have hi : (1-x)⁻¹ ≤ 1+2*x := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  linarith [Real.one_sub_inv_le_log_of_pos hp]

lemma slow_geometric_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) (J : ℕ) :
    Real.exp (-2*x*J) ≤ (1-x)^J := by
  have hp : 0 < 1-x := by linarith
  rw [←Real.exp_log hp,←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right (log_one_sub_lower hx hx') (show (0:ℝ) ≤ J by positivity)
  nlinarith

def isolated {n k M : ℕ} (w : Fin M → Clause n k) (i : Fin M) : Prop :=
  ∀ j, j ≠ i → Disjoint (w i).1.1 (w j).1.1

def isolateSet {n k M : ℕ} (w : Fin M → Clause n k) : Finset (Fin M) :=
  Finset.univ.filter (isolated w)

lemma isolated_insertNth {n k M : ℕ} (i : Fin (M+1)) (c : Clause n k) (w : Fin M → Clause n k) :
    isolated (i.insertNth c w) i ↔ ∀ j : Fin M, Disjoint c.1.1 (w j).1.1 := by
  unfold isolated
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, ne_eq, not_true_eq_false, false_implies, true_and,
    Fin.succAbove_ne, not_false_eq_true,true_implies,Fin.insertNth_apply_succAbove]

lemma favg_all.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α] (p : α → Prop) :
    favg (fun w : ι → α => if ∀ i, p (w i) then (1:ℝ) else 0) =
      (favg (fun a => if p a then (1:ℝ) else 0))^(Fintype.card ι) := by
  have he (w : ι → α) : (if ∀ i, p (w i) then (1:ℝ) else 0) =
      ∏ i, if p (w i) then (1:ℝ) else 0 := by simp only [Finset.prod_boole,Finset.mem_univ,true_implies]
  simp only [he]
  rw [favg_pi_product (fun _ a => if p a then (1:ℝ) else 0)]
  simp

lemma isolate_probability_lower {n k M R : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hn : 2*k^2 ≤ n) (hM : M ≤ 2*R*n) (i : Fin (M+1)) :
    Real.exp (-4*(R:ℝ)*k^2) ≤ favg (fun w : Fin (M+1) → Clause n k => if isolated w i then (1:ℝ) else 0) := by
  let := clause_nonempty n k hkn
  have hn' : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn'
  have hx : 0 ≤ (k:ℝ)^2/n := by positivity
  have hx' : (k:ℝ)^2/n ≤ 1/2 := by
    apply (div_le_iff₀ hnR).mpr
    have hnR' : 2*(k:ℝ)^2 ≤ n := by exact_mod_cast hn
    linarith
  have he : Real.exp (-4*(R:ℝ)*k^2) ≤ (1-(k:ℝ)^2/n)^M := by
    apply le_trans ?_ (slow_geometric_lower hx hx' M)
    apply Real.exp_le_exp.mpr
    have hMR : (M:ℝ) ≤ 2*R*n := by exact_mod_cast hM
    have hh := mul_le_mul_of_nonneg_right hMR hx
    have hd : (2*(R:ℝ)*n)*((k:ℝ)^2/n) = 2*R*k^2 := by field_simp
    rw [hd] at hh
    nlinarith
  rw [favg_insertNth i]
  simp only [isolated_insertNth]
  have hm (c : Clause n k) :
      favg (fun w : Fin M → Clause n k => if ∀ j, Disjoint c.1.1 (w j).1.1 then (1:ℝ) else 0) =
      (favg (fun d : Clause n k => if Disjoint c.1.1 d.1.1 then (1:ℝ) else 0))^M := by
    have hh := favg_all (ι := Fin M) (fun d : Clause n k => Disjoint c.1.1 d.1.1)
    simp only [Fintype.card_fin] at hh
    convert hh using 1
    · congr 1
      funext w
      by_cases h : ∀ j : Fin M, Disjoint c.1.1 (w j).1.1 <;> simp [h]
    · congr 2
      funext d
      by_cases h : Disjoint c.1.1 d.1.1 <;> simp [h]
  simp only [hm]
  rw [←favg_const (α := Clause n k) (Real.exp (-4*(R:ℝ)*k^2))]
  exact favg_mono (fun c => he.trans (pow_le_pow_left₀ (by linarith)
    (avoidance_probability_lower hkn hn' c) M))

lemma isolate_count_lower {n k M R : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hn : 2*k^2 ≤ n) (hM : M ≤ 2*R*n) :
    (M:ℝ)*Real.exp (-4*(R:ℝ)*k^2) ≤
      favg (fun w : Fin M → Clause n k => ((isolateSet w).card:ℝ)) := by
  have he (w : Fin M → Clause n k) : ((isolateSet w).card:ℝ) =
      ∑ i, if isolated w i then (1:ℝ) else 0 := by simp [isolateSet]
  simp only [he]
  rw [favg_sum]
  calc
    _ = ∑ _ : Fin M, Real.exp (-4*(R:ℝ)*k^2) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      cases M with
      | zero => exact i.elim0
      | succ M => exact isolate_probability_lower hk hkn hn (by omega) i)

end RandomKSAT

end

end OAI
