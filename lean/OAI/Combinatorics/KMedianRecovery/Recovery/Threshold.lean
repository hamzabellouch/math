import Mathlib

namespace OAI

namespace MetricKMedianRecovery.Anchoring

lemma geometric_half_sum (v : ℝ) (hv : 0 ≤ v) (J : ℕ) :
    (∑ a ∈ Finset.range J, v*(1/2:ℝ)^a) ≤ 2*v := by
  induction J with
  | zero => simp; positivity
  | succ J ih =>
    rw [Finset.sum_range_succ']
    have he : (∑ a ∈ Finset.range J, v*(1/2:ℝ)^(a+1)) =
        (1/2:ℝ)*(∑ a ∈ Finset.range J, v*(1/2:ℝ)^a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [pow_succ]; ring
    rw [he]
    norm_num only [pow_zero,mul_one]
    linarith

lemma geometric_half_tail (x v : ℝ) (hx : 0 ≤ x) (hv : 0 ≤ v) (J : ℕ) :
    (∑ a ∈ Finset.range J, if v*(1/2:ℝ)^a < x then v*(1/2:ℝ)^a else 0) ≤ 2*x := by
  induction J generalizing v with
  | zero => simp; positivity
  | succ J ih =>
    by_cases hvx : v < x
    · calc
        _ ≤ ∑ a ∈ Finset.range (J+1), v*(1/2:ℝ)^a := by
          apply Finset.sum_le_sum
          intro a _
          split_ifs
          · exact le_rfl
          · positivity
        _ ≤ 2*v := geometric_half_sum v hv (J+1)
        _ ≤ 2*x := by linarith
    · rw [Finset.sum_range_succ']
      simp only [pow_zero,mul_one,hvx,ite_false,add_zero]
      have he (a : ℕ) : v*(1/2:ℝ)^(a+1) = (v/2)*(1/2:ℝ)^a := by
        rw [pow_succ]; ring
      simp_rw [he]
      exact ih (v/2) (by positivity)

noncomputable def threshold (mu : ℝ) (a : ℕ) : ℝ := (mu/100)*(1/2:ℝ)^a
noncomputable def rounds (mu : ℝ) : ℕ := ⌈40/mu⌉₊
noncomputable def countConstant (mu : ℝ) : ℝ :=
  10+(600/mu)*(2:ℝ)^(rounds mu-1)

variable {I : Type*}

noncomputable def shortCenters (O : Finset I) (scale : I → ℝ) (b : ℝ) : Finset I :=
  O.filter (fun i => scale i < b)
noncomputable def badCenters (O : Finset I) (scale V : I → ℝ) (b t : ℝ) : Finset I :=
  O.filter (fun i => scale i < b ∨ t*b < V i)

lemma bad_count_pointwise (O : Finset I) (scale V : I → ℝ) (b t : ℝ)
    (hV : ∀ i ∈ O, 0 ≤ V i) :
    t*b*((badCenters O scale V b t).card:ℝ) ≤
      t*b*((shortCenters O scale b).card:ℝ)+(∑ i ∈ O, V i) := by
  have he (P : I → Prop) [DecidablePred P] :
      t*b*((O.filter P).card:ℝ) = ∑ i ∈ O, if P i then t*b else 0 := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    ring
  rw [badCenters,shortCenters,he,he,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hs : scale i < b
  · simp only [hs,true_or,ite_true]
    linarith [hV i hi]
  · simp only [hs,false_or,ite_false,zero_add]
    split_ifs with hv
    · exact hv.le
    · exact hV i hi

lemma threshold_total_bound (O : Finset I) (scale V : I → ℝ) (b v ell : ℝ) (J : ℕ)
    (hb : 0 ≤ b) (hv : 0 ≤ v) (hell : 0 ≤ ell) (hV : ∀ i ∈ O, 0 ≤ V i) :
    (∑ a ∈ Finset.range J, (v*(1/2:ℝ)^a)*b*
      ((badCenters O scale V b (v*(1/2:ℝ)^a)).card+ell)) ≤
      2*v*b*((shortCenters O scale b).card+ell)+2*(∑ i ∈ O, V i) := by
  have hsplit (a : ℕ) :
      (v*(1/2:ℝ)^a)*b*((badCenters O scale V b (v*(1/2:ℝ)^a)).card+ell) ≤
      ((v*b)*(1/2:ℝ)^a)*((shortCenters O scale b).card+ell)+
      ∑ i ∈ O, if ((v*b)*(1/2:ℝ)^a) < V i then ((v*b)*(1/2:ℝ)^a) else 0 := by
    let z := (v*b)*(1/2:ℝ)^a
    have hz : 0 ≤ z := by dsimp [z]; positivity
    have he (P : I → Prop) [DecidablePred P] :
        z*((O.filter P).card:ℝ) = ∑ i ∈ O, if P i then z else 0 := by
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]; ring
    have ht : v*(1/2:ℝ)^a*b = z := by dsimp [z]; ring
    rw [ht,mul_add,mul_add,add_right_comm,add_le_add_iff_right]
    unfold badCenters shortCenters
    rw [he,he,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [ht]
    change (if scale i < b ∨ z < V i then z else 0) ≤
      (if scale i < b then z else 0)+(if z < V i then z else 0)
    by_cases hs : scale i < b <;> by_cases hv : z < V i <;> simp [hs,hv,hz]
  calc
    _ ≤ ∑ a ∈ Finset.range J, (((v*b)*(1/2:ℝ)^a)*
        ((shortCenters O scale b).card+ell)+
        ∑ i ∈ O, if ((v*b)*(1/2:ℝ)^a) < V i then ((v*b)*(1/2:ℝ)^a) else 0) :=
      Finset.sum_le_sum (fun a _ => hsplit a)
    _ = (∑ a ∈ Finset.range J, (v*b)*(1/2:ℝ)^a)*
        ((shortCenters O scale b).card+ell)+
        ∑ i ∈ O, ∑ a ∈ Finset.range J,
          if ((v*b)*(1/2:ℝ)^a) < V i then ((v*b)*(1/2:ℝ)^a) else 0 := by
      rw [Finset.sum_add_distrib,Finset.sum_mul,Finset.sum_comm]
    _ ≤ (2*(v*b))*((shortCenters O scale b).card+ell)+∑ i ∈ O, 2*V i := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (geometric_half_sum (v*b) (by positivity) J)
          (by positivity)
      · exact Finset.sum_le_sum (fun i hi => geometric_half_tail (V i) (v*b) (hV i hi)
          (by positivity) J)
    _ = _ := by rw [Finset.mul_sum]; ring

lemma threshold_pos {mu : ℝ} (hmu : 0 < mu) (a : ℕ) : 0 < threshold mu a := by
  unfold threshold; positivity
lemma threshold_le {mu : ℝ} (hmu : 0 ≤ mu) (a : ℕ) : threshold mu a ≤ mu/100 := by
  unfold threshold
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
lemma rounds_bound {mu : ℝ} (hmu : 0 < mu) : 40 ≤ (rounds mu:ℝ)*mu := by
  have h := Nat.le_ceil (40/mu)
  exact (div_le_iff₀ hmu).mp h
lemma rounds_pos {mu : ℝ} (hmu : 0 < mu) : 0 < rounds mu := by
  have h := rounds_bound hmu
  by_contra hh
  have hh0 : rounds mu = 0 := by omega
  simp only [hh0,Nat.cast_zero,zero_mul] at h
  norm_num at h

theorem selected_threshold (O : Finset I) (scale V : I → ℝ) (b P mu ell : ℝ)
    (hb : 0 < b) (hP : 0 < P) (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hell : 0 ≤ ell)
    (hV : ∀ i ∈ O, 0 ≤ V i) (hsum : (∑ i ∈ O, V i) ≤ 6*P)
    (hscale : b*(ell+(shortCenters O scale b).card) ≤ 10*P) :
    ∃ a ∈ Finset.range (rounds mu),
      threshold mu a*b*((badCenters O scale V b (threshold mu a)).card+ell) ≤ mu*P/2 := by
  have ht := threshold_total_bound O scale V b (mu/100) ell (rounds mu)
    hb.le (by positivity) hell hV
  have htotal : (∑ a ∈ Finset.range (rounds mu), threshold mu a*b*
      ((badCenters O scale V b (threshold mu a)).card+ell)) ≤ (12+mu/5)*P := by
    dsimp only [threshold]
    calc
      _ ≤ 2*(mu/100)*b*((shortCenters O scale b).card+ell)+2*(∑ i ∈ O, V i) := ht
      _ ≤ 2*(mu/100)*(10*P)+2*(6*P) := by
        apply add_le_add
        · nlinarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2*(mu/100) by positivity)]
        · linarith
      _ = _ := by ring
  by_contra h
  push Not at h
  have hlt : (rounds mu:ℝ)*(mu*P/2) <
      ∑ a ∈ Finset.range (rounds mu), threshold mu a*b*
        ((badCenters O scale V b (threshold mu a)).card+ell) := by
    have hn : (Finset.range (rounds mu)).Nonempty := Finset.nonempty_range_iff.mpr (Nat.ne_of_gt (rounds_pos hmu))
    have htlt := Finset.sum_lt_sum_of_nonempty hn (fun a ha => h a ha)
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using htlt
  have h40 := rounds_bound hmu
  have hlo : 20*P ≤ (rounds mu:ℝ)*(mu*P/2) := by nlinarith [mul_le_mul_of_nonneg_right h40 hP.le]
  have hup : (12+mu/5)*P ≤ (61/5:ℝ)*P := by nlinarith
  linarith

end MetricKMedianRecovery.Anchoring

end OAI
