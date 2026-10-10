import OAI.Combinatorics.SharpThreshold.Model

namespace OAI

noncomputable section

namespace Problem313

lemma continuous_graphWeight {n : ℕ} (x : GraphConfig n) :
    Continuous (fun p : ℝ => graphWeight p x) := by
  classical
  unfold graphWeight
  apply continuous_finsetProd
  intro e he
  split_ifs <;> fun_prop

lemma continuous_graphMean {n : ℕ} (f : GraphConfig n → Bool) :
    Continuous (fun p : ℝ => graphMean p f) := by
  classical
  unfold graphMean
  apply continuous_finsetSum
  intro x hx
  exact (continuous_graphWeight x).mul continuous_const

lemma increasing_nontrivial_false {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    f (fun _ => false) = false := by
  obtain ⟨x, hx⟩ := hnt.2
  cases h : f (fun _ => false)
  · rfl
  · have hh := hmono (fun _ => false) x (by intro e he; cases he) h
    rw [hx] at hh
    contradiction

lemma increasing_nontrivial_true {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    f (fun _ => true) = true := by
  obtain ⟨x, hx⟩ := hnt.1
  exact hmono x (fun _ => true) (by intro e he; rfl) hx

lemma graphWeight_zero {n : ℕ} (x : GraphConfig n) :
    graphWeight 0 x = if x = (fun _ => false) then 1 else 0 := by
  classical
  by_cases hx : x = (fun _ => false)
  · subst x
    simp [graphWeight]
  · rw [ite_eq_right hx]
    obtain ⟨e, he⟩ : ∃ e, x e = true := by
      by_contra h
      apply hx
      funext e
      cases hxe : x e
      · rfl
      · exact False.elim (h ⟨e, hxe⟩)
    unfold graphWeight
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he]

lemma graphWeight_one {n : ℕ} (x : GraphConfig n) :
    graphWeight 1 x = if x = (fun _ => true) then 1 else 0 := by
  classical
  by_cases hx : x = (fun _ => true)
  · subst x
    simp [graphWeight]
  · rw [ite_eq_right hx]
    obtain ⟨e, he⟩ : ∃ e, x e = false := by
      by_contra h
      apply hx
      funext e
      cases hxe : x e
      · exact False.elim (h ⟨e, hxe⟩)
      · rfl
    unfold graphWeight
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he]

lemma graphMean_zero_eq {n : ℕ} (f : GraphConfig n → Bool) :
    graphMean 0 f = boolReal (f (fun _ => false)) := by
  classical
  simp [graphMean, graphWeight_zero]

lemma graphMean_one_eq {n : ℕ} (f : GraphConfig n → Bool) :
    graphMean 1 f = boolReal (f (fun _ => true)) := by
  classical
  simp [graphMean, graphWeight_one]

lemma graphMean_zero_of_increasing_nontrivial {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    graphMean 0 f = 0 := by
  rw [graphMean_zero_eq, increasing_nontrivial_false hmono hnt]
  rfl

lemma graphMean_one_of_increasing_nontrivial {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    graphMean 1 f = 1 := by
  rw [graphMean_one_eq, increasing_nontrivial_true hmono hnt]
  rfl

end Problem313

end

end OAI
