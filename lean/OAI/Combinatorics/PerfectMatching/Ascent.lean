import OAI.Combinatorics.PerfectMatching.ObjectivePenalty

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

lemma q_pos {n : ℕ} (hn : 2 ≤ n) : 0 < q n := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change 0 < 1; omega⟩⟩

lemma D₀_pos (G : Input) (hn : 2 ≤ G.n) : 0 < D₀ G := by
  have hL : 0 < L G := by unfold L; positivity
  exact Nat.mul_pos (q_pos hn) (pow_pos (by omega) _)

lemma clip_sq_le {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) (t : ℝ) :
    (min 1 (max 0 t)-z)^2 ≤ (t-z)^2 := by
  by_cases ht : t ≤ 0
  · rw [max_eq_left ht, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg ht hz.1, sq_nonneg t]
  · have ht0 : 0 ≤ t := le_of_not_ge ht
    rw [max_eq_right ht0]
    by_cases ht1 : 1 ≤ t
    · rw [min_eq_left ht1]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (show 0 ≤ t+1-2*z by linarith [hz.2])]
    · rw [min_eq_right (le_of_not_ge ht1)]

lemma update_box (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) :
    entry (update G a r) e ∈ Set.Icc (0:ℤ) (D₀ G) := by
  rw [update, at_toTable]
  exact ⟨le_min (Int.natCast_nonneg _) (le_max_left _ _), min_le_left _ _⟩

lemma iterate_box (G : Input) (j : ℕ) (e : Pair G.n) :
    entry (iterate G j).numerators e ∈ Set.Icc (0:ℤ) (D₀ G) := by
  cases j with
  | zero => simp [iterate, initial, at_tabulate]
  | succ j => exact update_box G _ _ e

def point (G : Input) (j : ℕ) (e : Pair G.n) : ℝ :=
  (coordinates (D₀ G) (iterate G j).numerators e : ℝ)

def sampledValue (G : Input) (j : ℕ) : ℚ :=
  trialValue G (iterate G j).numerators (activeRow (D₀ G) (iterate G j).numerators)

lemma coordinates_cast {n : ℕ} (D : ℕ) (a : Table n ℤ) (e : Pair n) :
    (coordinates D a e : ℝ) = (↑(entry a e) : ℝ)/(D:ℝ) := by
  simp [coordinates]

lemma point_box (G : Input) (hn : 2 ≤ G.n) (j : ℕ) (e : Pair G.n) :
    point G j e ∈ Set.Icc (0:ℝ) 1 := by
  have hD : (0:ℝ) < D₀ G := by exact_mod_cast D₀_pos G hn
  have ha := iterate_box G j e
  have ha' : (↑(entry (iterate G j).numerators e) : ℝ) ∈ Set.Icc (0:ℝ) (D₀ G) :=
    ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
  rw [point, coordinates_cast]
  exact ⟨div_nonneg ha'.1 hD.le, (div_le_one hD).mpr ha'.2⟩

lemma point_zero (G : Input) (e : Pair G.n) : point G 0 e=0 := by
  simp [point, coordinates, iterate, initial, at_tabulate]

lemma point_succ (G : Input) (hn : 2 ≤ G.n) (j : ℕ) (e : Pair G.n) :
    point G (j+1) e = min 1 (max 0 (point G j e+
      (gradient G (iterate G j).numerators (activeRow (D₀ G) (iterate G j).numerators) e:ℝ)/(D₀ G:ℝ))) := by
  have hD : (0:ℝ) < D₀ G := by exact_mod_cast D₀_pos G hn
  simp only [point, iterate, step, coordinates_cast, update, at_toTable,
    Int.cast_min, Int.cast_max, Int.cast_natCast, Int.cast_zero, Int.cast_add]
  rw [← min_div_div_right hD.le, ← max_div_div_right hD.le]
  rw [div_self hD.ne', zero_div, add_div]

lemma sampledValue_correct (G : Input) (hn : 2 ≤ G.n) (heven : Even G.n) (j : ℕ) :
    (sampledValue G j:ℝ)=penalized G (point G j) :=
  trialValue_correct G hn heven (D₀_pos G hn) _ (fun e => (iterate_box G j e).1)

lemma best_spec (G : Input) (t : ℕ) :
    ∃ v : ℚ, (iterate G (t+1)).best=some v ∧
      (∃ j < t+1, sampledValue G j=v) ∧
      ∀ j < t+1, sampledValue G j≤v := by
  induction t with
  | zero =>
    refine ⟨sampledValue G 0, rfl, ⟨0, by omega, rfl⟩, ?_⟩
    intro j hj
    have : j=0 := by omega
    subst j; rfl
  | succ t ih =>
    obtain ⟨v, hv, ⟨i, hi, hiv⟩, hmax⟩ := ih
    refine ⟨max (sampledValue G (t+1)) v, ?_, ?_, ?_⟩
    · change some ((iterate G (t+1)).best.elim (sampledValue G (t+1))
        (max (sampledValue G (t+1)))) = _
      rw [hv]; rfl
    · by_cases h : v ≤ sampledValue G (t+1)
      · exact ⟨t+1, by omega, (max_eq_left h).symm⟩
      · exact ⟨i, by omega, hiv.trans (max_eq_right (le_of_not_ge h)).symm⟩
    · intro j hj
      by_cases h : j=t+1
      · subst j; exact le_max_left _ _
      · exact (hmax j (by omega)).trans (le_max_right _ _)

def squareDistance {I : Type*} [Fintype I] (x z : I → ℝ) : ℝ :=
  ∑ e, (x e-z e)^2

lemma squareDistance_nonneg {I : Type*} [Fintype I] (x z : I → ℝ) :
    0 ≤ squareDistance x z := sum_nonneg fun _e _ => sq_nonneg _

lemma squareDistance_zero_bound (G : Input) (z : Pair G.n → ℝ)
    (hz : ∀ e, z e∈Set.Icc (0:ℝ) 1) : squareDistance (point G 0) z ≤ q G.n := by
  calc
    _ ≤ ∑ _e : Pair G.n, (1:ℝ) := by
      apply sum_le_sum; intro e _
      rw [point_zero]; nlinarith [(hz e).1, (hz e).2]
    _ = _ := by simp [q]

lemma distance_step (G : Input) (hn : 2 ≤ G.n) (heven : Even G.n) (j : ℕ)
    (z : Pair G.n → ℝ) (hz : ∀ e,z e∈Set.Icc (0:ℝ) 1) :
    2*(penalized G z-penalized G (point G j)) ≤
      (D₀ G:ℝ)*(squareDistance (point G j) z-squareDistance (point G (j+1)) z)+1 := by
  let x := point G j
  let g := fun e => (gradient G (iterate G j).numerators
    (activeRow (D₀ G) (iterate G j).numerators) e:ℝ)
  let D : ℝ := D₀ G
  have hD : 0<D := by change 0<(D₀ G:ℝ); exact_mod_cast D₀_pos G hn
  have hs : squareDistance (point G (j+1)) z ≤ ∑ e,(x e+g e/D-z e)^2 := by
    apply sum_le_sum; intro e _
    rw [point_succ G hn]
    exact clip_sq_le (hz e) _
  have he : D*(∑ e,(x e+g e/D-z e)^2) = D*squareDistance x z+
      2*(∑ e,g e*(x e-z e))+(∑ e,(g e)^2)/D := by
    calc
      _ = ∑ e, (D*(x e-z e)^2+2*(g e*(x e-z e))+(g e)^2/D) := by
        rw [mul_sum]
        apply sum_congr rfl; intro e _
        field_simp; ring
      _ = _ := by simp only [sum_add_distrib, ← mul_sum, ← sum_div, squareDistance]
  have hb : (∑ e,(g e)^2)/D ≤ 1 := by
    apply (div_le_one hD).mpr
    exact gradient_square_bound G hn heven (D₀_pos G hn) _ (fun e => (iterate_box G j e).1)
  have hg := gradient_supergradient G hn heven (D₀_pos G hn) (iterate G j).numerators
    (fun e => (iterate_box G j e).1) z
  have hsign : (∑ e,g e*(x e-z e)) = -(∑ e,g e*(z e-x e)) := by
    rw [← sum_neg_distrib]; apply sum_congr rfl; intro e _; ring
  change penalized G z ≤ penalized G x+∑ e,g e*(z e-x e) at hg
  have hh := mul_le_mul_of_nonneg_left hs hD.le
  rw [he, hsign] at hh
  change 2*(penalized G z-penalized G x) ≤ D*(squareDistance x z-squareDistance (point G (j+1)) z)+1
  linarith

lemma trial_max_bound (G : Input) (hn : 2 ≤ G.n) (heven : Even G.n) :
    ∃ v : ℚ, (iterate G (q G.n*D₀ G)).best=some v ∧
      (∃ j < q G.n*D₀ G, sampledValue G j=v) ∧
      ∀ z : Pair G.n → ℝ, (∀ e,z e∈Set.Icc (0:ℝ) 1) →
        penalized G z ≤ (v:ℝ)+1 := by
  let T := q G.n*D₀ G
  have hT : 0<T := Nat.mul_pos (q_pos hn) (D₀_pos G hn)
  obtain ⟨v,hv,hatt,hmax⟩ := best_spec G (T-1)
  have heT : T-1+1=T := by omega
  rw [heT] at hv hatt hmax
  refine ⟨v,hv,hatt,?_⟩
  intro z hz
  have htR : (0:ℝ)<T := by exact_mod_cast hT
  have hsteps := sum_le_sum (s := range T) (fun j _ => distance_step G hn heven j z hz)
  have hilower : (T:ℝ)*(2*(penalized G z-(v:ℝ))) ≤
      ∑ j∈range T,2*(penalized G z-penalized G (point G j)) := by
    calc
      _ = ∑ _j∈range T,2*(penalized G z-(v:ℝ)) := by simp
      _ ≤ _ := by
        apply sum_le_sum; intro j hj
        have hjv : (sampledValue G j:ℝ)≤(v:ℝ) := by
          exact_mod_cast hmax j (mem_range.mp hj)
        rw [sampledValue_correct G hn heven] at hjv
        linarith
  have htel : (∑ j∈range T, ((D₀ G:ℝ)*
      (squareDistance (point G j) z-squareDistance (point G (j+1)) z)+1)) =
      (D₀ G:ℝ)*(squareDistance (point G 0) z-squareDistance (point G T) z)+T := by
    rw [sum_add_distrib,←mul_sum,sum_range_sub']
    simp
  rw [htel] at hsteps
  have hend := squareDistance_nonneg (point G T) z
  have hstart := squareDistance_zero_bound G z hz
  have hD : (0:ℝ)<D₀ G := by exact_mod_cast D₀_pos G hn
  have he : (T:ℝ)=(q G.n:ℝ)*(D₀ G:ℝ) := by dsimp [T]; norm_cast
  have hdist : (D₀ G:ℝ)*(squareDistance (point G 0) z-squareDistance (point G T) z)≤T := by
    rw [he]; nlinarith
  nlinarith

theorem R_objective_bracket (G : Input) (hn : 4 ≤ G.n) (heven : Even G.n) :
    (∃ y∈(completeGraph G.n).polytope,(R G:ℝ)≤objective G y) ∧
      ∀ z∈(completeGraph G.n).polytope,objective G z≤(R G:ℝ)+2 := by
  obtain ⟨v,hv,⟨j,_hj,hjv⟩,hbound⟩ := trial_max_bound G (by omega) heven
  have hR : (R G:ℝ)=(Int.floor (v:ℝ):ℝ) := by
    simp only [R,hv,Option.getD_some,Rat.floor_cast]
  have hfloor : (R G:ℝ)≤(v:ℝ) := by rw [hR]; exact Int.floor_le _
  have hvfloor : (v:ℝ)<(R G:ℝ)+1 := by rw [hR]; exact Int.lt_floor_add_one _
  constructor
  · obtain ⟨y,hy,hyval⟩ := exact_penalty G hn heven (point G j) (point_box G (by omega) j)
    refine ⟨y,hy,hfloor.trans ?_⟩
    rw [←hjv,sampledValue_correct G (by omega) heven]
    exact hyval
  · intro z hz
    have hh := hbound z ((completeGraph G.n).coordinate_mem_Icc hz)
    rw [penalized_feasible G heven hz] at hh
    linarith

end
end BinaryMatching.Algorithm
end

end OAI
