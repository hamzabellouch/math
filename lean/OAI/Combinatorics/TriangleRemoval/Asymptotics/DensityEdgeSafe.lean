import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TriangleDegreeMean
import OAI.Combinatorics.TriangleRemoval.Process.HistoryAlive
import OAI.Combinatorics.TriangleRemoval.Asymptotics.LogStepSandwich

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave
open Classical

def densityEdgeSafe (n : ℕ) (p η : ℝ) (G : Graph n) : Prop :=
  G ⊆ completeGraph n ∧ (G.card : ℝ) = (n : ℝ)^2*p/2 ∧
    ∀ e ∈ G, |(triangleDegree G e : ℝ)-n*p^2| ≤ η*(n*p^2)

lemma triangle_count_from_edge_degrees {n : ℕ} (G : Graph n) (D δ : ℝ)
    (hd : ∀ e ∈ G, |(triangleDegree G e : ℝ)-D| ≤ δ) :
    |3*(triangles G).card-(G.card : ℝ)*D| ≤ (G.card : ℝ)*δ := by
  have he : 3*(triangles G).card-(G.card : ℝ)*D =
      ∑ e ∈ G, ((triangleDegree G e : ℝ)-D) := by
    rw [Finset.sum_sub_distrib,triangle_degree_sum]
    simp
  rw [he]
  calc
    _ ≤ ∑ e ∈ G, |(triangleDegree G e : ℝ)-D| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ G, δ := Finset.sum_le_sum (fun e he => hd e he)
    _ = _ := by simp

lemma densityEdgeSafe_triangle_bounds {n : ℕ} {p η : ℝ} {G : Graph n}
    (h : densityEdgeSafe n p η G) :
    (n : ℝ)^3*p^3/6*(1-η) ≤ (triangles G).card ∧
      (triangles G).card ≤ (n : ℝ)^3*p^3/6*(1+η) := by
  have hc := triangle_count_from_edge_degrees G (n*p^2) (η*(n*p^2)) h.2.2
  rw [h.2.1] at hc
  obtain ⟨hl,hu⟩ := abs_le.mp hc
  constructor <;> nlinarith only [hl,hu]

lemma densityEdgeSafe_triangle_positive {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (hη : η ≤ 1/2) (h : densityEdgeSafe n p η G) :
    (triangles G).Nonempty := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := (densityEdgeSafe_triangle_bounds h).1
  have hfac : 0 < 1-η := by linarith
  have hpos : (0 : ℝ) < (triangles G).card :=
    lt_of_lt_of_le (by positivity) hq
  exact Finset.card_pos.mp (by exact_mod_cast hpos)

theorem densityEdgeSafe_intact_step {n : ℕ} {p η : ℝ} {G : Graph n}
    (hn : 0 < n) (hp : 0 < p) (_hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (h : densityEdgeSafe n p η G) (F : Graph n) :
    pmfMean (step G) (intact F) ≤ Real.exp
      (-((F.card : ℝ)*(6/(n : ℝ)^2/p))+2*(F.card : ℝ)*η*(6/(n : ℝ)^2/p)+
        (F.card : ℝ)^2*(2*(6/(n : ℝ)^2)/(n*p^3))) * intact F G := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ := densityEdgeSafe_triangle_positive hn hp hη1 h
  have hq : (0 : ℝ) < (triangles G).card := by exact_mod_cast hQ.card_pos
  obtain ⟨hlo,hhi⟩ := densityEdgeSafe_triangle_bounds h
  let Q₀ : ℝ := (n : ℝ)^3*p^3/6
  let lam : ℝ := 6/(n : ℝ)^2/p
  let D : ℝ := n*p^2
  have hQ₀ : 0 < Q₀ := by dsimp [Q₀]; positivity
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hlamQ : lam*Q₀ = D := by dsimp [lam,Q₀,D]; field_simp
  have hQl : Q₀/2 ≤ (triangles G).card := by
    have hm := mul_le_mul_of_nonneg_left hη1 hQ₀.le
    dsimp only [Q₀] at hm ⊢
    nlinarith only [hlo,hm]
  have hrec : 1/(triangles G).card ≤ 2*(6/(n : ℝ)^2)/(n*p^3) := by
    have hr : 1/(triangles G).card ≤ 2/Q₀ := by
      apply (div_le_div_iff₀ hq hQ₀).mpr
      linarith only [hQl]
    have he : 2/Q₀ = 2*(6/(n : ℝ)^2)/(n*p^3) := by dsimp [Q₀]; field_simp
    rwa [he] at hr
  have hlin : lam*(1-2*η) ≤ D*(1-η)/(triangles G).card := by
    apply (le_div_iff₀ hq).mpr
    have hh : lam*(triangles G).card ≤ D*(1+η) := by
      have hmul := mul_le_mul_of_nonneg_left hhi hlam.le
      change lam*(triangles G).card ≤ lam*(Q₀*(1+η)) at hmul
      rwa [← mul_assoc,hlamQ] at hmul
    have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ 1-2*η by linarith)
    have he : (1+η)*(1-2*η) ≤ 1-η := by nlinarith [sq_nonneg η]
    have he' := mul_le_mul_of_nonneg_left he hD.le
    nlinarith only [hm,he']
  have hexp : -((F.card : ℝ)*D-((F.card : ℝ)*(η*D)+(F.card : ℝ)^2))/(triangles G).card ≤
      -((F.card : ℝ)*lam)+2*(F.card : ℝ)*η*lam+
        (F.card : ℝ)^2*(2*(6/(n : ℝ)^2)/(n*p^3)) := by
    have ha := mul_le_mul_of_nonneg_left hlin (Nat.cast_nonneg F.card)
    have hb := mul_le_mul_of_nonneg_left hrec (sq_nonneg (F.card : ℝ))
    simp only [div_eq_mul_inv] at ha hb ⊢
    nlinarith only [ha,hb]
  have hb := triangle_intact_exponential_bound G F D (η*D) hQ h.2.2
  exact hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (intact_nonnegative F G))

theorem density_killed_survival {n : ℕ} (initial : PMF (Graph n))
    (p : ℕ → ℝ) (η : ℝ) (T j : ℕ) (hj : j ≤ T) (hn : 0 < n)
    (hp : ∀ i ≤ T, 0 < p i) (hs : ∀ i < T, p i = p (i+1)+6/(n : ℝ)^2)
    (hp0 : p 0 ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1/2) (F : Graph n) :
    pmfMean (historyLaw initial (fun _ => step) T j)
      (fun ω => if historyAlive (fun i => densityEdgeSafe n (p i) η) T j ω then
        intact F (ω (historyIndex T j)) else 0) ≤
      p j^F.card * Real.exp
        ((F.card : ℝ)*(1-p 0)/p 0+(F.card : ℝ)*(6/(n : ℝ)^2)/p j+
          2*(F.card : ℝ)*η*(-Real.log (p j))+(F.card : ℝ)^2/(n*p j^2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let b : ℝ := F.card
  let h : ℝ := 6/(n : ℝ)^2
  let rate : ℕ → ℝ := fun i => -b*(h/p i)+2*b*η*(h/p i)+b^2*(2*h/(n*p i^3))
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hk := triangle_killed_survival initial (fun i => densityEdgeSafe n (p i) η) F rate T j hj
    (fun i hi G hG => by
      simpa only [rate,b,h,neg_mul] using densityEdgeSafe_intact_step hn (hp i hi.le) hη hη1 hG F)
  have hsumb := density_survival_exponent_bound p n h b η j hnR hh hb hη
    (fun i hi => hp i (hi.trans hj)) (fun i hi => hs i (by omega)) hp0
  have hi : pmfMean initial (intact F) ≤ 1 := by
    calc
      _ ≤ pmfMean initial (fun _ => (1 : ℝ)) := by
        apply pmfMean_mono
        intro G _
        unfold intact
        split_ifs <;> norm_num
      _ = 1 := pmfMean_const _ _
  apply hk.trans
  calc
    _ ≤ Real.exp (∑ i ∈ Finset.range j, rate i) := by
      nlinarith only [mul_le_mul_of_nonneg_left hi (Real.exp_pos (∑ i ∈ Finset.range j, rate i)).le]
    _ ≤ Real.exp (b*Real.log (p j)+b*(1-p 0)/p 0+b*h/p j+
        2*b*η*(-Real.log (p j))+b^2/(n*p j^2)) := Real.exp_le_exp.mpr hsumb
    _ = _ := by
      have he : Real.exp (b*Real.log (p j)) = p j^F.card := by
        dsimp only [b]
        rw [Real.exp_nat_mul,Real.exp_log (hp j hj)]
      rw [show b*Real.log (p j)+b*(1-p 0)/p 0+b*h/p j+
          2*b*η*(-Real.log (p j))+b^2/(n*p j^2) =
          b*Real.log (p j)+(b*(1-p 0)/p 0+b*h/p j+
          2*b*η*(-Real.log (p j))+b^2/(n*p j^2)) by ring,Real.exp_add,he]

end SharpTerminalLeave
end
end

end OAI
