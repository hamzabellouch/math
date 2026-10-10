import OAI.Probability.LatticePassage.PassageRegularity

namespace OAI

namespace CompanionFPP
open MeasureTheory Real

lemma latticeDistance_triangle (x y z : Vertex) :
    latticeDistance x z ≤ latticeDistance x y + latticeDistance y z := by
  have h₁ := Int.natAbs_add_le (y.1-x.1) (z.1-y.1)
  have h₂ := Int.natAbs_add_le (y.2-x.2) (z.2-y.2)
  rw [show y.1-x.1+(z.1-y.1)=z.1-x.1 by ring] at h₁
  rw [show y.2-x.2+(z.2-y.2)=z.2-x.2 by ring] at h₂
  unfold latticeDistance
  omega

lemma latticeDistance_of_adj {x y : Vertex} (h : lattice.Adj x y) :
    latticeDistance x y = 1 := by
  change |x.1-y.1| + |x.2-y.2| = 1 at h
  have he : (latticeDistance x y : ℤ) = 1 := by
    simpa only [latticeDistance, Nat.cast_add, Int.natCast_natAbs, abs_sub_comm] using h
  exact_mod_cast he

theorem latticeDistance_le_length {x y : Vertex} (p : lattice.Walk x y) :
    latticeDistance x y ≤ p.length := by
  induction p with
  | nil => simp [latticeDistance]
  | @cons x y z h p ih =>
    have ht := latticeDistance_triangle x y z
    rw [latticeDistance_of_adj h] at ht
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem exact_coordinate_path (x y : Vertex) :
    ∃ p : lattice.Walk x y, p.IsPath ∧ p.length = latticeDistance x y := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  exact ⟨p,hp,le_antisymm hl (latticeDistance_le_length p)⟩

theorem passageTime_lower_tail (x y : Vertex) (hd : 1 ≤ latticeDistance x y)
    (t : ℝ) (ht : 0 ≤ t) :
    environmentLaw.real {ω : Environment | passageTime ω x y ≤ t} ≤
      (8/3 : ℝ)*exp (5*t)*(1/2 : ℝ)^latticeDistance x y := by
  have hsub : environmentLaw {ω : Environment | passageTime ω x y ≤ t} ≤
      environmentLaw {ω : Environment | ∃ a ∈ ({x} : Finset Vertex), ∃ b,
        ∃ p : lattice.Walk a b, p.IsPath ∧ latticeDistance x y ≤ p.length ∧ pathCost ω p ≤ t} := by
    apply measure_mono_ae
    filter_upwards [geodesics_exist] with ω hω
    intro hcost
    obtain ⟨p,hp,hc⟩ := hω x y
    exact ⟨x,Finset.mem_singleton_self x,y,p,hp,latticeDistance_le_length p,hc ▸ hcost⟩
  apply (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
  change environmentLaw.real _ ≤ _
  simpa only [Finset.card_singleton, Nat.cast_one, mul_one] using
    no_long_cheap_paths {x} (latticeDistance x y) hd t ht

theorem passageTime_small_linear_tail (x y : Vertex) (hd : 1 ≤ latticeDistance x y) :
    environmentLaw.real {ω : Environment |
      passageTime ω x y ≤ (log 2/10)*latticeDistance x y} ≤
      (8/3 : ℝ)*exp (-(log 2/2)*latticeDistance x y) := by
  apply (passageTime_lower_tail x y hd ((log 2/10)*latticeDistance x y) (by positivity)).trans_eq
  have hp : (1/2 : ℝ)^latticeDistance x y =
      exp (-((latticeDistance x y : ℝ)*log 2)) := by
    rw [exp_neg, exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
    simp [one_div]
  rw [hp, mul_assoc, ← exp_add]
  congr 2
  ring

end CompanionFPP

end OAI
