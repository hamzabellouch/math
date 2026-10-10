import Mathlib
import OAI.Geometry.Cannon.Flows.Subdivision

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set Finset MeasureTheory Filter

namespace CannonPairCost

attribute [local instance] Classical.propDecidable

lemma sum_measure_le_multiplicity {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (s : Finset I) (B : I → Set X)
    (hm : ∀ i ∈ s, MeasurableSet (B i)) {M : ℝ}
    (hM : ∀ x, (s.filter (fun i => x ∈ B i)).card ≤ M) :
    ∑ i ∈ s, μ.real (B i) ≤ M * μ.real univ := by
  classical
  have hint : ∀ i ∈ s, Integrable ((B i).indicator (fun _ => (1 : ℝ))) μ := by
    intro i hi
    exact (integrable_const 1).indicator (hm i hi)
  have hid : ∀ x, (∑ i ∈ s, (B i).indicator (fun _ => (1 : ℝ)) x) ≤ M := by
    intro x
    simpa only [Set.indicator_apply, Finset.sum_boole] using hM x
  have h := integral_mono (integrable_finsetSum s hint) (integrable_const M) hid
  rw [integral_finsetSum s hint, integral_const] at h
  have heq : (∑ i ∈ s, ∫ x, (B i).indicator (fun _ => (1 : ℝ)) x ∂μ) =
      ∑ i ∈ s, μ.real (B i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator_const _ (hm i hi)]
    simp
  rw [heq] at h
  simpa only [smul_eq_mul, mul_comm] using h

theorem finite_pair_bound {X I P : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (pairs : Finset P)
    (pay : P → I) (B : P → Set X) (Δ weight : I → ℝ)
    (hm : ∀ p ∈ pairs, MeasurableSet (B p))
    {c A Pstar M : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hP : 0 ≤ Pstar)
    (hweight : ∀ p ∈ pairs, Pstar ≤ weight (pay p))
    (hgap : ∀ p ∈ pairs, A * weight (pay p) ≤ Δ (pay p))
    (hcost : ∀ p ∈ pairs, c * Δ (pay p)^2 ≤ μ.real (B p))
    (hmult : ∀ x, (pairs.filter (fun p => x ∈ B p)).card ≤ M) :
    (pairs.card : ℝ) * c * A^2 * Pstar^2 ≤ M * μ.real univ := by
  have hlocal : ∀ p ∈ pairs, c * A^2 * Pstar^2 ≤ μ.real (B p) := by
    intro p hp
    have h₁ := mul_le_mul_of_nonneg_left (hweight p hp) hA
    have h₂ := h₁.trans (hgap p hp)
    have h₃ : (A * Pstar)^2 ≤ Δ (pay p)^2 :=
      sq_le_sq₀ (mul_nonneg hA hP) (le_trans (mul_nonneg hA hP) h₂) |>.mpr h₂
    calc
      _ = c * (A * Pstar)^2 := by ring
      _ ≤ c * Δ (pay p)^2 := mul_le_mul_of_nonneg_left h₃ hc
      _ ≤ _ := hcost p hp
  calc
    _ = ∑ p ∈ pairs, c * A^2 * Pstar^2 := by simp; ring
    _ ≤ ∑ p ∈ pairs, μ.real (B p) := Finset.sum_le_sum hlocal
    _ ≤ _ := sum_measure_le_multiplicity μ pairs B hm hmult

lemma cost_comparison {N F c A Pstar M mass η k : ℝ}
    (hc : 0 ≤ c) (_hA : 0 ≤ A) (hP : 0 ≤ Pstar) (hη : 0 ≤ η)
    (hN : 0 ≤ N) (hk : 0 < k)
    (hfar : η * N^2 ≤ F) (hclass : 1 / k ≤ N * Pstar)
    (hbound : F * c * A^2 * Pstar^2 ≤ M * mass) :
    η * c * A^2 ≤ M * mass * k^2 := by
  have hh : (1 / k)^2 ≤ (N * Pstar)^2 :=
    (sq_le_sq₀ (by positivity) (mul_nonneg hN hP)).mpr hclass
  have hlow : η * c * A^2 * (1 / k)^2 ≤ F * c * A^2 * Pstar^2 := by
    calc
      _ ≤ η * c * A^2 * (N * Pstar)^2 :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (η * N^2) * c * A^2 * Pstar^2 := by ring
      _ ≤ _ := by gcongr
  have h := mul_le_mul_of_nonneg_right (hlow.trans hbound) (sq_nonneg k)
  field_simp at h
  nlinarith

theorem not_frequently_exp_le_quadratic {c : ℝ} (hc : 0 < c)
    (C k₀ D : ℝ) :
    ¬ ∃ᶠ n : ℕ in atTop,
      Real.exp (c * n) ≤ C * (k₀ + D * n)^2 := by
  have h₀ := (isLittleO_pow_exp_pos_mul_atTop 0 hc).const_mul_left (C * k₀^2)
  have h₁ := (isLittleO_pow_exp_pos_mul_atTop 1 hc).const_mul_left (2*C*k₀*D)
  have h₂ := (isLittleO_pow_exp_pos_mul_atTop 2 hc).const_mul_left (C*D^2)
  have hpoly : (fun x : ℝ => C * (k₀ + D * x)^2) =o[atTop]
      (fun x => Real.exp (c * x)) := by
    have hsum := (h₀.add h₁).add h₂
    have heq : (fun x : ℝ => C * k₀^2 * x^0 + (2*C*k₀*D)*x^1 +
          (C*D^2)*x^2) = (fun x : ℝ => C * (k₀ + D*x)^2) := by
      funext x
      ring
    change (fun x : ℝ => C * k₀^2 * x^0 + (2*C*k₀*D)*x^1 +
      (C*D^2)*x^2) =o[atTop] (fun x => Real.exp (c*x)) at hsum
    rw [heq] at hsum
    exact hsum
  have hevent := hpoly.bound (show (0 : ℝ) < 1/2 by norm_num)
  have hevent' := tendsto_natCast_atTop_atTop.eventually hevent
  intro hfreq
  obtain ⟨n, hn, hn'⟩ := (hfreq.and_eventually hevent').exists
  have hepos := Real.exp_pos (c * (n : ℝ))
  simp only [Real.norm_eq_abs, abs_of_pos hepos] at hn'
  have hle := le_abs_self (C * (k₀ + D * (n : ℝ))^2)
  linarith

end CannonPairCost

namespace CannonPairCost

open Metric

theorem separated_level_energy {X ι : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (x : ι → X) (Δ : ι → ℝ)
    (r H C E : ℝ) (hr : 0 < r) (hh : 2*C < H) (hE : 0 ≤ E)
    (hsep : ∀ i j, i ≠ j → H*r ≤ dist (x i) (x j))
    (hloc : ∀ i, (Δ i)^2 ≤ E*μ.real (closedBall (x i) (C*r))) :
    ∑ i, (Δ i)^2 ≤ E*μ.real Set.univ := by
  classical
  have hmul (z : X) : ((univ.filter (fun i => z ∈ closedBall (x i) (C*r))).card : ℝ) ≤ 1 := by
    have hc : (univ.filter (fun i => z ∈ closedBall (x i) (C*r))).card ≤ 1 := by
      apply card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hd := hsep i j hij
      have hi' := mem_closedBall.mp (mem_filter.mp hi).2
      have hj' := mem_closedBall.mp (mem_filter.mp hj).2
      have ht := dist_triangle (x i) z (x j)
      rw [dist_comm (x i) z] at ht
      have hh' := mul_lt_mul_of_pos_right hh hr
      linarith
    exact_mod_cast hc
  have hm := sum_measure_le_multiplicity μ univ (fun i => closedBall (x i) (C*r))
    (fun _ _ => isClosed_closedBall.measurableSet) hmul
  calc
    _ ≤ ∑ i, E*μ.real (closedBall (x i) (C*r)) := sum_le_sum (fun i _ => hloc i)
    _ = E*∑ i, μ.real (closedBall (x i) (C*r)) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hm) hE

end CannonPairCost

end

namespace CannonNode.SourceConstruction

open Set Metric Finset Filter Topology CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

abbrev state (g : ℕ) := (S.rule.generation S.root g).state

abbrev good (v : SourceNode f x₀ ε ell c₀ (B+1) S.kmin) :=
  LiteralGood f (S.Y v) c₀ (radius ell (v.depth+160*(qdim+1)*n)) v.a v.b S.κ

noncomputable def flow := S.rule.flow S.root S.good

abbrev center (g : ℕ) (i : Fin (S.flow.size g)) := (S.state g i).center

abbrev len (g : ℕ) (i : Fin (S.flow.size g)) := (S.state g i).length

abbrev scale (g : ℕ) := radius ell (S.kmin+160*(qdim+1)*n*g)

abbrev step (g : ℕ) (i : Fin (S.flow.size (g+1))) := S.rule.probOf (S.rule.generation S.root g) i

lemma state_depth (g : ℕ) (i : Fin (S.flow.size g)) :
    (S.state g i).depth=S.kmin+160*(qdim+1)*n*g := by
  exact (S.rule.generation_depth S.root SourceNode.depth _ S.child_depth g i).trans
    (by rw [S.root_depth])

lemma scale_succ (g : ℕ) : S.scale (g+1)=radius ell (160*(qdim+1)*n)*S.scale g := by
  rw [scale,Nat.mul_succ,← Nat.add_assoc,radius_add]

lemma len_pos (g : ℕ) (i : Fin (S.flow.size g)) : 0 < S.len g i := (S.state g i).length_pos

lemma root_length (i : Fin (S.flow.size 0)) : S.len 0 i=S.root.length := rfl

lemma step_pos (g : ℕ) (i : Fin (S.flow.size (g+1))) : 0 < S.step g i := S.rule.prob_pos _ _

lemma weight_step (g : ℕ) (i : Fin (S.flow.size (g+1))) :
    S.flow.weight (g+1) i=S.step g i*S.flow.weight g (S.flow.parent g i) := rfl

lemma step_linear (g : ℕ) (i : Fin (S.flow.size (g+1))) :
    S.step g i*S.len g (S.flow.parent g i) ≤ Real.exp (-ell*n)*S.len (g+1) i :=
  S.child_linear _ _

lemma step_nested (g : ℕ) (i : Fin (S.flow.size (g+1))) :
    S.len (g+1) i ≤ S.len g (S.flow.parent g i) := S.child_length_le _ _

lemma weight_linear (g : ℕ) (i : Fin (S.flow.size g)) :
    S.root.length*S.flow.weight g i ≤ (Real.exp (-ell*n))^g*S.len g i :=
  S.flow.linear_transition_product S.step S.len S.root.length_pos.le (Real.exp_pos _).le
    S.root_length (fun g i => (S.step_pos g i).le) S.weight_step S.step_linear g i

lemma weight_conditional (g m : ℕ) (i : Fin (S.flow.size (g+m))) :
    S.flow.weight (g+m) i ≤ (Real.exp (-ell*n))^m*
      S.flow.weight g (S.flow.ancestor g m i) := by
  apply S.flow.conditional_weight (Real.exp_pos _).le
  intro j v
  have h := (S.step_linear j v).trans (mul_le_mul_of_nonneg_left (S.step_nested j v)
    (Real.exp_pos _).le)
  have hp : S.step j v ≤ Real.exp (-ell*n) :=
    (mul_le_mul_iff_left₀ (S.len_pos j (S.flow.parent j v))).mp h
  rw [S.weight_step]
  exact mul_le_mul_of_nonneg_right hp (S.flow.nonneg _ _)

lemma center_step (g : ℕ) (i : Fin (S.flow.size (g+1))) :
    dist (S.center (g+1) i) (S.center g (S.flow.parent g i)) ≤ (B+1)*S.scale g := by
  have h := S.child_move ((S.rule.generation S.root g).state (S.flow.parent g i))
    ((Fintype.equivFin (S.rule.Offspring (S.rule.generation S.root g))).symm i).2
  change dist (S.center (g+1) i) (S.center g (S.flow.parent g i)) ≤
    (B+1)*radius ell (S.state g (S.flow.parent g i)).depth at h
  rwa [S.state_depth] at h

lemma centers_separated (hθ : radius ell (160*(qdim+1)*n) < 1/4)
    (hB : 0 ≤ B+1) (hH : 4*(B+1) < H) :
    ∀ g i j, i ≠ j → H*S.scale g ≤ dist (S.center g i) (S.center g j) := by
  apply S.flow.centers_separated S.center S.scale (B+1) H (radius ell (160*(qdim+1)*n))
    (fun g => (radius_pos _ _).le) S.scale_succ
  · have hHp : 0 < H := by linarith only [hB,hH]
    nlinarith only [hθ,hB,hH,hHp]
  · intro i j hij
    change Fin 1 at i j
    exact (hij (Subsingleton.elim (α := Fin 1) i j)).elim
  · exact S.center_step
  · intro g i j hp hij
    have hs := S.rule.generation_siblings S.root SourceNode.center
      (fun v => H*radius ell (v.depth+160*(qdim+1)*n))
      (fun v i j hij => (S.child_sep v i j hij).le) g i j hp hij
    change H*radius ell ((S.state g (S.flow.parent g i)).depth+160*(qdim+1)*n) ≤
      dist (S.center (g+1) i) (S.center (g+1) j) at hs
    rw [S.state_depth] at hs
    simpa only [scale,Nat.mul_succ,Nat.add_assoc] using hs

lemma descendant_displacement (hθ : radius ell (160*(qdim+1)*n) < 1/4)
    (hB : 0 ≤ B+1) (g m : ℕ) (i : Fin (S.flow.size (g+m))) :
    dist (S.center (g+m) i) (S.center g (S.flow.ancestor g m i)) ≤ 2*(B+1)*S.scale g := by
  have h := S.flow.descendant_displacement S.center S.scale (B+1) (2*(B+1))
    (radius ell (160*(qdim+1)*n)) (fun g => (radius_pos _ _).le)
    (by nlinarith only [hθ,hB]) S.scale_succ S.center_step g m i
  have hp := mul_nonneg (by linarith only [hB] : 0 ≤ 2*(B+1)) (show 0 ≤ S.scale (g+m) from (radius_pos _ _).le)
  linarith only [h,hp]

lemma step_quadratic (g : ℕ) (i : Fin (S.flow.size (g+1))) :
    S.step g i*Real.exp ((160*(qdim+1)*ell*n)*
      (if S.flow.good g (S.flow.parent g i) then -(1/20:ℝ) else 1/2))*
      (S.len g (S.flow.parent g i))^2 ≤ (S.len (g+1) i)^2 := by
  let v := S.state g (S.flow.parent g i)
  let j := ((Fintype.equivFin (S.rule.Offspring (S.rule.generation S.root g))).symm i).2
  have h := S.child_quadratic v j
  have he (t : ℝ) : Real.exp (-t)*Real.exp t=1 := by rw [← Real.exp_add]; simp

  by_cases hg : S.good v
  · simp only [ite_eq_left hg] at h
    change S.step g i*S.len g (S.flow.parent g i)^2 ≤
      Real.exp (8*(qdim+1)*ell*n)*S.len (g+1) i^2 at h
    have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(8*(qdim+1)*ell*n))).le
    have heq : (160*(qdim+1)*ell*(n:ℝ))*(-(1/20:ℝ))=-(8*(qdim+1)*ell*n) := by ring
    change S.step g i*Real.exp ((160*(qdim+1)*ell*n)*(if S.good v then _ else _))*_ ≤ _
    rw [ite_eq_left hg,heq]
    calc
      _ = Real.exp (-(8*(qdim+1)*ell*n))*(S.step g i*S.len g (S.flow.parent g i)^2) := by ring
      _ ≤ _ := hh
      _ = _ := by rw [← mul_assoc,he,one_mul]
  · simp only [ite_eq_right hg] at h
    change S.step g i*S.len g (S.flow.parent g i)^2 ≤
      Real.exp (-((80*(qdim+1):ℝ)*ell*n))*S.len (g+1) i^2 at h
    have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos ((80*(qdim+1):ℝ)*ell*n)).le
    have heq : (160*(qdim+1)*ell*(n:ℝ))*(1/2:ℝ)=(80*(qdim+1):ℝ)*ell*n := by ring
    change S.step g i*Real.exp ((160*(qdim+1)*ell*n)*(if S.good v then _ else _))*_ ≤ _
    rw [ite_eq_right hg,heq]
    calc
      _ = Real.exp ((80*(qdim+1):ℝ)*ell*n)*(S.step g i*S.len g (S.flow.parent g i)^2) := by ring
      _ ≤ _ := hh
      _ = _ := by rw [← mul_assoc, mul_comm (Real.exp _),he,one_mul]

end CannonNode.SourceConstruction

namespace CannonNode.SourceConstruction

open Set Metric Finset MeasureTheory CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

lemma weight_bound (g : ℕ) (i : Fin (S.flow.size g)) :
    S.flow.weight g i ≤ (Real.exp (-ell*n))^g := by
  have hlen : S.len g i ≤ S.root.length :=
    S.rule.generation_property S.root (fun v => v.length ≤ S.root.length) le_rfl
      (fun v j hv => (S.child_length_le v j).trans hv) g i
  have h := (S.weight_linear g i).trans
    (mul_le_mul_of_nonneg_left hlen (pow_nonneg (Real.exp_pos _).le g))
  rw [mul_comm ((Real.exp (-ell*n))^g) S.root.length] at h
  exact (mul_le_mul_iff_right₀ S.root.length_pos).mp h

lemma len_lt_one (g : ℕ) (i : Fin (S.flow.size g)) : S.len g i < 1 := by
  let v := S.state g i
  change v.b-v.a < 1
  linarith only [v.apos,v.bone]

lemma center_mem (hB : 0 ≤ B+1) (g : ℕ) (i : Fin (S.flow.size g)) :
    S.center g i ∈ closedBall x₀ ε := (S.state g i).center_mem hB

lemma level_energy [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (Cμ E : ℝ) (hE : 0 ≤ E)
    (hB : 0 ≤ B+1) (hc₀ : 0 ≤ c₀)
    (hθ : radius ell (160*(qdim+1)*n) < 1/4) (hH : 4*(B+1) < H)
    (hHμ : 2*(Cμ*c₀) < H)
    (hf : ∀ x ∈ closedBall x₀ ε, ∀ r : ℝ, 0 < r → r ≤ ρ →
      ContinuousOn f (closedBall x (c₀*r)))
    (hpair : ∀ x ∈ closedBall x₀ ε, ∀ r : ℝ, 0 < r → r ≤ ρ →
      ∀ y ∈ closedBall x (c₀*r), ∀ z ∈ closedBall x (c₀*r),
        (f y-f z)^2 ≤ E*μ.real (closedBall x (Cμ*(c₀*r)))) :
    ∀ g, ∑ i, (S.len g i)^2 ≤ E*μ.real univ := by
  intro g
  apply CannonPairCost.separated_level_energy μ (S.center g) (S.len g) (S.scale g) H
    (Cμ*c₀) E (radius_pos _ _) hHμ hE (S.centers_separated hθ hB hH g)
  intro i
  let v := S.state g i
  have hr : 0 < S.scale g := radius_pos _ _
  have hsmall : S.scale g ≤ ρ := by
    have hh := S.small v.depth v.lowerDepth
    simpa only [v,S.state_depth] using hh
  have hx := S.center_mem hB g i
  obtain ⟨⟨z,hz,hzv⟩,⟨y,hy,hyv⟩⟩ := ball_extrema (mul_nonneg hc₀ hr.le)
    (hf (S.center g i) hx (S.scale g) hr hsmall)
  have hs : lower f (S.center g i) (c₀*S.scale g) ≤ v.a ∧
      v.b ≤ upper f (S.center g i) (c₀*S.scale g) := by
    simpa only [v,S.state_depth] using v.straddle
  have hlen : S.len g i ≤ f y-f z := by
    change v.b-v.a ≤ _
    rw [hyv,hzv]
    linarith only [hs.1,hs.2]
  have hsq := pow_le_pow_left₀ (S.len_pos g i).le hlen 2
  have hp := hpair _ hx _ hr hsmall y hy z hz
  exact hsq.trans (by simpa only [mul_assoc] using hp)

theorem arbitrarily_late_good (hell : 0 < ell) (hn : 0 < n)
    (E : ℝ) (henergy : ∀ g, ∑ i, (S.len g i)^2 ≤ E) :
    ∀ N : ℕ, ∃ g ≥ N, (1/2:ℝ) ≤ S.flow.goodMass g := by
  apply S.flow.good_levels_of_transitions S.step S.len S.root.length_pos
    (show 0 < (160*(qdim+1):ℝ)*ell*n by positivity)
    S.root_length (fun g i => (S.step_pos g i).le) S.weight_step S.step_quadratic henergy

end CannonNode.SourceConstruction

end

section

section

section

section

open Set Metric Filter Topology

namespace CannonMagnification

theorem preimage_distance_bound {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x z₀ z : X) (r C L e d : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C) (he : 0 < e) (hd : 0 < d)
    (hexp : Expansion h x r C L)
    (hdiam : ∀ y z : X, dist y z ≤ 1)
    (hz₀ : d ≤ dist x z₀) (hz : e ≤ dist z (h z₀)) :
    dist x (h.symm z) ≤ (C/(e*d))*r := by
  have hh := (hexp (h.symm z) z₀).1
  rw [h.apply_symm_apply] at hh
  have h₁ : e*dist x (h.symm z)*d ≤
      dist z (h z₀)*max r (dist x (h.symm z))*max r (dist x z₀) := by
    apply mul_le_mul
    · exact mul_le_mul hz (le_max_right _ _) dist_nonneg (dist_nonneg)
    · exact hz₀.trans (le_max_right _ _)
    · exact hd.le
    · positivity
  have h₂ : C*r*dist (h.symm z) z₀ ≤ C*r := by
    exact (mul_le_mul_of_nonneg_left (hdiam _ _) (mul_nonneg hC hr.le)).trans_eq (mul_one _)
  have hh' := h₁.trans (hh.trans h₂)
  have hh'' : dist x (h.symm z) ≤ (C*r)/(e*d) := by
    apply (le_div_iff₀ (mul_pos he hd)).mpr
    calc
      dist x (h.symm z)*(e*d) = e*dist x (h.symm z)*d := by ring
      _ ≤ C*r := hh'
  exact hh''.trans_eq (by ring)

theorem inverse_lipschitz_on_preimages {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x z w : X) (r C L B : ℝ)
    (hr : 0 < r) (hL : 0 ≤ L) (hexp : Expansion h x r C L)
    (hz : dist x (h.symm z) ≤ B*r) (hw : dist x (h.symm w) ≤ B*r) :
    dist (h.symm z) (h.symm w) ≤ (L*(max 1 B)^2)*r*dist z w := by
  have hb : 0 ≤ max 1 B := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
  have hmax (v : X) (hv : dist x v ≤ B*r) : max r (dist x v) ≤ max 1 B*r := by
    apply max_le
    · simpa using mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) B) hr.le
    · exact hv.trans (mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) B) hr.le)
  have hh := (hexp (h.symm z) (h.symm w)).2
  rw [h.apply_symm_apply,h.apply_symm_apply] at hh
  have hprod : L*dist z w*max r (dist x (h.symm z))*max r (dist x (h.symm w)) ≤
      L*dist z w*(max 1 B*r)*(max 1 B*r) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (hmax _ hz) (mul_nonneg hL dist_nonneg)
    · exact hmax _ hw
    · exact hr.le.trans (le_max_left _ _)
    · positivity
  have hh' : r*dist (h.symm z) (h.symm w) ≤ r*((L*(max 1 B)^2)*r*dist z w) :=
    (hh.trans hprod).trans_eq (by ring)
  exact (mul_le_mul_iff_right₀ hr).mp hh'

theorem image_ball_avoids_puncture {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x z₀ y : X) (r C L d : ℝ)
    (hr : 0 < r) (hL : 0 < L) (_hd : 0 < d) (hrd : r ≤ d/2)
    (hexp : Expansion h x r C L) (hdiam : ∀ y z : X, dist y z ≤ 1)
    (hz₀ : d ≤ dist x z₀) (hy : dist x y ≤ r) :
    d/(2*L) ≤ dist (h y) (h z₀) := by
  have hdone : d ≤ 1 := hz₀.trans (hdiam _ _)
  have hrone : r ≤ 1 := by linarith
  have hfar : d/2 ≤ dist y z₀ := by
    have hh := dist_triangle x y z₀
    linarith
  have hh := (hexp y z₀).2
  rw [max_eq_left hy] at hh
  have hmax : max r (dist x z₀) ≤ 1 := max_le hrone (hdiam _ _)
  have hbound : L*dist (h y) (h z₀)*r*max r (dist x z₀) ≤
      L*dist (h y) (h z₀)*r := by
    exact (mul_le_mul_of_nonneg_left hmax (by positivity)).trans_eq (mul_one _)
  have heq : dist y z₀ ≤ L*dist (h y) (h z₀) := by
    have hh' : r*dist y z₀ ≤ r*(L*dist (h y) (h z₀)) :=
      (hh.trans hbound).trans_eq (by ring)
    exact (mul_le_mul_iff_right₀ hr).mp hh'
  apply (div_le_iff₀ (mul_pos (by norm_num) hL)).mpr
  nlinarith

end CannonMagnification

end

namespace CannonMagnification

open Set Metric

def denominator {X : Type*} [MetricSpace X] (x : X) (R : ℝ) (y : X) : ℝ :=
  max R (dist x y)

lemma denominator_triangle {X : Type*} [MetricSpace X] (x y z : X) (R : ℝ) :
    denominator x R z ≤ denominator x R y+dist y z := by
  apply max_le
  · exact (le_max_left _ _).trans (le_add_of_nonneg_right dist_nonneg)
  · exact (dist_triangle x y z).trans (add_le_add (le_max_right _ _) le_rfl)

theorem puncture_bounds {X : Type*} [MetricSpace X] (h : X ≃ₜ X)
    (x z₀ : X) (R C L d : ℝ) (hR : 0 < R) (hC : 0 ≤ C) (hL : 0 < L)
    (hd : 0 < d) (hRone : R ≤ 1) (hz₀ : d ≤ dist x z₀)
    (hdiam : ∀ y z : X, dist y z ≤ 1) (hexp : Expansion h x R C L) :
    (∀ y, dist (h y) (h z₀)*denominator x R y ≤ (C/d)*R) ∧
    (∀ y, denominator x R y ≤ d/2 →
      R ≤ (2*L/d)*dist (h y) (h z₀)*denominator x R y) := by
  constructor
  · intro y
    have hh := (hexp y z₀).1
    have hm : dist (h y) (h z₀)*max R (dist x y)*d ≤
        dist (h y) (h z₀)*max R (dist x y)*max R (dist x z₀) :=
      mul_le_mul_of_nonneg_left (hz₀.trans (le_max_right _ _)) (by positivity)
    have ht : C*R*dist y z₀ ≤ C*R :=
      (mul_le_mul_of_nonneg_left (hdiam y z₀) (mul_nonneg hC hR.le)).trans_eq (mul_one _)
    have hh' := hm.trans (hh.trans ht)
    calc
      _ ≤ C*R/d := (le_div_iff₀ hd).mpr hh'
      _ = _ := by ring
  · intro y hy
    have hxy : dist x y ≤ d/2 := (le_max_right _ _).trans hy
    have hdist : d/2 ≤ dist y z₀ := by linarith only [dist_triangle x y z₀,hz₀,hxy]
    have hh := (hexp y z₀).2
    have hmax : max R (dist x z₀) ≤ 1 := max_le hRone (hdiam _ _)
    have hm : L*dist (h y) (h z₀)*max R (dist x y)*max R (dist x z₀) ≤
        L*dist (h y) (h z₀)*max R (dist x y) :=
      (mul_le_mul_of_nonneg_left hmax (by positivity)).trans_eq (mul_one _)
    have hdR := mul_le_mul_of_nonneg_left hdist hR.le
    have hh' := hdR.trans (hh.trans hm)
    calc
      R ≤ 2*(L*dist (h y) (h z₀)*max R (dist x y))/d :=
        (le_div_iff₀ hd).mpr (by linarith only [hh'])
      _ = _ := by dsimp [denominator]; ring

theorem cost_ball_geometry {X : Type*} [MetricSpace X] (h : X ≃ₜ X)
    (x p p' : X) (R C L U V cutoff A B S t : ℝ)
    (hR : 0 < R) (hC : 0 ≤ C) (hL : 0 ≤ L) (hU : 0 < U) (hV : 0 < V)
    (hA : 0 < A) (hB : 0 < B) (hS : 0 < S) (ht : 0 < t) (htone : t ≤ 1)
    (hexp : Expansion h x R C L)
    (hupper : ∀ y, dist (h y) p*denominator x R y ≤ U*R)
    (hlower : ∀ y, denominator x R y ≤ cutoff →
      R ≤ V*dist (h y) p*denominator x R y)
    (hscale : R = dist p' p*t)
    (hfar : 2*A*R ≤ dist p' p)
    (hlocal : U*t ≤ cutoff)
    (hcoef : 2*L*A*U^2 ≤ S)
    (hsmall : 2*V*B*S*t ≤ 1) :
    let z := h.symm p'
    let s := S*t^2
    h.symm '' closedBall p' (A*R) ⊆ closedBall z s ∧
    h '' closedBall z (B*s) ⊆ closedBall p' ((2*C*V^2*B*S)*R) ∧
    closedBall z (B*s) ⊆ closedBall x ((U+B*S)*t) := by
  dsimp only
  let z := h.symm p'
  let δ := dist p' p
  have hδ : 0 < δ := by
    change 0 < dist p' p
    nlinarith only [hscale,hR,ht,dist_nonneg (x:=p') (y:=p)]
  have hz : h z = p' := h.apply_symm_apply _
  have hDznon : 0 < denominator x R z := hR.trans_le (le_max_left _ _)
  have hDz : denominator x R z ≤ U*t := by
    have hh : δ*denominator x R z ≤ δ*(U*t) := by
      calc
        _ ≤ U*R := by simpa only [δ,hz] using hupper z
        _ = _ := by rw [hscale]; dsimp [δ]; ring
    exact (mul_le_mul_iff_right₀ hδ).mp hh
  have htDz : t ≤ V*denominator x R z := by
    have hh : δ*t ≤ δ*(V*denominator x R z) := by
      calc
        _ = R := hscale.symm
        _ ≤ V*dist (h z) p*denominator x R z := hlower z (hDz.trans hlocal)
        _ = _ := by rw [hz]; dsimp [δ]; ring
    exact (mul_le_mul_iff_right₀ hδ).mp hh
  have hrad : 2*(B*(S*t^2)) ≤ denominator x R z := by
    have hh := mul_le_mul_of_nonneg_right hsmall ht.le
    have hh' : V*(2*(B*(S*t^2))) ≤ V*denominator x R z := by
      calc
        _ ≤ t := by nlinarith only [hh]
        _ ≤ _ := htDz
    exact (mul_le_mul_iff_right₀ hV).mp hh'
  constructor
  · rintro y ⟨w,hw,rfl⟩
    let y := h.symm w
    have hy : h y = w := h.apply_symm_apply _
    have hwδ : δ/2 ≤ dist w p := by
      have hh := dist_triangle p' w p
      have hw' := mem_closedBall.mp hw
      rw [dist_comm w p'] at hw'
      dsimp [δ]
      linarith only [hh,hw',hfar]
    have hDy : denominator x R y ≤ 2*U*t := by
      have hDypos : 0 ≤ denominator x R y := hR.le.trans (le_max_left _ _)
      have hh : δ/2*denominator x R y ≤ U*(δ*t) := by
        calc
          _ ≤ dist w p*denominator x R y := mul_le_mul_of_nonneg_right hwδ hDypos
          _ ≤ U*R := by simpa only [hy] using hupper y
          _ = _ := by rw [hscale]
      apply (mul_le_mul_iff_right₀ hδ).mp
      nlinarith only [hh]
    have hh := (hexp y z).2
    change R*dist y z ≤ L*dist (h y) (h z)*denominator x R y*denominator x R z at hh
    rw [hy,hz] at hh
    have hw' := mem_closedBall.mp hw
    have hm : L*dist w p'*denominator x R y*denominator x R z ≤
        L*(A*R)*(2*U*t)*(U*t) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hw' hL
        · exact hDy
        · exact hR.le.trans (le_max_left _ _)
        · positivity
      · exact hDz
      · exact hDznon.le
      · positivity
    have hh' : R*dist y z ≤ R*(2*L*A*U^2*t^2) :=
      (hh.trans hm).trans_eq (by ring)
    have hdist := (mul_le_mul_iff_right₀ hR).mp hh'
    apply mem_closedBall.mpr
    exact hdist.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
  constructor
  · rintro w ⟨y,hy,rfl⟩
    have hyz := mem_closedBall.mp hy
    have hDy : denominator x R z/2 ≤ denominator x R y := by
      have hh := denominator_triangle x y z R
      linarith only [hh,hyz,hrad]
    have htDy : t ≤ 2*V*denominator x R y := by
      have hh := mul_le_mul_of_nonneg_left hDy hV.le
      linarith only [hh,htDz]
    have htprod : t^2 ≤ 2*V^2*denominator x R y*denominator x R z := by
      calc
        t^2 = t*t := by ring
        _ ≤ (2*V*denominator x R y)*(V*denominator x R z) :=
          mul_le_mul htDy htDz ht.le (ht.le.trans htDy)
        _ = _ := by ring
    have hh := (hexp y z).1
    change dist (h y) (h z)*denominator x R y*denominator x R z ≤ C*R*dist y z at hh
    rw [hz] at hh
    have hdistnon := dist_nonneg (x:=h y) (y:=p')
    have hm := mul_le_mul_of_nonneg_left htprod hdistnon
    have hE := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 2*V^2)
    have hradE := mul_le_mul_of_nonneg_left hyz (by positivity : 0 ≤ 2*V^2*C*R)
    have hall : t^2*dist (h y) p' ≤ t^2*((2*C*V^2*B*S)*R) := by
      nlinarith only [hm,hE,hradE]
    exact mem_closedBall.mpr ((mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp hall)
  · intro y hy
    have hyz := mem_closedBall.mp hy
    have hxy := dist_triangle x z y
    rw [dist_comm z y] at hxy
    have hxz : dist x z ≤ U*t := (le_max_right _ _).trans hDz
    have htsq : t^2 ≤ t := by nlinarith only [ht,htone]
    have hm := mul_le_mul_of_nonneg_left htsq (by positivity : 0 ≤ B*S)
    apply mem_closedBall.mpr
    rw [dist_comm]
    nlinarith only [hxy,hxz,hyz,hm]

end CannonMagnification

end

end
end
end
end
end
end
end
end
end
end

end OAI
