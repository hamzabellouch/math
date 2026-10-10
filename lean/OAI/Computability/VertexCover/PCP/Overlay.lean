import Mathlib
import OAI.Computability.VertexCover.PCP.DegreeReplacement
import OAI.Computability.VertexCover.PCP.ZigzagSpectral

namespace OAI

                                                                                

open scoped BigOperators

namespace UniqueGames.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

def originalPortGraph (G : ConstraintGraph V (V × D) A) : PortGraph V D where
  rot := G.reverse
  rot_involutive := G.reverse_involutive

def rotate (G : PortGraph V D) (H : PortGraph V E) :
    V × (D ⊕ E) → V × (D ⊕ E)
  | (v, Sum.inl d) => ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2)
  | (v, Sum.inr e) => ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2)

theorem rotate_involutive (G : PortGraph V D) (H : PortGraph V E) :
    Function.Involutive (rotate G H) := by
  rintro ⟨v, p⟩
  rcases p with d | e
  · exact congrArg (fun a : V × D => (a.1, (Sum.inl a.2 : D ⊕ E)))
      (G.rot_involutive (v, d))
  · exact congrArg (fun a : V × E => (a.1, (Sum.inr a.2 : D ⊕ E)))
      (H.rot_involutive (v, e))

def portGraph (G : PortGraph V D) (H : PortGraph V E) : PortGraph V (D ⊕ E) where
  rot :=
    { toFun := rotate G H
      invFun := rotate G H
      left_inv := rotate_involutive G H
      right_inv := rotate_involutive G H }
  rot_involutive := rotate_involutive G H

@[simp] theorem portGraph_rot_inl (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (d : D) :
    (portGraph G H).rot (v, Sum.inl d) =
      ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2) := rfl

@[simp] theorem portGraph_rot_inr (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (e : E) :
    (portGraph G H).rot (v, Sum.inr e) =
      ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2) := rfl

def constraintGraph (G : ConstraintGraph V (V × D) A) (H : PortGraph V E) :
    ConstraintGraph V (V × (D ⊕ E)) A where
  reverse := (portGraph (originalPortGraph G) H).rot
  reverse_involutive := (portGraph (originalPortGraph G) H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl d => G.accepts (p.1, d) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v, p⟩ a b
    rcases p with d | e
    · exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) : (constraintGraph G H).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) :
    originalPortGraph (constraintGraph G H) = portGraph (originalPortGraph G) H := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (htail : G.tail = Prod.fst)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inl d) =
      G.edgeSatisfied labeling (v, d) := by
  change G.accepts (v, d) (labeling v) (labeling (G.reverse (v, d)).1) =
    G.accepts (v, d) (labeling (G.tail (v, d)))
      (labeling (G.tail (G.reverse (v, d))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (labeling : V → A) (v : V) (e : E) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inr e) = true := rfl

theorem complete (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) (labeling : V → A)
    (h : ∀ a, G.edgeSatisfied labeling a = true) :
    ∀ a, (constraintGraph G H).edgeSatisfied labeling a = true := by
  rintro ⟨v, p⟩
  rcases p with d | e
  · rw [edgeSatisfied_inl G H htail]
    exact h (v, d)
  · rfl

theorem satisfiable_iff (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) :
    (constraintGraph G H).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling, h⟩
    refine ⟨labeling, ?_⟩
    rintro ⟨v, d⟩
    rw [← edgeSatisfied_inl G H htail]
    exact h (v, Sum.inl d)
  · rintro ⟨labeling, h⟩
    exact ⟨labeling, complete G H htail labeling h⟩

theorem rejectionCount_eq [Fintype V] [Fintype D] [Fintype E]
    (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) (labeling : V → A) :
    (constraintGraph G H).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  simp [edgeSatisfied_inl G H htail]

theorem card_ports [Fintype D] [Fintype E] :
    Fintype.card (D ⊕ E) = Fintype.card D + Fintype.card E := Fintype.card_sum

theorem card_darts [Fintype V] [Fintype D] [Fintype E] :
    Fintype.card (V × (D ⊕ E)) =
      Fintype.card (V × D) + Fintype.card (V × E) := by
  simp only [Fintype.card_prod, Fintype.card_sum, Nat.mul_add]

variable [Fintype V] [Fintype D] [Fintype E]

omit [Fintype V] in
                                                                                       
theorem operator_mix [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (f : V → ℝ) (v : V) :
    averagingOperator (portGraph G H) f v =
      (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator G f v +
      (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator H f v := by
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  change mean (fun p : D ⊕ E => f ((portGraph G H).rot (v, p)).1) = _
  rw [mean_eq_sum_div_card]
  simp only [Fintype.sum_sum_type, Fintype.card_sum, Nat.cast_add,
    portGraph_rot_inl, portGraph_rot_inr]
  unfold averagingOperator
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  field_simp [hd.ne', he.ne', (add_pos hd he).ne']

theorem energy_convex_mix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (f g : V → ℝ) :
    energy (fun v => a * f v + b * g v) ≤ a * energy f + b * energy g := by
  calc
    energy (fun v => a * f v + b * g v) ≤
        mean (fun v => a * (f v) ^ 2 + b * (g v) ^ 2) := by
      apply mean_mono
      intro v
      have hnormalize := congrArg (fun t : ℝ => t * (a * (f v) ^ 2 + b * (g v) ^ 2)) hab
      have hnonneg := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (f v - g v))
      nlinarith
    _ = a * energy f + b * energy g := by
      rw [mean_add, mean_mul_left, mean_mul_left]
      rfl

theorem energy_bound [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (lambda : ℝ)
    (certificate : SpectralCertificate H lambda) (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * lambda ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) * energy f := by
  let a : ℝ := (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  let b : ℝ := (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := add_pos hd he
  have ha : 0 ≤ a := div_nonneg hd.le hden.le
  have hb : 0 ≤ b := div_nonneg he.le hden.le
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div, div_self hden.ne']
  have hop : averagingOperator (portGraph G H) f =
      fun v => a * averagingOperator G f v + b * averagingOperator H f v := by
    funext v
    exact operator_mix G H f v
  calc
    energy (averagingOperator (portGraph G H) f) ≤
        a * energy (averagingOperator G f) + b * energy (averagingOperator H f) := by
      rw [hop]
      exact energy_convex_mix a b ha hb hab _ _
    _ ≤ a * energy f + b * (lambda ^ 2 * energy f) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (ZigzagSpectral.averaging_energy_le G f) ha)
        (mul_le_mul_of_nonneg_left (certificate.contraction f hf) hb)
    _ = _ := by
      dsimp [a, b]
      ring

theorem energy_bound_three_quarters [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ))
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤ (3 / 4 : ℝ) * energy f := by
  let _ : Nonempty E := Fintype.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one hpositive)
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  have he : (1 : ℝ) ≤ Fintype.card E := by exact_mod_cast hpositive
  have hd : (Fintype.card D : ℝ) = (Fintype.card E : ℝ) + 1 := by exact_mod_cast hdegree
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := by linarith
  have hcoefficient :
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * (1 / 2 : ℝ) ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) ≤ (3 / 4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (energy_bound G H (1 / 2) certificate f hf).trans
    (mul_le_mul_of_nonneg_right hcoefficient (energy_nonnegative f))

theorem spectralCertificate_seven_eighths [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ)) :
    SpectralCertificate (portGraph G H) (7 / 8 : ℝ) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction := by
    intro f hf
    exact (energy_bound_three_quarters G H hdegree hpositive certificate f hf).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (3 / 4 : ℝ) ≤ (7 / 8 : ℝ) ^ 2)
        (energy_nonnegative f))

theorem constraintGraph_spectralCertificate [Nonempty V]
    (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ)) :
    SpectralCertificate (originalPortGraph (constraintGraph G H)) (7 / 8 : ℝ) := by
  rw [constraintGraph_portGraph]
  exact spectralCertificate_seven_eighths (originalPortGraph G) H
    hdegree hpositive certificate

end UniqueGames.Foundations.PCP.Overlay

end OAI
