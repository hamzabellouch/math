import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import OAI.Computability.UniqueGames.PCP.AlphabetRetractionLemmas
import OAI.Computability.UniqueGames.PCP.ExpandersLemmas
import OAI.Computability.UniqueGames.PCP.InitialGraphLemmas

namespace OAI

section

/-!
# Actual graph squares and zigzag products

Rotations operate on actual vertex-port pairs. All returned ports are retained,
including ports belonging to loops and parallel edges. Each construction is a
palindrome of involutions and hence defines a reversible regular port graph.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

/-- Regard a checked involution as a permutation with the same inverse. -/
def involutionEquiv {A : Type*} (f : A → A) (hf : Function.Involutive f) : A ≃ A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

/-- A palindrome of two involutions is itself an involution. -/
theorem palindrome_involutive {A : Type*} (B P : A ≃ A)
    (hB : Function.Involutive B) (hP : Function.Involutive P) :
    Function.Involutive (B.trans (P.trans B)) := by
  intro x
  change B (P (B (B (P (B x))))) = x
  rw [hB, hP, hB]

/-- Cross an original edge using the first port; retain its return port. -/
def squareFirst (G : PortGraph V D) (s : V × (D × D)) : V × (D × D) :=
  let step := G.rot (s.1, s.2.1)
  (step.1, (step.2, s.2.2))

theorem squareFirst_involutive (G : PortGraph V D) : Function.Involutive (squareFirst G) := by
  rintro ⟨v, d₁, d₂⟩
  change ((G.rot (G.rot (v, d₁))).1, ((G.rot (G.rot (v, d₁))).2, d₂)) =
    (v, (d₁, d₂))
  rw [G.rot_involutive]

def squareSwap (s : V × (D × D)) : V × (D × D) := (s.1, (s.2.2, s.2.1))

theorem squareSwap_involutive : Function.Involutive (squareSwap (V := V) (D := D)) := by
  rintro ⟨v, d₁, d₂⟩
  rfl

/-- The actual graph square. The two return ports appear in reverse order. -/
def square (G : PortGraph V D) : PortGraph V (D × D) := by
  let B := involutionEquiv (squareFirst G) (squareFirst_involutive G)
  let P := involutionEquiv (squareSwap (V := V) (D := D)) squareSwap_involutive
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (squareFirst_involutive G) squareSwap_involutive }

@[simp] theorem square_rot_apply (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    (square G).rot (v, (d₁, d₂)) =
      let first := G.rot (v, d₁)
      let second := G.rot (first.1, d₂)
      (second.1, (second.2, first.2)) := rfl

@[simp] theorem square_next (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    next (square G) v (d₁, d₂) = next G (next G v d₁) d₂ := rfl

/-- One inner step in a cloud, retaining its return port and the unused port. -/
def cloudFirst (H : PortGraph D E) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) :=
  let step := H.rot (s.1.2, s.2.1)
  ((s.1.1, step.1), (step.2, s.2.2))

theorem cloudFirst_involutive (H : PortGraph D E) :
    Function.Involutive (cloudFirst (V := V) H) := by
  rintro ⟨⟨v, d⟩, ⟨e₁, e₂⟩⟩
  change ((v, (H.rot (H.rot (d, e₁))).1), ((H.rot (H.rot (d, e₁))).2, e₂)) =
    ((v, d), (e₁, e₂))
  rw [H.rot_involutive]

/-- Cross the outer graph edge and swap the two inner ports. -/
def crossCloud (G : PortGraph V D) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) := (G.rot s.1, (s.2.2, s.2.1))

theorem crossCloud_involutive (G : PortGraph V D) :
    Function.Involutive (crossCloud (E := E) G) := by
  rintro ⟨x, e₁, e₂⟩
  change (G.rot (G.rot x), (e₁, e₂)) = (x, (e₁, e₂))
  rw [G.rot_involutive]

/-- The actual zigzag product: inner step, outer edge, inner step. -/
def zigzag (G : PortGraph V D) (H : PortGraph D E) : PortGraph (V × D) (E × E) := by
  let B := involutionEquiv (cloudFirst (V := V) H) (cloudFirst_involutive H)
  let P := involutionEquiv (crossCloud (E := E) G) (crossCloud_involutive G)
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (cloudFirst_involutive H) (crossCloud_involutive G) }

@[simp] theorem zigzag_rot_apply (G : PortGraph V D) (H : PortGraph D E)
    (v : V) (d : D) (e₁ e₂ : E) :
    (zigzag G H).rot ((v, d), (e₁, e₂)) =
      let first := H.rot (d, e₁)
      let middle := G.rot (v, first.1)
      let last := H.rot (middle.2, e₂)
      ((middle.1, last.1), (last.2, first.2)) := rfl

theorem natCard_square_ports : Nat.card (D × D) = Nat.card D ^ 2 := by
  simp [Nat.card_prod, pow_two]

theorem natCard_square_edges :
    Nat.card (Edge V (D × D)) = Nat.card V * Nat.card D ^ 2 := by
  simp [Edge, Nat.card_prod, pow_two]

theorem natCard_zigzag_vertices :
    Nat.card (V × D) = Nat.card V * Nat.card D := Nat.card_prod V D

theorem natCard_zigzag_ports : Nat.card (E × E) = Nat.card E ^ 2 := by
  simp [Nat.card_prod, pow_two]

theorem natCard_zigzag_edges :
    Nat.card (Edge (V × D) (E × E)) =
      Nat.card V * Nat.card D * Nat.card E ^ 2 := by
  simp [Edge, Nat.card_prod, pow_two]

/-! ## Exact averaging operators -/

noncomputable section

/-- Average only the inner cloud coordinate, keeping the outer vertex fixed. -/
def cloudOperator [Fintype E] (H : PortGraph D E) (f : V × D → ℝ) (x : V × D) : ℝ :=
  SpectralReturn.mean (fun e => f (x.1, (H.rot (x.2, e)).1))

/-- The permutation on cloud vertices induced by the actual outer rotation. -/
def graphPermutation (G : PortGraph V D) (f : V × D → ℝ) (x : V × D) : ℝ :=
  f (G.rot x)

/-- Uniform averaging on the graph square is two original averaging steps. -/
theorem averagingOperator_square [Fintype D] (G : PortGraph V D) (f : V → ℝ) :
    SpectralReturn.averagingOperator (square G) f =
      SpectralReturn.averagingOperator G (SpectralReturn.averagingOperator G f) := by
  funext v
  let w : D × D → ℝ := fun ds => f (G.rot ((G.rot (v, ds.1)).1, ds.2)).1
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun d₁ => SpectralReturn.mean (fun d₂ => w (d₁, d₂)))
  exact SpectralReturn.mean_prod w

/-- The zigzag operator is precisely inner average, outer permutation, inner
average. This factorization follows from the actual rotation formula. -/
theorem averagingOperator_zigzag [Fintype E] (G : PortGraph V D)
    (H : PortGraph D E) (f : V × D → ℝ) :
    SpectralReturn.averagingOperator (zigzag G H) f =
      cloudOperator H (graphPermutation G (cloudOperator H f)) := by
  funext x
  rcases x with ⟨v, d⟩
  let w : E × E → ℝ := fun es =>
    let first := H.rot (d, es.1)
    let middle := G.rot (v, first.1)
    let last := H.rot (middle.2, es.2)
    f (middle.1, last.1)
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun e₁ => SpectralReturn.mean (fun e₂ => w (e₁, e₂)))
  exact SpectralReturn.mean_prod w

end

end UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs

end

section

/-!
# Energy contraction for the actual zigzag graph

The proof splits a function into its cloud average and its cloud-centered
part. All operators are the actual graph averages from `ZigzagGraphs`.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ZigzagSpectral

open PoweringWalks SpectralReturn ZigzagGraphs

noncomputable section

variable {V D E : Type*}

def cloudMean [Fintype D] (f : V × D → ℝ) (v : V) : ℝ :=
  mean (fun d => f (v, d))

def liftCloud (f : V → ℝ) (x : V × D) : ℝ := f x.1

def projection [Fintype D] (f : V × D → ℝ) : V × D → ℝ :=
  liftCloud (cloudMean f)

def centered [Fintype D] (f : V × D → ℝ) : V × D → ℝ := f - projection f

theorem mean_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    mean (liftCloud (D := D) f) = mean f := by
  change mean (fun x : V × D => f x.1) = mean f
  rw [mean_prod]
  simp only [mean_const]

theorem energy_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    energy (liftCloud (D := D) f) = energy f :=
  mean_liftCloud (D := D) (fun v => f v ^ 2)

theorem mean_cloudMean [Fintype V] [Fintype D] (f : V × D → ℝ) :
    mean (cloudMean f) = mean f := (mean_prod f).symm

theorem energy_prod [Fintype V] [Fintype D] (f : V × D → ℝ) :
    energy f = mean (fun v => energy (fun d => f (v, d))) :=
  mean_prod (fun x => f x ^ 2)

theorem cloudMean_centered_zero [Fintype D] [Nonempty D]
    (f : V × D → ℝ) (v : V) : cloudMean (centered f) v = 0 := by
  change mean (fun d => f (v, d) - cloudMean f v) = 0
  rw [mean_sub, mean_const]
  exact sub_self _

theorem energy_centered_eq_sub [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) = energy f - energy (projection f) := by
  have hpoint (v : V) : energy (fun d => centered f (v, d)) =
      energy (fun d => f (v, d)) - (cloudMean f v) ^ 2 := by
    change energy (fun d => f (v, d) - cloudMean f v) = _
    rw [energy_sub_const]
    change energy (fun d => f (v, d)) - 2 * cloudMean f v * cloudMean f v +
      (cloudMean f v) ^ 2 = _
    ring
  have hproj : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  calc
    energy (centered f) = mean (fun v => energy (fun d => centered f (v, d))) :=
      energy_prod _
    _ = mean (fun v => energy (fun d => f (v, d)) - (cloudMean f v) ^ 2) := by
      congr 1
      funext v
      exact hpoint v
    _ = mean (fun v => energy (fun d => f (v, d))) -
        mean (fun v => (cloudMean f v) ^ 2) := mean_sub _ _
    _ = energy f - energy (projection f) := by
      rw [← energy_prod f, hproj]
      rfl

theorem projection_energy_decomposition [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy f = energy (projection f) + energy (centered f) := by
  rw [energy_centered_eq_sub]
  ring

theorem energy_projection_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (projection f) ≤ energy f := by
  have h := projection_energy_decomposition f
  have hn := energy_nonnegative (centered f)
  linarith

theorem energy_centered_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) ≤ energy f := by
  rw [energy_centered_eq_sub]
  exact sub_le_self _ (energy_nonnegative _)

/-- Squared normalized mean is bounded by normalized squared energy. -/
theorem mean_sq_le_energy {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    mean f ^ 2 ≤ energy f := by
  have h := correlation_sq_le f (fun _ => 1)
  simpa [correlation, energy] using h

/-- Every actual reversible regular graph average is an energy contraction. -/
theorem averaging_energy_le [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) : energy (averagingOperator G f) ≤ energy f := by
  calc
    energy (averagingOperator G f) ≤ mean (averagingOperator G (fun v => f v ^ 2)) := by
      apply mean_mono
      intro v
      exact mean_sq_le_energy (fun d => f (G.rot (v, d)).1)
    _ = energy f := mean_operator G _

theorem cloudOperator_add [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f + g) = cloudOperator H f + cloudOperator H g := by
  funext x
  exact mean_add _ _

theorem cloudOperator_sub [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f - g) = cloudOperator H f - cloudOperator H g := by
  funext x
  exact mean_sub _ _

theorem cloudOperator_projection [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) : cloudOperator H (projection f) = projection f := by
  funext x
  change mean (fun _ : E => cloudMean f x.1) = cloudMean f x.1
  exact mean_const _

theorem cloudOperator_centered [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) :
    cloudOperator H (centered f) = cloudOperator H f - projection f := by
  unfold centered
  rw [cloudOperator_sub, cloudOperator_projection]

theorem graphPermutation_energy [Fintype V] [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) : energy (graphPermutation G f) = energy f :=
  mean_equiv G.rot (fun x => f x ^ 2)

theorem cloud_energy_le [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (f : V × D → ℝ) :
    energy (cloudOperator H f) ≤ energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => energy (fun d => f (v, d))) :=
      mean_mono (fun v => averaging_energy_le H _)
    _ = energy f := (energy_prod f).symm

theorem cloud_centered_contraction [Fintype V] [Fintype D] [Fintype E]
    (H : PortGraph D E) (lambda : ℝ) (hH : SpectralCertificate H lambda)
    (f : V × D → ℝ) (hzero : ∀ v, cloudMean f v = 0) :
    energy (cloudOperator H f) ≤ lambda ^ 2 * energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => lambda ^ 2 * energy (fun d => f (v, d))) :=
      mean_mono (fun v => hH.contraction _ (hzero v))
    _ = lambda ^ 2 * mean (fun v => energy (fun d => f (v, d))) := mean_mul_left _ _
    _ = lambda ^ 2 * energy f := by rw [← energy_prod f]

theorem cloud_residual_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (lambda : ℝ)
    (hH : SpectralCertificate H lambda) (f : V × D → ℝ) :
    energy (cloudOperator H f - projection f) ≤ lambda ^ 2 * energy f := by
  rw [← cloudOperator_centered H f]
  exact (cloud_centered_contraction H lambda hH (centered f)
    (cloudMean_centered_zero f)).trans
      (mul_le_mul_of_nonneg_left (energy_centered_le f) (sq_nonneg lambda))

/-- Cloud projection of the outer permutation is the genuine outer graph
average when its input is constant on each cloud. -/
theorem projection_graphPermutation_projection [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) :
    projection (graphPermutation G (projection f)) =
      liftCloud (averagingOperator G (cloudMean f)) := rfl

theorem projected_outer_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (projection (graphPermutation G (projection f))) ≤
      lambda ^ 2 * energy (projection f) := by
  have hzero : mean (cloudMean f) = 0 := (mean_cloudMean f).trans hf
  have hleft : energy (projection (graphPermutation G (projection f))) =
      energy (averagingOperator G (cloudMean f)) := by
    rw [projection_graphPermutation_projection]
    exact energy_liftCloud _
  have hright : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  rw [hleft, hright]
  exact hG.contraction _ hzero

theorem energy_add_three_le {A : Type*} [Fintype A] (a b c : A → ℝ) :
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := by
  calc
    energy (a + b + c) ≤ mean (fun x => 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)) := by
      apply mean_mono
      intro x
      change (a x + b x + c x) ^ 2 ≤ 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)
      nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x - c x), sq_nonneg (b x - c x)]
    _ = 3 * (energy a + energy b + energy c) := by
      rw [mean_mul_left, mean_add, mean_add]
      rfl

/-- A deliberately loose bound sufficient for the expander iteration. -/
theorem zigzag_energy_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph D E) (lambdaG lambdaH : ℝ)
    (hG : SpectralCertificate G lambdaG) (hH : SpectralCertificate H lambdaH)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (zigzag G H) f) ≤
      3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
  let u := projection f
  let v := centered f
  let a := projection (graphPermutation G u)
  let b := cloudOperator H (graphPermutation G u) - a
  let c := cloudOperator H (graphPermutation G (cloudOperator H v))
  have hfactor : averagingOperator (zigzag G H) f = a + b + c := by
    rw [averagingOperator_zigzag]
    have hf' : f = u + v := by
      funext x
      change f x = projection f x + (f x - projection f x)
      ring
    have hbu : cloudOperator H u = u := cloudOperator_projection H f
    have hbf : cloudOperator H f = u + cloudOperator H v := by
      rw [hf', cloudOperator_add, hbu]
    rw [hbf]
    have hp : graphPermutation G (u + cloudOperator H v) =
        graphPermutation G u + graphPermutation G (cloudOperator H v) := rfl
    rw [hp, cloudOperator_add]
    change cloudOperator H (graphPermutation G u) + c =
      a + (cloudOperator H (graphPermutation G u) - a) + c
    funext x
    change cloudOperator H (graphPermutation G u) x + c x =
      a x + (cloudOperator H (graphPermutation G u) x - a x) + c x
    ring
  have ha : energy a ≤ lambdaG ^ 2 * energy u := projected_outer_bound G lambdaG hG f hf
  have hb : energy b ≤ lambdaH ^ 2 * energy u := by
    have h := cloud_residual_bound H lambdaH hH (graphPermutation G u)
    simpa only [graphPermutation_energy] using h
  have hc : energy c ≤ lambdaH ^ 2 * energy v := by
    calc
      energy c ≤ energy (graphPermutation G (cloudOperator H v)) := cloud_energy_le H _
      _ = energy (cloudOperator H v) := graphPermutation_energy G _
      _ ≤ lambdaH ^ 2 * energy v :=
        cloud_centered_contraction H lambdaH hH v (cloudMean_centered_zero f)
  rw [hfactor]
  calc
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := energy_add_three_le _ _ _
    _ ≤ 3 * (lambdaG ^ 2 * energy u + lambdaH ^ 2 * energy u + lambdaH ^ 2 * energy v) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha hb) hc) (by norm_num)
    _ ≤ 3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
      have hdecomp : energy f = energy u + energy v := projection_energy_decomposition f
      rw [hdecomp]
      have hn := mul_nonneg (sq_nonneg lambdaG) (energy_nonnegative v)
      nlinarith

theorem square_certificate [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda) :
    SpectralCertificate (square G) (lambda ^ 2) where
  nonnegative := sq_nonneg lambda
  lt_one := by
    have hprod := mul_pos (sub_pos.mpr hG.lt_one)
      (show 0 < 1 + lambda by linarith [hG.nonnegative])
    nlinarith
  contraction f hf := by
    rw [averagingOperator_square]
    calc
      energy (averagingOperator G (averagingOperator G f)) ≤
          lambda ^ 2 * energy (averagingOperator G f) :=
        hG.contraction _ ((mean_operator G f).trans hf)
      _ ≤ lambda ^ 2 * (lambda ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (hG.contraction f hf) (sq_nonneg lambda)
      _ = (lambda ^ 2) ^ 2 * energy f := by ring

/-- Squaring an outer graph with certificate `1/2`, then zigzagging with an
inner graph with certificate `1/100`, again has certificate `1/2`. -/
theorem square_zigzag_halfCertificate [Fintype V] [Fintype D] [Fintype E]
    [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph (D × D) E)
    (hG : SpectralCertificate G (1 / 2)) (hH : SpectralCertificate H (1 / 100)) :
    SpectralCertificate (zigzag (square G) H) (1 / 2) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := zigzag_energy_bound (square G) H ((1 / 2 : ℝ) ^ 2) (1 / 100)
      (square_certificate G (1 / 2) hG) hH f hf
    have hcoef : 3 * (((1 / 2 : ℝ) ^ 2) ^ 2 + (1 / 100) ^ 2) ≤ (1 / 2 : ℝ) ^ 2 := by
      norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end

end UniqueGamesTheorem.Foundations.PCP.ZigzagSpectral

end

section

/-!
# A concrete finite family from the Cayley base

The initial graph has one vertex and the fixed number of loop ports. Each
subsequent graph is the actual square-and-zigzag construction. Consequently
the vertex sizes are exact powers of one fixed integer, including size one.
The finite base is selected from the proved existence theorem.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

abbrev Port := BasePort × BasePort
abbrev CloudPort := Port × Port
def growth : Nat := baseDegree ^ 4

theorem card_port : Fintype.card Port = baseDegree ^ 2 := by
  change Fintype.card (BasePort × BasePort) = baseDegree ^ 2
  rw [Fintype.card_prod, card_basePort, pow_two]

theorem card_cloudPort : Fintype.card CloudPort = growth := by
  change Fintype.card (Port × Port) = growth
  rw [Fintype.card_prod, card_port]
  unfold growth
  ring

theorem growth_gt_one : 1 < growth := by
  norm_num [growth, baseDegree, initialDegree, basePower]

theorem port_degree_ge_eight : 8 ≤ Fintype.card Port := by
  rw [card_port]
  norm_num [baseDegree, initialDegree, basePower]

noncomputable def baseVertexEquiv : BaseVertex ≃ CloudPort :=
  Fintype.equivOfCardEq (card_baseVertex.trans card_cloudPort.symm)

noncomputable def baseOnCloud : PortGraph CloudPort BasePort :=
  GraphTransport.reindex (Classical.choose exists_baseGraph) baseVertexEquiv (Equiv.refl _)

theorem baseOnCloud_certificate : SpectralCertificate baseOnCloud (1 / 100 : ℝ) :=
  GraphTransport.reindex_spectralCertificate _ _ _ _ (Classical.choose_spec exists_baseGraph)

def Vertex : Nat → Type
  | 0 => Unit
  | n + 1 => Vertex n × CloudPort

instance vertexFintype (n : Nat) : Fintype (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI : Fintype (Vertex n) := ih
    change Fintype (Vertex n × CloudPort)
    infer_instance

instance basePortNonempty : Nonempty BasePort :=
  ⟨fun _ => ⟨0, by norm_num [initialQuarterDegree]⟩⟩

instance vertexNonempty (n : Nat) : Nonempty (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ n ih =>
    let : Nonempty (Vertex n) := ih
    change Nonempty (Vertex n × CloudPort)
    infer_instance

/-- The family is a recursive rotation algorithm when its fixed base is given. -/
def graph (H : PortGraph CloudPort BasePort) : (n : Nat) → PortGraph (Vertex n) Port
  | 0 => { rot := Equiv.refl _, rot_involutive := fun _ => rfl }
  | n + 1 => ZigzagGraphs.zigzag (ZigzagGraphs.square (graph H n)) H

theorem graph_certificate (H : PortGraph CloudPort BasePort)
    (hH : SpectralCertificate H (1 / 100 : ℝ)) (n : Nat) :
    SpectralCertificate (graph H n) (1 / 2 : ℝ) := by
  induction n with
  | zero =>
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro f hf
    have hm : mean f = f () := by
      change mean (fun x : Unit => f x) = f ()
      have hfun : (fun x : Unit => f x) = fun _ : Unit => f () := by
        funext x
        cases x
        rfl
      rw [hfun, mean_const]
    have hz : f = fun _ => 0 := by
      funext x
      cases x
      exact hm.symm.trans hf
    rw [hz]
    simp [energy, mean, averagingOperator]
  | succ n ih =>
    exact ZigzagSpectral.square_zigzag_halfCertificate (graph H n) H ih hH

noncomputable def family (n : Nat) : PortGraph (Vertex n) Port := graph baseOnCloud n

theorem family_certificate (n : Nat) : SpectralCertificate (family n) (1 / 2 : ℝ) :=
  graph_certificate baseOnCloud baseOnCloud_certificate n

theorem card_vertex (n : Nat) : Fintype.card (Vertex n) = growth ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Vertex n × CloudPort) = growth ^ (n + 1)
    rw [Fintype.card_prod, ih, card_cloudPort, pow_succ]

/-- The least geometric level covering a requested size. `Nat.clog` is the
ordinary finite ceiling logarithm algorithm. -/
def level (k : Nat) : Nat := Nat.clog growth k

def size (k : Nat) : Nat := growth ^ level k

theorem le_size (k : Nat) : k ≤ size k := Nat.le_pow_clog growth_gt_one k

theorem size_le_mul {k : Nat} (hk : 0 < k) : size k ≤ growth * k := by
  by_cases hk1 : k = 1
  · subst k
    simpa [size, level] using growth_gt_one.le
  · have hk2 : 1 < k := by omega
    have hl : 0 < level k := Nat.clog_pos growth_gt_one hk2
    have hp : growth ^ (level k).pred < k :=
      Nat.pow_pred_clog_lt_self growth_gt_one hk2
    have he : (level k).pred + 1 = level k := Nat.succ_pred_eq_of_pos hl
    calc
      size k = growth ^ ((level k).pred + 1) := by rw [he]; rfl
      _ = growth * growth ^ (level k).pred := by rw [pow_succ, Nat.mul_comm]
      _ ≤ growth * k := Nat.mul_le_mul_left growth hp.le

theorem padded_family_size {k : Nat} (hk : 0 < k) :
    k ≤ Fintype.card (Vertex (level k)) ∧
      Fintype.card (Vertex (level k)) ≤ growth * k := by
  rw [card_vertex]
  exact ⟨le_size k, size_le_mul hk⟩

end UniqueGamesTheorem.Foundations.PCP.ExpanderFamily

end

section

/-!
# Padding actual tail fibers to the geometric graph-family sizes

Every nonempty cloud is padded to the next family size. Empty clouds stay
empty, so their old vertices do not create new darts. Explicit equivalences
identify padded tail fibers and partition all darts by their original tails.
These facts give the global size bound without an expansion assumption.
-/

namespace UniqueGamesTheorem.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

/-- Leave empty clouds empty; pad every positive size to a geometric level. -/
def paddedSize (k : Nat) : Nat := if k = 0 then 0 else ExpanderFamily.size k

@[simp] theorem paddedSize_zero : paddedSize 0 = 0 := rfl

theorem paddedSize_of_pos {k : Nat} (hk : 0 < k) :
    paddedSize k = ExpanderFamily.size k := by
  simp only [paddedSize, ite_eq_right (Nat.ne_of_gt hk)]

theorem le_paddedSize (k : Nat) : k ≤ paddedSize k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [paddedSize, ite_eq_right hk]
    exact ExpanderFamily.le_size k

theorem paddedSize_le_mul (k : Nat) : paddedSize k ≤ ExpanderFamily.growth * k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [paddedSize, ite_eq_right hk]
    exact ExpanderFamily.size_le_mul (Nat.pos_of_ne_zero hk)

/-- The actual padded tail fiber contains old darts and exactly the dummy
darts indexed by that tail, with transport along the sigma index equality. -/
def paddedCloudEquiv (G : ConstraintGraph V E A) (dummy : V → Type*) (v : V) :
    Cloud (paddedGraph G dummy) v ≃ Cloud G v ⊕ dummy v where
  toFun := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · exact Sum.inl ⟨e, he⟩
    · change w = v at he
      cases he
      exact Sum.inr d
  invFun := fun z => match z with
    | Sum.inl e => ⟨Sum.inl e.val, e.property⟩
    | Sum.inr d => ⟨Sum.inr ⟨v, d⟩, rfl⟩
  left_inv := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · rfl
    · change w = v at he
      cases he
      rfl
  right_inv := by
    intro z
    cases z <;> rfl

/-- Every original dart occurs in exactly one cloud. -/
def dartCloudEquiv (G : ConstraintGraph V E A) : E ≃ Σ v : V, Cloud G v where
  toFun e := ⟨G.tail e, ⟨e, rfl⟩⟩
  invFun z := z.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨e, he⟩⟩
    cases he
    rfl

section Finite

variable [Fintype V] [DecidableEq V] [Fintype E]

theorem sum_card_cloud (G : ConstraintGraph V E A) :
    (∑ v, Fintype.card (Cloud G v)) = Fintype.card E := by
  simpa only [Fintype.card_sigma] using (Fintype.card_congr (dartCloudEquiv G)).symm

theorem card_padded_cloud (G : ConstraintGraph V E A) (dummy : V → Type*)
    [∀ v, Fintype (dummy v)] (v : V) :
    Fintype.card (Cloud (paddedGraph G dummy) v) =
      Fintype.card (Cloud G v) + Fintype.card (dummy v) := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (paddedCloudEquiv G dummy v)

/-- The precise number of always-accepting loop darts to add at each vertex. -/
abbrev dummy (G : ConstraintGraph V E A) (v : V) :=
  Fin (paddedSize (Fintype.card (Cloud G v)) - Fintype.card (Cloud G v))

theorem card_cloud (G : ConstraintGraph V E A) (v : V) :
    Fintype.card (Cloud (paddedGraph G (dummy G)) v) =
      paddedSize (Fintype.card (Cloud G v)) := by
  rw [card_padded_cloud]
  simp only [dummy, Fintype.card_fin]
  exact Nat.add_sub_of_le (le_paddedSize _)

omit [Fintype V] in
theorem card_dummy_of_empty (G : ConstraintGraph V E A) (v : V)
    (hk : Fintype.card (Cloud G v) = 0) : Fintype.card (dummy G v) = 0 := by
  simp [dummy, hk]

theorem card_cloud_of_empty (G : ConstraintGraph V E A) (v : V)
    (hk : Fintype.card (Cloud G v) = 0) :
    Fintype.card (Cloud (paddedGraph G (dummy G)) v) = 0 := by
  rw [card_cloud, hk, paddedSize_zero]

theorem card_cloud_eq_family (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    Fintype.card (Cloud (paddedGraph G (dummy G)) v) =
      Fintype.card (ExpanderFamily.Vertex
        (ExpanderFamily.level (Fintype.card (Cloud G v)))) := by
  rw [card_cloud, paddedSize_of_pos hk, ExpanderFamily.card_vertex]
  rfl

/-- Exact count over all padded tail fibers, including empty original fibers. -/
theorem card_paddedDart_eq_sum (G : ConstraintGraph V E A) :
    Fintype.card (PaddedDart G (dummy G)) =
      ∑ v, paddedSize (Fintype.card (Cloud G v)) := by
  calc
    Fintype.card (PaddedDart G (dummy G)) =
        ∑ v, Fintype.card (Cloud (paddedGraph G (dummy G)) v) :=
      (sum_card_cloud (paddedGraph G (dummy G))).symm
    _ = ∑ v, paddedSize (Fintype.card (Cloud G v)) := by
      apply Finset.sum_congr rfl
      intro v _
      exact card_cloud G v

/-- Padding increases the total number of darts by at most the fixed family
growth factor, independent of the number of empty vertices. -/
theorem card_paddedDart_le (G : ConstraintGraph V E A) :
    Fintype.card (PaddedDart G (dummy G)) ≤ ExpanderFamily.growth * Fintype.card E := by
  rw [card_paddedDart_eq_sum]
  calc
    (∑ v, paddedSize (Fintype.card (Cloud G v))) ≤
        ∑ v, ExpanderFamily.growth * Fintype.card (Cloud G v) := by
      apply Finset.sum_le_sum
      intro v _
      exact paddedSize_le_mul _
    _ = ExpanderFamily.growth * Fintype.card E := by
      rw [← Finset.mul_sum, sum_card_cloud]

end Finite

end UniqueGamesTheorem.Foundations.PCP.CloudPadding

end

end OAI
