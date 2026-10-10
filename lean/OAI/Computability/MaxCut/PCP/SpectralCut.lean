import Mathlib
import OAI.Computability.MaxCut.PCP.PreprocessingRegularTables
import OAI.Computability.MaxCut.PCP.GraphGap

namespace OAI

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/
noncomputable section
namespace MaxCutGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicator (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

theorem mean_indicator (S : Finset V) :
    mean (indicator S) = (S.card : ℝ) / (Fintype.card V : ℝ) := by
  have hf : Finset.univ.filter (fun v : V => v ∈ S) = S := by
    ext v
    simp
  rw [mean_eq_sum_div_card]
  simp only [indicator, Finset.sum_boole, hf]

theorem energy_indicator (S : Finset V) : energy (indicator S) = mean (indicator S) := by
  unfold energy
  congr 1
  funext v
  unfold indicator
  split_ifs <;> norm_num

omit [Fintype V] in
theorem indicator_nonnegative (S : Finset V) (v : V) : 0 ≤ indicator S v := by
  unfold indicator
  split_ifs <;> norm_num
end Indicators

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V]

def cut (G : PortGraph V D) (S : Finset V) : Finset (V × D) :=
  Finset.univ.filter (fun e => e.1 ∈ S ∧ (G.rot e).1 ∉ S)

section Nonempty
variable [Nonempty V] [Nonempty D] (G : PortGraph V D)

omit [Nonempty V] in
/-- The normalized cut count is exactly mean minus one-step correlation. -/
theorem cut_density_eq (S : Finset V) :
    ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) =
      mean (indicator S) - correlation (indicator S) (averagingOperator G (indicator S)) := by
  classical
  calc
    _ = mean (indicator (cut G S)) := (mean_indicator (cut G S)).symm
    _ = mean (fun e : V × D => indicator S e.1 -
        indicator S e.1 * indicator S (G.rot e).1) := by
      congr 1
      funext e
      by_cases hv : e.1 ∈ S <;> by_cases hw : (G.rot e).1 ∈ S <;>
        simp [indicator, cut, hv, hw]
    _ = mean (fun v => mean (fun d : D => indicator S v -
        indicator S v * indicator S (G.rot (v,d)).1)) := mean_prod _
    _ = mean (fun v => indicator S v -
        indicator S v * averagingOperator G (indicator S) v) := by
      congr 1
      funext v
      rw [mean_sub, mean_const, mean_mul_left]
      rfl
    _ = _ := mean_sub _ _

theorem cut_density_ge_variance
    (certificate : SpectralCertificate G (1/2)) (S : Finset V) :
    (1/2:ℝ) * mean (indicator S) * (1 - mean (indicator S)) ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  let f := indicator S
  have hz : mean (fun v => f v - mean f) = 0 := by
    rw [mean_sub, mean_const, sub_self]
  have he : energy (fun v => f v - mean f) = mean f - mean f ^ 2 := by
    rw [energy_sub_const, energy_indicator]
    ring
  have hb := zero_mean_correlation_bound G (1/2) certificate
    (fun v => f v - mean f) hz 1
  have hc := correlation_centered G f 1
  simp only [iterateOperator, pow_one, he] at hb hc
  rw [cut_density_eq]
  change (1/2:ℝ) * mean f * (1 - mean f) ≤
    mean f - correlation f (averagingOperator G f)
  nlinarith

theorem cut_density_ge_quarter
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    mean (indicator S) / 4 ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hp0 : 0 ≤ mean (indicator S) := mean_nonnegative _ (indicator_nonnegative S)
  have hp : mean (indicator S) ≤ (1/2:ℝ) := by
    rw [mean_indicator]
    apply (div_le_iff₀ hN).mpr
    have hs : (2:ℝ) * (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hsmall
    nlinarith
  have hv := cut_density_ge_variance G certificate S
  have hprod := mul_nonneg hp0 (sub_nonneg.mpr hp)
  nlinarith

/-- The real cardinal estimate before removing denominators. -/
theorem cut_card_ge_quarter_degree
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    (Fintype.card D : ℝ) * (S.card : ℝ) / 4 ≤ ((cut G S).card : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD : (0:ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have h := cut_density_ge_quarter G certificate S hsmall
  rw [Fintype.card_prod, Nat.cast_mul] at h
  have hh := (le_div_iff₀ (mul_pos hN hD)).mp h
  have he : mean (indicator S) / 4 *
      ((Fintype.card V : ℝ) * (Fintype.card D : ℝ)) =
        (Fintype.card D : ℝ) * (S.card : ℝ) / 4 := by
    rw [mean_indicator]
    field_simp [ne_of_gt hN]

  rw [he] at hh
  exact hh

theorem degree_mul_card_le_four_cut
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    Fintype.card D * S.card ≤ 4 * (cut G S).card := by
  have h := cut_card_ge_quarter_degree G certificate S hsmall
  have hr : (Fintype.card D : ℝ) * (S.card : ℝ) ≤ 4 * ((cut G S).card : ℝ) := by
    linarith
  exact_mod_cast hr

theorem cut_card_ge_quarter_degree_of_card_le_half
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : S.card ≤ Fintype.card V / 2) :
    (Fintype.card D : ℝ) * (S.card : ℝ) / 4 ≤ ((cut G S).card : ℝ) :=
  cut_card_ge_quarter_degree G certificate S (by omega)
end Nonempty

/-- The natural-number expansion used in cloud rounding. Empty vertex sets
are included; a degree of at least eight supplies the nonempty port type. -/
theorem cut_card_ge_twice (G : PortGraph V D)
    (certificate : SpectralCertificate G (1/2)) (hdegree : 8 ≤ Fintype.card D)
    (S : Finset V) (hsmall : 2 * S.card ≤ Fintype.card V) :
    2 * S.card ≤ (cut G S).card := by
  let : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  rcases isEmpty_or_nonempty V with hV | hV
  · let := hV
    have hzero : Fintype.card V = 0 := Fintype.card_eq_zero
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · let := hV
    have h := degree_mul_card_le_four_cut G certificate S hsmall
    have hdeg := Nat.mul_le_mul_right S.card hdegree
    omega

end MaxCutGames.Foundations.PCP.SpectralCut
end

/-!
An actual fixed-degree graph obtained by padding each outgoing-dart cloud to
the explicit expander family and then replacing vertices by cloud darts.
Expansion and majority rounding are proved dependencies, not hypotheses of
the final soundness theorem. Isolated original vertices have empty clouds.
-/

noncomputable section

namespace MaxCutGames.Foundations.PCP.Regularization

open PoweringWalks DegreeReplacement

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

abbrev Vertex (G : ConstraintGraph V E A) := PaddedDart G (CloudPadding.dummy G)
abbrev Port := ExpanderFamily.Port ⊕ Unit

/-- The degree is one absolute constant, independent of the input graph. -/
def degree : Nat := Fintype.card Port

theorem degree_eq : degree = Fintype.card ExpanderFamily.Port + 1 := by
  simp [degree, Port]

theorem degree_positive : 0 < degree := by rw [degree_eq]; omega

/-- A positive padded cloud has exactly the size of one explicit family member. -/
def cloudEquiv (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    ExpanderFamily.Vertex (ExpanderFamily.level (Fintype.card (Cloud G v))) ≃
      Cloud (paddedGraph G (CloudPadding.dummy G)) v :=
  Fintype.equivOfCardEq (CloudPadding.card_cloud_eq_family G v hk).symm

/-- Empty clouds use the empty rotation; every other cloud uses the proved family. -/
def cloudGraph (G : ConstraintGraph V E A) (v : V) :
    PortGraph (Cloud (paddedGraph G (CloudPadding.dummy G)) v) ExpanderFamily.Port :=
  if hk : Fintype.card (Cloud G v) = 0 then
    { rot := Equiv.refl _
      rot_involutive := fun _ => rfl }
  else
    GraphTransport.reindex
      (ExpanderFamily.family (ExpanderFamily.level (Fintype.card (Cloud G v))))
      (cloudEquiv G v (Nat.pos_of_ne_zero hk)) (Equiv.refl _)

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem cloudGraph_of_pos (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    cloudGraph G v = GraphTransport.reindex
      (ExpanderFamily.family (ExpanderFamily.level (Fintype.card (Cloud G v))))
      (cloudEquiv G v hk) (Equiv.refl _) := by
  simp only [cloudGraph, dite_eq_right (Nat.ne_of_gt hk)]

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem cloudGraph_certificate_of_pos (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    SpectralReturn.SpectralCertificate (cloudGraph G v) (1 / 2 : ℝ) := by
  rw [cloudGraph_of_pos G v hk]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (ExpanderFamily.family_certificate _)

omit [Fintype A] [DecidableEq A] in
/-- The exact expansion premise required by the checked finite rounding theorem. -/
theorem cloud_expansion (G : ConstraintGraph V E A) (v : V)
    (S : Finset (Cloud (paddedGraph G (CloudPadding.dummy G)) v))
    (hsmall : S.card ≤
      Fintype.card (Cloud (paddedGraph G (CloudPadding.dummy G)) v) / 2) :
    2 * S.card ≤
      (CloudRounding.directedCut (fun ed => ((cloudGraph G v).rot ed).1) S).card := by
  by_cases hk : Fintype.card (Cloud G v) = 0
  · have hzero : Fintype.card (Cloud (paddedGraph G (CloudPadding.dummy G)) v) = 0 := by
      rw [CloudPadding.card_cloud, hk, CloudPadding.paddedSize_zero]
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · exact SpectralCut.cut_card_ge_twice (cloudGraph G v)
      (cloudGraph_certificate_of_pos G v (Nat.pos_of_ne_zero hk))
      ExpanderFamily.port_degree_ge_eight S (by omega)

def portGraph (G : ConstraintGraph V E A) : PortGraph (Vertex G) Port :=
  paddedReplacementPortGraph G (CloudPadding.dummy G) (cloudGraph G)

/-- The actual constraint graph, with its equality and inherited original tests. -/
def graph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Port) A :=
  paddedReplacementGraph G (CloudPadding.dummy G) (cloudGraph G)

omit [Fintype A] [DecidableEq E] in
@[simp] theorem graph_tail (G : ConstraintGraph V E A) (e : Vertex G × Port) :
    (graph G).tail e = e.1 := rfl

omit [Fintype A] [DecidableEq E] in
theorem graph_reverse (G : ConstraintGraph V E A) :
    (graph G).reverse = (portGraph G).rot := rfl

/-- The outgoing darts at each new vertex are exactly its fixed port alphabet. -/
def degreeEquiv (G : ConstraintGraph V E A) (v : Vertex G) :
    Cloud (graph G) v ≃ Port where
  toFun e := e.val.2
  invFun d := ⟨(v, d), rfl⟩
  left_inv := by
    rintro ⟨⟨w, d⟩, hw⟩
    change w = v at hw
    cases hw
    rfl
  right_inv _ := rfl

omit [Fintype A] in
theorem fixed_degree (G : ConstraintGraph V E A) (v : Vertex G) :
    Fintype.card (Cloud (graph G) v) = degree :=
  Fintype.card_congr (degreeEquiv G v)

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem vertex_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G) ≤ ExpanderFamily.growth * Fintype.card E :=
  CloudPadding.card_paddedDart_le G

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem dart_count (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) = Fintype.card (Vertex G) * degree :=
  Fintype.card_prod _ _

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem dart_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) ≤
      (ExpanderFamily.growth * degree) * Fintype.card E := by
  rw [dart_count]
  calc
    Fintype.card (Vertex G) * degree ≤
        (ExpanderFamily.growth * Fintype.card E) * degree :=
      Nat.mul_le_mul_right degree (vertex_count_le G)
    _ = (ExpanderFamily.growth * degree) * Fintype.card E := Nat.mul_right_comm _ _ _

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : Vertex G → A :=
  DegreeReplacement.liftLabel (paddedGraph G (CloudPadding.dummy G)) labeling

omit [Fintype A] [DecidableEq E] in
/-- Completeness preserves the absolute rejection count exactly. -/
theorem lift_rejectionCount (G : ConstraintGraph V E A) (labeling : V → A) :
    (graph G).rejectionCount (liftLabel G labeling) = G.rejectionCount labeling :=
  paddedReplacement_rejectionCount G (CloudPadding.dummy G) (cloudGraph G) labeling

omit [Fintype A] [DecidableEq E] in
theorem completeness (G : ConstraintGraph V E A) (h : G.Satisfiable) :
    (graph G).Satisfiable :=
  replacement_satisfiable (paddedGraph G (CloudPadding.dummy G)) (cloudGraph G)
    (padded_satisfiable G (CloudPadding.dummy G) h)

def roundLabels [Nonempty A] (G : ConstraintGraph V E A) (ell : Vertex G → A) : V → A :=
  CloudRounding.roundLabels (paddedGraph G (CloudPadding.dummy G)) ell

/-- Actual regularization soundness with no remaining expansion or rounding premise. -/
theorem soundness [Nonempty A] (G : ConstraintGraph V E A) (ell : Vertex G → A) :
    G.rejectionCount (roundLabels G ell) ≤ (graph G).rejectionCount ell :=
  CloudRounding.padded_replacement_soundness G (CloudPadding.dummy G)
    (cloudGraph G) (cloud_expansion G) ell

theorem exists_rounding [Nonempty A] (G : ConstraintGraph V E A) (ell : Vertex G → A) :
    ∃ labeling : V → A, G.rejectionCount labeling ≤ (graph G).rejectionCount ell :=
  ⟨roundLabels G ell, soundness G ell⟩

theorem soundness_of_uniform_lower_bound [Nonempty A] (G : ConstraintGraph V E A)
    (k : Nat) (lower : ∀ labeling : V → A, k ≤ G.rejectionCount labeling)
    (ell : Vertex G → A) : k ≤ (graph G).rejectionCount ell :=
  (lower (roundLabels G ell)).trans (soundness G ell)

end MaxCutGames.Foundations.PCP.Regularization

end

/-! Spectral contraction for the actual Boolean-flag lazy port graph. The
operator identity is proved in `PoweringLazy`; the estimate here averages the
elementary two-term square inequality. -/

namespace MaxCutGames.Foundations.PCP.LazySpectral

open PoweringWalks SpectralReturn

noncomputable section

variable {V D : Type*}

theorem half_sum_sq_le (a b : ℝ) : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Lazification averages the input and one actual graph step, so its energy
is at most the corresponding average of the two energies. -/
theorem lazy_energy_le_average [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) :
    energy (averagingOperator (lazyGraph G) f) ≤
      (energy f + energy (averagingOperator G f)) / 2 := by
  calc
    energy (averagingOperator (lazyGraph G) f) =
        mean (fun v => ((f v + averagingOperator G f v) / 2) ^ 2) := by
      unfold energy
      congr 1
      funext v
      rw [PoweringLazy.averagingOperator_lazy]
    _ ≤ mean (fun v => (f v ^ 2 + averagingOperator G f v ^ 2) / 2) :=
      mean_mono (fun v => half_sum_sq_le _ _)
    _ = mean (fun v => (1 / 2 : ℝ) * (f v ^ 2 + averagingOperator G f v ^ 2)) := by
      congr 1
      funext v
      ring
    _ = (1 / 2 : ℝ) * (energy f + energy (averagingOperator G f)) := by
      rw [mean_mul_left, mean_add]
      rfl
    _ = (energy f + energy (averagingOperator G f)) / 2 := by ring

/-- The concrete lazy graph inherits a squared-energy bound from an actual
certificate for its underlying graph. -/
theorem lazy_energy_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (lazyGraph G) f) ≤
      ((1 + lambda ^ 2) / 2) * energy f := by
  calc
    energy (averagingOperator (lazyGraph G) f) ≤
        (energy f + energy (averagingOperator G f)) / 2 := lazy_energy_le_average G f
    _ ≤ (energy f + lambda ^ 2 * energy f) / 2 := by
      have h := hG.contraction f hf
      linarith
    _ = ((1 + lambda ^ 2) / 2) * energy f := by ring

/-- An actual `7/8` certificate gives the stated `31/32` certificate after
lazification: its intermediate squared-energy factor is `113/128`. -/
theorem lazy_certificate_31_32 [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (hG : SpectralCertificate G (7 / 8)) :
    SpectralCertificate (lazyGraph G) (31 / 32) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := lazy_energy_bound G (7 / 8) hG f hf
    have hcoef : ((1 + (7 / 8 : ℝ) ^ 2) / 2) ≤ (31 / 32 : ℝ) ^ 2 := by norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end

end MaxCutGames.Foundations.PCP.LazySpectral

noncomputable section

namespace MaxCutGames.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

abbrev Vertex (G : ConstraintGraph V E A) := VertexPadding.Vertex (Regularization.Vertex G)
abbrev OverlayPort := Regularization.Port ⊕ ExpanderFamily.Port
abbrev Port := Bool × OverlayPort

def degree : Nat := 2 * (2 * Expanders.baseDegree ^ 2 + 1)
def sizeFactor : Nat := ExpanderFamily.growth ^ 2 * degree

private theorem card_lazy_sum_inline_Preprocessing {X Y : Type*} [Fintype X] [Fintype Y]
    (a b : Nat) (hX : Fintype.card X = a) (hY : Fintype.card Y = b) :
    Fintype.card (Bool × (X ⊕ Y)) = 2 * (a + b) := by
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_sum, hX, hY]

private theorem doubled_add_inline_Preprocessing (a : Nat) : 2 * (2 * a + 1) = 2 * ((a + 1) + a) := by omega

theorem degree_eq_card : degree = Fintype.card Port := by
  have hr : Fintype.card Regularization.Port = Expanders.baseDegree ^ 2 + 1 :=
    Regularization.degree_eq.trans
      (congrArg (fun n : Nat => n + 1) ExpanderFamily.card_port)
  have hp : Fintype.card Port =
      2 * ((Expanders.baseDegree ^ 2 + 1) + Expanders.baseDegree ^ 2) :=
    card_lazy_sum_inline_Preprocessing _ _ hr ExpanderFamily.card_port
  exact (doubled_add_inline_Preprocessing _).trans hp.symm

theorem degree_positive : 0 < degree := by
  unfold degree
  omega

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hg : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  exact Nat.mul_pos (Nat.pow_pos hg) degree_positive

/-- Whole-graph padding retains each original regularized constraint. -/
def paddedGraph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Regularization.Port) A :=
  VertexPadding.paddedG (Regularization.graph G)

/-- The overlay expander is transported to this exact padded vertex set. -/
def overlayExpander (G : ConstraintGraph V E A) :
    PortGraph (Vertex G) ExpanderFamily.Port :=
  GraphTransport.reindex
    (ExpanderFamily.family (ExpanderFamily.level (Fintype.card (Regularization.Vertex G))))
    (VertexPadding.familyVertexEquiv (Regularization.Vertex G)).symm (Equiv.refl _)

omit [Fintype A] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A] in
theorem overlayExpander_certificate (G : ConstraintGraph V E A) :
    SpectralCertificate (overlayExpander G) (1 / 2 : ℝ) :=
  GraphTransport.reindex_spectralCertificate _ _ _ _ (ExpanderFamily.family_certificate _)

def overlayGraph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × OverlayPort) A :=
  Overlay.constraintGraph (paddedGraph G) (overlayExpander G)

def graph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Port) A :=
  LazyConstraint.constraintGraph (overlayGraph G)

def portGraph (G : ConstraintGraph V E A) : PortGraph (Vertex G) Port :=
  Overlay.originalPortGraph (graph G)

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
@[simp] theorem graph_tail (G : ConstraintGraph V E A) : (graph G).tail = Prod.fst := rfl

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
@[simp] theorem graph_reverse (G : ConstraintGraph V E A) :
    (graph G).reverse = (portGraph G).rot := rfl

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
theorem accepts_reverse (G : ConstraintGraph V E A) (e : Vertex G × Port) (a b : A) :
    (graph G).accepts ((portGraph G).rot e) b a = (graph G).accepts e a b :=
  (graph G).reverse_accepts e a b

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
theorem portGraph_eq_lazyGraph (G : ConstraintGraph V E A) :
    portGraph G = lazyGraph (Overlay.originalPortGraph (overlayGraph G)) := rfl

omit [Fintype A] [DecidableEq E] [Nonempty A] in
theorem overlayGraph_certificate (G : ConstraintGraph V E A) :
    SpectralCertificate (Overlay.originalPortGraph (overlayGraph G)) (7 / 8 : ℝ) := by
  apply Overlay.constraintGraph_spectralCertificate
  · exact Regularization.degree_eq
  · have h := ExpanderFamily.port_degree_ge_eight
    omega
  · exact overlayExpander_certificate G

omit [Fintype A] [DecidableEq E] [Nonempty A] in
/-- The actual output operator has one fixed spectral contraction factor. -/
theorem spectral_certificate (G : ConstraintGraph V E A) :
    SpectralCertificate (portGraph G) (31 / 32 : ℝ) := by
  rw [portGraph_eq_lazyGraph]
  exact LazySpectral.lazy_certificate_31_32 _ (overlayGraph_certificate G)

omit [Nonempty A] in
omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem vertex_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G) ≤ ExpanderFamily.growth ^ 2 * Fintype.card E := by
  calc
    _ ≤ ExpanderFamily.growth * Fintype.card (Regularization.Vertex G) :=
      VertexPadding.card_vertex_le _
    _ ≤ ExpanderFamily.growth * (ExpanderFamily.growth * Fintype.card E) :=
      Nat.mul_le_mul_left _ (Regularization.vertex_count_le G)
    _ = _ := by ring

omit [Fintype A] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A] in
theorem dart_count (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) = Fintype.card (Vertex G) * degree := by
  rw [Fintype.card_prod, ← degree_eq_card]

omit [Nonempty A] in
omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem dart_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) ≤ sizeFactor * Fintype.card E := by
  rw [dart_count]
  calc
    _ ≤ (ExpanderFamily.growth ^ 2 * Fintype.card E) * degree :=
      Nat.mul_le_mul_right degree (vertex_count_le G)
    _ = _ := Nat.mul_right_comm _ _ _

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : Vertex G → A :=
  VertexPadding.liftLabel (Classical.choice ‹Nonempty A›) (Regularization.liftLabel G labeling)

omit [Nonempty E] in
omit [Fintype A] [DecidableEq E] in
/-- Lifting any original assignment preserves its absolute rejection count. -/
theorem lift_rejectionCount (G : ConstraintGraph V E A) (labeling : V → A) :
    (graph G).rejectionCount (liftLabel G labeling) = G.rejectionCount labeling := by
  unfold graph
  rw [LazyConstraint.rejectionCount_eq _ rfl]
  unfold overlayGraph
  rw [Overlay.rejectionCount_eq _ _ rfl]
  unfold paddedGraph liftLabel
  rw [VertexPadding.rejectionCount_liftLabel _ rfl]
  exact Regularization.lift_rejectionCount G labeling

omit [Nonempty E] in
omit [Fintype A] [DecidableEq E] in
theorem completeness (G : ConstraintGraph V E A) (hG : G.Satisfiable) :
    (graph G).Satisfiable := by
  apply (LazyConstraint.satisfiable_iff _ rfl).mpr
  apply (Overlay.satisfiable_iff _ _ rfl).mpr
  exact VertexPadding.paddedG_satisfiable (Regularization.graph G) rfl
    (Classical.choice ‹Nonempty A›) (Regularization.completeness G hG)

def roundLabels (G : ConstraintGraph V E A) (labeling : Vertex G → A) : V → A :=
  Regularization.roundLabels G (fun v => labeling (Sum.inl v))

omit [Nonempty E] in
/-- Rounding an arbitrary output assignment gives an original assignment
with no more rejected darts. There are no expansion or rounding hypotheses. -/
theorem soundness (G : ConstraintGraph V E A) (labeling : Vertex G → A) :
    G.rejectionCount (roundLabels G labeling) ≤ (graph G).rejectionCount labeling := by
  calc
    _ ≤ (Regularization.graph G).rejectionCount (fun v => labeling (Sum.inl v)) :=
      Regularization.soundness G _
    _ = (paddedGraph G).rejectionCount labeling :=
      (VertexPadding.paddedG_rejectionCount (Regularization.graph G) rfl labeling).symm
    _ = (overlayGraph G).rejectionCount labeling :=
      (Overlay.rejectionCount_eq (paddedGraph G) (overlayExpander G) rfl labeling).symm
    _ = (graph G).rejectionCount labeling :=
      (LazyConstraint.rejectionCount_eq (overlayGraph G) rfl labeling).symm

omit [Nonempty E] in
theorem satisfiable_iff (G : ConstraintGraph V E A) :
    (graph G).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling, hlabel⟩
    by_contra hG
    have hpositive := G.rejectionCount_positive hG (roundLabels G labeling)
    have hzero : (graph G).rejectionCount labeling = 0 := by
      simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts, hlabel]
    have hsound := soundness G labeling
    omega
  · exact completeness G

/-- The quantitative lower bound used by each amplification iteration. The
single constant `sizeFactor` is independent of the alphabet and input graph. -/
theorem gap_transfer (G : ConstraintGraph V E A) (epsilon : ℚ) (he : 0 ≤ epsilon)
    (lower : ∀ labeling : V → A,
      epsilon * Fintype.card E ≤ (G.rejectionCount labeling : ℚ))
    (labeling : Vertex G → A) :
    (epsilon / sizeFactor) * Fintype.card (Vertex G × Port) ≤
      ((graph G).rejectionCount labeling : ℚ) := by
  have hfactor : (0 : ℚ) < sizeFactor := by exact_mod_cast sizeFactor_positive
  have hcard : (Fintype.card (Vertex G × Port) : ℚ) ≤
      sizeFactor * Fintype.card E := by exact_mod_cast dart_count_le G
  calc
    _ ≤ (epsilon / sizeFactor) * (sizeFactor * Fintype.card E) :=
      mul_le_mul_of_nonneg_left hcard (div_nonneg he hfactor.le)
    _ = epsilon * Fintype.card E := by field_simp
    _ ≤ (G.rejectionCount (roundLabels G labeling) : ℚ) := lower _
    _ ≤ ((graph G).rejectionCount labeling : ℚ) := by exact_mod_cast soundness G labeling

/-- The same actual counting guarantee in the real normalization used for
walk amplification. No rational approximation premise is needed. -/
theorem gap_transfer_real (G : ConstraintGraph V E A) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (lower : ∀ labeling : V → A,
      epsilon * Fintype.card E ≤ (G.rejectionCount labeling : ℝ))
    (labeling : Vertex G → A) :
    (epsilon / sizeFactor) * Fintype.card (Vertex G × Port) ≤
      ((graph G).rejectionCount labeling : ℝ) := by
  have hfactor : (0 : ℝ) < sizeFactor := by exact_mod_cast sizeFactor_positive
  have hcard : (Fintype.card (Vertex G × Port) : ℝ) ≤
      sizeFactor * Fintype.card E := by exact_mod_cast dart_count_le G
  calc
    _ ≤ (epsilon / sizeFactor) * (sizeFactor * Fintype.card E) :=
      mul_le_mul_of_nonneg_left hcard (div_nonneg he hfactor.le)
    _ = epsilon * Fintype.card E := by field_simp
    _ ≤ (G.rejectionCount (roundLabels G labeling) : ℝ) := lower _
    _ ≤ ((graph G).rejectionCount labeling : ℝ) := by exact_mod_cast soundness G labeling

end MaxCutGames.Foundations.PCP.Preprocessing
end

/-!
# Concrete preprocessing table algorithm

Given one fixed expander base table, this function computes regularized
cloud rows, pads the whole vertex set, overlays a stored family table, and
adds the half-lazy rows. It is total even on zero-dart input tables. The
bounds below concern actual output data; an actual TM2 execution certificate
is a separate theorem and is not inferred from these size bounds.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

abbrev BaseTable := PreprocessingRegularTables.BaseTable

def degree : Nat := 2 * ((internalDegree + 1) + internalDegree)

theorem degree_eq : degree = Preprocessing.degree := by
  unfold degree internalDegree Preprocessing.degree
  rw [pow_two]
  omega

def regularVertices (t : GraphTables.Table) : Nat := vertexCount t (padding t)
def vertices (t : GraphTables.Table) : Nat := PreprocessingLevels.paddedSize (regularVertices t)

def padded (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) (internalDegree + 1) :=
  PreprocessingPaddingTables.pad (regularize H t)
    (PreprocessingLevels.le_paddedSize (regularVertices t))

def overlayFamily (H : BaseTable) (t : GraphTables.Table) :
    ExpanderTables.Table (vertices t) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize (regularVertices t))
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel (regularVertices t)))

def preprocess (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) degree :=
  PreprocessingOverlayTables.lazy
    (PreprocessingOverlayTables.overlay (padded H t) (overlayFamily H t))

def output (H : BaseTable) (t : GraphTables.Table) : PortTables.Input degree :=
  ⟨vertices t, preprocess H t⟩

def graphTable (H : BaseTable) (t : GraphTables.Table) : GraphTables.Table :=
  PortTables.graphTable (preprocess H t)

def outputBits (H : BaseTable) (t : GraphTables.Table) : List Bool :=
  PortTables.tableBits (preprocess H t)

theorem regularVertices_ge_darts (t : GraphTables.Table) : t.darts ≤ regularVertices t := by
  change t.darts ≤ t.darts + _
  omega

theorem regularVertices_le (t : GraphTables.Table) :
    regularVertices t ≤ ExpanderFamily.growth * t.darts := vertexCount_le t

theorem vertices_positive (t : GraphTables.Table) : 0 < vertices t :=
  PreprocessingLevels.paddedSize_positive _

theorem vertices_le_of_positive (t : GraphTables.Table) (ht : 0 < t.darts) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * t.darts := by
  have hr : 0 < regularVertices t := ht.trans_le (regularVertices_ge_darts t)
  calc
    _ ≤ ExpanderFamily.growth * regularVertices t :=
      (PreprocessingLevels.paddedSize_bounds hr).2
    _ ≤ ExpanderFamily.growth * (ExpanderFamily.growth * t.darts) :=
      Nat.mul_le_mul_left _ (regularVertices_le t)
    _ = _ := by ring

theorem vertices_eq_one_of_no_darts (t : GraphTables.Table) (ht : t.darts = 0) :
    vertices t = 1 := by
  unfold vertices regularVertices
  rw [vertexCount_eq_zero_of_no_darts t ht, PreprocessingLevels.paddedSize_zero]

/-- The total algorithm also has a uniform data bound on empty inputs. -/
theorem vertices_le (t : GraphTables.Table) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * (t.darts + 1) := by
  by_cases ht : t.darts = 0
  · rw [vertices_eq_one_of_no_darts t ht, ht]
    have hg : 0 < ExpanderFamily.growth := Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
    have hp : 0 < ExpanderFamily.growth ^ 2 := Nat.pow_pos hg
    simpa using Nat.succ_le_of_lt hp
  · exact (vertices_le_of_positive t (Nat.pos_of_ne_zero ht)).trans
      (Nat.mul_le_mul_left _ (Nat.le_succ _))

theorem darts_eq (H : BaseTable) (t : GraphTables.Table) :
    (graphTable H t).darts = vertices t * degree := rfl

theorem darts_le (H : BaseTable) (t : GraphTables.Table) :
    (graphTable H t).darts ≤ Preprocessing.sizeFactor * (t.darts + 1) := by
  rw [darts_eq]
  calc
    _ ≤ (ExpanderFamily.growth ^ 2 * (t.darts + 1)) * degree :=
      Nat.mul_le_mul_right _ (vertices_le t)
    _ = _ := by rw [degree_eq]; unfold Preprocessing.sizeFactor; ring

theorem vertices_le_inputBits (t : GraphTables.Table) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * ((GraphTables.tableBits t).length + 1) :=
  (vertices_le t).trans (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (GraphTables.darts_le_tableBits_length t) 1))

theorem darts_le_inputBits (H : BaseTable) (t : GraphTables.Table) :
    (graphTable H t).darts ≤
      Preprocessing.sizeFactor * ((GraphTables.tableBits t).length + 1) :=
  (darts_le H t).trans (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (GraphTables.darts_le_tableBits_length t) 1))

end MaxCutGames.Foundations.PCP.PreprocessingTables

end OAI
