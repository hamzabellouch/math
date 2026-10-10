import Mathlib
import OAI.Computability.VertexCover.PCP.VertexPadding
import OAI.Computability.VertexCover.PCP.LazyConstraint
import OAI.Computability.VertexCover.PCP.Regularization
import OAI.Computability.VertexCover.PCP.LazySpectral

namespace OAI

                                                                                      

noncomputable section

namespace UniqueGames.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

abbrev Vertex (G : ConstraintGraph V E A) := VertexPadding.Vertex (Regularization.Vertex G)
abbrev OverlayPort := Regularization.Port ⊕ ExpanderFamily.Port
abbrev Port := Bool × OverlayPort

def degree : Nat := 2 * (2 * Expanders.baseDegree ^ 2 + 1)
def sizeFactor : Nat := ExpanderFamily.growth ^ 2 * degree

private theorem card_lazy_sum {X Y : Type*} [Fintype X] [Fintype Y]
    (a b : Nat) (hX : Fintype.card X = a) (hY : Fintype.card Y = b) :
    Fintype.card (Bool × (X ⊕ Y)) = 2 * (a + b) := by
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_sum, hX, hY]

private theorem doubled_add (a : Nat) : 2 * (2 * a + 1) = 2 * ((a + 1) + a) := by omega

theorem degree_eq_card : degree = Fintype.card Port := by
  have hr : Fintype.card Regularization.Port = Expanders.baseDegree ^ 2 + 1 :=
    Regularization.degree_eq.trans
      (congrArg (fun n : Nat => n + 1) ExpanderFamily.card_port)
  have hp : Fintype.card Port =
      2 * ((Expanders.baseDegree ^ 2 + 1) + Expanders.baseDegree ^ 2) :=
    card_lazy_sum _ _ hr ExpanderFamily.card_port
  exact (doubled_add _).trans hp.symm

theorem degree_positive : 0 < degree := by
  unfold degree
  omega

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hg : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  exact Nat.mul_pos (Nat.pow_pos hg) degree_positive

def paddedGraph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Regularization.Port) A :=
  VertexPadding.paddedG (Regularization.graph G)

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

end UniqueGames.Foundations.PCP.Preprocessing
end

end OAI
