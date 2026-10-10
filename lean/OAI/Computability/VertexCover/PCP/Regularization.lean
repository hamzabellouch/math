import Mathlib
import OAI.Computability.VertexCover.PCP.CloudPadding
import OAI.Computability.VertexCover.PCP.CloudRounding
import OAI.Computability.VertexCover.PCP.SpectralCut

namespace OAI

                                                                                       

noncomputable section

namespace UniqueGames.Foundations.PCP.Regularization

open PoweringWalks DegreeReplacement

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

abbrev Vertex (G : ConstraintGraph V E A) := PaddedDart G (CloudPadding.dummy G)
abbrev Port := ExpanderFamily.Port ⊕ Unit

def degree : Nat := Fintype.card Port

theorem degree_eq : degree = Fintype.card ExpanderFamily.Port + 1 := by
  simp [degree, Port]

theorem degree_positive : 0 < degree := by rw [degree_eq]; omega

def cloudEquiv (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    ExpanderFamily.Vertex (ExpanderFamily.level (Fintype.card (Cloud G v))) ≃
      Cloud (paddedGraph G (CloudPadding.dummy G)) v :=
  Fintype.equivOfCardEq (CloudPadding.card_cloud_eq_family G v hk).symm

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

def graph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Port) A :=
  paddedReplacementGraph G (CloudPadding.dummy G) (cloudGraph G)

omit [Fintype A] [DecidableEq E] in
@[simp] theorem graph_tail (G : ConstraintGraph V E A) (e : Vertex G × Port) :
    (graph G).tail e = e.1 := rfl

omit [Fintype A] [DecidableEq E] in
theorem graph_reverse (G : ConstraintGraph V E A) :
    (graph G).reverse = (portGraph G).rot := rfl

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

end UniqueGames.Foundations.PCP.Regularization

end

end OAI
