import Mathlib
import OAI.Computability.VertexCover.PCP.Expanders
import OAI.Computability.VertexCover.PCP.GraphTransport
import OAI.Computability.VertexCover.PCP.ZigzagSpectral

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.ExpanderFamily

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

end UniqueGames.Foundations.PCP.ExpanderFamily

end OAI
