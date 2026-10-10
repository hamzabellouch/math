import OAI.Combinatorics.HoneycombChords.PhysicalWeights

namespace OAI

/-!
# Physical center tensors and local connectivity

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb.Transfer.PhysicalTiles
open scoped BigOperators
open Planar

def spinOccupied (i : Fin 3) : Bool := decide (i ≠ 1)

lemma vacant_support {i j : Fin 3} (h : vacant i j ≠ 0) : i=1 ∧ j=1 := by
  simpa [vacant] using h
lemma occupied_support {i j : Fin 3} (h : occupied i j ≠ 0) : i=j ∧ i≠1 := by
  simpa [occupied] using h
lemma empty_support {i : Fin 3} (h : Planar.empty i ≠ 0) : i=1 := by
  simpa [Planar.empty] using h
lemma cup_support {i j : Fin 3} (h : cup i j ≠ 0) : i≠1 ∧ j≠1 := by
  fin_cases i <;> fin_cases j <;> simp_all [cup]

/-- Nonzero local orientation factors have exactly the selected occupied
edges. Thus matching a wire spin also matches the unoriented occupancy. -/
theorem shapeTensor_support (q : Shape) (w n s e : Fin 3)
    (h : shapeTensor q w n s e ≠ 0) :
    spinOccupied w = q.selection.west ∧ spinOccupied n = q.selection.north ∧
      spinOccupied s = q.selection.south ∧ spinOccupied e = q.selection.east := by
  cases q <;> simp only [shapeTensor,mul_ne_zero_iff] at h
  · obtain ⟨hw,hs⟩ := vacant_support h.1
    obtain ⟨hn,he⟩ := vacant_support h.2
    simp [spinOccupied,Shape.selection,hw,hs,hn,he]
  · obtain ⟨hws,hw⟩ := occupied_support h.1
    obtain ⟨hn,he⟩ := vacant_support h.2
    simp [spinOccupied,Shape.selection,←hws,hw,hn,he]
  · obtain ⟨hw,hs⟩ := vacant_support h.1
    obtain ⟨hne,hn⟩ := occupied_support h.2
    simp [spinOccupied,Shape.selection,hw,hs,←hne,hn]
  · obtain ⟨hws,hw⟩ := occupied_support h.1
    obtain ⟨hne,hn⟩ := occupied_support h.2
    simp [spinOccupied,Shape.selection,←hws,hw,←hne,hn]
  · obtain ⟨hw,hn⟩ := cup_support h.1.1
    have hs := empty_support h.1.2
    have he := empty_support h.2
    simp [spinOccupied,Shape.selection,hw,hs,hn,he]
  · have hw := empty_support h.1.1
    have hn := empty_support h.1.2
    obtain ⟨hs,he⟩ := cup_support h.2
    simp [spinOccupied,Shape.selection,hw,hs,hn,he]
  · have hn := empty_support h.1.1
    have hs := empty_support h.1.2
    obtain ⟨hwe,hw⟩ := occupied_support h.2
    simp [spinOccupied,Shape.selection,←hwe,hw,hs,hn]
  · have hw := empty_support h.1.1
    have he := empty_support h.1.2
    obtain ⟨hns,hn⟩ := occupied_support h.2
    simp [spinOccupied,Shape.selection,hw,he,←hns,hn]

/-- A finite gluing of the exact physical lozenges. A wire label shared by
tiles is summed only once; open boundary values are imposed separately. -/
structure TileNetwork (V T : Type*) where
  west : T → V
  north : T → V
  south : T → V
  east : T → V

noncomputable def TileNetwork.orientation {V T : Type*} [Fintype T] [DecidableEq T]
    (A : TileNetwork V T) (q : T → Shape) (σ : V → Fin 3) : ℂ :=
  ∏ t, shapeTensor (q t) (σ (A.west t)) (σ (A.north t))
    (σ (A.south t)) (σ (A.east t))

noncomputable def TileNetwork.physical {V T : Type*} [Fintype T] [DecidableEq T]
    (A : TileNetwork V T) (σ : V → Fin 3) : ℂ :=
  ∏ t, sourceR (kappa:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) 0
    (σ (A.north t),σ (A.west t)) (σ (A.south t),σ (A.east t))

/-- The global finite product expansion, with the exact visited-center
weight. No path/loop cancellation is assumed in this algebraic equality. -/
theorem physical_network_expansion {V T : Type*} [Fintype T] [DecidableEq T]
    (A : TileNetwork V T) (σ : V → Fin 3) :
    A.physical σ = ∑ q : T → Shape,
      (kappa:ℂ) ^ (∑ t, (q t).visits) * A.orientation q σ := by
  classical
  simp only [TileNetwork.physical,physical_tile_expansion]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.prod_mul_distrib,←Finset.prod_pow_eq_pow_sum]
  rfl

/-- Full finite contraction with any fixed boundary weight. For a prescribed
boundary spin assignment this factor is its zero/one indicator. -/
theorem contracted_network_expansion {V T : Type*} [Fintype V] [Fintype T] [DecidableEq V] [DecidableEq T]
    (A : TileNetwork V T) (boundary : (V → Fin 3) → ℂ) :
    (∑ σ, boundary σ * A.physical σ) =
      ∑ q : T → Shape, (kappa:ℂ) ^ (∑ t, (q t).visits) *
        ∑ σ, boundary σ * A.orientation q σ := by
  classical
  simp_rw [physical_network_expansion,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro σ hσ
  ring

/-- Every contributing shape assignment is globally consistent on all
identified wires; there can be no spurious unmatched occupied half-edge. -/
theorem orientation_support {V T : Type*} [Fintype T] [DecidableEq T]
    (A : TileNetwork V T) (q : T → Shape) (σ : V → Fin 3)
    (h : A.orientation q σ ≠ 0) (t : T) :
    spinOccupied (σ (A.west t)) = (q t).selection.west ∧
    spinOccupied (σ (A.north t)) = (q t).selection.north ∧
    spinOccupied (σ (A.south t)) = (q t).selection.south ∧
    spinOccupied (σ (A.east t)) = (q t).selection.east := by
  classical
  apply shapeTensor_support
  exact (Finset.prod_ne_zero_iff.mp h) t (Finset.mem_univ t)

end CriticalHoneycomb.Transfer.PhysicalTiles

namespace CriticalHoneycomb.Transfer.PhysicalTiles
open scoped BigOperators
open Planar

/-- The three-leg tensor at one actual up triangle center. Its empty state
has weight one, and each of the three simple passages has exactly one κ. -/
noncomputable def upTensor (w s m : Fin 3) : ℂ :=
  Planar.empty w * Planar.empty s * Planar.empty m +
  (kappa:ℂ) * (occupied w s * Planar.empty m +
    occupied w m * Planar.empty s + cup s m * Planar.empty w)

/-- The down-center tensor, with the ordinary, not conjugate, contraction
on the internal edge. The order m,n is essential for the snake identity. -/
noncomputable def downTensor (e n m : Fin 3) : ℂ :=
  Planar.empty e * Planar.empty n * Planar.empty m +
  (kappa:ℂ) * (occupied n e * Planar.empty m +
    occupied m e * Planar.empty n + cup m n * Planar.empty e)

/-- Exact factorization through the actual middle honeycomb edge. Thus the
integrable physical tile is a contraction of two genuine visited-center
tensors, not only a list of formal connectivities. -/
theorem sourceR_eq_center_contraction (w n s e : Fin 3) :
    sourceR (kappa:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) 0 (n,w) (s,e) =
      ∑ m : Fin 3, upTensor w s m * downTensor e n m := by
  rw [tile_decomposition]
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [upTensor,downTensor,vacant,occupied,Planar.empty,cup,
      Fin.sum_univ_three] <;> ring_nf <;>
    simp [phase_ne_zero]

noncomputable def centerOccupied (a b c : Fin 3) : ℕ :=
  (spinOccupied a).toNat+(spinOccupied b).toNat+(spinOccupied c).toNat

/-- A nonzero occupied center has exactly two selected incident edges.
Repeated centers and degree-four crossings are not hidden in the transfer. -/
theorem upTensor_degree (w s m : Fin 3) (h : upTensor w s m ≠ 0) :
    centerOccupied w s m=0 ∨ centerOccupied w s m=2 := by
  fin_cases w <;> fin_cases s <;> fin_cases m <;>
    norm_num [upTensor,centerOccupied,spinOccupied,Planar.empty,occupied,cup] at * 

theorem downTensor_degree (e n m : Fin 3) (h : downTensor e n m ≠ 0) :
    centerOccupied e n m=0 ∨ centerOccupied e n m=2 := by
  fin_cases e <;> fin_cases n <;> fin_cases m <;>
    norm_num [downTensor,centerOccupied,spinOccupied,Planar.empty,occupied,cup] at * 

/-- In any finite lozenge network, all internal middle-edge indices can be
introduced simultaneously. All remaining wire indices are left unchanged. -/
theorem physical_network_center_expansion {V T : Type*} [Fintype T] [DecidableEq T]
    (A : TileNetwork V T) (σ : V → Fin 3) :
    A.physical σ = ∑ μ : T → Fin 3,
      ∏ t, upTensor (σ (A.west t)) (σ (A.south t)) (μ t) *
        downTensor (σ (A.east t)) (σ (A.north t)) (μ t) := by
  simp only [TileNetwork.physical,sourceR_eq_center_contraction]
  exact Fintype.prod_sum _

/-- The genuine finite center partition, including any prescribed boundary
indicator. This is the exact tensor precursor to selecting the unique chord
and cancelling its detached loop components. -/
theorem contracted_center_expansion {V T : Type*} [Fintype V] [Fintype T]
    [DecidableEq V] [DecidableEq T] (A : TileNetwork V T)
    (boundary : (V → Fin 3) → ℂ) :
    (∑ σ, boundary σ * A.physical σ) =
      ∑ σ : V → Fin 3, ∑ μ : T → Fin 3, boundary σ *
        ∏ t, upTensor (σ (A.west t)) (σ (A.south t)) (μ t) *
          downTensor (σ (A.east t)) (σ (A.north t)) (μ t) := by
  simp_rw [physical_network_center_expansion,Finset.mul_sum]

end CriticalHoneycomb.Transfer.PhysicalTiles

namespace CriticalHoneycomb.Transfer.CenterPartition
open SimpleGraph PhysicalTiles FiniteConfigurations

/-- The tensor sits at an actual honeycomb center, indexed by its actual
three honeycomb wires. The order at an up and a down center is the source
physical R factorization order, not a symmetrized substitute. -/
noncomputable def centerTensor (σ : Wire → Fin 3) (v : Center) : ℂ :=
  if v.2.2 then
    upTensor (σ (incidentWire v 2)) (σ (incidentWire v 1)) (σ (incidentWire v 0))
  else
    downTensor (σ (incidentWire v 2)) (σ (incidentWire v 1)) (σ (incidentWire v 0))

noncomputable def centerProduct (D : Finset Center) (σ : Wire → Fin 3) : ℂ :=
  ∏ v∈D, centerTensor σ v

def selected (σ : Wire → Fin 3) : Wire → Bool := fun w => spinOccupied (σ w)

lemma nonzero_center_degree (σ : Wire → Fin 3) (v : Center)
    (h : centerTensor σ v ≠ 0) :
    selectedSideCount (selected σ) v=0 ∨ selectedSideCount (selected σ) v=2 := by
  have he : selectedSideCount (selected σ) v =
      centerOccupied (σ (incidentWire v 2)) (σ (incidentWire v 1))
        (σ (incidentWire v 0)) := by
    simp [selectedSideCount,selected,centerOccupied,Nat.add_comm,Nat.add_assoc]
  rw [he]
  unfold centerTensor at h
  split at h
  · exact upTensor_degree _ _ _ h
  · exact downTensor_degree _ _ _ h

/-- This packages *derived*, not assumed, local degree conditions. -/
noncomputable def configurationOfNonzero {D : Finset Center}
    (a b : Port (D : Set Center)) (hab : a≠b) (σ : Wire → Fin 3)
    (hboundary : BoundarySelection a b (selected σ))
    (h : centerProduct D σ ≠ 0) : Configuration D a b :=
  configurationOfSides a b hab (selected σ) hboundary (by
    intro v hv
    apply nonzero_center_degree σ v
    exact (Finset.prod_ne_zero_iff.mp h) v hv)

/-- Every contributing physical center configuration has an actual simple
chord with precisely the prescribed ports. All other occupied components
are detached cycles: the ensuing loop cancellation is a separate obligation. -/
theorem nonzero_product_contains_chord {D : Finset Center}
    (a b : Port (D : Set Center)) (hab : a≠b) (σ : Wire → Fin 3)
    (hboundary : BoundarySelection a b (selected σ))
    (h : centerProduct D σ ≠ 0) :
    ∃ (γ : Chord (D : Set Center) a b) (xs : List (Interior D))
      (p : (selectedGraph a b (selected σ)).Walk (.inr false) (.inr true)),
      xs.map Subtype.val = γ.val ∧ p.IsPath ∧
      p.support = Sum.inr false :: (xs.map Sum.inl ++ [Sum.inr true]) ∧
      ((selectedGraph a b (selected σ)) \ p.toSubgraph.spanningCoe).IsCycles :=
  configuration_contains_chord (configurationOfNonzero a b hab σ hboundary h)

end CriticalHoneycomb.Transfer.CenterPartition

end OAI
