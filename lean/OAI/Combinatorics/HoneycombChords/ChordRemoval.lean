import OAI.Combinatorics.HoneycombChords.RasterChords

namespace OAI

/-!
# Chord removal and finite partition identities

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb.Transfer.ChordOrientations
open PhysicalTiles CenterPartition FiniteConfigurations
open scoped BigOperators

lemma three_slots_excludes_third (σ : Fin 3 → Fin 3) (a b k : Fin 3)
    (hab : a≠b) (hka : k≠a) (hkb : k≠b) (ha : σ a≠1) (hb : σ b≠1)
    (hd : centerOccupied (σ 2) (σ 1) (σ 0)=0 ∨
      centerOccupied (σ 2) (σ 1) (σ 0)=2) : σ k=1 := by
  by_contra hk
  fin_cases a <;> fin_cases b <;> fin_cases k <;>
    simp_all [centerOccupied,spinOccupied]

/-- In a contributing center configuration, the two sides of a selected
simple path occupy the full local degree. Thus all detached components
are genuinely disjoint from every center on that path. -/
lemma CenterPath.isolated {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (he : ∀ i, σ (p.edge i)≠1) (hn : ∀ i, centerTensor σ (p.center i)≠0)
    (i : Fin n) (k : Fin 3) (hk : incidentWire (p.center i) k∉Set.range p.edge) :
    σ (incidentWire (p.center i) k)=1 := by
  have hka : k≠p.side i.castSucc := by
    intro hh; apply hk; exact (p.incident_edge_iff i k).mpr (Or.inl hh)
  have hkb : k≠p.side i.succ := by
    intro hh; apply hk; exact (p.incident_edge_iff i k).mpr (Or.inr hh)
  apply three_slots_excludes_third (fun k=>σ (incidentWire (p.center i) k))
    (p.side i.castSucc) (p.side i.succ) k (p.sides_distinct i) hka hkb
  · rw [p.in_wire]; exact he _
  · rw [p.out_wire]; exact he _
  · have h := hn i
    unfold centerTensor at h
    split at h
    · exact upTensor_degree _ _ _ h
    · exact downTensor_degree _ _ _ h

lemma CenterPath.factor_of_isolated {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (hi : ∀ i k, incidentWire (p.center i) k∉Set.range p.edge →
      σ (incidentWire (p.center i) k)=1) (i : Fin n) :
    centerTensor σ (p.center i)=p.factor i (fun j=>σ (p.edge j)) := by
  change localTensor _ (fun k=>σ (incidentWire (p.center i) k))=_
  unfold CenterPath.factor
  congr 1
  funext k
  split_ifs with h1 h2
  · rw [h1,p.in_wire]
  · rw [h2,p.out_wire]
  · apply hi i k
    simp only [p.incident_edge_iff]
    exact not_or_intro h1 h2

lemma CenterPath.selected_orientation_unique {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (he : ∀ i, σ (p.edge i)≠1) (hn : ∀ i, centerTensor σ (p.center i)≠0)
    (hroot : σ (p.edge 0)=outSpin (p.point 0) (p.side 0)) :
    ∀ i, σ (p.edge i)=p.spins (p.edge i) := by
  have hu := p.orientation_unique (fun j=>σ (p.edge j)) hroot (by
    intro i
    rw [←p.factor_of_isolated σ (p.isolated σ he hn) i]
    exact hn i)
  intro i
  rw [p.spins_edge]
  exact congrFun hu i

noncomputable def CenterPath.erase {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3) : Wire → Fin 3 :=
  fun w=>if w∈Set.range p.edge then 1 else σ w

noncomputable def CenterPath.fill {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3) : Wire → Fin 3 :=
  fun w=>if w∈Set.range p.edge then p.spins w else σ w

lemma CenterPath.erased_center {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (hi : ∀ i k, incidentWire (p.center i) k∉Set.range p.edge →
      σ (incidentWire (p.center i) k)=1) (i : Fin n) :
    centerTensor (p.erase σ) (p.center i)=1 := by
  have hs (k : Fin 3) : p.erase σ (incidentWire (p.center i) k)=1 := by
    unfold CenterPath.erase
    split_ifs with h
    · rfl
    · exact hi i k h
  unfold centerTensor
  simp only [hs]
  split <;> simp [upTensor,downTensor,Planar.empty,Planar.occupied,Planar.cup]

lemma CenterPath.erased_off {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (v : Center) (h0 : v≠p.point 0) (hl : v≠p.point (Fin.last (n+1)))
    (hv : v∉Set.range p.center) : centerTensor (p.erase σ) v=centerTensor σ v := by
  have hs (k : Fin 3) : p.erase σ (incidentWire v k)=σ (incidentWire v k) :=
    ite_eq_right (p.incident_off v h0 hl hv k)
  unfold centerTensor
  simp only [hs]

lemma CenterPath.tensor_selected {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (hi : ∀ i k, incidentWire (p.center i) k∉Set.range p.edge →
      σ (incidentWire (p.center i) k)=1)
    (he : ∀ i, σ (p.edge i)=p.spins (p.edge i)) (i : Fin n) :
    centerTensor σ (p.center i)=centerTensor p.spins (p.center i) := by
  rw [p.factor_of_isolated σ hi i]
  have he' : (fun j=>σ (p.edge j))=(fun j=>outSpin (p.point j.castSucc) (p.side j)) := by
    funext j; rw [he,p.spins_edge]
  rw [he',p.factor_true]

/-- Removing a forced directed chord factors its exact physical weight
from the remaining center product. No independence or loop cancellation
is assumed here. -/
theorem CenterPath.remove_product {n : ℕ} (p : CenterPath n) (D : Finset Center)
    (σ : Wire → Fin 3) (h0 : p.point 0∉D) (hl : p.point (Fin.last (n+1))∉D)
    (he : ∀ i, σ (p.edge i)≠1) (hn : ∀ i, centerTensor σ (p.center i)≠0)
    (hroot : σ (p.edge 0)=outSpin (p.point 0) (p.side 0)) :
    centerProduct D σ=centerProduct D p.spins * centerProduct D (p.erase σ) := by
  unfold centerProduct
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases hc : v∈Set.range p.center
  · obtain ⟨i,rfl⟩ := hc
    rw [p.erased_center σ (p.isolated σ he hn),mul_one]
    exact p.tensor_selected σ (p.isolated σ he hn) (p.selected_orientation_unique σ he hn hroot) i
  · rw [p.erased_off σ v (fun h=>h0 (h ▸ hv)) (fun h=>hl (h ▸ hv)) hc,
      p.off_center_one v (fun h=>h0 (h ▸ hv)) (fun h=>hl (h ▸ hv)) hc,one_mul]

end CriticalHoneycomb.Transfer.ChordOrientations

namespace CriticalHoneycomb.Transfer.ChordOrientations
open PhysicalTiles CenterPartition FiniteConfigurations SimpleGraph

noncomputable def vertexCenter {D : Finset Center} (a b : Port (D : Set Center)) : Vertices D → Center
  | .inl v => v.val
  | .inr q => (portAt a b q).outside

lemma selected_to_actual {D : Finset Center} (a b : Port (D : Set Center)) (s : Wire → Bool)
    (x y : Vertices D) (h : (selectedGraph a b s).Adj x y) :
    ∃ k : Fin 3, neighbor (vertexCenter a b x) k=vertexCenter a b y ∧
      s (incidentWire (vertexCenter a b x) k)=true := by
  cases x with
  | inl v => cases y with
    | inl w => exact h
    | inr q =>
      change v.val=(portAt a b q).inside ∧ s (portAt a b q).wire=true at h
      refine ⟨(portAt a b q).side,?_,?_⟩
      · change neighbor v.val (portAt a b q).side=(portAt a b q).outside
        rw [h.1]; exact (portAt a b q).neighbor_side
      · change s (incidentWire v.val _)=true
        rw [h.1]; exact h.2
  | inr q => cases y with
    | inl v =>
      change v.val=(portAt a b q).inside ∧ s (portAt a b q).wire=true at h
      refine ⟨(portAt a b q).side,?_,?_⟩
      · change neighbor (portAt a b q).outside _=v.val
        rw [←(portAt a b q).neighbor_side,neighbor_neighbor,h.1]
      · change s (incidentWire (portAt a b q).outside _)=true
        rw [←(portAt a b q).neighbor_side,incidentWire_neighbor]
        exact h.2
    | inr r => exact h.elim

/-- Chord extraction remembers the literal occupied wires, so removal is
not an abstraction to a different path model. -/
theorem chord_edges_of_selected_path {D : Finset Center} {a b : Port (D : Set Center)}
    (γ : Chord (D : Set Center) a b) (hab : a.outside≠b.outside) (s : Wire → Bool)
    (xs : List (Interior D))
    (p : (selectedGraph a b s).Walk (.inr false) (.inr true))
    (hm : xs.map Subtype.val=γ.val)
    (hs : p.support=Sum.inr false :: (xs.map Sum.inl ++ [Sum.inr true])) :
    ∀ i, s ((ofChord γ hab).edge i)=true := by
  let R : Center → Center → Prop := fun x y=>∃ k : Fin 3,
    neighbor x k=y ∧ s (incidentWire x k)=true
  have hc : (p.support.map (vertexCenter a b)).IsChain R :=
    List.isChain_map_of_isChain _ (selected_to_actual a b s) p.isChain_adj_support
  have hl : p.support.map (vertexCenter a b)=extendedTrace γ := by
    rw [hs,List.map_cons,List.map_append,List.map_map]
    have hx : (fun x : Interior D=>vertexCenter a b (Sum.inl x))=Subtype.val := rfl
    simp only [Function.comp_def,hm,List.map_cons,List.map_nil,vertexCenter,portAt,
      Bool.false_eq_true,ite_false,ite_true,extendedTrace]
  rw [hl] at hc
  intro i
  obtain ⟨k,hk,hsk⟩ := List.isChain_iff_getElem.mp hc i.val
    (by rw [extendedTrace_length]; omega)
  have hp : neighbor ((ofChord γ hab).point i.castSucc) k=(ofChord γ hab).point i.succ := hk
  have he : k=(ofChord γ hab).side i := neighbor_injective _ (hp.trans ((ofChord γ hab).step i).symm)
  change s (incidentWire ((ofChord γ hab).point i.castSucc) ((ofChord γ hab).side i))=true
  rw [←he]
  exact hsk

/-- A contributing physical configuration contains an actual source chord
all of whose center tensors use an isolated two-side passage. -/
theorem nonzero_contains_selected_chord {D : Finset Center}
    (a b : Port (D : Set Center)) (hab : a.outside≠b.outside) (σ : Wire → Fin 3)
    (hboundary : BoundarySelection a b (selected σ)) (h : centerProduct D σ≠0) :
    ∃ γ : Chord (D : Set Center) a b,
      ∀ i, σ ((ofChord γ hab).edge i)≠1 := by
  obtain ⟨γ,xs,p,hm,hp,hs,hcycl⟩ := nonzero_product_contains_chord a b
    (fun he=>hab (congrArg Port.outside he)) σ hboundary h
  refine ⟨γ,?_⟩
  intro i
  have he := chord_edges_of_selected_path γ hab (selected σ) xs p hm hs i
  simpa [selected,spinOccupied] using he

end CriticalHoneycomb.Transfer.ChordOrientations

namespace CriticalHoneycomb.Transfer.ChordOrientations
open PhysicalTiles CenterPartition
open scoped BigOperators

lemma CenterPath.fill_tensor {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (hi : ∀ i k, σ (incidentWire (p.center i) k)=1) (i : Fin n) :
    centerTensor (p.fill σ) (p.center i)=centerTensor p.spins (p.center i) := by
  have hs (k : Fin 3) : p.fill σ (incidentWire (p.center i) k)=p.spins (incidentWire (p.center i) k) := by
    unfold CenterPath.fill
    split_ifs with h
    · rfl
    · rw [hi,p.spins_off _ h]
  unfold centerTensor
  simp only [hs]

lemma CenterPath.fill_off {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (v : Center) (h0 : v≠p.point 0) (hl : v≠p.point (Fin.last (n+1)))
    (hv : v∉Set.range p.center) : centerTensor (p.fill σ) v=centerTensor σ v := by
  have hs (k : Fin 3) : p.fill σ (incidentWire v k)=σ (incidentWire v k) :=
    ite_eq_right (p.incident_off v h0 hl hv k)
  unfold centerTensor
  simp only [hs]

lemma tensor_empty (σ : Wire → Fin 3) (v : Center) (h : ∀ k, σ (incidentWire v k)=1) :
    centerTensor σ v=1 := by
  unfold centerTensor
  simp only [h]
  split <;> simp [upTensor,downTensor,Planar.empty,Planar.occupied,Planar.cup]

lemma CenterPath.fill_product {n : ℕ} (p : CenterPath n) (D : Finset Center)
    (σ : Wire → Fin 3) (h0 : p.point 0∉D) (hl : p.point (Fin.last (n+1))∉D)
    (hi : ∀ i k, σ (incidentWire (p.center i) k)=1) :
    centerProduct D (p.fill σ)=centerProduct D p.spins * centerProduct D σ := by
  unfold centerProduct
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases hc : v∈Set.range p.center
  · obtain ⟨i,rfl⟩ := hc
    rw [p.fill_tensor σ hi i,tensor_empty σ _ (hi i),mul_one]
  · rw [p.fill_off σ v (fun h=>h0 (h ▸ hv)) (fun h=>hl (h ▸ hv)) hc,
      p.off_center_one v (fun h=>h0 (h ▸ hv)) (fun h=>hl (h ▸ hv)) hc,one_mul]

@[simp] lemma CenterPath.erase_fill {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (he : ∀ i, σ (p.edge i)=1) : p.erase (p.fill σ)=σ := by
  funext w
  unfold CenterPath.erase CenterPath.fill
  split_ifs with hw
  · obtain ⟨i,rfl⟩ := hw; exact (he i).symm
  · rfl

lemma CenterPath.fill_erase {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (he : ∀ i, σ (p.edge i)=p.spins (p.edge i)) : p.fill (p.erase σ)=σ := by
  funext w
  by_cases hw : w∈Set.range p.edge
  · obtain ⟨i,rfl⟩ := hw
    simpa only [CenterPath.fill,ite_eq_left (Set.mem_range_self i)] using (he i).symm
  · simp [CenterPath.fill,CenterPath.erase,hw]

end CriticalHoneycomb.Transfer.ChordOrientations

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations
open scoped BigOperators

abbrev Assignment (W H : ℕ) := (GridWire W H → Fin 3) × (Cell W H → Fin 3)

noncomputable def assignmentSpins {W H : ℕ} (x : Assignment W H) : Wire → Fin 3 := spins x.1 x.2

noncomputable def restrictAssignment {W H : ℕ} (σ : Wire → Fin 3) : Assignment W H :=
  (restrictGrid σ,restrictMiddle σ)

lemma restrictAssignment_spins {W H : ℕ} (x : Assignment W H) :
    restrictAssignment (assignmentSpins x)=x := by
  apply Prod.ext
  · funext w; exact spins_wire x.1 x.2 (.inl w)
  · funext t; exact spins_wire x.1 x.2 (.inr t)

lemma assignmentSpins_injective {W H : ℕ} : Function.Injective (assignmentSpins (W:=W) (H:=H)) := by
  intro x y h
  have he := spins_injective h
  exact Prod.ext he.1 he.2

lemma assignmentSpins_supported {W H : ℕ} (x : Assignment W H) {w : Wire}
    (hw : w∉Set.range (wireEmbedding (W:=W) (H:=H))) : assignmentSpins x w=1 := by
  exact Function.extend_apply' (Sum.elim x.1 x.2) (fun _=>1) w hw

lemma assignmentSpins_restrict {W H : ℕ} (σ : Wire → Fin 3)
    (h : ∀ w, w∉Set.range (wireEmbedding (W:=W) (H:=H)) → σ w=1) :
    assignmentSpins (restrictAssignment (W:=W) (H:=H) σ)=σ := by
  funext w
  by_cases hw : w∈Set.range (wireEmbedding (W:=W) (H:=H))
  · obtain ⟨w,rfl⟩ := hw
    rw [assignmentSpins,spins_wire]
    cases w <;> rfl
  · exact (assignmentSpins_supported _ hw).trans (h w hw).symm

noncomputable def eraseAssignment {W H n : ℕ} (p : CenterPath n) (x : Assignment W H) : Assignment W H :=
  restrictAssignment (p.erase (assignmentSpins x))

noncomputable def fillAssignment {W H n : ℕ} (p : CenterPath n) (x : Assignment W H) : Assignment W H :=
  restrictAssignment (p.fill (assignmentSpins x))

lemma eraseAssignment_spins {W H n : ℕ} (p : CenterPath n) (x : Assignment W H) :
    assignmentSpins (eraseAssignment p x)=p.erase (assignmentSpins x) := by
  apply assignmentSpins_restrict
  intro w hw
  unfold CenterPath.erase
  split_ifs <;> simp only [assignmentSpins_supported x hw]

lemma fillAssignment_spins {W H n : ℕ} (p : CenterPath n) (x : Assignment W H)
    (hp : ∀ i, p.edge i∈Set.range (wireEmbedding (W:=W) (H:=H))) :
    assignmentSpins (fillAssignment p x)=p.fill (assignmentSpins x) := by
  apply assignmentSpins_restrict
  intro w hw
  have hn : w∉Set.range p.edge := by rintro ⟨i,rfl⟩; exact hw (hp i)
  rw [CenterPath.fill,ite_eq_right hn,assignmentSpins_supported x hw]

lemma matches_of_occupied_eq {W H : ℕ} {cfg : Cell W H → Shape}
    {x y : Assignment W H} (hm : Matches cfg x.1 x.2)
    (he : selected (assignmentSpins x)=selected (assignmentSpins y)) : Matches cfg y.1 y.2 := by
  have hh (w : FullWire W H) := congrFun he (wireEmbedding w)
  simp only [selected,assignmentSpins,spins_wire] at hh
  intro t
  exact ⟨(hh (.inl ((network W H).west t))).symm.trans (hm t).1,
    (hh (.inl ((network W H).north t))).symm.trans (hm t).2.1,
    (hh (.inl ((network W H).south t))).symm.trans (hm t).2.2.1,
    (hh (.inl ((network W H).east t))).symm.trans (hm t).2.2.2.1,
    (hh (.inr t)).symm.trans (hm t).2.2.2.2⟩

lemma selected_erase_congr {n : ℕ} (p : CenterPath n) {σ τ : Wire → Fin 3}
    (he : selected σ=selected τ) : selected (p.erase σ)=selected (p.erase τ) := by
  funext w
  unfold selected CenterPath.erase
  split_ifs <;> try rfl
  exact congrFun he w

lemma selected_fill_erase {n : ℕ} (p : CenterPath n) {σ : Wire → Fin 3}
    (he : ∀ i, σ (p.edge i)≠1) : selected (p.fill (p.erase σ))=selected σ := by
  funext w
  unfold selected CenterPath.fill CenterPath.erase
  split_ifs with hw
  · obtain ⟨i,rfl⟩ := hw
    simp [p.spins_edge,spinOccupied,outSpin_ne_empty,he i]
  · rfl

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.ChordOrientations
open PhysicalTiles CenterPartition

lemma CenterPath.erase_eq_one {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (w : Wire) (h : σ w=p.spins w) : p.erase σ w=1 := by
  unfold CenterPath.erase
  split_ifs with hw
  · rfl
  · rw [h,p.spins_off w hw]

lemma CenterPath.fill_eq_spins {n : ℕ} (p : CenterPath n) (σ : Wire → Fin 3)
    (w : Wire) (h : σ w=1) : p.fill σ w=p.spins w := by
  unfold CenterPath.fill
  split_ifs with hw
  · rfl
  · rw [h,p.spins_off w hw]

end CriticalHoneycomb.Transfer.ChordOrientations

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations
open scoped BigOperators

/-- All four literal cuts, with the prescribed boundary spin at each wire. -/
def HasBoundary {W H : ℕ} (west east : Column H) (south north : Fin W → Fin 3)
    (σ : GridWire W H → Fin 3) : Prop :=
    HasWestNorth west north σ ∧ (∀ j, σ (.inl (Fin.last W,j))=east j) ∧
      (∀ i, σ (.inr (i,0))=south i)

noncomputable instance {W H : ℕ} (west east : Column H) (south north : Fin W → Fin 3)
    (σ : GridWire W H → Fin 3) : Decidable (HasBoundary west east south north σ) :=
  Classical.propDecidable _

noncomputable def maskedTerm {W H : ℕ} (cfg : Cell W H → Shape)
    (west east : Column H) (south north : Fin W → Fin 3) (x : Assignment W H) : ℂ :=
  if HasBoundary west east south north x.1 ∧ Matches cfg x.1 x.2 then
    centerProduct (domain W H) (assignmentSpins x) else 0

lemma maskedTerm_ne_zero {W H : ℕ} (cfg : Cell W H → Shape)
    (west east : Column H) (south north : Fin W → Fin 3) (x : Assignment W H) :
    maskedTerm cfg west east south north x≠0 ↔
      HasBoundary west east south north x.1 ∧ Matches cfg x.1 x.2 ∧
      centerProduct (domain W H) (assignmentSpins x)≠0 := by
  unfold maskedTerm
  split_ifs <;> tauto

lemma sum_subtype_indicator {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (f : α → ℂ) : (∑ x, if P x then f x else 0)=∑ x : {x // P x}, f x.val := by
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- Unrestricted wires with explicit indicators. This form is suitable for
an actual chord erasure bijection of nonzero tensor terms. -/
theorem sum_maskedTerm {W H : ℕ} (cfg : Cell W H → Shape)
    (west east : Column H) (south north : Fin W → Fin 3) :
    (∑ x : Assignment W H, maskedTerm cfg west east south north x)=
      (kappa:ℂ)^(∑ t, (cfg t).visits) * chosenPartition cfg west east south north := by
  classical
  rw [masked_chosenPartition,Fintype.sum_prod_type]
  calc
    _ = ∑ σ : GridWire W H → Fin 3,
      if HasWestNorth west north σ then
        ∑ μ : Cell W H → Fin 3, if (∀ j, σ (.inl (Fin.last W,j))=east j) ∧
          (∀ i, σ (.inr (i,0))=south i) ∧ Matches cfg σ μ then
          centerProduct (domain W H) (spins σ μ) else 0
      else 0 := by
      apply Finset.sum_congr rfl
      intro σ hσ
      by_cases hn : HasWestNorth west north σ
      · simp only [hn,ite_true]
        apply Finset.sum_congr rfl
        intro μ hμ
        unfold maskedTerm HasBoundary assignmentSpins
        simp only [hn,true_and]
        congr 1
        exact propext and_assoc
      · simp [maskedTerm,HasBoundary,hn]
    _ = _ := by
      rw [sum_subtype_indicator]
      congr 1
      ext x
      simp

lemma boundary_erase {W H n : ℕ} (p : CenterPath n) (x : Assignment W H)
    (west east : Column H) (south north : Fin W → Fin 3)
    (hp : HasBoundary west east south north (restrictGrid p.spins))
    (hx : HasBoundary west east south north x.1) :
    HasBoundary (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1) (eraseAssignment p x).1 := by
  have he (w : GridWire W H) (hw : x.1 w=restrictGrid p.spins w) :
      (eraseAssignment p x).1 w=1 := by
    change p.erase (assignmentSpins x) (wireEmbedding (.inl w))=1
    apply p.erase_eq_one
    exact (spins_wire x.1 x.2 (.inl w)).trans hw
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro j; exact he _ ((hx.1.1 j).trans (hp.1.1 j).symm)
  · intro i; exact he _ ((hx.1.2 i).trans (hp.1.2 i).symm)
  · intro j; exact he _ ((hx.2.1 j).trans (hp.2.1 j).symm)
  · intro i; exact he _ ((hx.2.2 i).trans (hp.2.2 i).symm)

lemma boundary_fill {W H n : ℕ} (p : CenterPath n) (x : Assignment W H)
    (west east : Column H) (south north : Fin W → Fin 3)
    (hp : HasBoundary west east south north (restrictGrid p.spins))
    (hx : HasBoundary (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1) x.1) :
    HasBoundary west east south north (fillAssignment p x).1 := by
  have he (w : GridWire W H) (hw : x.1 w=1) :
      (fillAssignment p x).1 w=restrictGrid p.spins w := by
    change p.fill (assignmentSpins x) (wireEmbedding (.inl w))=p.spins (wireEmbedding (.inl w))
    apply p.fill_eq_spins
    exact (spins_wire x.1 x.2 (.inl w)).trans hw
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro j; exact (he _ (hx.1.1 j)).trans (hp.1.1 j)
  · intro i; exact (he _ (hx.1.2 i)).trans (hp.1.2 i)
  · intro j; exact (he _ (hx.2.1 j)).trans (hp.2.1 j)
  · intro i; exact (he _ (hx.2.2 i)).trans (hp.2.2 i)

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations
open scoped BigOperators

lemma selected_fill_congr {n : ℕ} (p : CenterPath n) {σ τ : Wire → Fin 3}
    (he : selected σ=selected τ) : selected (p.fill σ)=selected (p.fill τ) := by
  funext w
  unfold selected CenterPath.fill
  split_ifs <;> try rfl
  exact congrFun he w

/-- Factorization by removal of the actual boundary chord. `cfgR` is the
occupancy left on deleting that chord; it has empty boundary, and is not
assumed to have zero coefficient. The next step applies the already proved
vacuum cancellation to it. -/
theorem actual_path_factorization {W H n : ℕ} (hW : 0<W) (hH : 0<H)
    (cfg cfgR : Cell W H → Shape) (west east : Column H) (south north : Fin W → Fin 3)
    (p : CenterPath n) (x₀ : Assignment W H)
    (hx₀ : maskedTerm cfg west east south north x₀≠0)
    (hc : ∀ i, p.center i∈domain W H)
    (h0 : p.point 0∉domain W H) (hl : p.point (Fin.last (n+1))∉domain W H)
    (hcover : ∀ i, p.edge i∈Set.range (wireEmbedding (W:=W) (H:=H)))
    (hsel : ∀ i, assignmentSpins x₀ (p.edge i)≠1)
    (hp : HasBoundary west east south north (restrictGrid p.spins))
    (hroot : ∀ x : Assignment W H, HasBoundary west east south north x.1 →
      assignmentSpins x (p.edge 0)=outSpin (p.point 0) (p.side 0))
    (hR : Matches cfgR (eraseAssignment p x₀).1 (eraseAssignment p x₀).2) :
    (∑ x : Assignment W H, maskedTerm cfg west east south north x)=
      centerProduct (domain W H) p.spins *
      ∑ y : Assignment W H, maskedTerm cfgR (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1) y := by
  classical
  let P := centerProduct (domain W H) p.spins
  let F := maskedTerm cfg west east south north
  let G := maskedTerm cfgR (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1)
  have hP : P≠0 := p.product_nonzero _ h0 hl
  obtain ⟨hB₀,hM₀,hN₀⟩ := (maskedTerm_ne_zero cfg west east south north x₀).mp hx₀
  have hNcenter₀ (i) : centerTensor (assignmentSpins x₀) (p.center i)≠0 :=
    Finset.prod_ne_zero_iff.mp hN₀ _ (hc i)
  have erased_empty (i) (k) : p.erase (assignmentSpins x₀) (incidentWire (p.center i) k)=1 := by
    unfold CenterPath.erase
    split_ifs with hw
    · rfl
    · exact p.isolated _ hsel hNcenter₀ i k hw
  have RX (y : Assignment W H) (hmy : Matches cfgR y.1 y.2) :
      selected (assignmentSpins y)=selected (p.erase (assignmentSpins x₀)) := by
    have he : selected (assignmentSpins y)=selected (assignmentSpins (eraseAssignment p x₀)) := by
      funext w; exact matches_occupied hW hH hmy hR w
    rw [eraseAssignment_spins] at he
    exact he
  have forward (x : Assignment W H) (hx : F x≠0) :
      F x=P*G (eraseAssignment p x) ∧ fillAssignment p (eraseAssignment p x)=x := by
    obtain ⟨hB,hM,hN⟩ := (maskedTerm_ne_zero cfg west east south north x).mp hx
    have heq : selected (assignmentSpins x)=selected (assignmentSpins x₀) := by
      funext w; exact matches_occupied hW hH hM hM₀ w
    have hs (i) : assignmentSpins x (p.edge i)≠1 := by
      have hh := congrFun heq (p.edge i)
      simpa [selected,spinOccupied,hsel i] using hh
    have hn (i) : centerTensor (assignmentSpins x) (p.center i)≠0 :=
      Finset.prod_ne_zero_iff.mp hN _ (hc i)
    have hr := hroot x hB
    have hProd := p.remove_product (domain W H) (assignmentSpins x) h0 hl hs hn hr
    have hmE : Matches cfgR (eraseAssignment p x).1 (eraseAssignment p x).2 := by
      apply matches_of_occupied_eq hR
      rw [eraseAssignment_spins,eraseAssignment_spins]
      exact selected_erase_congr p heq.symm
    have hbE := boundary_erase p x west east south north hp hB
    constructor
    · dsimp only [F,G,P]
      rw [maskedTerm,ite_eq_left ⟨hB,hM⟩,maskedTerm,ite_eq_left ⟨hbE,hmE⟩,eraseAssignment_spins]
      exact hProd
    · apply assignmentSpins_injective
      rw [fillAssignment_spins p _ hcover,eraseAssignment_spins]
      exact p.fill_erase _ (p.selected_orientation_unique _ hs hn hr)
  have backward (y : Assignment W H) (hy : G y≠0) :
      F (fillAssignment p y)≠0 ∧ eraseAssignment p (fillAssignment p y)=y := by
    obtain ⟨hB,hM,hN⟩ := (maskedTerm_ne_zero cfgR (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1) y).mp hy
    have heq := RX y hM
    have hlocal (i) (k) : assignmentSpins y (incidentWire (p.center i) k)=1 := by
      have hh := congrFun heq (incidentWire (p.center i) k)
      simpa [selected,spinOccupied,erased_empty i k] using hh
    have he (i) : assignmentSpins y (p.edge i)=1 := by
      have hh := congrFun heq (p.edge i)
      simpa [selected,spinOccupied,CenterPath.erase,Set.mem_range_self] using hh
    have hmF : Matches cfg (fillAssignment p y).1 (fillAssignment p y).2 := by
      apply matches_of_occupied_eq hM₀
      rw [fillAssignment_spins p y hcover]
      exact ((selected_fill_congr p heq).trans (selected_fill_erase p hsel)).symm
    have hbF := boundary_fill p y west east south north hp hB
    constructor
    · apply (maskedTerm_ne_zero cfg west east south north _).mpr
      refine ⟨hbF,hmF,?_⟩
      rw [fillAssignment_spins p y hcover,p.fill_product _ _ h0 hl hlocal]
      exact mul_ne_zero hP hN
    · apply assignmentSpins_injective
      rw [eraseAssignment_spins,fillAssignment_spins p y hcover,p.erase_fill _ he]
  change (∑ x, F x)=P*∑ y, G y
  rw [Finset.mul_sum]
  apply Finset.sum_bij_ne_zero (fun x _ _=>eraseAssignment p x)
  · intro x hx hn; exact Finset.mem_univ _
  · intro x hx hn y hy hm he
    have hxf := (forward x hn).2
    have hyf := (forward y hm).2
    rw [←hxf,←hyf,he]
  · intro y hy hn
    have hg : G y≠0 := (mul_ne_zero_iff.mp hn).2
    have hh := backward y hg
    exact ⟨fillAssignment p y,Finset.mem_univ _,hh.1,hh.2⟩
  · intro x hx hn
    exact (forward x hn).1

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations

lemma mem_domain_iff {W H : ℕ} (v : Center) : v∈domain W H ↔
    0≤v.1 ∧ v.1<(W:ℤ) ∧ 0≤v.2.1 ∧ v.2.1<(H:ℤ) := by
  constructor
  · exact domain_coord_bounds
  · rintro ⟨hx,hW,hy,hH⟩
    let i : Fin W := ⟨v.1.toNat,by omega⟩
    let j : Fin H := ⟨v.2.1.toNat,by omega⟩
    have hv : v=cellCenter (i,j) v.2.2 := by
      simp [cellCenter,i,j,Int.toNat_of_nonneg hx,Int.toNat_of_nonneg hy]
    rw [hv]
    exact cellCenter_mem _ _

lemma boundary_wire_exhaustive {W H : ℕ} {v : Center} (hv : v∈domain (W+1) (H+1))
    (s : Fin 3) (hn : neighbor v s∉domain (W+1) (H+1)) :
    (∃ j, incidentWire v s=(westPort W H j).wire) ∨
    (∃ j, incidentWire v s=(eastPort W H j).wire) ∨
    (∃ i, incidentWire v s=(southPort W H i).wire) ∨
    (∃ i, incidentWire v s=(northPort W H i).wire) := by
  obtain ⟨⟨⟨i,j⟩,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
  rw [mem_domain_iff] at hn
  cases b <;> fin_cases s
  · exact False.elim (hn (by simpa [neighbor,cellCenter,up,down] using
      (domain_coord_bounds (cellCenter_mem (i,j) true))))
  · have hj : j=Fin.last H := by
      apply Fin.ext
      have := j.isLt
      have := i.isLt
      simp [neighbor,cellCenter,up] at hn
      simp only [Fin.val_last]
      omega
    subst j
    right; right; right
    exact ⟨i,by rw [Port.wire,northPort_side]; rfl⟩
  · have hi : i=Fin.last W := by
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      have := i.isLt
      simp [neighbor,cellCenter,up] at hn
      simp only [Fin.val_last]
      omega
    subst i
    right; left
    exact ⟨j,by rw [Port.wire,eastPort_side]; rfl⟩
  · exact False.elim (hn (by simpa [neighbor,cellCenter,up,down] using
      (domain_coord_bounds (cellCenter_mem (i,j) false))))
  · have hj : j=0 := by
      apply Fin.ext
      have := j.isLt
      have := i.isLt
      simp [neighbor,cellCenter,down] at hn
      simp only [Fin.val_zero]
      omega
    subst j
    right; right; left
    exact ⟨i,by rw [Port.wire,southPort_side]; rfl⟩
  · have hi : i=0 := by
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      have := i.isLt
      simp [neighbor,cellCenter,down] at hn
      simp only [Fin.val_zero]
      omega
    subst i
    left
    exact ⟨j,by rw [Port.wire,westPort_side]; rfl⟩

lemma assignment_boundary_selection {W H : ℕ} {j k : Fin (H+1)}
    (x : Assignment (W+1) (H+1))
    (hx : HasBoundary (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1) x.1) :
    BoundarySelection (westPort W H j) (eastPort W H k) (selected (assignmentSpins x)) := by
  have hw (r) : assignmentSpins x (westPort W H r).wire=singleColumn j r := by
    rw [westPort_wire]; exact (spins_wire x.1 x.2 _).trans (hx.1.1 r)
  have he (r) : assignmentSpins x (eastPort W H r).wire=singleColumn k r := by
    rw [eastPort_wire]; exact (spins_wire x.1 x.2 _).trans (hx.2.1 r)
  have hs (r) : assignmentSpins x (southPort W H r).wire=1 := by
    rw [southPort_wire]; exact (spins_wire x.1 x.2 _).trans (hx.2.2 r)
  have hn (r) : assignmentSpins x (northPort W H r).wire=1 := by
    rw [northPort_wire]; exact (spins_wire x.1 x.2 _).trans (hx.1.2 r)
  refine ⟨?_,?_,?_⟩
  · simp [selected,hw,singleColumn,spinOccupied]
  · simp [selected,he,singleColumn,spinOccupied]
  · intro v hv s hout hsel
    rcases boundary_wire_exhaustive hv s hout with ⟨r,hr⟩|⟨r,hr⟩|⟨r,hr⟩|⟨r,hr⟩
    · rw [hr] at hsel ⊢
      have h : r=j := by
        by_contra hc
        simp [selected,hw,singleColumn,hc,spinOccupied] at hsel
      subst r; exact Or.inl rfl
    · rw [hr] at hsel ⊢
      have h : r=k := by
        by_contra hc
        simp [selected,he,singleColumn,hc,spinOccupied] at hsel
      subst r; exact Or.inr rfl
    · rw [hr] at hsel
      simp [selected,hs,spinOccupied] at hsel
    · rw [hr] at hsel
      simp [selected,hn,spinOccupied] at hsel

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations
open scoped BigOperators

lemma matches_unique {W H : ℕ} {cfg cfg' : Cell W H → Shape}
    {σ : GridWire W H → Fin 3} {μ : Cell W H → Fin 3}
    (h : Matches cfg σ μ) (h' : Matches cfg' σ μ) : cfg=cfg' := by
  funext t
  have hh := h t
  have hh' := h' t
  cases hc : cfg t <;> cases hc' : cfg' t <;> simp_all [Shape.selection]

lemma matches_empty {W H : ℕ} :
    Matches (fun _ : Cell W H=>.empty) (fun _=>1) (fun _=>1) := by
  intro t
  simp [spinOccupied,Shape.selection]

lemma assignment_empty {W H : ℕ} (hW : 0<W) (hH : 0<H) (x : Assignment W H)
    (hx : Matches (fun _=>.empty) x.1 x.2) : assignmentSpins x=fun _=>1 := by
  have h (w) := matches_occupied hW hH hx (matches_empty (W:=W) (H:=H)) w
  have hv : spins (fun _ : GridWire W H=>1) (fun _=>1)=(fun _=>1) := by
    funext w
    by_cases he : w∈Set.range (wireEmbedding (W:=W) (H:=H))
    · obtain ⟨w,rfl⟩ := he
      rw [spins_wire]; cases w <;> rfl
    · exact Function.extend_apply' _ _ _ he
  funext w
  simpa [assignmentSpins,hv,spinOccupied] using h w

lemma rectanglePath_boundary {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k) :
    HasBoundary (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)
      (restrictGrid (W:=W+1) (H:=H+1) (rectanglePath γ).spins) :=
  ⟨⟨rectanglePath_west γ,rectanglePath_north γ⟩,rectanglePath_east γ,rectanglePath_south γ⟩

lemma rectangle_root {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k)
    (x : Assignment (W+1) (H+1))
    (hx : HasBoundary (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1) x.1) :
    assignmentSpins x ((rectanglePath γ).edge 0)=
      outSpin ((rectanglePath γ).point 0) ((rectanglePath γ).side 0) := by
  rw [rectanglePath,ofChord_first_edge,westPort_wire]
  rw [assignmentSpins,spins_wire]
  change x.1 (.inl (0,j))=_
  rw [hx.1.1]
  rw [ofChord_first,ofChord_first_side,westPort_side]
  simp [singleColumn,outSpin,westPort,down]

/-- The actual one-strand tensor has no contribution from detached polygons:
every nonzero resolved shape is exactly one literal prescribed-port chord. -/
theorem nonzero_shape_is_chord {W H : ℕ} (j k : Fin (H+1))
    (cfg : Cell (W+1) (H+1) → Shape)
    (hn : chosenPartition cfg (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)≠0) :
    ∃ γ : RectChord W H j k, cfg=rectangleShape γ := by
  classical
  have hκ : (kappa:ℂ)≠0 := by
    rw [Complex.ofReal_ne_zero]
    unfold kappa
    exact_mod_cast (Real.rpow_pos_of_pos (by positivity : (0:ℝ)<2+Real.sqrt 2) (-(1:ℝ)/2)).ne'
  have hs : (∑ x : Assignment (W+1) (H+1),
      maskedTerm cfg (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1) x)≠0 := by
    rw [sum_maskedTerm]
    exact mul_ne_zero (pow_ne_zero _ hκ) hn
  obtain ⟨x,hxmem,hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨hB,hM,hN⟩ := (maskedTerm_ne_zero cfg _ _ _ _ x).mp hx
  obtain ⟨γ,hsel⟩ := nonzero_contains_selected_chord (westPort W H j) (eastPort W H k)
    (west_outside_ne_east W H j k) (assignmentSpins x) (assignment_boundary_selection x hB) hN
  let p := rectanglePath γ
  have hc : ∀ i, p.center i∈domain (W+1) (H+1) := ofChord_center_mem γ _
  have h0 : p.point 0∉domain (W+1) (H+1) := by
    rw [show p.point 0=(westPort W H j).outside from ofChord_first γ _]
    exact (westPort W H j).outside_not_mem
  have hl : p.point (Fin.last (γ.val.length+1))∉domain (W+1) (H+1) := by
    rw [show p.point (Fin.last (γ.val.length+1))=(eastPort W H k).outside from ofChord_last γ _]
    exact (eastPort W H k).outside_not_mem
  have hcover := path_wire_covered p (chord_length_pos γ) hc
  have hroot := rectangle_root γ x hB
  have hNi (i) : centerTensor (assignmentSpins x) (p.center i)≠0 :=
    Finset.prod_ne_zero_iff.mp hN _ (hc i)
  have hprod := p.remove_product _ (assignmentSpins x) h0 hl hsel hNi hroot
  have hE : centerProduct (domain (W+1) (H+1)) (assignmentSpins (eraseAssignment p x))≠0 := by
    rw [eraseAssignment_spins]
    intro he
    rw [he,mul_zero] at hprod
    exact hN hprod
  let cfgR := occupancyShape (eraseAssignment p x).1 (eraseAssignment p x).2 hE
  have hR : Matches cfgR (eraseAssignment p x).1 (eraseAssignment p x).2 := occupancyShape_matches _ _ _
  have hfact := actual_path_factorization (Nat.succ_pos W) (Nat.succ_pos H)
    cfg cfgR _ _ _ _ p x hx hc h0 hl hcover hsel (rectanglePath_boundary γ)
    (rectangle_root γ) hR
  have hRempty : cfgR=fun _=>.empty := by
    by_contra he
    have hz := chosen_nonempty_vacuum_zero cfgR he
    have hzero : (∑ y : Assignment (W+1) (H+1),
        maskedTerm cfgR (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1) y)=0 := by
      rw [sum_maskedTerm,hz,mul_zero]
    rw [hzero,mul_zero] at hfact
    exact hs hfact
  have he : p.erase (assignmentSpins x)=fun _=>1 := by
    rw [←eraseAssignment_spins]
    apply assignment_empty (Nat.succ_pos W) (Nat.succ_pos H)
    rw [←hRempty]
    exact hR
  have hp : assignmentSpins x=p.spins := by
    rw [←p.fill_erase (assignmentSpins x) (p.selected_orientation_unique _ hsel hNi hroot),he]
    funext w
    exact p.fill_eq_spins (fun _=>1) w rfl
  refine ⟨γ,?_⟩
  apply matches_unique (σ:=restrictGrid p.spins) (μ:=restrictMiddle p.spins)
  · apply matches_of_occupied_eq (y:=(restrictGrid p.spins,restrictMiddle p.spins)) hM
    change selected (assignmentSpins x)=selected (spins (restrictGrid p.spins) (restrictMiddle p.spins))
    rw [hp,path_spins_restrict p (chord_length_pos γ) hc]
  · exact pathShape_matches p (chord_length_pos γ) hc h0 hl


end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations
open scoped BigOperators

/-- Exact finite original-source path partition. Each occupied center has
weight κ; the two prescribed boundary ports are unweighted. Detached cycles
cancel in the tensor contraction rather than being dropped by fiat. -/
theorem actual_chord_sum_eq_transfer {W H : ℕ} (j k : Fin (H+1)) :
    (prescribedPartition (W+1) (H+1) (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)) =
      ∑ γ : RectChord W H j k, (kappa:ℂ)^γ.val.length := by
  classical
  rw [prescribed_shape_expansion]
  let F : (Cell (W+1) (H+1) → Shape) → ℂ := fun cfg=>
    (kappa:ℂ)^(∑ t, (cfg t).visits) * chosenPartition cfg
      (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)
  have hsub : (∑ cfg, F cfg)=
      ∑ cfg ∈ Finset.univ.image (rectangleShape (W:=W) (H:=H) (j:=j) (k:=k)), F cfg := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro cfg hcfg hnot
    have hn : chosenPartition cfg (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)=0 := by
      by_contra h
      obtain ⟨γ,hγ⟩ := nonzero_shape_is_chord j k cfg h
      apply hnot
      exact Finset.mem_image.mpr ⟨γ,Finset.mem_univ _,hγ.symm⟩
    simp [F,hn]
  change (∑ cfg, F cfg)=_
  rw [hsub,Finset.sum_image (fun x _ y _ h=>rectangleShape_injective h)]
  apply Finset.sum_congr rfl
  intro γ hγ
  dsimp only [F]
  rw [actual_chord_chosen_one,mul_one,actual_chord_visits]

/-- The ENNReal mass defined directly from the literal path subtype agrees
with the finite physical transfer entry. This is finite identification only;
no uniform bound in width or infinite-strip asymptotic is assumed. -/
theorem actual_chordMass_eq_transfer {W H : ℕ} (j k : Fin (H+1)) :
    chordMass (domain (W+1) (H+1) : Set Center) (westPort W H j) (eastPort W H k) =
      ENNReal.ofReal (prescribedPartition (W+1) (H+1)
        (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)).re := by
  classical
  rw [actual_chord_sum_eq_transfer]
  simp only [Complex.re_sum,←Complex.ofReal_pow,Complex.ofReal_re]
  unfold chordMass weight
  rw [tsum_fintype,ENNReal.ofReal_sum_of_nonneg]
  intro γ hγ
  exact pow_nonneg (Real.rpow_pos_of_pos (by positivity : (0:ℝ)<2+Real.sqrt 2) _).le _

end CriticalHoneycomb.Transfer.RasterGrid

end OAI
