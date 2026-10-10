import OAI.Combinatorics.HoneycombChords.Continuation

namespace OAI

/-!
# All-boundary chord decompositions

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations

/-- The actual four rectangle cuts; internal edges are not constrained. -/
def BoundaryWire {W H : ℕ} : GridWire W H → Prop
  | .inl (i,_) => i=0 ∨ i=Fin.last W
  | .inr (_,j) => j=0 ∨ j=Fin.last H

def SameBoundary {W H : ℕ} (x y : Assignment W H) : Prop :=
  ∀ w,BoundaryWire w → x.1 w=y.1 w

lemma sameBoundary_refl {W H : ℕ} (x : Assignment W H) : SameBoundary x x := fun _ _=>rfl
lemma sameBoundary_symm {W H : ℕ} {x y : Assignment W H} (h : SameBoundary x y) :
    SameBoundary y x := fun w hw=>(h w hw).symm
lemma sameBoundary_trans {W H : ℕ} {x y z : Assignment W H}
    (h : SameBoundary x y) (h' : SameBoundary y z) : SameBoundary x z :=
  fun w hw=>(h w hw).trans (h' w hw)
lemma sameBoundary_hasBoundary {W H : ℕ} (x y : Assignment W H) :
    SameBoundary x y ↔ HasBoundary (fun j=>y.1 (.inl (0,j)))
      (fun j=>y.1 (.inl (Fin.last W,j))) (fun i=>y.1 (.inr (i,0)))
      (fun i=>y.1 (.inr (i,Fin.last H))) x.1 := by
  constructor
  · intro hh
    exact ⟨⟨fun j=>hh _ (Or.inl rfl),fun i=>hh _ (Or.inr rfl)⟩,
      fun j=>hh _ (Or.inr rfl),fun i=>hh _ (Or.inl rfl)⟩
  · intro hh w hw
    cases w with
    | inl w =>
      rcases w with ⟨i,j⟩
      rcases hw with rfl|rfl
      · exact hh.1.1 j
      · exact hh.2.1 j
    | inr w =>
      rcases w with ⟨i,j⟩
      rcases hw with rfl|rfl
      · exact hh.2.2 i
      · exact hh.1.2 i

lemma erase_sameBoundary {W H n : ℕ} (p : CenterPath n) {x y : Assignment W H}
    (h : SameBoundary x y) : SameBoundary (eraseAssignment p x) (eraseAssignment p y) := by
  intro w hw
  change p.erase (assignmentSpins x) (wireEmbedding (.inl w))=
    p.erase (assignmentSpins y) (wireEmbedding (.inl w))
  unfold CenterPath.erase
  split_ifs
  · rfl
  · simp only [assignmentSpins,spins_wire]
    exact h w hw

lemma fill_sameBoundary {W H n : ℕ} (p : CenterPath n) {x y : Assignment W H}
    (h : SameBoundary x y) : SameBoundary (fillAssignment p x) (fillAssignment p y) := by
  intro w hw
  change p.fill (assignmentSpins x) (wireEmbedding (.inl w))=
    p.fill (assignmentSpins y) (wireEmbedding (.inl w))
  unfold CenterPath.fill
  split_ifs
  · rfl
  · simp only [assignmentSpins,spins_wire]
    exact h w hw

noncomputable instance {W H : ℕ} (x y : Assignment W H) : Decidable (SameBoundary x y) :=
  Classical.propDecidable _
noncomputable def relativeTerm {W H : ℕ} (cfg : Cell W H → Shape)
    (x₀ x : Assignment W H) : ℂ :=
  if SameBoundary x x₀ ∧ Matches cfg x.1 x.2 then
    centerProduct (domain W H) (assignmentSpins x) else 0
lemma relativeTerm_ne_zero {W H : ℕ} (cfg : Cell W H → Shape)
    (x₀ x : Assignment W H) : relativeTerm cfg x₀ x≠0 ↔
      SameBoundary x x₀ ∧ Matches cfg x.1 x.2 ∧
      centerProduct (domain W H) (assignmentSpins x)≠0 := by
  unfold relativeTerm
  split_ifs <;> tauto

lemma relativeTerm_eq_masked {W H : ℕ} (cfg : Cell W H → Shape)
    (x₀ x : Assignment W H) : relativeTerm cfg x₀ x=
      maskedTerm cfg (fun j=>x₀.1 (.inl (0,j))) (fun j=>x₀.1 (.inl (Fin.last W,j)))
        (fun i=>x₀.1 (.inr (i,0))) (fun i=>x₀.1 (.inr (i,Fin.last H))) x := by
  simp only [relativeTerm,maskedTerm,sameBoundary_hasBoundary]

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations

/-- Removing one actual oriented component, retaining every other boundary
port in the residual path system. -/
theorem arbitrary_boundary_path_factorization {W H n : ℕ} (hW : 0<W) (hH : 0<H)
    (cfg cfgR : Cell W H → Shape)
    (p : CenterPath n) (x₀ : Assignment W H)
    (hx₀ : relativeTerm cfg x₀ x₀≠0)
    (hc : ∀ i, p.center i∈domain W H)
    (h0 : p.point 0∉domain W H) (hl : p.point (Fin.last (n+1))∉domain W H)
    (hcover : ∀ i, p.edge i∈Set.range (wireEmbedding (W:=W) (H:=H)))
    (hsel : ∀ i, assignmentSpins x₀ (p.edge i)≠1)
    (hroot : ∀ x : Assignment W H, SameBoundary x x₀ →
      assignmentSpins x (p.edge 0)=outSpin (p.point 0) (p.side 0))
    (hR : Matches cfgR (eraseAssignment p x₀).1 (eraseAssignment p x₀).2) :
    (∑ x : Assignment W H, relativeTerm cfg x₀ x)=
      centerProduct (domain W H) p.spins *
      ∑ y : Assignment W H, relativeTerm cfgR (eraseAssignment p x₀) y := by
  classical
  let P := centerProduct (domain W H) p.spins
  let F := relativeTerm cfg x₀
  let G := relativeTerm cfgR (eraseAssignment p x₀)
  have hP : P≠0 := p.product_nonzero _ h0 hl
  obtain ⟨hB₀,hM₀,hN₀⟩ := (relativeTerm_ne_zero cfg x₀ x₀).mp hx₀
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
    obtain ⟨hB,hM,hN⟩ := (relativeTerm_ne_zero cfg x₀ x).mp hx
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
    have hbE := erase_sameBoundary p hB
    constructor
    · dsimp only [F,G,P]
      rw [relativeTerm,ite_eq_left ⟨hB,hM⟩,relativeTerm,ite_eq_left ⟨hbE,hmE⟩,eraseAssignment_spins]
      exact hProd
    · apply assignmentSpins_injective
      rw [fillAssignment_spins p _ hcover,eraseAssignment_spins]
      exact p.fill_erase _ (p.selected_orientation_unique _ hs hn hr)
  have backward (y : Assignment W H) (hy : G y≠0) :
      F (fillAssignment p y)≠0 ∧ eraseAssignment p (fillAssignment p y)=y := by
    obtain ⟨hB,hM,hN⟩ := (relativeTerm_ne_zero cfgR (eraseAssignment p x₀) y).mp hy
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
    have hfill₀ : fillAssignment p (eraseAssignment p x₀)=x₀ := by
      apply assignmentSpins_injective
      rw [fillAssignment_spins p _ hcover,eraseAssignment_spins]
      exact p.fill_erase _ (p.selected_orientation_unique _ hsel hNcenter₀
        (hroot x₀ (sameBoundary_refl _)))
    have hbF : SameBoundary (fillAssignment p y) x₀ := by
      rw [←hfill₀]
      exact fill_sameBoundary p hB
    constructor
    · apply (relativeTerm_ne_zero cfg x₀ _).mpr
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

namespace CriticalHoneycomb.Transfer.ChordOrientations
open PhysicalTiles CenterPartition

lemma localTensor_pair_unique (v : Center) (a b : Fin 3) (hab : a≠b)
    (s t u : Fin 3)
    (ht : localTensor v (fun k=>if k=a then s else if k=b then t else 1)≠0)
    (hu : localTensor v (fun k=>if k=a then s else if k=b then u else 1)≠0) : t=u := by
  rcases v with ⟨i,j,c⟩
  cases c <;> fin_cases a <;> fin_cases b <;> fin_cases s <;> fin_cases t <;> fin_cases u <;>
    simp_all [localTensor,upTensor,downTensor,Planar.empty,Planar.occupied,Planar.cup]

/-- Unique propagation for either orientation of an actual path. -/
lemma CenterPath.orientation_agree {n : ℕ} (p : CenterPath n)
    (σ τ : Fin (n+1)→Fin 3) (hr : σ 0=τ 0)
    (hs : ∀ i,p.factor i σ≠0) (ht : ∀ i,p.factor i τ≠0) : σ=τ := by
  funext i
  induction i using Fin.induction with
  | zero => exact hr
  | succ i ih =>
    apply localTensor_pair_unique (p.center i) (p.side i.castSucc) (p.side i.succ)
      (p.sides_distinct i) (σ i.castSucc) (σ i.succ) (τ i.succ)
    · exact hs i
    · simpa only [CenterPath.factor,ih] using ht i

lemma CenterPath.selected_orientation_agree {n : ℕ} (p : CenterPath n)
    (σ τ : Wire→Fin 3) (hr : σ (p.edge 0)=τ (p.edge 0))
    (hs : ∀ i,σ (p.edge i)≠1) (ht : ∀ i,τ (p.edge i)≠1)
    (hsn : ∀ i,centerTensor σ (p.center i)≠0)
    (htn : ∀ i,centerTensor τ (p.center i)≠0) :
    ∀ i,σ (p.edge i)=τ (p.edge i) := by
  have he:=p.orientation_agree (fun i=>σ (p.edge i)) (fun i=>τ (p.edge i)) hr
    (fun i=>by rw [←p.factor_of_isolated σ (p.isolated σ hs hsn)];exact hsn i)
    (fun i=>by rw [←p.factor_of_isolated τ (p.isolated τ ht htn)];exact htn i)
  exact congrFun he
end CriticalHoneycomb.Transfer.ChordOrientations

namespace CriticalHoneycomb.Transfer.ChordOrientations
open PhysicalTiles CenterPartition

noncomputable def CenterPath.restrictSpins {n : ℕ} (p : CenterPath n) (σ : Wire→Fin 3) : Wire→Fin 3 :=
  fun w=>if w∈Set.range p.edge then σ w else 1
noncomputable def CenterPath.superpose {n : ℕ} (p : CenterPath n) (σ τ : Wire→Fin 3) : Wire→Fin 3 :=
  fun w=>if w∈Set.range p.edge then σ w else τ w
lemma CenterPath.restrict_center {n : ℕ} (p : CenterPath n) (σ : Wire→Fin 3)
    (hi : ∀ i k,incidentWire (p.center i) k∉Set.range p.edge → σ (incidentWire (p.center i) k)=1)
    (i : Fin n) : centerTensor (p.restrictSpins σ) (p.center i)=centerTensor σ (p.center i) := by
  have he (k) : p.restrictSpins σ (incidentWire (p.center i) k)=σ (incidentWire (p.center i) k) := by
    unfold CenterPath.restrictSpins
    split_ifs with h
    · rfl
    · exact (hi i k h).symm
  unfold centerTensor
  simp only [he]
lemma CenterPath.restrict_off {n : ℕ} (p : CenterPath n) (σ : Wire→Fin 3)
    (v : Center) (h0 : v≠p.point 0) (hl : v≠p.point (Fin.last (n+1)))
    (hv : v∉Set.range p.center) : centerTensor (p.restrictSpins σ) v=1 := by
  apply tensor_empty
  intro k
  exact ite_eq_right (p.incident_off v h0 hl hv k)
lemma CenterPath.restrict_product_ne_zero {n : ℕ} (p : CenterPath n) (D : Finset Center) (σ : Wire→Fin 3)
    (h0 : p.point 0∉D) (hl : p.point (Fin.last (n+1))∉D)
    (he : ∀ i,σ (p.edge i)≠1) (hn : ∀ i,centerTensor σ (p.center i)≠0) :
    centerProduct D (p.restrictSpins σ)≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  by_cases hc : v∈Set.range p.center
  · obtain ⟨i,rfl⟩:=hc
    rw [p.restrict_center σ (p.isolated σ he hn)]
    exact hn i
  · rw [p.restrict_off σ v (fun h=>h0 (h ▸ hv)) (fun h=>hl (h ▸ hv)) hc]
    exact one_ne_zero
lemma CenterPath.restrict_center_agree {n : ℕ} (p : CenterPath n) (σ τ : Wire→Fin 3)
    (he : ∀ i,σ (p.edge i)=τ (p.edge i)) : p.restrictSpins σ=p.restrictSpins τ := by
  funext w
  unfold CenterPath.restrictSpins
  split_ifs with h
  · obtain ⟨i,rfl⟩:=h;exact he i
  · rfl

lemma CenterPath.remove_reference_product {n : ℕ} (p : CenterPath n) (D : Finset Center)
    (σ₀ σ : Wire→Fin 3) (h0 : p.point 0∉D) (hl : p.point (Fin.last (n+1))∉D)
    (he : ∀ i,σ (p.edge i)≠1) (hn : ∀ i,centerTensor σ (p.center i)≠0)
    (ha : ∀ i,σ (p.edge i)=σ₀ (p.edge i)) :
    centerProduct D σ=centerProduct D (p.restrictSpins σ₀)*centerProduct D (p.erase σ) := by
  have heq:=p.restrict_center_agree σ σ₀ ha
  rw [←heq]
  unfold centerProduct
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases hc : v∈Set.range p.center
  · obtain ⟨i,rfl⟩:=hc
    rw [p.erased_center σ (p.isolated σ he hn),mul_one,p.restrict_center σ (p.isolated σ he hn)]
  · rw [p.erased_off σ v (fun h=>h0 (h ▸ hv)) (fun h=>hl (h ▸ hv)) hc,
      p.restrict_off σ v (fun h=>h0 (h ▸ hv)) (fun h=>hl (h ▸ hv)) hc,one_mul]

lemma CenterPath.superpose_tensor {n : ℕ} (p : CenterPath n) (σ τ : Wire→Fin 3)
    (hi : ∀ i k,τ (incidentWire (p.center i) k)=1) (i : Fin n) :
    centerTensor (p.superpose σ τ) (p.center i)=centerTensor (p.restrictSpins σ) (p.center i) := by
  have hs (k) : p.superpose σ τ (incidentWire (p.center i) k)=
      p.restrictSpins σ (incidentWire (p.center i) k) := by
    unfold CenterPath.superpose CenterPath.restrictSpins
    split_ifs
    · rfl
    · exact hi i k
  unfold centerTensor
  simp only [hs]
lemma CenterPath.superpose_off {n : ℕ} (p : CenterPath n) (σ τ : Wire→Fin 3)
    (v : Center) (h0 : v≠p.point 0) (hl : v≠p.point (Fin.last (n+1)))
    (hv : v∉Set.range p.center) : centerTensor (p.superpose σ τ) v=centerTensor τ v := by
  have hs (k) : p.superpose σ τ (incidentWire v k)=τ (incidentWire v k) :=
    ite_eq_right (p.incident_off v h0 hl hv k)
  unfold centerTensor
  simp only [hs]
lemma CenterPath.superpose_product {n : ℕ} (p : CenterPath n) (D : Finset Center)
    (σ τ : Wire→Fin 3) (h0 : p.point 0∉D) (hl : p.point (Fin.last (n+1))∉D)
    (hi : ∀ i k,τ (incidentWire (p.center i) k)=1) :
    centerProduct D (p.superpose σ τ)=centerProduct D (p.restrictSpins σ)*centerProduct D τ := by
  unfold centerProduct
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases hc : v∈Set.range p.center
  · obtain ⟨i,rfl⟩:=hc
    rw [p.superpose_tensor σ τ hi i,tensor_empty τ _ (hi i),mul_one]
  · rw [p.superpose_off σ τ v (fun h=>h0 (h ▸ hv)) (fun h=>hl (h ▸ hv)) hc,
      p.restrict_off σ v (fun h=>h0 (h ▸ hv)) (fun h=>hl (h ▸ hv)) hc,one_mul]
lemma CenterPath.erase_superpose {n : ℕ} (p : CenterPath n) (σ τ : Wire→Fin 3)
    (he : ∀ i,τ (p.edge i)=1) : p.erase (p.superpose σ τ)=τ := by
  funext w
  unfold CenterPath.erase CenterPath.superpose
  split_ifs with h
  · obtain ⟨i,rfl⟩:=h;exact (he i).symm
  · rfl
lemma CenterPath.superpose_erase {n : ℕ} (p : CenterPath n) (σ τ : Wire→Fin 3)
    (he : ∀ i,τ (p.edge i)=σ (p.edge i)) : p.superpose σ (p.erase τ)=τ := by
  funext w
  unfold CenterPath.erase CenterPath.superpose
  split_ifs with h
  · obtain ⟨i,rfl⟩:=h;exact (he i).symm
  · simp only [ite_eq_right h]
lemma CenterPath.selected_superpose_congr {n : ℕ} (p : CenterPath n) (σ : Wire→Fin 3)
    {τ η : Wire→Fin 3} (he : selected τ=selected η) :
    selected (p.superpose σ τ)=selected (p.superpose σ η) := by
  funext w
  unfold selected CenterPath.superpose
  split_ifs
  · rfl
  · exact congrFun he w
end CriticalHoneycomb.Transfer.ChordOrientations

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations
noncomputable def superposeAssignment {W H n : ℕ} (p : CenterPath n)
    (σ : Wire→Fin 3) (x : Assignment W H) : Assignment W H :=
  restrictAssignment (p.superpose σ (assignmentSpins x))
lemma superposeAssignment_spins {W H n : ℕ} (p : CenterPath n) (σ : Wire→Fin 3) (x : Assignment W H)
    (hp : ∀ i,p.edge i∈Set.range (wireEmbedding (W:=W) (H:=H))) :
    assignmentSpins (superposeAssignment p σ x)=p.superpose σ (assignmentSpins x) := by
  apply assignmentSpins_restrict
  intro w hw
  have hn : w∉Set.range p.edge := by rintro ⟨i,rfl⟩;exact hw (hp i)
  rw [CenterPath.superpose,ite_eq_right hn,assignmentSpins_supported x hw]
lemma superpose_sameBoundary {W H n : ℕ} (p : CenterPath n) (σ : Wire→Fin 3)
    {x y : Assignment W H} (h : SameBoundary x y) :
    SameBoundary (superposeAssignment p σ x) (superposeAssignment p σ y) := by
  intro w hw
  change p.superpose σ (assignmentSpins x) (wireEmbedding (.inl w))=
    p.superpose σ (assignmentSpins y) (wireEmbedding (.inl w))
  unfold CenterPath.superpose
  split_ifs
  · rfl
  · simp only [assignmentSpins,spins_wire];exact h w hw

theorem all_orientation_path_factorization {W H n : ℕ} (hW : 0<W) (hH : 0<H)
    (cfg cfgR : Cell W H → Shape)
    (p : CenterPath n) (x₀ : Assignment W H)
    (hx₀ : relativeTerm cfg x₀ x₀≠0)
    (hc : ∀ i, p.center i∈domain W H)
    (h0 : p.point 0∉domain W H) (hl : p.point (Fin.last (n+1))∉domain W H)
    (hcover : ∀ i, p.edge i∈Set.range (wireEmbedding (W:=W) (H:=H)))
    (hsel : ∀ i, assignmentSpins x₀ (p.edge i)≠1)
    (hroot : ∀ x : Assignment W H, SameBoundary x x₀ →
      assignmentSpins x (p.edge 0)=assignmentSpins x₀ (p.edge 0))
    (hR : Matches cfgR (eraseAssignment p x₀).1 (eraseAssignment p x₀).2) :
    (∑ x : Assignment W H, relativeTerm cfg x₀ x)=
      centerProduct (domain W H) (p.restrictSpins (assignmentSpins x₀)) *
      ∑ y : Assignment W H, relativeTerm cfgR (eraseAssignment p x₀) y := by
  classical
  let P := centerProduct (domain W H) (p.restrictSpins (assignmentSpins x₀))
  let F := relativeTerm cfg x₀
  let G := relativeTerm cfgR (eraseAssignment p x₀)
  obtain ⟨hB₀,hM₀,hN₀⟩ := (relativeTerm_ne_zero cfg x₀ x₀).mp hx₀
  have hNcenter₀ (i) : centerTensor (assignmentSpins x₀) (p.center i)≠0 :=
    Finset.prod_ne_zero_iff.mp hN₀ _ (hc i)
  have hP : P≠0 := p.restrict_product_ne_zero _ _ h0 hl hsel hNcenter₀
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
      F x=P*G (eraseAssignment p x) ∧ superposeAssignment p (assignmentSpins x₀) (eraseAssignment p x)=x := by
    obtain ⟨hB,hM,hN⟩ := (relativeTerm_ne_zero cfg x₀ x).mp hx
    have heq : selected (assignmentSpins x)=selected (assignmentSpins x₀) := by
      funext w; exact matches_occupied hW hH hM hM₀ w
    have hs (i) : assignmentSpins x (p.edge i)≠1 := by
      have hh := congrFun heq (p.edge i)
      simpa [selected,spinOccupied,hsel i] using hh
    have hn (i) : centerTensor (assignmentSpins x) (p.center i)≠0 :=
      Finset.prod_ne_zero_iff.mp hN _ (hc i)
    have hr := hroot x hB
    have hagree := p.selected_orientation_agree _ _ hr hs hsel hn hNcenter₀
    have hProd := p.remove_reference_product (domain W H) (assignmentSpins x₀) (assignmentSpins x) h0 hl hs hn hagree
    have hmE : Matches cfgR (eraseAssignment p x).1 (eraseAssignment p x).2 := by
      apply matches_of_occupied_eq hR
      rw [eraseAssignment_spins,eraseAssignment_spins]
      exact selected_erase_congr p heq.symm
    have hbE := erase_sameBoundary p hB
    constructor
    · dsimp only [F,G,P]
      rw [relativeTerm,ite_eq_left ⟨hB,hM⟩,relativeTerm,ite_eq_left ⟨hbE,hmE⟩,eraseAssignment_spins]
      exact hProd
    · apply assignmentSpins_injective
      rw [superposeAssignment_spins p _ _ hcover,eraseAssignment_spins]
      exact p.superpose_erase _ _ hagree
  have backward (y : Assignment W H) (hy : G y≠0) :
      F (superposeAssignment p (assignmentSpins x₀) y)≠0 ∧ eraseAssignment p (superposeAssignment p (assignmentSpins x₀) y)=y := by
    obtain ⟨hB,hM,hN⟩ := (relativeTerm_ne_zero cfgR (eraseAssignment p x₀) y).mp hy
    have heq := RX y hM
    have hlocal (i) (k) : assignmentSpins y (incidentWire (p.center i) k)=1 := by
      have hh := congrFun heq (incidentWire (p.center i) k)
      simpa [selected,spinOccupied,erased_empty i k] using hh
    have he (i) : assignmentSpins y (p.edge i)=1 := by
      have hh := congrFun heq (p.edge i)
      simpa [selected,spinOccupied,CenterPath.erase,Set.mem_range_self] using hh
    have hmF : Matches cfg (superposeAssignment p (assignmentSpins x₀) y).1 (superposeAssignment p (assignmentSpins x₀) y).2 := by
      apply matches_of_occupied_eq hM₀
      rw [superposeAssignment_spins p _ y hcover]
      rw [p.selected_superpose_congr _ heq,p.superpose_erase _ _ (fun _=>rfl)]
    have hfill₀ : superposeAssignment p (assignmentSpins x₀) (eraseAssignment p x₀)=x₀ := by
      apply assignmentSpins_injective
      rw [superposeAssignment_spins p _ _ hcover,eraseAssignment_spins]
      exact p.superpose_erase _ _ (fun _=>rfl)
    have hbF : SameBoundary (superposeAssignment p (assignmentSpins x₀) y) x₀ := by
      simpa only [hfill₀] using (superpose_sameBoundary p (assignmentSpins x₀) hB)
    constructor
    · apply (relativeTerm_ne_zero cfg x₀ _).mpr
      refine ⟨hbF,hmF,?_⟩
      rw [superposeAssignment_spins p _ y hcover,p.superpose_product _ _ _ h0 hl hlocal]
      exact mul_ne_zero hP hN
    · apply assignmentSpins_injective
      rw [eraseAssignment_spins,superposeAssignment_spins p _ y hcover,p.erase_superpose _ _ he]
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
    exact ⟨superposeAssignment p (assignmentSpins x₀) y,Finset.mem_univ _,hh.1,hh.2⟩
  · intro x hx hn
    exact (forward x hn).1


end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.AllPorts
open SimpleGraph FiniteConfigurations

noncomputable instance portFintype (D : Finset Center) : Fintype (Port (D : Set Center)) :=
  Fintype.ofInjective (fun p : Port (D : Set Center)=>(portInside p,p.side)) (by
    intro p q he
    apply Port.wire_ext
    have hi:=congrArg (fun x : Interior D × Fin 3=>x.1.val) he
    have hs:=congrArg Prod.snd he
    change p.inside=q.inside at hi
    change p.side=q.side at hs
    simp only [Port.wire,hi,hs])

abbrev Vertices (D : Finset Center) := Interior D ⊕ Port (D : Set Center)

def selectedRel {D : Finset Center} (s : Wire→Bool) : Vertices D→Vertices D→Prop
  | .inl v,.inl w => ∃ k : Fin 3,neighbor v.val k=w.val ∧ s (incidentWire v.val k)=true
  | .inl v,.inr q => v.val=q.inside ∧ s q.wire=true
  | .inr q,.inl v => v.val=q.inside ∧ s q.wire=true
  | .inr _,.inr _ => False
lemma selectedRel_symm {D : Finset Center} (s : Wire→Bool) :
    ∀ ⦃v w : Vertices D⦄, selectedRel s v w → selectedRel s w v := by
  intro x y h
  cases x with
  | inl v =>
    cases y with
    | inl w =>
      obtain ⟨k,hk,hs⟩ := h
      refine ⟨k,?_,?_⟩
      · rw [←hk,neighbor_neighbor]
      · rw [←hk,incidentWire_neighbor];exact hs
    | inr q => exact h
  | inr q => cases y <;> exact h
noncomputable def graph (D : Finset Center) (s : Wire→Bool) : SimpleGraph (Vertices D) where
  Adj := selectedRel s
  symm := ⟨selectedRel_symm s⟩
  loopless := ⟨by
    intro x h
    cases x with
    | inl v => obtain ⟨k,hk,_⟩:=h;exact neighbor_ne v.val k hk
    | inr q => exact h⟩

noncomputable instance graphDecidable {D : Finset Center} (s : Wire→Bool) :
    DecidableRel (graph D s).Adj := Classical.decRel _

lemma port_neighbors {D : Finset Center} (s : Wire→Bool) (q : Port (D : Set Center)) :
    (graph D s).neighborSet (.inr q)=if s q.wire then {.inl (portInside q)} else ∅ := by
  ext x
  cases hs : s q.wire <;> cases x with
  | inl v => simp [SimpleGraph.neighborSet,graph,selectedRel,hs,portInside,Subtype.ext_iff]
  | inr r => simp [SimpleGraph.neighborSet,graph,selectedRel]
lemma port_degree {D : Finset Center} (s : Wire→Bool) (q : Port (D : Set Center)) :
    (graph D s).degree (.inr q)=(s q.wire).toNat := by
  classical
  rw [←PathComponents.ncard_neighbors,port_neighbors]
  cases hs : s q.wire <;> simp

def sideNeighbor {D : Finset Center} (v : Interior D) (k : Fin 3) : Vertices D→Prop
  | .inl w => neighbor v.val k=w.val
  | .inr q => v.val=q.inside ∧ k=q.side
lemma side_unique {D : Finset Center} (v : Interior D) {k l : Fin 3} {w : Vertices D}
    (hk : sideNeighbor v k w) (hl : sideNeighbor v l w) : k=l := by
  cases w with
  | inl w => exact neighbor_injective v.val (hk.trans hl.symm)
  | inr q => exact hk.2.trans hl.2.symm
lemma neighbor_unique {D : Finset Center} (v : Interior D) (k : Fin 3) {x y : Vertices D}
    (hx : sideNeighbor v k x) (hy : sideNeighbor v k y) : x=y := by
  cases x with
  | inl x => cases y with
    | inl y => exact congrArg Sum.inl (Subtype.ext (hx.symm.trans hy))
    | inr q =>
      have hh : neighbor v.val k=q.outside := by rw [hy.1,hy.2,q.neighbor_side]
      exact (q.outside_not_mem (hh ▸ hx.symm ▸ x.property)).elim
  | inr p => cases y with
    | inl y =>
      have hh : neighbor v.val k=p.outside := by rw [hx.1,hx.2,p.neighbor_side]
      exact (p.outside_not_mem (hh ▸ hy.symm ▸ y.property)).elim
    | inr q =>
      apply congrArg Sum.inr
      apply Port.wire_ext
      simp only [Port.wire,←hx.1,←hy.1,←hx.2,←hy.2]

lemma side_has_neighbor {D : Finset Center} (v : Interior D) (k : Fin 3) :
    ∃ w : Vertices D,sideNeighbor v k w := by
  classical
  by_cases hh : neighbor v.val k∈D
  · exact ⟨.inl ⟨_,hh⟩,rfl⟩
  · let q : Port (D : Set Center) := ⟨v.val,neighbor v.val k,
      (adj_iff_neighbor _ _).mpr ⟨k,rfl⟩,v.property,hh⟩
    refine ⟨.inr q,rfl,?_⟩
    exact neighbor_injective v.val (by exact q.neighbor_side.symm)
lemma side_adj {D : Finset Center} (s : Wire→Bool) (v : Interior D) (k : Fin 3)
    (w : Vertices D) (hk : s (incidentWire v.val k)=true) (hw : sideNeighbor v k w) :
    (graph D s).Adj (.inl v) w := by
  cases w with
  | inl w => exact ⟨k,hw,hk⟩
  | inr q => exact ⟨hw.1,by simpa [Port.wire,←hw.1,←hw.2] using hk⟩
lemma adj_side {D : Finset Center} (s : Wire→Bool) (v : Interior D) (w : Vertices D)
    (h : (graph D s).Adj (.inl v) w) :
    ∃ k : Fin 3,s (incidentWire v.val k)=true ∧ sideNeighbor v k w := by
  cases w with
  | inl w => obtain ⟨k,hw,hk⟩:=h;exact ⟨k,hk,hw⟩
  | inr q => exact ⟨q.side,by simpa [h.1,Port.wire] using h.2,h.1,rfl⟩

noncomputable def neighborEquiv {D : Finset Center} (s : Wire→Bool) (v : Interior D) :
    {k : Fin 3//s (incidentWire v.val k)=true} ≃ (graph D s).neighborSet (.inl v) := by
  classical
  let f : {k : Fin 3//s (incidentWire v.val k)=true}→(graph D s).neighborSet (.inl v) := fun k=>
    ⟨(side_has_neighbor v k.val).choose,side_adj s v k.val _ k.property (side_has_neighbor v k.val).choose_spec⟩
  apply Equiv.ofBijective f
  constructor
  · intro k l he
    apply Subtype.ext
    apply side_unique v (side_has_neighbor v k.val).choose_spec
    have he' := congrArg Subtype.val he
    change (side_has_neighbor v k.val).choose=(side_has_neighbor v l.val).choose at he'
    rw [he']
    exact (side_has_neighbor v l.val).choose_spec
  · intro w
    obtain ⟨k,hk,hw⟩:=adj_side s v w.val w.property
    exact ⟨⟨k,hk⟩,Subtype.ext (neighbor_unique v k (side_has_neighbor v k).choose_spec hw)⟩

lemma center_degree {D : Finset Center} (s : Wire→Bool) (v : Interior D) :
    (graph D s).degree (.inl v)=selectedSideCount s v.val := by
  classical
  rw [←PathComponents.ncard_neighbors]
  change Nat.card ((graph D s).neighborSet (.inl v))=_
  rw [Nat.card_eq_fintype_card,selectedSideCount_eq_card]
  exact (Fintype.card_congr (neighborEquiv s v)).symm

end CriticalHoneycomb.Transfer.AllPorts

namespace CriticalHoneycomb.Transfer.AllPorts
open SimpleGraph FiniteConfigurations

/-- A selected boundary component ends at another selected boundary port.
This is derived from the actual local 0/2 rule and the finite handshake
lemma, with no prescribed pairing assumed. -/
theorem selected_port_partner {D : Finset Center} (s : Wire→Bool)
    (hd : ∀ v∈D,selectedSideCount s v=0 ∨ selectedSideCount s v=2)
    (a : Port (D : Set Center)) (ha : s a.wire=true) :
    ∃ b : Port (D : Set Center), b≠a ∧ s b.wire=true ∧
      ∃ p : (graph D s).Walk (.inr a) (.inr b),p.IsPath ∧
        ∀ v∈p.support,p.toSubgraph.neighborSet v=(graph D s).neighborSet v := by
  classical
  let G := graph D s
  let S : Set (Vertices D) := {v | G.Reachable (.inr a) v}
  let A : S := ⟨.inr a,SimpleGraph.Reachable.rfl⟩
  have deg (v : S) : (G.induce S).degree v=G.degree v := by
    apply G.degree_induce_of_neighborSet_subset
    intro w hw
    exact v.property.trans hw.reachable
  have hA : Odd ((G.induce S).degree A) := by
    rw [deg,show G.degree (.inr a)=1 from by change (graph D s).degree (.inr a)=1; rw [port_degree,ha];rfl]
    decide
  obtain ⟨v,hvA,hv⟩:=(G.induce S).exists_ne_odd_degree_of_exists_odd_degree A hA
  have hodd : Odd (G.degree v.val) := by simpa only [deg] using hv
  cases hvv : v.val with
  | inl u =>
    rw [hvv] at hodd
    change Odd ((graph D s).degree (.inl u)) at hodd
    rw [center_degree] at hodd
    rcases hd u.val u.property with h|h <;> rw [h] at hodd <;> norm_num at hodd
  | inr b =>
    have hba : b≠a := by
      intro he
      apply hvA
      apply Subtype.ext
      exact hvv.trans (congrArg Sum.inr he)
    have hb : s b.wire=true := by
      rw [hvv] at hodd
      change Odd ((graph D s).degree (.inr b)) at hodd
      rw [port_degree] at hodd
      cases hh : s b.wire
      · simp [hh] at hodd
      · rfl
    have hr : G.Reachable (.inr a) (.inr b) := hvv ▸ v.property
    obtain ⟨p,hp⟩:=hr.exists_isPath
    refine ⟨b,hba,hb,p,hp,?_⟩
    have hu (w : Vertices D) : G.degree w≤2 := by
      cases w with
      | inl w =>
        change (graph D s).degree (.inl w)≤2
        rw [center_degree]
        rcases hd w.val w.property with h|h <;> omega
      | inr q => change (graph D s).degree (.inr q)≤2; rw [port_degree];cases s q.wire <;> decide
    intro w hw
    apply PathComponents.path_neighbor_eq G (by simpa using hba.symm)
      (by change (graph D s).degree (.inr a)=1; rw [port_degree,ha];rfl) (by change (graph D s).degree (.inr b)=1; rw [port_degree,hb];rfl) hu p hp hw

lemma port_degree_le_one {D : Finset Center} (s : Wire→Bool) (q : Port (D : Set Center)) :
    (graph D s).degree (.inr q)≤1 := by
  rw [port_degree]
  cases s q.wire <;> decide

end CriticalHoneycomb.Transfer.AllPorts

namespace CriticalHoneycomb.Transfer.PathComponents
open SimpleGraph
variable {α β : Type*} [Fintype α] [Fintype β]

lemma port_mem_support_ends (G : SimpleGraph (α⊕β)) [DecidableRel G.Adj]
    (hd : ∀ q : β,G.degree (.inr q)≤1) {a b q : β}
    (p : G.Walk (.inr a) (.inr b)) (hp : p.IsPath) (hq : Sum.inr q∈p.support) :
    q=a ∨ q=b := by
  classical
  by_contra hh
  have hqa : q≠a := fun he=>hh (Or.inl he)
  have hqb : q≠b := fun he=>hh (Or.inr he)
  obtain ⟨i,hi,hil⟩:=Walk.mem_support_iff_exists_getVert.mp hq
  have hi0 : i≠0 := by
    intro he;subst i
    exact hqa (Sum.inr.inj (hi.symm.trans p.getVert_zero))
  have hiL : i<p.length := by
    apply lt_of_le_of_ne hil
    intro he;subst i
    exact hqb (Sum.inr.inj (hi.symm.trans p.getVert_length))
  have hn : (p.toSubgraph.neighborSet (.inr q)).ncard=2 := by
    rw [←hi,hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hiL]
  have hle:=Set.ncard_le_ncard (p.toSubgraph.neighborSet_subset (.inr q))
  rw [hn,ncard_neighbors] at hle
  have hh:=hd q
  omega

omit [Fintype α] [Fintype β] in
lemma list_all_inl_many (l : List (α⊕β))
    (h : ∀ t∈l,∀ b : β,t≠Sum.inr b) : ∃ xs : List α,xs.map Sum.inl=l := by
  induction l with
  | nil => exact ⟨[],rfl⟩
  | cons t l ih =>
    cases t with
    | inr b => exact (h _ (by simp) b rfl).elim
    | inl x =>
      obtain ⟨xs,hxs⟩:=ih (by aesop)
      exact ⟨x::xs,by simp [hxs]⟩

/-- The inside trace of any simple component between degree-one ports;
other marked boundary ports cannot occur in its interior. -/
lemma support_decomposition_many (G : SimpleGraph (α⊕β)) [DecidableRel G.Adj]
    (hd : ∀ q : β,G.degree (.inr q)≤1) {a b : β} (hab : a≠b)
    (p : G.Walk (.inr a) (.inr b)) (hp : p.IsPath) :
    ∃ xs : List α,p.support=Sum.inr a::(xs.map Sum.inl++[Sum.inr b]) ∧ xs.Nodup := by
  have hs:=p.cons_tail_support.symm
  have hn:=hp.support_nodup
  rw [hs] at hn
  obtain ⟨hna,hnt⟩:=List.nodup_cons.mp hn
  have ht : p.support.tail.getLast?=some (.inr b) := by
    have hl : p.support.getLast?=some (.inr b) := by
      rw [List.getLast?_eq_some_getLast (by simp),p.getLast_support]
    cases h : p.support.tail with
    | nil =>
      have he:=congrArg List.getLast? hs
      simp [h,hl] at he
      exact (hab he.symm).elim
    | cons t ts =>
      have he:=congrArg List.getLast? hs
      simpa [h,hl] using he.symm
  obtain ⟨mid,hmid⟩:=List.getLast?_eq_some_iff.mp ht
  rw [hmid] at hna hnt
  obtain ⟨hnm,_,hdm⟩:=List.nodup_append.mp hnt
  obtain ⟨xs,hxs⟩:=list_all_inl_many mid (by
    intro t ht q he
    have hm : Sum.inr q∈p.support := by rw [hs,hmid];simp [←he,ht]
    rcases port_mem_support_ends G hd p hp hm with hqa|hqb
    · subst q
      exact hna (by simp [←he,ht])
    · subst q
      exact hdm t ht (.inr b) (by simp) he)
  exact ⟨xs,by simpa [hmid,←hxs] using hs,List.Nodup.of_map Sum.inl (hxs.symm ▸ hnm)⟩
end CriticalHoneycomb.Transfer.PathComponents

namespace CriticalHoneycomb.Transfer.AllPorts
open SimpleGraph FiniteConfigurations ChordOrientations PhysicalTiles CenterPartition

def hardRel {D : Finset Center} : Vertices D→Vertices D→Prop
  | .inl v,.inl w => CriticalHoneycomb.Adj v.val w.val
  | .inl v,.inr q => v=portInside q
  | .inr q,.inl v => v=portInside q
  | .inr _,.inr _ => False
lemma selected_hard {D : Finset Center} (s : Wire→Bool) (v w : Vertices D)
    (h : (graph D s).Adj v w) : hardRel v w := by
  cases v with
  | inl v => cases w with
    | inl w => obtain ⟨k,hk,_⟩:=h;exact (adj_iff_neighbor _ _).mpr ⟨k,hk⟩
    | inr q => exact Subtype.ext h.1
  | inr q => cases w with
    | inl v => exact Subtype.ext h.1
    | inr r => exact h
lemma chain_snoc_ports {D : Finset Center} (b : Port (D : Set Center)) (xs : List (Interior D)) :
    (xs.map Sum.inl++[Sum.inr b]).IsChain hardRel ↔
      xs.IsChain (fun x y=>CriticalHoneycomb.Adj x.val y.val) ∧ ∀ z∈xs.getLast?,z=portInside b := by
  rw [List.isChain_append,List.isChain_map]
  constructor
  · rintro ⟨hc,_,hl⟩
    refine ⟨hc,?_⟩
    intro z hz
    exact hl (.inl z) (by simpa only [List.getLast?_map] using Option.mem_map.mpr ⟨z,hz,rfl⟩)
      (.inr b) (by simp)
  · rintro ⟨hc,hl⟩
    refine ⟨hc,by simp,?_⟩
    intro x hx y hy
    have hy' : Sum.inr b=y := by simpa using hy
    subst y
    rw [List.getLast?_map] at hx
    obtain ⟨z,hz,rfl⟩ := Option.mem_map.mp hx
    exact hl z hz

lemma chain_ports {D : Finset Center} (a b : Port (D : Set Center)) (xs : List (Interior D)) :
    (Sum.inr a::(xs.map Sum.inl++[Sum.inr b])).IsChain hardRel ↔
      xs.IsChain (fun x y=>CriticalHoneycomb.Adj x.val y.val) ∧
        xs.head?=some (portInside a) ∧ xs.getLast?=some (portInside b) := by
  cases xs with
  | nil => simp [hardRel]
  | cons x xs =>
    rw [List.isChain_cons,chain_snoc_ports]
    have hh : (∀ y∈((x::xs).map Sum.inl++[Sum.inr b]).head?,hardRel (.inr a) y) ↔ x=portInside a := by
      simp [hardRel]
    have hl : (∀ z∈(x::xs).getLast?,z=portInside b) ↔ (x::xs).getLast?=some (portInside b) := by
      rw [List.getLast?_eq_some_getLast (by simp)]
      simp
    rw [hh,hl]
    simp only [List.head?_cons,Option.some.injEq]
    tauto

noncomputable def vertexCenter {D : Finset Center} : Vertices D→Center
  | .inl v => v.val
  | .inr q => q.outside
lemma selected_to_actual {D : Finset Center} (s : Wire→Bool) (x y : Vertices D)
    (h : (graph D s).Adj x y) :
    ∃ k : Fin 3,neighbor (vertexCenter x) k=vertexCenter y ∧
      s (incidentWire (vertexCenter x) k)=true := by
  cases x with
  | inl v => cases y with
    | inl w => exact h
    | inr q =>
      refine ⟨q.side,?_,?_⟩
      · change neighbor v.val q.side=q.outside
        rw [h.1];exact q.neighbor_side
      · change s (incidentWire v.val _)=true
        rw [h.1];exact h.2
  | inr q => cases y with
    | inl v =>
      refine ⟨q.side,?_,?_⟩
      · change neighbor q.outside _=v.val
        rw [←q.neighbor_side,neighbor_neighbor,h.1]
      · change s (incidentWire q.outside _)=true
        rw [←q.neighbor_side,incidentWire_neighbor]
        exact h.2
    | inr r => exact h.elim

lemma chord_edges {D : Finset Center} {a b : Port (D : Set Center)}
    (γ : Chord (D : Set Center) a b) (hab : a.outside≠b.outside) (s : Wire→Bool)
    (xs : List (Interior D)) (p : (graph D s).Walk (.inr a) (.inr b))
    (hm : xs.map Subtype.val=γ.val)
    (hs : p.support=Sum.inr a::(xs.map Sum.inl++[Sum.inr b])) :
    ∀ i,s ((ofChord γ hab).edge i)=true := by
  let R : Center→Center→Prop := fun x y=>∃ k : Fin 3,
    neighbor x k=y ∧ s (incidentWire x k)=true
  have hc : (p.support.map vertexCenter).IsChain R :=
    List.isChain_map_of_isChain _ (selected_to_actual s) p.isChain_adj_support
  have hl : p.support.map vertexCenter=extendedTrace γ := by
    rw [hs,List.map_cons,List.map_append,List.map_map]
    have hx : (fun x : Interior D=>vertexCenter (Sum.inl x))=Subtype.val := rfl
    simp only [Function.comp_def,hm,List.map_cons,List.map_nil,vertexCenter,extendedTrace]
  rw [hl] at hc
  intro i
  obtain ⟨k,hk,hsk⟩:=List.isChain_iff_getElem.mp hc i.val (by rw [extendedTrace_length];omega)
  have hp : neighbor ((ofChord γ hab).point i.castSucc) k=(ofChord γ hab).point i.succ := hk
  have he : k=(ofChord γ hab).side i := neighbor_injective _ (hp.trans ((ofChord γ hab).step i).symm)
  change s (incidentWire ((ofChord γ hab).point i.castSucc) ((ofChord γ hab).side i))=true
  rw [←he];exact hsk

/-- At each selected port of an actual nonzero configuration, its isolated
component is a literal simple-center chord, even with other marked ports. -/
theorem nonzero_contains_chord {D : Finset Center} (σ : Wire→Fin 3)
    (h : centerProduct D σ≠0) (a : Port (D : Set Center))
    (ha : σ a.wire≠1) :
    ∃ b : Port (D : Set Center),b≠a ∧ σ b.wire≠1 ∧
      ∃ γ : Chord (D : Set Center) a b,
        ∀ hab : a.outside≠b.outside,∀ i,σ ((ofChord γ hab).edge i)≠1 := by
  have hd (v) (hv : v∈D) : selectedSideCount (selected σ) v=0 ∨ selectedSideCount (selected σ) v=2 :=
    nonzero_center_degree σ v (Finset.prod_ne_zero_iff.mp h v hv)
  have has : selected σ a.wire=true := by simpa [selected,spinOccupied] using ha
  obtain ⟨b,hba,hb,p,hp,_⟩:=selected_port_partner (selected σ) hd a has
  obtain ⟨xs,hxs,hn⟩:=PathComponents.support_decomposition_many (graph D (selected σ))
    (port_degree_le_one _) hba.symm p hp
  have hch : p.support.IsChain hardRel := p.isChain_adj_support.imp (selected_hard _)
  rw [hxs] at hch
  obtain ⟨hchain,hhead,hlast⟩:=(chain_ports a b xs).mp hch
  let γ : Chord (D : Set Center) a b := ⟨xs.map Subtype.val,by
    refine ⟨⟨hn.map Subtype.val_injective,?_,?_⟩,?_,?_⟩
    · exact (List.isChain_map Subtype.val).mpr hchain
    · intro v hv;obtain ⟨x,_,rfl⟩:=List.mem_map.mp hv;exact x.property
    · rw [List.head?_map,hhead];rfl
    · rw [List.getLast?_map,hlast];rfl⟩
  refine ⟨b,hba,by simpa [selected,spinOccupied] using hb,γ,?_⟩
  intro hab i
  have he:=chord_edges γ hab (selected σ) xs p rfl hxs i
  simpa [selected,spinOccupied] using he
end CriticalHoneycomb.Transfer.AllPorts

namespace CriticalHoneycomb.Transfer.RasterGrid
lemma port_exhaustive {W H : ℕ} (p : Port (domain (W+1) (H+1) : Set Center)) :
    (∃ j,p=westPort W H j) ∨ (∃ j,p=eastPort W H j) ∨
      (∃ i,p=southPort W H i) ∨ (∃ i,p=northPort W H i) := by
  have hh:=boundary_wire_exhaustive p.inside_mem p.side
    (by rw [p.neighbor_side];exact p.outside_not_mem)
  rcases hh with ⟨j,hj⟩|⟨j,hj⟩|⟨i,hi⟩|⟨i,hi⟩
  · exact Or.inl ⟨j,Port.wire_ext _ _ hj⟩
  · exact Or.inr (Or.inl ⟨j,Port.wire_ext _ _ hj⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i,Port.wire_ext _ _ hi⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i,Port.wire_ext _ _ hi⟩))

lemma port_outside_injective (W H : ℕ) :
    Function.Injective (fun p : Port (domain (W+1) (H+1) : Set Center)=>p.outside) := by
  intro p q he
  rcases port_exhaustive p with ⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩ <;>
    rcases port_exhaustive q with ⟨j,rfl⟩|⟨j,rfl⟩|⟨j,rfl⟩|⟨j,rfl⟩ <;>
    simp only [westPort,eastPort,southPort,northPort,up,down,Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false,and_false,and_true] at he
  all_goals first
    | exact he.elim
    | have hij : i=j := by apply Fin.ext;omega
      subst j
      rfl
    | have hi:=i.isLt; have hj:=j.isLt; omega
end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations

lemma sameBoundary_port {W H : ℕ} {x y : Assignment (W+1) (H+1)} (h : SameBoundary x y)
    (a : Port (domain (W+1) (H+1) : Set Center)) :
    assignmentSpins x a.wire=assignmentSpins y a.wire := by
  rcases port_exhaustive a with ⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩
  · rw [westPort_wire,assignmentSpins,assignmentSpins,spins_wire,spins_wire]
    exact h _ (Or.inl rfl)
  · rw [eastPort_wire,assignmentSpins,assignmentSpins,spins_wire,spins_wire]
    exact h _ (Or.inr rfl)
  · rw [southPort_wire,assignmentSpins,assignmentSpins,spins_wire,spins_wire]
    exact h _ (Or.inl rfl)
  · rw [northPort_wire,assignmentSpins,assignmentSpins,spins_wire,spins_wire]
    exact h _ (Or.inr rfl)

lemma relativeTerm_change_reference {W H : ℕ} (cfg : Cell W H→Shape)
    {x y : Assignment W H} (h : SameBoundary y x) : relativeTerm cfg x=relativeTerm cfg y := by
  funext z
  have hb : SameBoundary z x ↔ SameBoundary z y :=
    ⟨fun hh=>sameBoundary_trans hh (sameBoundary_symm h),fun hh=>sameBoundary_trans hh h⟩
  simp only [relativeTerm,hb]

noncomputable def occupiedWires {W H : ℕ} (x : Assignment W H) : Finset (FullWire W H) :=
  Finset.univ.filter (fun w=>Sum.elim x.1 x.2 w≠1)

lemma erase_occupied_subset {W H n : ℕ} (p : CenterPath n) (x : Assignment W H) :
    occupiedWires (eraseAssignment p x)⊆occupiedWires x := by
  intro w hw
  have he : assignmentSpins (eraseAssignment p x) (wireEmbedding w)≠1 := by
    simpa only [occupiedWires,Finset.mem_filter,Finset.mem_univ,true_and,assignmentSpins,spins_wire] using hw
  rw [eraseAssignment_spins] at he
  have hn : assignmentSpins x (wireEmbedding w)≠1 := by
    unfold CenterPath.erase at he
    split_ifs at he with h
    · exact (he rfl).elim
    · exact he
  simpa only [occupiedWires,Finset.mem_filter,Finset.mem_univ,true_and,assignmentSpins,spins_wire] using hn

lemma erase_occupied_card_lt {W H n : ℕ} (p : CenterPath n) (x : Assignment W H)
    (hc : p.edge 0∈Set.range (wireEmbedding (W:=W) (H:=H)))
    (hs : assignmentSpins x (p.edge 0)≠1) :
    (occupiedWires (eraseAssignment p x)).card<(occupiedWires x).card := by
  obtain ⟨w,hw⟩:=hc
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨erase_occupied_subset p x,?_⟩
  intro heq
  have hm : w∈occupiedWires x := by
    simpa only [occupiedWires,Finset.mem_filter,Finset.mem_univ,true_and,←hw,assignmentSpins,spins_wire] using hs
  rw [←heq] at hm
  have he : assignmentSpins (eraseAssignment p x) (wireEmbedding w)≠1 := by
    simpa only [occupiedWires,Finset.mem_filter,Finset.mem_univ,true_and,assignmentSpins,spins_wire] using hm
  rw [eraseAssignment_spins,hw,CenterPath.erase,ite_eq_left (Set.mem_range_self 0)] at he
  exact he rfl

/-- One genuine all-boundary recursion step: an actual chord is removed,
any detached cycles remain in the residual sum, and the finite support
strictly decreases. No global path expansion is assumed. -/
theorem boundary_recursion_step {W H : ℕ} (cfg : Cell (W+1) (H+1)→Shape)
    (x : Assignment (W+1) (H+1))
    (hx : relativeTerm cfg x x≠0)
    (a : Port (domain (W+1) (H+1) : Set Center))
    (ha : assignmentSpins x a.wire≠1) :
    ∃ (b : Port (domain (W+1) (H+1) : Set Center)) (hab : a.outside≠b.outside)
      (γ : Chord (domain (W+1) (H+1) : Set Center) a b)
      (cfgR : Cell (W+1) (H+1)→Shape),
      let p:=ofChord γ hab
      (∀ i,assignmentSpins x (p.edge i)≠1) ∧
      relativeTerm cfgR (eraseAssignment p x) (eraseAssignment p x)≠0 ∧
      (occupiedWires (eraseAssignment p x)).card<(occupiedWires x).card ∧
      (∑ z : Assignment (W+1) (H+1),relativeTerm cfg x z)=
        centerProduct (domain (W+1) (H+1)) (p.restrictSpins (assignmentSpins x))*
          ∑ z : Assignment (W+1) (H+1),relativeTerm cfgR (eraseAssignment p x) z := by
  classical
  obtain ⟨_,hM,hN⟩:=(relativeTerm_ne_zero cfg x x).mp hx
  obtain ⟨b,hba,_,γ,hsel⟩:=AllPorts.nonzero_contains_chord (assignmentSpins x) hN a ha
  have hab : a.outside≠b.outside := fun hh=>hba ((port_outside_injective W H) hh).symm
  let p:=ofChord γ hab
  have hc : ∀ i,p.center i∈domain (W+1) (H+1) := ofChord_center_mem γ hab
  have h0 : p.point 0∉domain (W+1) (H+1) := by
    rw [ofChord_first];exact a.outside_not_mem
  have hl : p.point (Fin.last (γ.val.length+1))∉domain (W+1) (H+1) := by
    rw [ofChord_last];exact b.outside_not_mem
  have hcover:=path_wire_covered p (chord_length_pos γ) hc
  have hs:=hsel hab
  have hn (i) : centerTensor (assignmentSpins x) (p.center i)≠0 :=
    Finset.prod_ne_zero_iff.mp hN _ (hc i)
  have hprod:=p.remove_reference_product _ (assignmentSpins x) (assignmentSpins x) h0 hl hs hn (fun _=>rfl)
  have hE : centerProduct (domain (W+1) (H+1)) (assignmentSpins (eraseAssignment p x))≠0 := by
    rw [eraseAssignment_spins]
    intro he;rw [he,mul_zero] at hprod;exact hN hprod
  let cfgR:=occupancyShape (eraseAssignment p x).1 (eraseAssignment p x).2 hE
  have hR : Matches cfgR (eraseAssignment p x).1 (eraseAssignment p x).2 := occupancyShape_matches _ _ _
  refine ⟨b,hab,γ,cfgR,hs,?_,erase_occupied_card_lt p x (hcover 0) (hs 0),?_⟩
  · exact (relativeTerm_ne_zero _ _ _).mpr ⟨sameBoundary_refl _,hR,hE⟩
  · apply all_orientation_path_factorization (Nat.succ_pos W) (Nat.succ_pos H)
      cfg cfgR p x hx hc h0 hl hcover hs _ hR
    intro y hy
    rw [ofChord_first_edge]
    exact sameBoundary_port hy a
end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations

lemma ports_vacuum_sameBoundary {W H : ℕ} (x : Assignment (W+1) (H+1))
    (h : ∀ a : Port (domain (W+1) (H+1) : Set Center),assignmentSpins x a.wire=1) :
    SameBoundary x ((fun _=>1),(fun _=>1)) := by
  intro w hw
  cases w with
  | inl w =>
    rcases w with ⟨i,j⟩
    rcases hw with rfl|rfl
    · have hh:=h (westPort W H j)
      simpa only [westPort_wire,assignmentSpins,spins_wire,Sum.elim_inl] using hh
    · have hh:=h (eastPort W H j)
      simpa only [eastPort_wire,assignmentSpins,spins_wire,Sum.elim_inl] using hh
  | inr w =>
    rcases w with ⟨i,j⟩
    rcases hw with rfl|rfl
    · have hh:=h (southPort W H i)
      simpa only [southPort_wire,assignmentSpins,spins_wire,Sum.elim_inl] using hh
    · have hh:=h (northPort W H i)
      simpa only [northPort_wire,assignmentSpins,spins_wire,Sum.elim_inl] using hh

lemma relative_sum_vacuum {W H : ℕ} (cfg : Cell (W+1) (H+1)→Shape)
    (x : Assignment (W+1) (H+1))
    (hv : ∀ a : Port (domain (W+1) (H+1) : Set Center),assignmentSpins x a.wire=1) :
    (∑ y : Assignment (W+1) (H+1),relativeTerm cfg x y)=
      (kappa:ℂ)^(∑ t,(cfg t).visits)*chosenPartition cfg (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1) := by
  rw [relativeTerm_change_reference cfg (sameBoundary_symm (ports_vacuum_sameBoundary x hv))]
  simp only [relativeTerm_eq_masked]
  exact sum_maskedTerm _ _ _ _ _

lemma nonzero_vacuum_empty {W H : ℕ} (cfg : Cell (W+1) (H+1)→Shape)
    (x : Assignment (W+1) (H+1)) (hx : relativeTerm cfg x x≠0)
    (hn : (∑ y : Assignment (W+1) (H+1),relativeTerm cfg x y)≠0)
    (hv : ∀ a : Port (domain (W+1) (H+1) : Set Center),assignmentSpins x a.wire=1) :
    x=((fun _=>1),(fun _=>1)) ∧ (∑ y : Assignment (W+1) (H+1),relativeTerm cfg x y)=1 := by
  have he : cfg=fun _=>.empty := by
    by_contra hh
    have hz:=chosen_nonempty_vacuum_zero cfg hh
    rw [relative_sum_vacuum cfg x hv,hz,mul_zero] at hn
    exact hn rfl
  subst cfg
  have hM:=(relativeTerm_ne_zero _ _ _).mp hx |>.2.1
  have hs:=assignment_empty (Nat.succ_pos W) (Nat.succ_pos H) x hM
  constructor
  · apply assignmentSpins_injective
    rw [hs]
    symm
    apply assignmentSpins_restrict (fun _=>1)
    intro w hw;rfl
  · rw [relative_sum_vacuum _ x hv,chosen_empty_partition]
    simp [Shape.visits]
end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations

/-- Literal chord components with endpoints on any two distinct rectangle ports. -/
structure BoundaryChord (W H : ℕ) where
  source : Port (domain (W+1) (H+1) : Set Center)
  target : Port (domain (W+1) (H+1) : Set Center)
  distinct : source.outside≠target.outside
  chord : Chord (domain (W+1) (H+1) : Set Center) source target
noncomputable def BoundaryChord.path {W H : ℕ} (c : BoundaryChord W H) : CenterPath c.chord.val.length :=
  ofChord c.chord c.distinct
noncomputable def BoundaryChord.amplitude {W H : ℕ} (c : BoundaryChord W H)
    (x : Assignment (W+1) (H+1)) : ℂ :=
  centerProduct (domain (W+1) (H+1)) (c.path.restrictSpins (assignmentSpins x))
noncomputable def systemAmplitude {W H : ℕ} (x : Assignment (W+1) (H+1)) : List (BoundaryChord W H)→ℂ
  | []=>1
  | c::cs=>c.amplitude x*systemAmplitude (eraseAssignment c.path x) cs

/-- A fully selected list of actual path components, ending with no occupied
wire. This is a structural conclusion, not an axiom enumerating tensor terms. -/
inductive SelectedSystem {W H : ℕ} : Assignment (W+1) (H+1)→List (BoundaryChord W H)→Prop
  | nil : SelectedSystem ((fun _=>1),(fun _=>1)) []
  | cons (x : Assignment (W+1) (H+1)) (c : BoundaryChord W H) (cs : List (BoundaryChord W H))
      (selected : ∀ i,assignmentSpins x (c.path.edge i)≠1)
      (nonzero : ∀ i,centerTensor (assignmentSpins x) (c.path.center i)≠0)
      (rest : SelectedSystem (eraseAssignment c.path x) cs) : SelectedSystem x (c::cs)

/-- No detached polygon survives the all-boundary orientation sum. Every
nonzero resolved shape is a finite system of literal honeycomb chords,
and its coefficient is the exact product of their isolated amplitudes. -/
theorem all_boundary_shape_decomposition {W H : ℕ} (cfg : Cell (W+1) (H+1)→Shape)
    (x : Assignment (W+1) (H+1)) (hx : relativeTerm cfg x x≠0)
    (hn : (∑ y : Assignment (W+1) (H+1),relativeTerm cfg x y)≠0) :
    ∃ cs : List (BoundaryChord W H),SelectedSystem x cs ∧
      (∑ y : Assignment (W+1) (H+1),relativeTerm cfg x y)=systemAmplitude x cs := by
  classical
  generalize hm : (occupiedWires x).card=m
  induction m using Nat.strong_induction_on generalizing cfg x with
  | h m ih =>
    by_cases hb : ∃ a : Port (domain (W+1) (H+1) : Set Center),assignmentSpins x a.wire≠1
    · obtain ⟨a,ha⟩:=hb
      obtain ⟨b,hab,γ,cfgR,hs,hR,hlt,hfact⟩:=boundary_recursion_step cfg x hx a ha
      let c : BoundaryChord W H:=⟨a,b,hab,γ⟩
      have hNR : (∑ z : Assignment (W+1) (H+1),relativeTerm cfgR (eraseAssignment c.path x) z)≠0 := by
        exact (mul_ne_zero_iff.mp (hfact ▸ hn)).2
      obtain ⟨cs,hcs,hval⟩:=ih (occupiedWires (eraseAssignment c.path x)).card
        (by simpa [c,BoundaryChord.path,hm] using hlt) cfgR (eraseAssignment c.path x) hR hNR rfl
      refine ⟨c::cs,SelectedSystem.cons x c cs hs ?_ hcs,?_⟩
      · intro i
        exact Finset.prod_ne_zero_iff.mp ((relativeTerm_ne_zero _ _ _).mp hx).2.2 _
          (ofChord_center_mem γ hab i)
      · change _=c.amplitude x*systemAmplitude (eraseAssignment c.path x) cs
        rw [←hval]
        exact hfact
    · have hv : ∀ a : Port (domain (W+1) (H+1) : Set Center),assignmentSpins x a.wire=1 := by
        intro a;by_contra hh;exact hb ⟨a,hh⟩
      obtain ⟨he,hv⟩:=nonzero_vacuum_empty cfg x hx hn hv
      refine ⟨[],?_,hv⟩
      rw [he]
      exact SelectedSystem.nil
end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.ChordOrientations
open PhysicalTiles CenterPartition
lemma physical_phase_norm : ‖Planar.phase‖=1 := by
  exact Complex.norm_exp_ofReal_mul_I _
lemma localTensor_norm_nonempty (v : Center) (s : Fin 3→Fin 3)
    (hn : localTensor v s≠0) (k : Fin 3) (hk : s k≠1) : ‖localTensor v s‖=kappa := by
  have he : s=![s 0,s 1,s 2] := by ext i;fin_cases i<;>rfl
  rw [he] at hn hk ⊢
  rcases v with ⟨i,j,b⟩
  generalize ha : s 0=a at hn hk ⊢
  generalize hb : s 1=c at hn hk ⊢
  generalize hc : s 2=d at hn hk ⊢
  cases b <;> fin_cases k <;> fin_cases a <;> fin_cases c <;> fin_cases d <;>
    simp_all [localTensor,upTensor,downTensor,Planar.empty,Planar.occupied,Planar.cup,
      physical_phase_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_pos FiniteContinuation.kappa_positive]

lemma CenterPath.restrict_product_norm {n : ℕ} (p : CenterPath n) (D : Finset Center)
    (σ : Wire→Fin 3) (hc : ∀ i,p.center i∈D)
    (h0 : p.point 0∉D) (hl : p.point (Fin.last (n+1))∉D)
    (hs : ∀ i,σ (p.edge i)≠1) (hn : ∀ i,centerTensor σ (p.center i)≠0) :
    ‖centerProduct D (p.restrictSpins σ)‖=kappa^n := by
  classical
  have hinj := p.center_injective
  let S : Finset Center:=Finset.univ.image p.center
  have hS : S⊆D := by intro v hv;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv;exact hc i
  have hoff (v) (hv : v∈D) (hh : v∉S) : centerTensor (p.restrictSpins σ) v=1 := by
    apply p.restrict_off σ v (fun he=>h0 (he ▸ hv)) (fun he=>hl (he ▸ hv))
    simpa [S] using hh
  rw [centerProduct]
  rw [←Finset.prod_subset hS (fun v hv hh=>hoff v hv hh)]
  rw [Finset.prod_image (fun i _ j _ he=>hinj he),norm_prod]
  have hnorm (i) : ‖centerTensor (p.restrictSpins σ) (p.center i)‖=kappa := by
    rw [p.restrict_center σ (p.isolated σ hs hn)]
    apply localTensor_norm_nonempty (p.center i) (fun k=>σ (incidentWire (p.center i) k))
      (hn i) (p.side i.castSucc)
    rw [p.in_wire]
    exact hs i.castSucc
  simp only [hnorm,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
end CriticalHoneycomb.Transfer.ChordOrientations

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations

def systemNodes {W H : ℕ} (cs : List (BoundaryChord W H)) : List Center :=
  cs.flatMap (fun c=>c.chord.val)
lemma BoundaryChord.nodes_mem {W H : ℕ} (c : BoundaryChord W H) (v : Center) :
    v∈c.chord.val ↔ v∈Set.range c.path.center := by
  constructor
  · intro hv
    obtain ⟨i,hi⟩:=List.mem_iff_get.mp hv
    refine ⟨i,?_⟩
    simpa [BoundaryChord.path,ofChord_center] using hi
  · rintro ⟨i,rfl⟩
    rw [BoundaryChord.path,ofChord_center]
    exact List.getElem_mem _
lemma BoundaryChord.amplitude_norm {W H : ℕ} (c : BoundaryChord W H)
    (x : Assignment (W+1) (H+1))
    (hs : ∀ i,assignmentSpins x (c.path.edge i)≠1)
    (hn : ∀ i,centerTensor (assignmentSpins x) (c.path.center i)≠0) :
    ‖c.amplitude x‖=kappa^c.chord.val.length := by
  apply c.path.restrict_product_norm _ _ (ofChord_center_mem c.chord c.distinct) _ _ hs hn
  · rw [BoundaryChord.path,ofChord_first];exact c.source.outside_not_mem
  · rw [BoundaryChord.path,ofChord_last];exact c.target.outside_not_mem

lemma SelectedSystem.amplitude_norm {W H : ℕ} {x : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (h : SelectedSystem x cs) :
    ‖systemAmplitude x cs‖=kappa^(systemNodes cs).length := by
  induction h with
  | nil => simp [systemAmplitude,systemNodes]
  | cons x c cs hs hn hr ih =>
    rw [systemAmplitude,norm_mul,c.amplitude_norm x hs hn,ih]
    simp only [systemNodes,List.flatMap_cons,List.length_append,pow_add]

lemma SelectedSystem.empty_center {W H : ℕ} {x : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (h : SelectedSystem x cs) (v : Center)
    (hv : ∀ k,assignmentSpins x (incidentWire v k)=1) : v∉systemNodes cs := by
  induction h with
  | nil => simp [systemNodes]
  | cons x c cs hs hn hr ih =>
    have hoff : v∉c.chord.val := by
      intro hh
      obtain ⟨i,hi⟩:=(c.nodes_mem v).mp hh
      have he:=hv (c.path.side i.castSucc)
      rw [←hi,c.path.in_wire] at he
      exact hs i.castSucc he
    have hrest : ∀ k,assignmentSpins (eraseAssignment c.path x) (incidentWire v k)=1 := by
      intro k;rw [eraseAssignment_spins]
      unfold CenterPath.erase
      split_ifs
      · rfl
      · exact hv k
    change v∉c.chord.val++systemNodes cs
    intro hm
    exact (List.mem_append.mp hm).elim hoff (ih hrest)

lemma SelectedSystem.nodes_nodup {W H : ℕ} {x : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (h : SelectedSystem x cs) : (systemNodes cs).Nodup := by
  induction h with
  | nil => simp [systemNodes]
  | cons x c cs hs hn hr ih =>
    apply List.nodup_append.mpr
    refine ⟨c.chord.property.1.1,ih,?_⟩
    intro v hv w hw he
    subst w
    obtain ⟨i,rfl⟩:=(c.nodes_mem v).mp hv
    apply hr.empty_center _ _ hw
    intro k
    rw [eraseAssignment_spins]
    unfold CenterPath.erase
    split_ifs with he
    · rfl
    · exact c.path.isolated _ hs hn i k he
end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations

lemma SelectedSystem.edge_union {W H : ℕ} {x : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (h : SelectedSystem x cs) (w : Wire) :
    assignmentSpins x w≠1 ↔ ∃ c∈cs,w∈Set.range c.path.edge := by
  induction h with
  | nil =>
    have he : assignmentSpins ((fun _ : GridWire (W+1) (H+1)=>1),(fun _=>1))=(fun _=>1) := by
      exact assignmentSpins_restrict (fun _=>1) (fun _ _=>rfl)
    simp [he]
  | cons x c cs hs hn hr ih =>
    by_cases hw : w∈Set.range c.path.edge
    · obtain ⟨i,hi⟩:=hw
      exact iff_of_true (hi ▸ hs i) ⟨c,List.mem_cons_self,⟨i,hi⟩⟩
    · have he : assignmentSpins (eraseAssignment c.path x) w=assignmentSpins x w := by
        rw [eraseAssignment_spins,CenterPath.erase,ite_eq_right hw]
      rw [←he,ih]
      simp only [List.mem_cons,exists_eq_or_imp,hw,false_or]

lemma SelectedSystem.selected_eq {W H : ℕ} {x y : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (hx : SelectedSystem x cs) (hy : SelectedSystem y cs) :
    selected (assignmentSpins x)=selected (assignmentSpins y) := by
  funext w
  have he:=(hx.edge_union w).trans (hy.edge_union w).symm
  by_cases hh : assignmentSpins x w≠1
  · have hh':=he.mp hh
    simp [selected,spinOccupied,hh,hh']
  · have hh' : ¬assignmentSpins y w≠1:=fun hh'=>hh (he.mpr hh')
    simp [selected,spinOccupied,hh,hh']

lemma SelectedSystem.shape_unique {W H : ℕ} {x y : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (hx : SelectedSystem x cs) (hy : SelectedSystem y cs)
    {cfg cfg' : Cell (W+1) (H+1)→Shape} (hM : Matches cfg x.1 x.2) (hM' : Matches cfg' y.1 y.2) :
    cfg=cfg' := by
  exact matches_unique hM (matches_of_occupied_eq hM' (hy.selected_eq hx))

/-- Full all-boundary shape decomposition at exactly its actual κ-weight,
including center-disjointness and the uniqueness required for subsequent
mass comparisons. -/
theorem all_boundary_literal_norm {W H : ℕ} (cfg : Cell (W+1) (H+1)→Shape)
    (x : Assignment (W+1) (H+1)) (hx : relativeTerm cfg x x≠0)
    (hn : (∑ y : Assignment (W+1) (H+1),relativeTerm cfg x y)≠0) :
    ∃ cs : List (BoundaryChord W H),SelectedSystem x cs ∧ (systemNodes cs).Nodup ∧
      ‖∑ y : Assignment (W+1) (H+1),relativeTerm cfg x y‖=kappa^(systemNodes cs).length := by
  obtain ⟨cs,hcs,he⟩:=all_boundary_shape_decomposition cfg x hx hn
  exact ⟨cs,hcs,hcs.nodes_nodup,he ▸ hcs.amplitude_norm⟩
end CriticalHoneycomb.Transfer.RasterGrid

end OAI
