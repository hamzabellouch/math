import OAI.Combinatorics.HoneycombChords.ChordTensors

namespace OAI

/-!
# Literal chord expansions in finite rectangles

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition
open scoped BigOperators

def Matches {W H : ℕ} (cfg : Cell W H → Shape)
    (σ : GridWire W H → Fin 3) (μ : Cell W H → Fin 3) : Prop :=
  ∀ t, spinOccupied (σ ((network W H).west t))=(cfg t).selection.west ∧
    spinOccupied (σ ((network W H).north t))=(cfg t).selection.north ∧
    spinOccupied (σ ((network W H).south t))=(cfg t).selection.south ∧
    spinOccupied (σ ((network W H).east t))=(cfg t).selection.east ∧
    spinOccupied (μ t)=(cfg t).selection.middle

instance {W H : ℕ} (cfg : Cell W H → Shape)
    (σ : GridWire W H → Fin 3) (μ : Cell W H → Fin 3) : Decidable (Matches cfg σ μ) := by
  unfold Matches
  infer_instance

lemma maskedCell_sum (q : Shape) (w n s e : Fin 3) :
    maskedCell q w n s e = ∑ m : Fin 3,
      if spinOccupied w=q.selection.west ∧ spinOccupied n=q.selection.north ∧
        spinOccupied s=q.selection.south ∧ spinOccupied e=q.selection.east ∧
        spinOccupied m=q.selection.middle then upTensor w s m * downTensor e n m else 0 := by
  classical
  unfold maskedCell
  split_ifs with h
  · apply Finset.sum_congr rfl
    intro m hm
    simp only [h.1,h.2.1,h.2.2.1,h.2.2.2,true_and]
  · have h' : ∀ m : Fin 3, ¬ (spinOccupied w=q.selection.west ∧
        spinOccupied n=q.selection.north ∧ spinOccupied s=q.selection.south ∧
        spinOccupied e=q.selection.east ∧ spinOccupied m=q.selection.middle) := by
      intro m hm
      exact h ⟨hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1⟩
    simp [h']

/-- A resolved occupancy history is the literal finite-domain center sum
with exactly its five occupied-edge masks, including each middle edge. -/
theorem masked_orientation {W H : ℕ} (cfg : Cell W H → Shape)
    (σ : GridWire W H → Fin 3) :
    (kappa:ℂ)^(∑ t, (cfg t).visits) * (network W H).orientation cfg σ =
      ∑ μ : Cell W H → Fin 3, if Matches cfg σ μ then
        centerProduct (domain W H) (spins σ μ) else 0 := by
  classical
  calc
    _ = ∏ t, (kappa:ℂ)^(cfg t).visits * shapeTensor (cfg t)
        (σ ((network W H).west t)) (σ ((network W H).north t))
        (σ ((network W H).south t)) (σ ((network W H).east t)) := by
      rw [Finset.prod_mul_distrib,←Finset.prod_pow_eq_pow_sum]
      rfl
    _ = ∏ t, maskedCell (cfg t) (σ ((network W H).west t))
        (σ ((network W H).north t)) (σ ((network W H).south t))
        (σ ((network W H).east t)) := by simp_rw [maskedCell_eq]
    _ = _ := by
      simp_rw [maskedCell_sum]
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [Fintype.prod_ite_zero,center_product_eq]
      rfl

/-- Its prescribed-boundary contraction, with no auxiliary local model. -/
theorem masked_chosenPartition {W H : ℕ} (cfg : Cell W H → Shape)
    (west east : Column H) (south north : Fin W → Fin 3) :
    (kappa:ℂ)^(∑ t, (cfg t).visits) * chosenPartition cfg west east south north =
      ∑ σ : {σ : GridWire W H → Fin 3 // HasWestNorth west north σ},
        ∑ μ : Cell W H → Fin 3,
          if (∀ j, σ.val (.inl (Fin.last W,j))=east j) ∧
              (∀ i, σ.val (.inr (i,0))=south i) ∧ Matches cfg σ.val μ then
            centerProduct (domain W H) (spins σ.val μ) else 0 := by
  classical
  rw [chosenPartition_eq_grid_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  by_cases he : (∀ j, σ.val (.inl (Fin.last W,j))=east j) ∧
      (∀ i, σ.val (.inr (i,0))=south i)
  · rw [ite_eq_left he,masked_orientation]
    apply Finset.sum_congr rfl
    intro μ hμ
    congr 1
    exact propext ⟨fun hm=>⟨he.1,he.2,hm⟩,fun hh=>hh.2.2⟩
  · rw [ite_eq_right he,mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro μ hμ
    apply ite_eq_right
    intro he'
    exact he ⟨he'.1,he'.2.1⟩

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations
open scoped BigOperators

def selectionAt {W H : ℕ} (σ : GridWire W H → Fin 3) (μ : Cell W H → Fin 3)
    (t : Cell W H) : Selection :=
  ⟨spinOccupied (σ ((network W H).west t)),spinOccupied (σ ((network W H).south t)),
    spinOccupied (σ ((network W H).east t)),spinOccupied (σ ((network W H).north t)),
    spinOccupied (μ t)⟩

lemma selectionAt_admissible {W H : ℕ} (σ : GridWire W H → Fin 3) (μ : Cell W H → Fin 3)
    (h : centerProduct (domain W H) (spins σ μ)≠0) (t : Cell W H) :
    Admissible (selectionAt σ μ t) := by
  rw [center_product_eq] at h
  have ht := (Finset.prod_ne_zero_iff.mp h) t (Finset.mem_univ t)
  exact ⟨upTensor_degree _ _ _ (mul_ne_zero_iff.mp ht).1,
    downTensor_degree _ _ _ (mul_ne_zero_iff.mp ht).2⟩

noncomputable def occupancyShape {W H : ℕ} (σ : GridWire W H → Fin 3) (μ : Cell W H → Fin 3)
    (h : centerProduct (domain W H) (spins σ μ)≠0) (t : Cell W H) : Shape :=
  ((selection_classification _).mp (selectionAt_admissible σ μ h t)).choose

lemma occupancyShape_selection {W H : ℕ} (σ : GridWire W H → Fin 3) (μ : Cell W H → Fin 3)
    (h : centerProduct (domain W H) (spins σ μ)≠0) (t : Cell W H) :
    (occupancyShape σ μ h t).selection=selectionAt σ μ t :=
  ((selection_classification _).mp (selectionAt_admissible σ μ h t)).choose_spec

lemma occupancyShape_matches {W H : ℕ} (σ : GridWire W H → Fin 3) (μ : Cell W H → Fin 3)
    (h : centerProduct (domain W H) (spins σ μ)≠0) :
    Matches (occupancyShape σ μ h) σ μ := by
  intro t
  rw [occupancyShape_selection]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma matches_grid_occupied {W H : ℕ} (hW : 0<W) (hH : 0<H)
    {cfg : Cell W H → Shape} {σ τ : GridWire W H → Fin 3} {μ ν : Cell W H → Fin 3}
    (ha : Matches cfg σ μ) (hb : Matches cfg τ ν) (w : GridWire W H) :
    spinOccupied (σ w)=spinOccupied (τ w) := by
  cases w with
  | inl w =>
    rcases w with ⟨i,j⟩
    cases W with
    | zero => omega
    | succ W =>
      cases i using Fin.lastCases with
      | last => exact (ha (Fin.last W,j)).2.2.2.1.trans (hb (Fin.last W,j)).2.2.2.1.symm
      | cast i => exact (ha (i,j)).1.trans (hb (i,j)).1.symm
  | inr w =>
    rcases w with ⟨i,j⟩
    cases H with
    | zero => omega
    | succ H =>
      cases j using Fin.lastCases with
      | last => exact (ha (i,Fin.last H)).2.1.trans (hb (i,Fin.last H)).2.1.symm
      | cast j => exact (ha (i,j)).2.2.1.trans (hb (i,j)).2.2.1.symm

lemma matches_occupied {W H : ℕ} (hW : 0<W) (hH : 0<H)
    {cfg : Cell W H → Shape} {σ τ : GridWire W H → Fin 3} {μ ν : Cell W H → Fin 3}
    (ha : Matches cfg σ μ) (hb : Matches cfg τ ν) (w : Wire) :
    spinOccupied (spins σ μ w)=spinOccupied (spins τ ν w) := by
  by_cases hw : w∈Set.range (wireEmbedding (W:=W) (H:=H))
  · obtain ⟨w,rfl⟩ := hw
    rw [spins_wire,spins_wire]
    cases w with
    | inl w => exact matches_grid_occupied hW hH ha hb w
    | inr t => exact (ha t).2.2.2.2.trans (hb t).2.2.2.2.symm
  · rw [show spins σ μ w=1 from Function.extend_apply' _ _ _ hw,
      show spins τ ν w=1 from Function.extend_apply' _ _ _ hw]

lemma spins_injective {W H : ℕ} {σ τ : GridWire W H → Fin 3} {μ ν : Cell W H → Fin 3}
    (h : spins σ μ=spins τ ν) : σ=τ ∧ μ=ν := by
  constructor
  · funext w
    exact (spins_wire σ μ (.inl w)).symm.trans ((congrFun h (wireEmbedding (.inl w))).trans
      (spins_wire τ ν (.inl w)))
  · funext t
    exact (spins_wire σ μ (.inr t)).symm.trans ((congrFun h (wireEmbedding (.inr t))).trans
      (spins_wire τ ν (.inr t)))

/-- If a fixed occupancy really is a simple actual path, every nonzero
center term is its unique rooted orientation. This excludes the zero-branch
without assuming any phase or noncancellation conclusion. -/
theorem path_mask_unique {W H n : ℕ} (hW : 0<W) (hH : 0<H)
    (p : CenterPath n) {cfg : Cell W H → Shape}
    {σ τ : GridWire W H → Fin 3} {μ ν : Cell W H → Fin 3}
    (ha : Matches cfg σ μ) (hb : Matches cfg τ ν) (hp : spins τ ν=p.spins)
    (hc : ∀ i, p.center i∈domain W H)
    (hr : spins σ μ (p.edge 0)=outSpin (p.point 0) (p.side 0))
    (hn : centerProduct (domain W H) (spins σ μ)≠0) : σ=τ ∧ μ=ν := by
  apply spins_injective
  rw [hp]
  apply p.full_orientation_unique
  · intro w hw
    have he := matches_occupied hW hH ha hb w
    rw [hp,p.spins_off w hw] at he
    simpa [spinOccupied] using he
  · exact hr
  · intro i
    exact (Finset.prod_ne_zero_iff.mp hn) _ (hc i)

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations
open scoped BigOperators

/-- Reindexing a literal loop-free occupancy does not lose its nonzero
rooted orientation inside the source rectangular transfer contraction. -/
theorem path_mask_contraction {W H n : ℕ} (hW : 0<W) (hH : 0<H)
    (p : CenterPath n) (cfg : Cell W H → Shape)
    (west east : Column H) (south north : Fin W → Fin 3)
    (τ : GridWire W H → Fin 3) (ν : Cell W H → Fin 3)
    (hτ : HasWestNorth west north τ)
    (hE : ∀ j, τ (.inl (Fin.last W,j))=east j)
    (hS : ∀ i, τ (.inr (i,0))=south i)
    (hb : Matches cfg τ ν) (hp : spins τ ν=p.spins)
    (hc : ∀ i, p.center i∈domain W H)
    (j : Fin H) (hroot : p.edge 0=wireEmbedding (W:=W) (H:=H) (.inl (.inl (0,j))))
    (hrootSpin : west j=outSpin (p.point 0) (p.side 0)) :
    (kappa:ℂ)^(∑ t, (cfg t).visits) * chosenPartition cfg west east south north =
      centerProduct (domain W H) p.spins := by
  classical
  rw [masked_chosenPartition]
  let F : ({σ : GridWire W H → Fin 3 // HasWestNorth west north σ} × (Cell W H → Fin 3)) → ℂ :=
    fun x=>if (∀ j, x.1.val (.inl (Fin.last W,j))=east j) ∧
      (∀ i, x.1.val (.inr (i,0))=south i) ∧ Matches cfg x.1.val x.2 then
        centerProduct (domain W H) (spins x.1.val x.2) else 0
  change (∑ σ, ∑ μ, F (σ,μ))=_
  rw [←Fintype.sum_prod_type]
  let x₀ : {σ : GridWire W H → Fin 3 // HasWestNorth west north σ} × (Cell W H → Fin 3) :=
    (⟨τ,hτ⟩,ν)
  rw [Finset.sum_eq_single x₀]
  · dsimp only [F,x₀]
    rw [ite_eq_left ⟨hE,hS,hb⟩,hp]
  · intro x hx hne
    dsimp only [F]
    split_ifs with hcond
    · by_contra hn
      have hr : spins x.1.val x.2 (p.edge 0)=outSpin (p.point 0) (p.side 0) := by
        rw [hroot,spins_wire]
        exact (x.1.property.1 j).trans hrootSpin
      have he := path_mask_unique hW hH p hcond.2.2 hb hp hc hr hn
      apply hne
      apply Prod.ext
      · exact Subtype.ext he.1
      · exact he.2
    · rfl
  · simp

theorem path_chosen_nonzero {W H n : ℕ} (hW : 0<W) (hH : 0<H)
    (p : CenterPath n) (cfg : Cell W H → Shape)
    (west east : Column H) (south north : Fin W → Fin 3)
    (τ : GridWire W H → Fin 3) (ν : Cell W H → Fin 3)
    (hτ : HasWestNorth west north τ)
    (hE : ∀ j, τ (.inl (Fin.last W,j))=east j)
    (hS : ∀ i, τ (.inr (i,0))=south i)
    (hb : Matches cfg τ ν) (hp : spins τ ν=p.spins)
    (hc : ∀ i, p.center i∈domain W H)
    (h0 : p.point 0∉domain W H) (hl : p.point (Fin.last (n+1))∉domain W H)
    (j : Fin H) (hroot : p.edge 0=wireEmbedding (W:=W) (H:=H) (.inl (.inl (0,j))))
    (hrootSpin : west j=outSpin (p.point 0) (p.side 0)) :
    chosenPartition cfg west east south north≠0 := by
  have he := path_mask_contraction hW hH p cfg west east south north τ ν hτ hE hS hb hp hc
    j hroot hrootSpin
  intro hz
  rw [hz,mul_zero] at he
  exact p.product_nonzero (domain W H) h0 hl he.symm

/-- Exact one, not merely nonzero: a literal center chord has the normalized
coefficient prescribed by the source single-strand transfer sector. -/
theorem path_chosen_eq_one {W H n : ℕ} (hW : 0<W) (hH : 0<H)
    (p : CenterPath n) (cfg : Cell W H → Shape)
    (west east : Column H)
    (hi : (PlanarNormalization.occupancy (List.ofFn (fun j=>spinEquiv.symm (east j)))).count true=1)
    (ho : (PlanarNormalization.occupancy (List.ofFn (fun j=>spinEquiv.symm (west j)))).count true=1)
    (τ : GridWire W H → Fin 3) (ν : Cell W H → Fin 3)
    (hτ : HasWestNorth west (fun _=>1) τ)
    (hE : ∀ j, τ (.inl (Fin.last W,j))=east j)
    (hS : ∀ i, τ (.inr (i,0))=1)
    (hb : Matches cfg τ ν) (hp : spins τ ν=p.spins)
    (hc : ∀ i, p.center i∈domain W H)
    (h0 : p.point 0∉domain W H) (hl : p.point (Fin.last (n+1))∉domain W H)
    (j : Fin H) (hroot : p.edge 0=wireEmbedding (W:=W) (H:=H) (.inl (.inl (0,j))))
    (hrootSpin : west j=outSpin (p.point 0) (p.side 0)) :
    chosenPartition cfg west east (fun _=>1) (fun _=>1)=1 := by
  exact (chosenPartition_zero_or_one cfg west east hi ho).resolve_left
    (path_chosen_nonzero hW hH p cfg west east (fun _=>1) (fun _=>1) τ ν hτ hE hS hb hp hc
      h0 hl j hroot hrootSpin)

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations
open scoped BigOperators

lemma cellCenter_mem {W H : ℕ} (t : Cell W H) (b : Bool) :
    cellCenter t b∈domain W H := by
  classical
  exact Finset.mem_image.mpr ⟨(t,b),Finset.mem_univ _,rfl⟩

lemma domain_coord_bounds {W H : ℕ} {v : Center} (hv : v∈domain W H) :
    0≤v.1 ∧ v.1<(W:ℤ) ∧ 0≤v.2.1 ∧ v.2.1<(H:ℤ) := by
  obtain ⟨⟨⟨i,j⟩,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
  simp only [cellCenter]
  exact ⟨Int.natCast_nonneg _,by exact_mod_cast i.isLt,
    Int.natCast_nonneg _,by exact_mod_cast j.isLt⟩

lemma domain_wire_covered {W H : ℕ} {v : Center} (hv : v∈domain W H) (k : Fin 3) :
    incidentWire v k∈Set.range (wireEmbedding (W:=W) (H:=H)) := by
  obtain ⟨⟨t,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
  cases b
  · fin_cases k
    · exact ⟨.inr t,(down_wires t).1.symm⟩
    · exact ⟨.inl ((network W H).north t),(down_wires t).2.1.symm⟩
    · exact ⟨.inl ((network W H).east t),(down_wires t).2.2.symm⟩
  · fin_cases k
    · exact ⟨.inr t,(up_wires t).1.symm⟩
    · exact ⟨.inl ((network W H).south t),(up_wires t).2.1.symm⟩
    · exact ⟨.inl ((network W H).west t),(up_wires t).2.2.symm⟩

lemma path_wire_covered {W H n : ℕ} (p : CenterPath n) (hn : 0<n)
    (hc : ∀ i, p.center i∈domain W H) (j : Fin (n+1)) :
    p.edge j∈Set.range (wireEmbedding (W:=W) (H:=H)) := by
  cases j using Fin.cases with
  | zero =>
    have he := p.in_wire ⟨0,hn⟩
    have hz : (⟨0,hn⟩ : Fin n).castSucc=0 := Fin.ext rfl
    rw [hz] at he
    rw [←he]
    exact domain_wire_covered (hc _) _
  | succ i =>
    rw [←p.out_wire i]
    exact domain_wire_covered (hc i) _

noncomputable def restrictGrid {W H : ℕ} (f : Wire → Fin 3) : GridWire W H → Fin 3 :=
  fun w=>f (wireEmbedding (.inl w))
noncomputable def restrictMiddle {W H : ℕ} (f : Wire → Fin 3) : Cell W H → Fin 3 :=
  fun t=>f (wireEmbedding (.inr t))

lemma path_spins_restrict {W H n : ℕ} (p : CenterPath n) (hn : 0<n)
    (hc : ∀ i, p.center i∈domain W H) :
    spins (restrictGrid (W:=W) (H:=H) p.spins) (restrictMiddle p.spins)=p.spins := by
  funext w
  by_cases hw : w∈Set.range (wireEmbedding (W:=W) (H:=H))
  · obtain ⟨w,rfl⟩ := hw
    rw [spins_wire]
    cases w <;> rfl
  · rw [show spins (restrictGrid (W:=W) (H:=H) p.spins) (restrictMiddle p.spins) w=1 from
        Function.extend_apply' _ _ _ hw]
    symm
    apply p.spins_off
    rintro ⟨j,rfl⟩
    exact hw (path_wire_covered p hn hc j)

/-- Every actual loop-free path through the rectangle supplies an exact
occupancy shape; no hypothetical shape data is needed. -/
noncomputable def pathShape {W H n : ℕ} (p : CenterPath n) (hn : 0<n)
    (hc : ∀ i, p.center i∈domain W H)
    (h0 : p.point 0∉domain W H) (hl : p.point (Fin.last (n+1))∉domain W H) :
    Cell W H → Shape :=
  occupancyShape (restrictGrid p.spins) (restrictMiddle p.spins) (by
    rw [path_spins_restrict p hn hc]
    exact p.product_nonzero _ h0 hl)

lemma pathShape_matches {W H n : ℕ} (p : CenterPath n) (hn : 0<n)
    (hc : ∀ i, p.center i∈domain W H)
    (h0 : p.point 0∉domain W H) (hl : p.point (Fin.last (n+1))∉domain W H) :
    Matches (pathShape p hn hc h0 hl) (restrictGrid p.spins) (restrictMiddle p.spins) :=
  occupancyShape_matches _ _ _

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations

noncomputable def westPort (W H : ℕ) (j : Fin (H+1)) : Port (domain (W+1) (H+1) : Set Center) where
  inside := cellCenter (0,j) true
  outside := down (-1) j.val
  adjacent := by simp [cellCenter,Adj,down]
  inside_mem := cellCenter_mem _ _
  outside_not_mem := by
    intro h
    have hh := (domain_coord_bounds h).1
    norm_num [down] at hh

noncomputable def eastPort (W H : ℕ) (j : Fin (H+1)) : Port (domain (W+1) (H+1) : Set Center) where
  inside := cellCenter (Fin.last W,j) false
  outside := up (W+1) j.val
  adjacent := by simp [cellCenter,Adj,up]
  inside_mem := cellCenter_mem _ _
  outside_not_mem := by
    intro h
    have hh := (domain_coord_bounds h).2.1
    simp [up] at hh

noncomputable def southPort (W H : ℕ) (i : Fin (W+1)) : Port (domain (W+1) (H+1) : Set Center) where
  inside := cellCenter (i,0) true
  outside := down i.val (-1)
  adjacent := by simp [cellCenter,Adj,down]
  inside_mem := cellCenter_mem _ _
  outside_not_mem := by
    intro h
    have hh := (domain_coord_bounds h).2.2.1
    norm_num [down] at hh

noncomputable def northPort (W H : ℕ) (i : Fin (W+1)) : Port (domain (W+1) (H+1) : Set Center) where
  inside := cellCenter (i,Fin.last H) false
  outside := up i.val (H+1)
  adjacent := by simp [cellCenter,Adj,up]
  inside_mem := cellCenter_mem _ _
  outside_not_mem := by
    intro h
    have hh := (domain_coord_bounds h).2.2.2
    simp [up] at hh

lemma westPort_side (W H : ℕ) (j : Fin (H+1)) : (westPort W H j).side=2 := by
  apply neighbor_injective (westPort W H j).inside
  rw [Port.neighbor_side]
  simp [westPort,neighbor,cellCenter,down]

lemma eastPort_side (W H : ℕ) (j : Fin (H+1)) : (eastPort W H j).side=2 := by
  apply neighbor_injective (eastPort W H j).inside
  rw [Port.neighbor_side]
  simp [eastPort,neighbor,cellCenter,up]

lemma southPort_side (W H : ℕ) (i : Fin (W+1)) : (southPort W H i).side=1 := by
  apply neighbor_injective (southPort W H i).inside
  rw [Port.neighbor_side]
  simp [southPort,neighbor,cellCenter,down]

lemma northPort_side (W H : ℕ) (i : Fin (W+1)) : (northPort W H i).side=1 := by
  apply neighbor_injective (northPort W H i).inside
  rw [Port.neighbor_side]
  simp [northPort,neighbor,cellCenter,up]

lemma westPort_wire (W H : ℕ) (j : Fin (H+1)) :
    (westPort W H j).wire=wireEmbedding (W:=W+1) (H:=H+1) (.inl (.inl (0,j))) := by
  rw [Port.wire,westPort_side]
  simp [westPort,incidentWire,wireEmbedding,cellCenter]

lemma eastPort_wire (W H : ℕ) (j : Fin (H+1)) :
    (eastPort W H j).wire=wireEmbedding (W:=W+1) (H:=H+1) (.inl (.inl (Fin.last (W+1),j))) := by
  rw [Port.wire,eastPort_side]
  simp [eastPort,incidentWire,wireEmbedding,cellCenter]

lemma southPort_wire (W H : ℕ) (i : Fin (W+1)) :
    (southPort W H i).wire=wireEmbedding (W:=W+1) (H:=H+1) (.inl (.inr (i,0))) := by
  rw [Port.wire,southPort_side]
  simp [southPort,incidentWire,wireEmbedding,cellCenter]

lemma northPort_wire (W H : ℕ) (i : Fin (W+1)) :
    (northPort W H i).wire=wireEmbedding (W:=W+1) (H:=H+1) (.inl (.inr (i,Fin.last (H+1)))) := by
  rw [Port.wire,northPort_side]
  simp [northPort,incidentWire,wireEmbedding,cellCenter]

lemma westPort_injective (W H : ℕ) : Function.Injective (westPort W H) := by
  intro i j he
  have hh := congrArg (fun q=>q.outside.2.1) he
  simpa only [westPort,down,Int.natCast_inj,Fin.val_inj] using hh

lemma eastPort_injective (W H : ℕ) : Function.Injective (eastPort W H) := by
  intro i j he
  have hh := congrArg (fun q=>q.outside.2.1) he
  simpa only [eastPort,up,Int.natCast_inj,Fin.val_inj] using hh

lemma west_ne_east (W H : ℕ) (j k : Fin (H+1)) : westPort W H j≠eastPort W H k := by
  intro he
  have hh := congrArg (fun q=>q.outside.2.2) he
  simp [westPort,eastPort,down,up] at hh

lemma south_ne_west (W H : ℕ) (i : Fin (W+1)) (j : Fin (H+1)) :
    southPort W H i≠westPort W H j := by
  intro he
  have hh := congrArg (fun q=>q.outside.1) he
  simp only [southPort,westPort,down] at hh
  omega

lemma south_ne_east (W H : ℕ) (i : Fin (W+1)) (j : Fin (H+1)) :
    southPort W H i≠eastPort W H j := by
  intro he
  have hh := congrArg (fun q=>q.outside.2.2) he
  simp [southPort,eastPort,down,up] at hh

lemma north_ne_west (W H : ℕ) (i : Fin (W+1)) (j : Fin (H+1)) :
    northPort W H i≠westPort W H j := by
  intro he
  have hh := congrArg (fun q=>q.outside.2.2) he
  simp [northPort,westPort,down,up] at hh

lemma north_ne_east (W H : ℕ) (i : Fin (W+1)) (j : Fin (H+1)) :
    northPort W H i≠eastPort W H j := by
  intro he
  have hh := congrArg (fun q=>q.outside.1) he
  simp only [northPort,eastPort,up] at hh
  have hi := i.isLt
  omega

lemma west_outside_ne_east (W H : ℕ) (j k : Fin (H+1)) :
    (westPort W H j).outside≠(eastPort W H k).outside := by
  simp [westPort,eastPort,down,up]

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.ChordOrientations
open CenterPartition
variable {D : Set Center} {a b : Port D}

lemma chord_length_pos (γ : Chord D a b) : 0<γ.val.length := by
  obtain ⟨xs,hxs⟩ := List.head?_eq_some_iff.mp γ.property.2.1
  simp [hxs]

lemma ofChord_first (γ : Chord D a b) (hab : a.outside≠b.outside) :
    (ofChord γ hab).point 0=a.outside := by
  rw [ofChord_point]
  rfl

lemma ofChord_last (γ : Chord D a b) (hab : a.outside≠b.outside) :
    (ofChord γ hab).point (Fin.last (γ.val.length+1))=b.outside := by
  rw [ofChord_point]
  simp only [Fin.val_last,extendedTrace,List.getElem_cons_succ]
  rw [List.getElem_append_right (le_refl _)]
  simp

lemma ofChord_second (γ : Chord D a b) (hab : a.outside≠b.outside) :
    (ofChord γ hab).point (0 : Fin (γ.val.length+1)).succ=a.inside := by
  rw [ofChord_point]
  obtain ⟨xs,hxs⟩ := List.head?_eq_some_iff.mp γ.property.2.1
  simp [extendedTrace,hxs]

lemma ofChord_penultimate (γ : Chord D a b) (hab : a.outside≠b.outside) :
    (ofChord γ hab).point (Fin.last γ.val.length).castSucc=b.inside := by
  rw [ofChord_point]
  have hn := chord_length_pos γ
  have he : (Fin.last γ.val.length).castSucc.val=γ.val.length-1+1 := by
    simp only [Fin.val_castSucc,Fin.val_last]
    omega
  simp only [he,extendedTrace,List.getElem_cons_succ]
  rw [List.getElem_append_left (by omega)]
  apply Option.some.inj
  rw [←List.getElem?_eq_getElem (by omega),←List.getLast?_eq_getElem?,γ.property.2.2]

lemma ofChord_center_mem (γ : Chord D a b) (hab : a.outside≠b.outside)
    (i : Fin γ.val.length) : (ofChord γ hab).center i∈D := by
  rw [ofChord_center]
  exact γ.property.1.2.2 _ (List.getElem_mem i.isLt)

lemma ofChord_first_side (γ : Chord D a b) (hab : a.outside≠b.outside) :
    (ofChord γ hab).side 0=a.side := by
  apply neighbor_injective a.outside
  have he := (ofChord γ hab).step 0
  rw [show (0 : Fin (γ.val.length+1)).castSucc=0 from rfl,ofChord_first,ofChord_second] at he
  rw [he,←a.neighbor_side,neighbor_neighbor]

lemma ofChord_last_side (γ : Chord D a b) (hab : a.outside≠b.outside) :
    (ofChord γ hab).side (Fin.last γ.val.length)=b.side := by
  apply neighbor_injective b.inside
  have he := (ofChord γ hab).step (Fin.last γ.val.length)
  rw [ofChord_penultimate,show (Fin.last γ.val.length).succ=Fin.last (γ.val.length+1) from rfl,
    ofChord_last] at he
  rw [he,b.neighbor_side]

lemma ofChord_first_edge (γ : Chord D a b) (hab : a.outside≠b.outside) :
    (ofChord γ hab).edge 0=a.wire := by
  unfold CenterPath.edge
  rw [show (0 : Fin (γ.val.length+1)).castSucc=0 from rfl,ofChord_first,ofChord_first_side]
  rw [←a.neighbor_side,incidentWire_neighbor]
  rfl

lemma ofChord_last_edge (γ : Chord D a b) (hab : a.outside≠b.outside) :
    (ofChord γ hab).edge (Fin.last γ.val.length)=b.wire := by
  unfold CenterPath.edge
  rw [ofChord_penultimate,ofChord_last_side]
  rfl

/-- A path never uses another exterior edge: its only outside incidences
are the first and last edges, with their literal chronological indices. -/
lemma CenterPath.outside_incident_index {n : ℕ} (p : CenterPath n)
    (hc : ∀ i, p.center i∈D) {v : Center} (hv : v∉D)
    (k : Fin 3) (j : Fin (n+1)) (he : incidentWire v k=p.edge j) :
    j=0 ∨ j=Fin.last n := by
  obtain ⟨hk,hleft|hright⟩ := (incidentWire_eq_iff _ _ _ _).mp he
  · rcases p.point_cases j.castSucc with h0|hl|⟨i,hi⟩
    · left
      have he' := congrArg (fun z : Fin (n+2)=>z.val) (p.injective h0)
      apply Fin.ext
      exact he'
    · have he' := congrArg (fun z : Fin (n+2)=>z.val) (p.injective hl)
      have hj := j.isLt
      simp only [Fin.val_castSucc,Fin.val_last] at he'
      omega
    · exact False.elim (hv (hleft ▸ hi.symm ▸ hc i))
  · have he' : v=p.point j.succ := by
      rw [←p.step j,←hk,←hright,neighbor_neighbor]
    rcases p.point_cases j.succ with h0|hl|⟨i,hi⟩
    · have hh := congrArg (fun z : Fin (n+2)=>z.val) (p.injective h0)
      simp only [Fin.val_succ,Fin.val_zero] at hh
      omega
    · right
      have hh := congrArg (fun z : Fin (n+2)=>z.val) (p.injective hl)
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_last] at hh ⊢
      omega
    · exact False.elim (hv (he' ▸ hi.symm ▸ hc i))

lemma ofChord_boundary_wire (γ : Chord D a b) (hab : a.outside≠b.outside)
    (q : Port D) : q.wire∈Set.range (ofChord γ hab).edge ↔ q=a ∨ q=b := by
  constructor
  · rintro ⟨j,hj⟩
    have hi : incidentWire q.outside q.side=(ofChord γ hab).edge j := by
      rw [←q.neighbor_side,incidentWire_neighbor]
      exact hj.symm
    rcases (ofChord γ hab).outside_incident_index (ofChord_center_mem γ hab)
      q.outside_not_mem q.side j hi with h0|hl
    · left
      apply Port.wire_ext
      rw [←hj,h0,ofChord_first_edge]
    · right
      apply Port.wire_ext
      rw [←hj,hl,ofChord_last_edge]
  · rintro (rfl|rfl)
    · exact ⟨0,ofChord_first_edge γ hab⟩
    · exact ⟨Fin.last γ.val.length,ofChord_last_edge γ hab⟩

lemma ofChord_boundary_vacant (γ : Chord D a b) (hab : a.outside≠b.outside)
    (q : Port D) (qa : q≠a) (qb : q≠b) : (ofChord γ hab).spins q.wire=1 := by
  apply CenterPath.spins_off
  rw [ofChord_boundary_wire]
  exact not_or.mpr ⟨qa,qb⟩

end CriticalHoneycomb.Transfer.ChordOrientations

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations

abbrev RectChord (W H : ℕ) (j k : Fin (H+1)) :=
  Chord (domain (W+1) (H+1) : Set Center) (westPort W H j) (eastPort W H k)

noncomputable def rectanglePath {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k) :
    CenterPath γ.val.length := ofChord γ (west_outside_ne_east W H j k)

lemma rectanglePath_first_spins {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k) :
    (rectanglePath γ).spins (westPort W H j).wire=2 := by
  rw [←ofChord_first_edge γ (west_outside_ne_east W H j k)]
  change (rectanglePath γ).spins ((rectanglePath γ).edge 0)=2
  rw [CenterPath.spins_edge]
  change outSpin ((ofChord γ _).point 0) ((ofChord γ _).side 0)=2
  rw [ofChord_first,ofChord_first_side,westPort_side]
  simp [westPort,outSpin,down]

lemma rectanglePath_last_spins {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k) :
    (rectanglePath γ).spins (eastPort W H k).wire=2 := by
  rw [←ofChord_last_edge γ (west_outside_ne_east W H j k)]
  change (rectanglePath γ).spins ((rectanglePath γ).edge (Fin.last γ.val.length))=2
  rw [CenterPath.spins_edge]
  change outSpin ((ofChord γ _).point (Fin.last γ.val.length).castSucc)
    ((ofChord γ _).side (Fin.last γ.val.length))=2
  rw [ofChord_penultimate,ofChord_last_side,eastPort_side]
  simp [eastPort,outSpin,cellCenter]

def singleColumn {H : ℕ} (j : Fin H) : Column H := fun k=>if k=j then 2 else 1

lemma singleColumn_occupancy {H : ℕ} (j : Fin H) :
    (PlanarNormalization.occupancy (List.ofFn (fun k=>spinEquiv.symm (singleColumn j k)))).count true=1 := by
  have he : PlanarNormalization.occupancy (List.ofFn (fun k=>spinEquiv.symm (singleColumn j k))) =
      List.ofFn (fun k=>decide (k=j)) := by
    simp only [PlanarNormalization.occupancy,List.map_ofFn]
    congr 1
    funext k
    by_cases hk : k=j <;> simp [singleColumn,hk,spinEquiv]
  rw [he]
  clear he
  induction H with
  | zero => exact Fin.elim0 j
  | succ H ih =>
    cases j using Fin.cases with
    | zero => simp [List.ofFn_succ,List.count_replicate]
    | succ j =>
      have hz : (0:Fin (H+1))≠j.succ := by intro h; have := congrArg Fin.val h; simp at this
      simpa [List.ofFn_succ,hz] using ih j

lemma rectanglePath_west {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k)
    (r : Fin (H+1)) :
    restrictGrid (W:=W+1) (H:=H+1) (rectanglePath γ).spins (.inl (0,r))=singleColumn j r := by
  unfold restrictGrid
  rw [←westPort_wire]
  by_cases hr : r=j
  · subst r
    rw [rectanglePath_first_spins]
    simp [singleColumn]
  · change (ofChord γ (west_outside_ne_east W H j k)).spins _ = _
    rw [ofChord_boundary_vacant γ (west_outside_ne_east W H j k) (westPort W H r)
      (fun he=>hr (westPort_injective W H he)) (west_ne_east W H r k)]
    simp [singleColumn,hr]

lemma rectanglePath_east {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k)
    (r : Fin (H+1)) :
    restrictGrid (W:=W+1) (H:=H+1) (rectanglePath γ).spins (.inl (Fin.last (W+1),r))=singleColumn k r := by
  unfold restrictGrid
  rw [←eastPort_wire]
  by_cases hr : r=k
  · subst r
    rw [rectanglePath_last_spins]
    simp [singleColumn]
  · change (ofChord γ (west_outside_ne_east W H j k)).spins _ = _
    rw [ofChord_boundary_vacant γ (west_outside_ne_east W H j k) (eastPort W H r)
      (Ne.symm (west_ne_east W H j r)) (fun he=>hr (eastPort_injective W H he))]
    simp [singleColumn,hr]

lemma rectanglePath_north {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k)
    (r : Fin (W+1)) :
    restrictGrid (W:=W+1) (H:=H+1) (rectanglePath γ).spins (.inr (r,Fin.last (H+1)))=1 := by
  unfold restrictGrid
  rw [←northPort_wire]
  exact ofChord_boundary_vacant γ (west_outside_ne_east W H j k) (northPort W H r)
    (north_ne_west W H r j) (north_ne_east W H r k)

lemma rectanglePath_south {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k)
    (r : Fin (W+1)) :
    restrictGrid (W:=W+1) (H:=H+1) (rectanglePath γ).spins (.inr (r,0))=1 := by
  unfold restrictGrid
  rw [←southPort_wire]
  exact ofChord_boundary_vacant γ (west_outside_ne_east W H j k) (southPort W H r)
    (south_ne_west W H r j) (south_ne_east W H r k)

noncomputable def rectangleShape {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k) :
    Cell (W+1) (H+1) → Shape :=
  pathShape (rectanglePath γ) (chord_length_pos γ) (ofChord_center_mem γ _) (by
    rw [rectanglePath,ofChord_first]; exact (westPort W H j).outside_not_mem) (by
    rw [rectanglePath,ofChord_last]; exact (eastPort W H k).outside_not_mem)

/-- The normalized finite transfer coefficient of each literal source chord
is exactly one. No path noncancellation or single-strand phase has been
postulated; both are proved from the exact center tensors. -/
theorem actual_chord_chosen_one {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k) :
    chosenPartition (rectangleShape γ) (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)=1 := by
  apply path_chosen_eq_one (by omega) (by omega) (rectanglePath γ) (rectangleShape γ)
    (singleColumn j) (singleColumn k) (singleColumn_occupancy k) (singleColumn_occupancy j)
    (restrictGrid (rectanglePath γ).spins) (restrictMiddle (rectanglePath γ).spins) (j:=j)
  · exact ⟨rectanglePath_west γ,rectanglePath_north γ⟩
  · exact rectanglePath_east γ
  · exact rectanglePath_south γ
  · exact pathShape_matches _ _ _ _ _
  · exact path_spins_restrict (rectanglePath γ) (chord_length_pos γ) (ofChord_center_mem γ _)
  · exact ofChord_center_mem γ _
  · rw [rectanglePath,ofChord_first]
    exact (westPort W H j).outside_not_mem
  · rw [rectanglePath,ofChord_last]
    exact (eastPort W H k).outside_not_mem
  · rw [rectanglePath,ofChord_first_edge,westPort_wire]
  · rw [rectanglePath,ofChord_first,ofChord_first_side,westPort_side]
    simp [singleColumn,outSpin,westPort,down]

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.ChordOrientations
open PhysicalTiles FiniteConfigurations CenterPartition
open scoped BigOperators

noncomputable def usedCenter (σ : Wire → Fin 3) (v : Center) : ℕ :=
  if ∃ k : Fin 3, σ (incidentWire v k)≠1 then 1 else 0

lemma usedCenter_degree (σ : Wire → Fin 3) (v : Center) :
    usedCenter σ v = if selectedSideCount (fun w=>spinOccupied (σ w)) v=0 then 0 else 1 := by
  classical
  have hz : selectedSideCount (fun w=>spinOccupied (σ w)) v=0 ↔
      ∀ k : Fin 3, σ (incidentWire v k)=1 := by
    simp [selectedSideCount,spinOccupied,Fin.forall_fin_succ,and_assoc]
  simp only [hz]
  by_cases h : ∃ k : Fin 3, σ (incidentWire v k)≠1
  · have hn : ¬∀ k : Fin 3, σ (incidentWire v k)=1 := by
      rintro hf; obtain ⟨k,hk⟩ := h; exact hk (hf k)
    simp [usedCenter,h,hn]
  · have hn : ∀ k : Fin 3, σ (incidentWire v k)=1 := by simpa only [not_exists,not_not] using h
    simp [usedCenter,hn]

lemma CenterPath.used_iff {n : ℕ} (p : CenterPath n) (v : Center)
    (h0 : v≠p.point 0) (hl : v≠p.point (Fin.last (n+1))) :
    usedCenter p.spins v = if v∈Set.range p.center then 1 else 0 := by
  classical
  by_cases hv : v∈Set.range p.center
  · obtain ⟨i,rfl⟩ := hv
    have h : ∃ k : Fin 3, p.spins (incidentWire (p.center i) k)≠1 := by
      refine ⟨p.side i.succ,?_⟩
      rw [p.out_wire,p.spins_edge]
      exact outSpin_ne_empty _ _
    simp [usedCenter,h]
  · have h : ¬∃ k : Fin 3, p.spins (incidentWire v k)≠1 := by
      rintro ⟨k,hk⟩
      exact hk (p.spins_off _ (p.incident_off v h0 hl hv k))
    simp [usedCenter,h,hv]

lemma CenterPath.center_injective {n : ℕ} (p : CenterPath n) : Function.Injective p.center := by
  intro i j h
  have he := congrArg Fin.val (p.injective h)
  apply Fin.ext
  simpa [CenterPath.center] using he

lemma CenterPath.sum_used {n : ℕ} (p : CenterPath n) (D : Finset Center)
    (hc : ∀ i, p.center i∈D) (h0 : p.point 0∉D) (hl : p.point (Fin.last (n+1))∉D) :
    ∑ v ∈ D, usedCenter p.spins v = n := by
  classical
  have he : D.filter (fun v=>v∈Set.range p.center)=Finset.univ.image p.center := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range]
    exact ⟨fun h=>h.2,fun ⟨i,hi⟩=>⟨hi ▸ hc i,⟨i,hi⟩⟩⟩
  calc
    _ = ∑ v ∈ D, if v∈Set.range p.center then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      exact p.used_iff v (fun h=>h0 (h ▸ hv)) (fun h=>hl (h ▸ hv))
    _ = (D.filter (fun v=>v∈Set.range p.center)).card := by simp
    _ = n := by rw [he,Finset.card_image_of_injective _ p.center_injective]; simp

end CriticalHoneycomb.Transfer.ChordOrientations

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles FiniteConfigurations CenterPartition ChordOrientations
open scoped BigOperators

lemma shape_visits_used {W H : ℕ} {cfg : Cell W H → Shape}
    {σ : GridWire W H → Fin 3} {μ : Cell W H → Fin 3} (hm : Matches cfg σ μ) (t : Cell W H) :
    (cfg t).visits = usedCenter (spins σ μ) (cellCenter t true) +
      usedCenter (spins σ μ) (cellCenter t false) := by
  rw [visits_eq,usedCenter_degree,usedCenter_degree]
  have hu : selectedSideCount (fun w=>spinOccupied (spins σ μ w)) (cellCenter t true)=
      (cfg t).selection.upDegree := by
    unfold selectedSideCount
    rw [(up_wires t).1,(up_wires t).2.1,(up_wires t).2.2]
    simp only [spins_wire,Sum.elim_inl,Sum.elim_inr,(hm t).1,(hm t).2.2.1,(hm t).2.2.2.2]
    unfold Selection.upDegree
    omega
  have hd : selectedSideCount (fun w=>spinOccupied (spins σ μ w)) (cellCenter t false)=
      (cfg t).selection.downDegree := by
    unfold selectedSideCount
    rw [(down_wires t).1,(down_wires t).2.1,(down_wires t).2.2]
    simp only [spins_wire,Sum.elim_inl,Sum.elim_inr,(hm t).2.1,(hm t).2.2.2.1,(hm t).2.2.2.2]
    unfold Selection.downDegree
    omega
  rw [hu,hd]

lemma sum_visits_used {W H : ℕ} {cfg : Cell W H → Shape}
    {σ : GridWire W H → Fin 3} {μ : Cell W H → Fin 3} (hm : Matches cfg σ μ) :
    (∑ t, (cfg t).visits) = ∑ v ∈ domain W H, usedCenter (spins σ μ) v := by
  classical
  rw [domain,Finset.sum_image (fun x _ y _ h=>cellCenter_injective W H h)]
  rw [Fintype.sum_prod_type (fun p : Cell W H × Bool=>usedCenter (spins σ μ) (cellCenter p.1 p.2))]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Fintype.sum_bool]
  exact shape_visits_used hm t

/-- Port half-edges are unweighted: the exact raster exponent is the number
of centers in the source trace, with no additive endpoint correction. -/
theorem actual_chord_visits {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k) :
    (∑ t, (rectangleShape γ t).visits)=γ.val.length := by
  have hm : Matches (rectangleShape γ) (restrictGrid (rectanglePath γ).spins)
      (restrictMiddle (rectanglePath γ).spins) := pathShape_matches _ _ _ _ _
  rw [sum_visits_used hm,path_spins_restrict (rectanglePath γ) (chord_length_pos γ) (ofChord_center_mem γ _)]
  apply CenterPath.sum_used
  · exact ofChord_center_mem γ _
  · rw [rectanglePath,ofChord_first]; exact (westPort W H j).outside_not_mem
  · rw [rectanglePath,ofChord_last]; exact (eastPort W H k).outside_not_mem

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.PathComponents
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma paths_eq_of_edges_subset {a b : V} (p q : G.Walk a b)
    (hp : p.IsPath) (hq : q.IsPath) (hsub : p.edges ⊆ q.edges) : p = q := by
  induction p with
  | nil =>
    have hnil : q.Nil := Walk.isPath_iff_nil.mp hq
    cases hnil
    rfl
  | @cons a c b hac p ih =>
    cases q with
    | nil => simp at hp
    | @cons _ d _ had q =>
      have hcd : c = d := by
        have he : s(a,c) ∈ (Walk.cons had q).edges := hsub (by simp)
        simpa using hq.eq_snd_of_mem_edges he
      subst d
      have hn : a ∉ p.support := (Walk.cons_isPath_iff hac p).mp hp |>.2
      congr 1
      apply ih q hp.of_cons hq.of_cons
      intro e he
      have heq := hsub (List.mem_cons_of_mem _ he)
      simp only [Walk.edges_cons,List.mem_cons] at heq
      rcases heq with heq | heq
      · subst e
        exact (hn (p.fst_mem_support_of_mem_edges he)).elim
      · exact heq

lemma walk_in_closed_set (S : Set V)
    (hclosed : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ S)
    {a b : V} (p : G.Walk a b) (ha : a ∈ S) : ∀ v ∈ p.support, v ∈ S := by
  induction p with
  | nil => simpa using ha
  | @cons a c b hac p ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ha
    · exact ih (hclosed a ha c hac) v hv

/-- The boundary path of a finite 0/2-degree configuration is unique.
This prevents multiplicity in the physical path expansion. -/
theorem two_port_path_unique [Fintype V] [DecidableRel G.Adj]
    {a b : V} (hab : a ≠ b) (ha : G.degree a = 1) (hb : G.degree b = 1)
    (upper : ∀ v, G.degree v ≤ 2) (p q : G.Walk a b)
    (hp : p.IsPath) (hq : q.IsPath) : p = q := by
  have hs : ∀ v ∈ p.support, v ∈ q.support :=
    walk_in_closed_set {v | v ∈ q.support}
      (fun _ hv _ h => path_closed G hab ha hb upper q hq hv h) p q.start_mem_support
  apply paths_eq_of_edges_subset p q hp hq
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    apply Walk.adj_toSubgraph_iff_mem_edges.mp
    change y ∈ q.toSubgraph.neighborSet x
    rw [path_neighbor_eq G hab ha hb upper q hq (hs x (p.fst_mem_support_of_mem_edges he))]
    exact p.adj_of_mem_edges he
end CriticalHoneycomb.Transfer.PathComponents

namespace CriticalHoneycomb.Transfer.ChordOrientations
open SimpleGraph PhysicalTiles CenterPartition FiniteConfigurations

lemma CenterPath.selected_edge {n : ℕ} (p : CenterPath n) (i : Fin (n+1)) :
    selected p.spins (p.edge i)=true := by
  simp [selected,spinOccupied,p.spins_edge,outSpin_ne_empty]

lemma chord_boundary_selection {D : Finset Center} {a b : Port (D : Set Center)}
    (γ : Chord (D : Set Center) a b) (hab : a.outside≠b.outside) :
    BoundarySelection a b (selected (ofChord γ hab).spins) := by
  refine ⟨?_,?_,?_⟩
  · rw [←ofChord_first_edge γ hab]; exact CenterPath.selected_edge _ _
  · rw [←ofChord_last_edge γ hab]; exact CenterPath.selected_edge _ _
  · intro v hv k hk hs
    let q : Port (D : Set Center) := ⟨v,neighbor v k,(adj_iff_neighbor _ _).mpr ⟨k,rfl⟩,hv,hk⟩
    have hq : q.wire=incidentWire v k := by
      unfold Port.wire
      congr 1
      apply neighbor_injective v
      exact q.neighbor_side
    have hw : q.wire ∈ Set.range (ofChord γ hab).edge := by
      by_contra he
      have hh := (ofChord γ hab).spins_off q.wire he
      rw [hq] at hh
      simp [selected,spinOccupied,hh] at hs
    rcases (ofChord_boundary_wire γ hab q).mp hw with h|h
    · left; rw [←hq,h]
    · right; rw [←hq,h]

/-- The converse path is bound to the actual selected midpoint edges, not
just to the underlying hard-wall graph. -/
theorem chord_selected_path {D : Finset Center} {a b : Port (D : Set Center)}
    (γ : Chord (D : Set Center) a b) (hab : a.outside≠b.outside) (s : Wire → Bool)
    (he : ∀ i, s ((ofChord γ hab).edge i)=true) :
    ∃ (xs : List (Interior D))
      (p : (selectedGraph a b s).Walk (.inr false) (.inr true)),
      xs.map Subtype.val=γ.val ∧ p.IsPath ∧
      p.support=Sum.inr false :: (xs.map Sum.inl ++ [Sum.inr true]) := by
  classical
  let xs : List (Interior D) := γ.val.attach.map fun v=>⟨v.val,γ.property.1.2.2 v.val v.property⟩
  have hmap : xs.map Subtype.val=γ.val := by
    simpa only [xs,List.map_map,Function.comp_def] using List.attach_map_subtype_val γ.val
  have hnd : xs.Nodup := List.Nodup.of_map _ (hmap.symm ▸ γ.property.1.1)
  have hlen : xs.length=γ.val.length := by
    simpa only [List.length_map] using congrArg List.length hmap
  have hget (i : ℕ) (hi : i<xs.length) : (xs[i]).val=γ.val[i]'(by omega) := by
    have hh := congrArg (fun l : List Center=>l[i]?) hmap
    have h1 : (xs.map Subtype.val)[i]?=some (xs[i]).val := by
      simp [List.getElem?_map,List.getElem?_eq_getElem hi]
    have h2 : γ.val[i]?=some (γ.val[i]'(by omega)) := List.getElem?_eq_getElem _
    exact Option.some.inj (h1.symm.trans (hh.trans h2))
  have hchain : xs.IsChain (fun v w=>∃ k : Fin 3, neighbor v.val k=w.val ∧ s (incidentWire v.val k)=true) := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    let z : Fin (γ.val.length+1) := ⟨i+1,by omega⟩
    let u : Fin γ.val.length := ⟨i,by omega⟩
    let v : Fin γ.val.length := ⟨i+1,by omega⟩
    have hu : (ofChord γ hab).point z.castSucc=(xs[i]).val := by
      change (ofChord γ hab).center u=_
      rw [ofChord_center,hget]
    have hv : (ofChord γ hab).point z.succ=(xs[i+1]).val := by
      change (ofChord γ hab).center v=_
      rw [ofChord_center,hget]
    refine ⟨(ofChord γ hab).side z,?_,?_⟩
    · rw [←hu,←hv]; exact (ofChord γ hab).step z
    · rw [←hu]
      exact he z
  have hhead : xs.head?=some (portInside a) := by
    apply Option.map_injective Subtype.val_injective
    change xs.head?.map Subtype.val=some a.inside
    rw [←List.head?_map,hmap]; exact γ.property.2.1
  have hlast : xs.getLast?=some (portInside b) := by
    apply Option.map_injective Subtype.val_injective
    change xs.getLast?.map Subtype.val=some b.inside
    rw [←List.getLast?_map,hmap]; exact γ.property.2.2
  have ha : s a.wire=true := by rw [←ofChord_first_edge γ hab]; exact he _
  have hb : s b.wire=true := by rw [←ofChord_last_edge γ hab]; exact he _
  let support : List (Vertices D) := Sum.inr false :: (xs.map Sum.inl ++ [Sum.inr true])
  have hsc : support.IsChain (selectedGraph a b s).Adj := by
    have hc := (chain_ports (fun v w : Interior D=>∃ k : Fin 3,
      neighbor v.val k=w.val ∧ s (incidentWire v.val k)=true) (portInside a) (portInside b) xs).mpr
      ⟨hchain,hhead,hlast⟩
    apply hc.imp
    intro x y h
    cases x with
    | inl v => cases y with
      | inl w => exact h
      | inr q => cases q <;> exact ⟨congrArg Subtype.val h,by assumption⟩
    | inr q => cases y with
      | inl v => cases q <;> exact ⟨congrArg Subtype.val h,by assumption⟩
      | inr r => cases q <;> cases r <;> exact h.elim
  have hne : support≠[] := List.cons_ne_nil _ _
  have hsh : support.head hne = .inr false := rfl
  have hsl : support.getLast hne = .inr true := by simp [support]
  let p : (selectedGraph a b s).Walk (.inr false) (.inr true) :=
    (Walk.ofSupport support hne hsc).copy hsh hsl
  have hps : p.support=support := by simp [p]
  refine ⟨xs,p,hmap,?_,hps⟩
  rw [Walk.isPath_def,hps]
  simp [support,List.nodup_append,hnd.map Sum.inl_injective]

/-- An unoriented occupied configuration has at most one literal source
chord. This prevents hidden multiplicity in the finite transfer expansion. -/
theorem chord_eq_of_selected_eq {D : Finset Center} {a b : Port (D : Set Center)}
    (γ δ : Chord (D : Set Center) a b) (hab : a.outside≠b.outside)
    (hs : selected (ofChord γ hab).spins=selected (ofChord δ hab).spins) : γ=δ := by
  classical
  let C := configurationOfNonzero a b (fun h=>hab (congrArg Port.outside h))
    (ofChord γ hab).spins (chord_boundary_selection γ hab)
    ((ofChord γ hab).product_nonzero D (by rw [ofChord_first]; exact a.outside_not_mem)
      (by rw [ofChord_last]; exact b.outside_not_mem))
  obtain ⟨xs,p,hxs,hp,hps⟩ := chord_selected_path γ hab _ (CenterPath.selected_edge _)
  obtain ⟨ys,q,hys,hq,hqs⟩ := chord_selected_path δ hab (selected (ofChord γ hab).spins) (by
    intro i; rw [hs]; exact CenterPath.selected_edge _ _)
  have hd (r : Bool) : C.graph.degree (.inr r)=1 := by
    rw [←PathComponents.ncard_neighbors]; exact C.port_degree r
  have hu (v : Vertices D) : C.graph.degree v≤2 := by
    cases v with
    | inl v =>
      have h := C.center_degree v
      rw [PathComponents.ncard_neighbors] at h
      omega
    | inr r => rw [hd]; omega
  have hpq : p=q := PathComponents.two_port_path_unique (G:=C.graph) (by simp)
    (hd false) (hd true) hu p q hp hq
  have hl := congrArg Walk.support hpq
  rw [hps,hqs] at hl
  have he : xs.map Sum.inl=ys.map (Sum.inl : Interior D → Vertices D) :=
    List.append_cancel_right (List.cons.inj hl).2
  have hxy : xs=ys := List.map_injective_iff.mpr Sum.inl_injective he
  apply Subtype.ext
  rw [←hxs,←hys,hxy]

end CriticalHoneycomb.Transfer.ChordOrientations

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations

/-- No two different actual source chords are counted by the same literal
raster shape configuration. -/
theorem rectangleShape_injective {W H : ℕ} {j k : Fin (H+1)} :
    Function.Injective (rectangleShape (W:=W) (H:=H) (j:=j) (k:=k)) := by
  intro γ δ he
  apply chord_eq_of_selected_eq γ δ (west_outside_ne_east W H j k)
  have hg : Matches (rectangleShape γ) (restrictGrid (rectanglePath γ).spins)
      (restrictMiddle (rectanglePath γ).spins) := pathShape_matches _ _ _ _ _
  have hd : Matches (rectangleShape δ) (restrictGrid (rectanglePath δ).spins)
      (restrictMiddle (rectanglePath δ).spins) := pathShape_matches _ _ _ _ _
  rw [←he] at hd
  funext w
  have hh := matches_occupied (by omega) (by omega) hg hd w
  rw [path_spins_restrict (rectanglePath γ) (chord_length_pos γ) (ofChord_center_mem γ _),
    path_spins_restrict (rectanglePath δ) (chord_length_pos δ) (ofChord_center_mem δ _)] at hh
  exact hh

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations
open scoped BigOperators

noncomputable instance rectChordFintype {W H : ℕ} {j k : Fin (H+1)} : Fintype (RectChord W H j k) :=
  Fintype.ofInjective rectangleShape rectangleShape_injective

lemma chord_term_real {W H : ℕ} {j k : Fin (H+1)} (γ : RectChord W H j k) :
    ((kappa:ℂ)^(∑ t, (rectangleShape γ t).visits) * chosenPartition (rectangleShape γ)
      (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)).re=kappa^γ.val.length := by
  rw [actual_chord_chosen_one,mul_one]
  calc
    ((kappa:ℂ)^(∑ t, (rectangleShape γ t).visits)).re = kappa^(∑ t, (rectangleShape γ t).visits) :=
      congrArg Complex.re (Complex.ofReal_pow kappa _).symm
    _ = kappa^γ.val.length := congrArg (fun n : ℕ=>kappa^n) (actual_chord_visits γ)

lemma shape_term_nonnegative {W H : ℕ} (j k : Fin (H+1)) (cfg : Cell (W+1) (H+1) → Shape) :
    0≤((kappa:ℂ)^(∑ t, (cfg t).visits) * chosenPartition cfg
      (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)).re := by
  rcases chosenPartition_zero_or_one cfg _ _ (singleColumn_occupancy k) (singleColumn_occupancy j) with h|h
  · simp [h]
  · simp only [h,mul_one,←Complex.ofReal_pow,Complex.ofReal_re]
    exact pow_nonneg (le_of_lt (Real.rpow_pos_of_pos (by positivity : 0<(2+Real.sqrt 2:ℝ)) (-(1:ℝ)/2))) _

/-- Every literal source chord appears with its exact critical weight and
multiplicity one in the finite physical transfer expansion. Detached loops
are not ignored here: all other fixed configurations are nonnegative. -/
theorem actual_chord_sum_le_transfer {W H : ℕ} (j k : Fin (H+1)) :
    (∑ γ : RectChord W H j k, kappa^γ.val.length) ≤
      (prescribedPartition (W+1) (H+1) (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)).re := by
  classical
  let F : (Cell (W+1) (H+1) → Shape) → ℝ := fun cfg=>
    ((kappa:ℂ)^(∑ t, (cfg t).visits) * chosenPartition cfg
      (singleColumn j) (singleColumn k) (fun _=>1) (fun _=>1)).re
  have hsum : (∑ γ : RectChord W H j k, kappa^γ.val.length) =
      ∑ cfg ∈ Finset.univ.image (rectangleShape (W:=W) (H:=H) (j:=j) (k:=k)), F cfg := by
    rw [Finset.sum_image (fun x _ y _ h=>rectangleShape_injective h)]
    apply Finset.sum_congr rfl
    intro γ hγ
    exact (chord_term_real γ).symm
  rw [hsum,prescribed_shape_expansion]
  simp only [Complex.re_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro cfg hcfg hnot
  exact shape_term_nonnegative j k cfg

/-- A finite-domain mass bound: the actual ENNReal chord mass is dominated by the literal source
physical transfer coefficient. -/
theorem actual_chordMass_le_transfer {W H : ℕ} (j k : Fin (H+1)) :
    chordMass (domain (W+1) (H+1) : Set Center) (westPort W H j) (eastPort W H k) ≤
      ENNReal.ofReal (prescribedPartition (W+1) (H+1) (singleColumn j) (singleColumn k)
        (fun _=>1) (fun _=>1)).re := by
  rw [chordMass,tsum_fintype]
  simp only [weight]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun γ _=>pow_nonneg (le_of_lt (Real.rpow_pos_of_pos (by positivity : 0<(2+Real.sqrt 2:ℝ)) (-(1:ℝ)/2))) γ.val.length)]
  exact ENNReal.ofReal_le_ofReal (actual_chord_sum_le_transfer j k)

end CriticalHoneycomb.Transfer.RasterGrid

end OAI
