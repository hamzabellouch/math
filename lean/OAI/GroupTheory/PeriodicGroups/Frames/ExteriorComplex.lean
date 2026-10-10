import Mathlib

namespace OAI

section
namespace SourceBurnside.Stability.Frames
noncomputable section
open Classical Module

variable (V : Type*)
abbrev Labels := V →₀ ℚ
abbrev Ambient := ExteriorAlgebra ℚ (Labels V)

def vertex (v : V) : Ambient V := ExteriorAlgebra.ι ℚ (Finsupp.single v 1)

def augmentation : Labels V →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun _ : V => (1 : ℚ))

def boundary : Ambient V →ₗ[ℚ] Ambient V :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℚ (Labels V))) (augmentation V)

variable {V}
@[simp] lemma augmentation_single (v : V) : augmentation V (Finsupp.single v 1) = 1 := by
  simp [augmentation]

@[simp] lemma boundary_vertex (v : V) : boundary V (vertex V v) = 1 := by
  simp [boundary, vertex]

@[simp] lemma boundary_one : boundary V (1 : Ambient V) = 0 := by
  simp [boundary]

@[simp] lemma boundary_boundary (x : Ambient V) : boundary V (boundary V x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft (augmentation V) x

lemma boundary_cone (v : V) (x : Ambient V) :
    boundary V (vertex V v * x) = x - vertex V v * boundary V x := by
  simpa [boundary, vertex, augmentation] using
    (CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm ℚ (Labels V)))
      (augmentation V) (Finsupp.single v 1) x)

variable [LinearOrder V]

def basis : Basis (Finset V) ℚ (Ambient V) := (Finsupp.basisSingleOne : Basis V ℚ (Labels V)).ExteriorAlgebra

@[simp] lemma basis_empty : basis (V := V) ∅ = 1 := by
  rw [basis, ExteriorAlgebra.basis_apply_ofCard (s_card := Finset.card_empty)]
  simp [ExteriorAlgebra.ιMulti_family]

@[simp] lemma basis_singleton (v : V) : basis (V := V) {v} = vertex V v := by
  rw [basis, ExteriorAlgebra.basis_apply_ofCard (s_card := Finset.card_singleton v)]
  have he : (Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_singleton v))) 0 = v := by
    apply Finset.mem_singleton.mp
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (Set.powersetCard.ofCard (Finset.card_singleton v)) _).mp ⟨0, rfl⟩
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply, vertex, he]

lemma vertex_mul_basis (v : V) (s : Finset V) (hv : v ∉ s) :
    ∃ c : ℚ, c ≠ 0 ∧ vertex V v * basis s = c • basis (insert v s) := by
  let t := Set.powersetCard.ofCard (Finset.card_singleton v)
  let u := Set.powersetCard.ofCard (rfl : s.card = s.card)
  have hd : Disjoint t.val u.val := by simpa [t, u] using Finset.disjoint_singleton_left.mpr hv
  have he := ExteriorAlgebra.basis_mul_of_disjoint
    (Finsupp.basisSingleOne : Basis V ℚ (Labels V)) t u hd
  have hu : (Set.powersetCard.disjUnion hd : Finset V) = insert v s := by
    ext x
    simp [Set.powersetCard.coe_disjUnion, t, u]
  change basis {v} * basis s = _ at he
  rw [basis_singleton, hu] at he
  refine ⟨((Set.powersetCard.permOfDisjoint hd).sign : ℤ), ?_, ?_⟩
  · exact_mod_cast (Set.powersetCard.permOfDisjoint hd).sign.ne_zero
  · simpa only [basis, Units.smul_def, Int.cast_smul_eq_zsmul] using he

variable {F W : Type*} [DivisionRing F] [AddCommGroup W] [Module F W]

def chains (ρ : V → W) (s : Set V) (k : ℕ) : Submodule ℚ (Ambient V) :=
  Submodule.span ℚ {x | ∃ t : Finset V, (t : Set V) ⊆ s ∧ t.card = k ∧
    LinearIndepOn F ρ (t : Set V) ∧ x = basis t}

lemma basis_mem_chains (ρ : V → W) {s : Set V} (t : Finset V) (ht : (t : Set V) ⊆ s)
    (hi : LinearIndepOn F ρ (t : Set V)) : basis t ∈ chains (F := F) ρ s t.card :=
  Submodule.subset_span ⟨t, ht, rfl, hi, rfl⟩

lemma chains_mono (ρ : V → W) {s t : Set V} (hst : s ⊆ t) (k : ℕ) :
    chains (F := F) ρ s k ≤ chains (F := F) ρ t k := by
  apply Submodule.span_mono
  rintro x ⟨u, hu, hc, hi, rfl⟩
  exact ⟨u, hu.trans hst, hc, hi, rfl⟩

lemma cone_mem_chains (ρ : V → W) {s : Set V} (v : V)
    (hv : ρ v ∉ Submodule.span F (ρ '' s)) {k : ℕ} {x : Ambient V}
    (hx : x ∈ chains (F := F) ρ s k) :
    vertex V v * x ∈ chains (F := F) ρ (insert v s) (k+1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl, hi, rfl⟩ := hx
    have hn : v ∉ t := fun h => hv (Submodule.subset_span ⟨v, ht h, rfl⟩)
    obtain ⟨c, _, he⟩ := vertex_mul_basis v t hn
    rw [he]
    apply Submodule.smul_mem
    have hi' : LinearIndepOn F ρ (insert v (t : Set V)) :=
      hi.insert (fun h => hv (Submodule.span_mono (Set.image_mono ht) h))
    have hc : (insert v t).card = t.card+1 := Finset.card_insert_of_notMem hn
    rw [← hc]
    exact basis_mem_chains ρ _ (by simp only [Finset.coe_insert]; exact Set.insert_subset_insert ht)
      (by simpa only [Finset.coe_insert] using hi')
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [mul_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [mul_smul_comm] using Submodule.smul_mem _ c ih

lemma boundary_basis_mem (ρ : V → W) (k : ℕ) (t : Finset V) (hc : t.card = k+1)
    (hi : LinearIndepOn F ρ (t : Set V)) :
    boundary V (basis t) ∈ chains (F := F) ρ (t : Set V) k := by
  induction k generalizing t with
  | zero =>
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    simp only [basis_singleton, boundary_vertex]
    rw [← basis_empty]
    exact basis_mem_chains ρ ∅ (by simp) (by simp [LinearIndepOn])
  | succ k ih =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
    let u := t.erase v
    have hn : v ∉ u := Finset.notMem_erase _ _
    have hu : insert v u = t := Finset.insert_erase hv
    have hcu : u.card = k+1 := by
      have h := Finset.card_erase_of_mem hv
      change (t.erase v).card = k+1
      omega
    have hiu : LinearIndepOn F ρ (u : Set V) := hi.mono (Finset.erase_subset v t)
    have hout : ρ v ∉ Submodule.span F (ρ '' (u : Set V)) := by
      apply LinearIndepOn.notMem_span_of_insert _ hn
      simpa only [← Finset.coe_insert, hu] using hi
    obtain ⟨c, hc0, he⟩ := vertex_mul_basis v u hn
    rw [hu] at he
    have hmem : boundary V (vertex V v * basis u) ∈ chains (F := F) ρ (t : Set V) (k+1) := by
      rw [boundary_cone]
      apply Submodule.sub_mem
      · rw [← hcu]
        exact basis_mem_chains ρ u (Finset.erase_subset v t) hiu
      · have hm := cone_mem_chains ρ v hout (ih u hcu hiu)
        simpa only [← Finset.coe_insert, hu] using hm
    rw [he, map_smul] at hmem
    exact (Submodule.smul_mem_iff _ hc0).mp hmem

lemma boundary_mem_chains (ρ : V → W) {s : Set V} {k : ℕ} {x : Ambient V}
    (hx : x ∈ chains (F := F) ρ s (k+1)) :
    boundary V x ∈ chains (F := F) ρ s k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    exact chains_mono ρ ht k (boundary_basis_mem ρ k t hc hi)
  | zero => simpa only [map_zero] using (chains (F := F) ρ s k).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma vertex_mem_chains (ρ : V → W) {s : Set V} (v : V) (hv : v ∈ s) (hn : ρ v ≠ 0) :
    vertex V v ∈ chains (F := F) ρ s 1 := by
  rw [← basis_singleton]
  simpa using basis_mem_chains ρ {v} (by simpa using hv)
    (by simpa using ((linearIndepOn_singleton_iff F).mpr hn : LinearIndepOn F ρ {v}))

section EnoughRank
variable (ρ : V → W) [FiniteDimensional F W]

omit [LinearOrder V] [FiniteDimensional F W] in
lemma exists_outside_labels (hρ : Submodule.span F (Set.range ρ) = ⊤)
    (s : Finset V) (hs : s.card < Module.finrank F W) :
    ∃ v, ρ v ∉ Submodule.span F (ρ '' (s : Set V)) := by
  by_contra! hn
  have ht : Submodule.span F (ρ '' (s : Set V)) = ⊤ := by
    apply top_unique
    rw [← hρ]
    exact Submodule.span_le.mpr (by rintro x ⟨v, rfl⟩; exact hn v)
  have hc := finrank_span_finset_le_card (R := F) (s.image ρ)
  change Module.finrank F (Submodule.span F ((s.image ρ : Finset W) : Set W)) ≤ _ at hc
  rw [Finset.coe_image, ht] at hc
  have : Module.finrank F W ≤ s.card := by
    simpa using hc.trans (Finset.card_image_le)
  omega

structure ConeSupply (N : ℕ) where
  pick : Finset V → V
  outside : ∀ s : Finset V, s.card ≤ N →
    ρ (pick s) ∉ Submodule.span F (ρ '' (s : Set V))

def coneSupply (hρ : Submodule.span F (Set.range ρ) = ⊤) (N : ℕ)
    (hN : N < Module.finrank F W) : ConeSupply (F := F) ρ N where
  pick s := if hs : s.card ≤ N then
      (exists_outside_labels ρ hρ s (lt_of_le_of_lt hs hN)).choose
    else (exists_outside_labels ρ hρ ∅ (by simpa using lt_of_le_of_lt (Nat.zero_le N) hN)).choose
  outside s hs := by
    simp only [dite_eq_left hs]
    exact (exists_outside_labels ρ hρ s (lt_of_le_of_lt hs hN)).choose_spec

end EnoughRank

variable (ρ : V → W) (C : ConeSupply (F := F) ρ 10)

def baseLabel : V := C.pick ∅

omit [LinearOrder V] in
lemma baseLabel_ne_zero : ρ (baseLabel ρ C) ≠ 0 := by
  have h := C.outside ∅ (by simp)
  simpa [baseLabel] using h

def cone0 (v : V) : V := C.pick {baseLabel ρ C, v}

def support0 (s : Finset V) : Finset V := insert (baseLabel ρ C) (s ∪ s.image (cone0 ρ C))

lemma subset_support0 (s : Finset V) : s ⊆ support0 ρ C s := by
  intro v hv
  simp [support0, hv]

lemma support0_mono {s t : Finset V} (h : s ⊆ t) : support0 ρ C s ⊆ support0 ρ C t :=
  Finset.insert_subset_insert _ (Finset.union_subset_union h (Finset.image_subset_image h))

lemma card_support0 (s : Finset V) : (support0 ρ C s).card ≤ 1+2*s.card := by
  calc
    _ ≤ (s ∪ s.image (cone0 ρ C)).card+1 := Finset.card_insert_le _ _
    _ ≤ s.card+(s.image (cone0 ρ C)).card+1 := Nat.add_le_add_right (Finset.card_union_le _ _) 1
    _ ≤ s.card+s.card+1 := Nat.add_le_add_right (Nat.add_le_add_left Finset.card_image_le _) 1
    _ = _ := by omega

def homotopy0Vertex (v : V) : Ambient V :=
  vertex V (cone0 ρ C v) * (vertex V v - vertex V (baseLabel ρ C))

lemma boundary_homotopy0Vertex (v : V) :
    boundary V (homotopy0Vertex ρ C v) = vertex V v - vertex V (baseLabel ρ C) := by
  simp [homotopy0Vertex, boundary_cone]

def homotopy0 : Ambient V →ₗ[ℚ] Ambient V :=
  (basis (V := V)).constr ℚ (fun t => ∑ v ∈ t, homotopy0Vertex ρ C v)

@[simp] lemma homotopy0_vertex (v : V) : homotopy0 ρ C (vertex V v) = homotopy0Vertex ρ C v := by
  unfold homotopy0
  rw [← basis_singleton, Basis.constr_basis, Finset.sum_singleton]

lemma boundary_homotopy0 {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 1) :
    boundary V (homotopy0 ρ C x) = x - vertex V (baseLabel ρ C) * boundary V x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    simp [boundary_homotopy0Vertex]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, mul_add]; abel
  | smul c x hx ih => simp only [map_smul, ih, smul_sub, mul_smul_comm]

lemma homotopy0Vertex_mem (v : V) (hv : ρ v ≠ 0) :
    homotopy0Vertex ρ C v ∈ chains (F := F) ρ (support0 ρ C {v} : Set V) 2 := by
  have hout : ρ (cone0 ρ C v) ∉
      Submodule.span F (ρ '' ({baseLabel ρ C, v} : Set V)) := by
    simpa only [cone0, Finset.coe_insert, Finset.coe_singleton] using
      C.outside {baseLabel ρ C, v} (Finset.card_le_two.trans (by decide : 2 ≤ 10))
  have h1 : vertex V v - vertex V (baseLabel ρ C) ∈
      chains (F := F) ρ ({baseLabel ρ C, v} : Set V) 1 :=
    Submodule.sub_mem _ (vertex_mem_chains ρ v (by simp) hv)
      (vertex_mem_chains ρ _ (by simp) (baseLabel_ne_zero ρ C))
  have h2 : homotopy0Vertex ρ C v ∈
      chains (F := F) ρ (insert (cone0 ρ C v) {baseLabel ρ C, v}) 2 :=
    cone_mem_chains ρ (cone0 ρ C v) hout h1
  refine chains_mono ρ (t := (support0 ρ C {v} : Set V)) ?_ 2 h2
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> simp [support0, cone0]

lemma homotopy0_mem {s : Finset V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ (s : Set V) 1) :
    homotopy0 ρ C x ∈ chains (F := F) ρ (support0 ρ C s : Set V) 2 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    rw [basis_singleton, homotopy0_vertex]
    have hn : ρ v ≠ 0 := (linearIndepOn_singleton_iff F).mp (by simpa using hi)
    exact chains_mono ρ (support0_mono ρ C ht) 2 (homotopy0Vertex_mem ρ C v hn)
  | zero => simpa only [map_zero] using (chains (F := F) ρ (support0 ρ C s : Set V) 2).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

def cone1 (t : Finset V) : V := C.pick (support0 ρ C t)

def support1 (s : Finset V) : Finset V :=
  support0 ρ C s ∪ (s.powersetCard 2).image (cone1 ρ C)

lemma subset_support1 (s : Finset V) : s ⊆ support1 ρ C s :=
  (subset_support0 ρ C s).trans Finset.subset_union_left

lemma small_support1 {s : Finset V} (hs : s.card = 3) : (support1 ρ C s).card ≤ 10 := by
  have h0 := card_support0 ρ C s
  have h1 := Finset.card_image_le (s := s.powersetCard 2) (f := cone1 ρ C)
  have h2 : (s.powersetCard 2).card = 3 := by rw [Finset.card_powersetCard, hs]; decide
  have h3 := Finset.card_union_le (support0 ρ C s) ((s.powersetCard 2).image (cone1 ρ C))
  change (support0 ρ C s ∪ _).card ≤ 10
  omega

def homotopy1Basis (t : Finset V) : Ambient V :=
  vertex V (cone1 ρ C t) * (basis t - homotopy0 ρ C (boundary V (basis t)))

def homotopy1 : Ambient V →ₗ[ℚ] Ambient V :=
  (basis (V := V)).constr ℚ (homotopy1Basis ρ C)

@[simp] lemma homotopy1_basis (t : Finset V) :
    homotopy1 ρ C (basis t) = homotopy1Basis ρ C t := by
  exact Basis.constr_basis _ _ _ _

lemma boundary_homotopy1Basis (t : Finset V) (ht : t.card = 2)
    (hi : LinearIndepOn F ρ (t : Set V)) :
    boundary V (homotopy1Basis ρ C t) = basis t - homotopy0 ρ C (boundary V (basis t)) := by
  have hd := boundary_basis_mem ρ 1 t ht hi
  have he := boundary_homotopy0 ρ C hd
  simp only [boundary_boundary, mul_zero, sub_zero] at he
  simp only [homotopy1Basis, boundary_cone, map_sub, he, sub_self, mul_zero, sub_zero]

lemma boundary_homotopy1 {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 2) :
    boundary V (homotopy1 ρ C x) = x - homotopy0 ρ C (boundary V x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    rw [homotopy1_basis]
    exact boundary_homotopy1Basis ρ C t hc hi
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]; abel
  | smul c x hx ih => simp only [map_smul, ih, smul_sub]

lemma homotopy1Basis_mem (t : Finset V) (ht : t.card = 2)
    (hi : LinearIndepOn F ρ (t : Set V)) :
    homotopy1Basis ρ C t ∈
      chains (F := F) ρ (insert (cone1 ρ C t) (support0 ρ C t : Set V)) 3 := by
  have hd := boundary_basis_mem ρ 1 t ht hi
  have h0 := homotopy0_mem ρ C hd
  have hcard : (support0 ρ C t).card ≤ 10 := by have := card_support0 ρ C t; omega
  have hout : ρ (cone1 ρ C t) ∉ Submodule.span F (ρ '' (support0 ρ C t : Set V)) :=
    C.outside _ hcard
  have hb : basis t ∈ chains (F := F) ρ (support0 ρ C t : Set V) 2 := by
    rw [← ht]
    exact basis_mem_chains ρ t (subset_support0 ρ C t) hi
  exact cone_mem_chains ρ _ hout (Submodule.sub_mem _ hb h0)

lemma homotopy1_mem {s : Finset V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ (s : Set V) 2) :
    homotopy1 ρ C x ∈ chains (F := F) ρ (support1 ρ C s : Set V) 3 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    rw [homotopy1_basis]
    have h2 := homotopy1Basis_mem ρ C t hc hi
    refine chains_mono ρ ?_ 3 h2
    intro v hv
    rcases hv with rfl | hv
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_powersetCard.mpr ⟨ht, hc⟩, rfl⟩)
    · exact Finset.mem_union_left _ (support0_mono ρ C ht hv)
  | zero => simpa only [map_zero] using (chains (F := F) ρ (support1 ρ C s : Set V) 3).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

def cone2 (t : Finset V) : V := C.pick (support1 ρ C t)

def homotopy2Basis (t : Finset V) : Ambient V :=
  vertex V (cone2 ρ C t) * (basis t - homotopy1 ρ C (boundary V (basis t)))

def homotopy2 : Ambient V →ₗ[ℚ] Ambient V :=
  (basis (V := V)).constr ℚ (homotopy2Basis ρ C)

@[simp] lemma homotopy2_basis (t : Finset V) :
    homotopy2 ρ C (basis t) = homotopy2Basis ρ C t := by
  exact Basis.constr_basis _ _ _ _

lemma boundary_homotopy2Basis (t : Finset V) (ht : t.card = 3)
    (hi : LinearIndepOn F ρ (t : Set V)) :
    boundary V (homotopy2Basis ρ C t) = basis t - homotopy1 ρ C (boundary V (basis t)) := by
  have hd := boundary_basis_mem ρ 2 t ht hi
  have he := boundary_homotopy1 ρ C hd
  simp only [boundary_boundary, map_zero, sub_zero] at he
  simp only [homotopy2Basis, boundary_cone, map_sub, he, sub_self, mul_zero, sub_zero]

lemma boundary_homotopy2 {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 3) :
    boundary V (homotopy2 ρ C x) = x - homotopy1 ρ C (boundary V x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    rw [homotopy2_basis]
    exact boundary_homotopy2Basis ρ C t hc hi
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]; abel
  | smul c x hx ih => simp only [map_smul, ih, smul_sub]

lemma homotopy2Basis_mem (t : Finset V) (ht : t.card = 3)
    (hi : LinearIndepOn F ρ (t : Set V)) :
    homotopy2Basis ρ C t ∈ chains (F := F) ρ Set.univ 4 := by
  have hd := boundary_basis_mem ρ 2 t ht hi
  have h1 := homotopy1_mem ρ C hd
  have hout : ρ (cone2 ρ C t) ∉ Submodule.span F (ρ '' (support1 ρ C t : Set V)) :=
    C.outside _ (small_support1 ρ C ht)
  have hb : basis t ∈ chains (F := F) ρ (support1 ρ C t : Set V) 3 := by
    rw [← ht]
    exact basis_mem_chains ρ t (subset_support1 ρ C t) hi
  have hcone : homotopy2Basis ρ C t ∈
      chains (F := F) ρ (insert (cone2 ρ C t) (support1 ρ C t : Set V)) 4 :=
    cone_mem_chains ρ _ hout (Submodule.sub_mem _ hb h1)
  exact chains_mono ρ (Set.subset_univ _) 4 hcone

lemma homotopy2_mem {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 3) :
    homotopy2 ρ C x ∈ chains (F := F) ρ Set.univ 4 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    rw [homotopy2_basis]
    exact homotopy2Basis_mem ρ C t hc hi
  | zero => simpa only [map_zero] using (chains (F := F) ρ Set.univ 4).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem twoCycle_bounds [FiniteDimensional F W]
    (hρ : Submodule.span F (Set.range ρ) = ⊤) (hrank : 10 < Module.finrank F W)
    {z : Ambient V} (hz : z ∈ chains (F := F) ρ Set.univ 3) (hcycle : boundary V z = 0) :
    ∃ w ∈ chains (F := F) ρ Set.univ 4, boundary V w = z := by
  let D := coneSupply ρ hρ 10 hrank
  refine ⟨homotopy2 ρ D z, homotopy2_mem ρ D hz, ?_⟩
  rw [boundary_homotopy2 ρ D hz, hcycle, map_zero, sub_zero]

lemma homotopy0_mem_univ {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 1) :
    homotopy0 ρ C x ∈ chains (F := F) ρ Set.univ 2 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    have hb : basis t ∈ chains (F := F) ρ (t : Set V) 1 := by
      rw [← hc]; exact basis_mem_chains ρ t (Set.Subset.refl _) hi
    exact chains_mono ρ (Set.subset_univ _) 2 (homotopy0_mem ρ C hb)
  | zero => simpa only [map_zero] using (chains (F := F) ρ Set.univ 2).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma homotopy1_mem_univ {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 2) :
    homotopy1 ρ C x ∈ chains (F := F) ρ Set.univ 3 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    have hb : basis t ∈ chains (F := F) ρ (t : Set V) 2 := by
      rw [← hc]; exact basis_mem_chains ρ t (Set.Subset.refl _) hi
    exact chains_mono ρ (Set.subset_univ _) 3 (homotopy1_mem ρ C hb)
  | zero => simpa only [map_zero] using (chains (F := F) ρ Set.univ 3).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma degreeZero_support {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 0) :
    x ∈ chains (F := F) ρ ∅ 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    have : t = ∅ := Finset.card_eq_zero.mp hc
    subst t
    exact Submodule.subset_span ⟨∅, by simp, rfl, hi, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => exact Submodule.smul_mem _ c ih

lemma boundary_degreeZero {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 0) :
    boundary V x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    have : t = ∅ := Finset.card_eq_zero.mp hc
    subst t
    simp
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul c x hx ih => simp [ih]

include C in
lemma degreeZero_lift {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 0) :
    ∃ y ∈ chains (F := F) ρ Set.univ 1, boundary V y = x := by
  have ho : ρ (baseLabel ρ C) ∉ Submodule.span F (ρ '' (∅ : Set V)) := by
    simpa only [baseLabel, Finset.coe_empty] using C.outside ∅ (by simp)
  have hm := cone_mem_chains ρ (baseLabel ρ C) ho (degreeZero_support ρ hx)
  exact ⟨vertex V (baseLabel ρ C) * x, chains_mono ρ (Set.subset_univ _) 1 hm,
    by rw [boundary_cone, boundary_degreeZero ρ hx, mul_zero, sub_zero]⟩

theorem cycles_bound_upToThree [FiniteDimensional F W]
    (hρ : Submodule.span F (Set.range ρ) = ⊤) (hrank : 10 < Module.finrank F W)
    (k : ℕ) (hk : k ≤ 3) {z : Ambient V}
    (hz : z ∈ chains (F := F) ρ Set.univ k) (hcycle : boundary V z = 0) :
    ∃ w ∈ chains (F := F) ρ Set.univ (k+1), boundary V w = z := by
  let D := coneSupply ρ hρ 10 hrank
  interval_cases k
  · exact degreeZero_lift ρ D hz
  · refine ⟨homotopy0 ρ D z, homotopy0_mem_univ ρ D hz, ?_⟩
    rw [boundary_homotopy0 ρ D hz, hcycle, mul_zero, sub_zero]
  · refine ⟨homotopy1 ρ D z, homotopy1_mem_univ ρ D hz, ?_⟩
    rw [boundary_homotopy1 ρ D hz, hcycle, map_zero, sub_zero]
  · exact twoCycle_bounds ρ hρ hrank hz hcycle

def differential (k : ℕ) : chains (F := F) ρ Set.univ (k+1) →ₗ[ℚ] chains (F := F) ρ Set.univ k :=
  LinearMap.codRestrict _ ((boundary V).domRestrict _) (fun z => boundary_mem_chains ρ z.property)

@[simp] lemma differential_val (k : ℕ) (z : chains (F := F) ρ Set.univ (k+1)) :
    (differential (F := F) ρ k z).val = boundary V z.val := rfl

lemma differential_sq (k : ℕ) : (differential (F := F) ρ k).comp (differential (F := F) ρ (k+1)) = 0 := by
  ext x
  exact boundary_boundary _

open CategoryTheory in

def augmentedComplex : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of ℚ (chains (F := F) ρ Set.univ k))
    (fun k => ModuleCat.ofHom (differential (F := F) ρ k))
    (fun k => by ext x; exact boundary_boundary _)

@[simp] lemma augmentedComplex_d (k : ℕ) :
    (augmentedComplex (F := F) ρ).d (k+1) k =
      ModuleCat.ofHom (differential (F := F) ρ k) :=
  by
    dsimp [augmentedComplex]
    exact ChainComplex.of_d _ _ k

theorem augmentedComplex_exact [FiniteDimensional F W]
    (hρ : Submodule.span F (Set.range ρ) = ⊤) (hrank : 10 < Module.finrank F W)
    (k : ℕ) (hk : k ≤ 3) : (augmentedComplex (F := F) ρ).ExactAt k := by
  rw [HomologicalComplex.exactAt_iff, CategoryTheory.ShortComplex.moduleCat_exact_iff]
  change ∀ z : (augmentedComplex (F := F) ρ).X k,
    (augmentedComplex (F := F) ρ).d k ((ComplexShape.down ℕ).next k) z = 0 →
    ∃ w : (augmentedComplex (F := F) ρ).X ((ComplexShape.down ℕ).prev k),
      (augmentedComplex (F := F) ρ).d ((ComplexShape.down ℕ).prev k) k w = z
  rw [ChainComplex.prev]
  intro z hz
  change chains (F := F) ρ Set.univ k at z
  have hx : (z : Ambient V) ∈ chains (F := F) ρ Set.univ k := z.property
  have hc : boundary V (z : Ambient V) = 0 := by
    cases k with
    | zero => exact boundary_degreeZero ρ hx
    | succ k =>
      rw [ChainComplex.next_nat_succ] at hz
      rw [augmentedComplex_d] at hz
      exact congrArg Subtype.val hz
  obtain ⟨w, hw, he⟩ := cycles_bound_upToThree ρ hρ hrank k hk hx hc
  rw [augmentedComplex_d]
  exact ⟨⟨w, hw⟩, Subtype.ext he⟩

end
end SourceBurnside.Stability.Frames

end
section
namespace SourceBurnside.Stability.Frames
noncomputable section
open Classical Module
variable {V : Type*}

def labelMap (f : V → V) : Ambient V →ₐ[ℚ] Ambient V :=
  ExteriorAlgebra.map (Finsupp.lmapDomain ℚ ℚ f)

@[simp] lemma labelMap_vertex (f : V → V) (v : V) :
    labelMap f (vertex V v) = vertex V (f v) := by
  simp [labelMap,vertex,Finsupp.lmapDomain_apply]

@[simp] lemma labelMap_id : labelMap (V := V) id = AlgHom.id ℚ _ := by
  simp [labelMap,Finsupp.lmapDomain_id]

lemma labelMap_comp (f g : V → V) : labelMap (g ∘ f) = (labelMap g).comp (labelMap f) := by
  simp [labelMap,Finsupp.lmapDomain_comp]

variable [LinearOrder V]

lemma basis_insert_inverse (v : V) (s : Finset V) (hv : v∉s) :
    ∃c : ℚ, c≠0 ∧ basis (insert v s) = c • (vertex V v * basis s) := by
  obtain ⟨c,hc,he⟩ := vertex_mul_basis v s hv
  refine ⟨c⁻¹,inv_ne_zero hc,?_⟩
  rw [he,smul_smul,inv_mul_cancel₀ hc,one_smul]

lemma labelMap_basis (f : V → V) (hf : Function.Injective f) (s : Finset V) :
    ∃c : ℚ, c≠0 ∧ labelMap f (basis s) = c • basis (s.image f) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,one_ne_zero,by simp⟩
  | @insert v s hv ih =>
    obtain ⟨c,hc,he⟩ := basis_insert_inverse v s hv
    obtain ⟨d,hd,hde⟩ := ih
    have hv' : f v ∉ s.image f := by simpa only [Finset.mem_image, hf.eq_iff, exists_eq_right] using hv
    obtain ⟨e,he0,hee⟩ := vertex_mul_basis (f v) (s.image f) hv'
    refine ⟨c*(d*e),mul_ne_zero hc (mul_ne_zero hd he0),?_⟩
    rw [he,map_smul,map_mul,labelMap_vertex,hde,mul_smul_comm,hee,smul_smul,smul_smul,
      Finset.image_insert]
    simp only [mul_assoc]

lemma boundary_labelMap (f : V → V) (x : Ambient V) :
    boundary V (labelMap f x) = labelMap f (boundary V x) := by
  suffices h : (boundary V).comp (labelMap f).toLinearMap =
      (labelMap f).toLinearMap.comp (boundary V) from DFunLike.congr_fun h x
  apply (basis (V := V)).ext
  intro s
  change boundary V (labelMap f (basis s)) = labelMap f (boundary V (basis s))
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
    obtain ⟨c,hc,he⟩ := basis_insert_inverse v s hv
    rw [he,map_smul,map_smul,map_smul,map_smul,map_mul,labelMap_vertex,
      boundary_cone,boundary_cone,map_sub,map_mul,labelMap_vertex,ih]

variable (G : Type*) [Group G] [MulAction G V]

def ambientAction : Representation ℚ G (Ambient V) where
  toFun g := (labelMap (g • ·)).toLinearMap
  map_one' := by
    change (labelMap (fun v : V => 1 • v)).toLinearMap = LinearMap.id
    simp only [one_smul]
    change (labelMap (V := V) id).toLinearMap = LinearMap.id
    rw [labelMap_id]
    rfl
  map_mul' g h := by
    change (labelMap (fun v : V => (g*h) • v)).toLinearMap =
      (labelMap (g • ·)).toLinearMap.comp (labelMap (h • ·)).toLinearMap
    have he : (fun v : V => (g*h) • v) = (g • ·) ∘ (h • ·) := funext (mul_smul g h)
    rw [he,labelMap_comp]
    rfl

variable {F W : Type*} [DivisionRing F] [AddCommGroup W] [Module F W]
variable (ρ : V → W)
variable (hind : ∀(g : G) (s : Set V), LinearIndepOn F ρ s →
  LinearIndepOn F ρ ((g • ·) '' s))

include hind in
lemma labelMap_chains (g : G) (k : ℕ) {x : Ambient V}
    (hx : x ∈ chains (F := F) ρ Set.univ k) :
    labelMap (g • ·) x ∈ chains (F := F) ρ Set.univ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s,hs,hcard,hi,rfl⟩ := hx
    obtain ⟨c,hc,he⟩ := labelMap_basis (g • ·) (MulAction.injective g) s
    rw [he]
    apply (chains (F := F) ρ Set.univ k).smul_mem c
    have hc : (s.image (g • ·)).card = k := by
      rw [Finset.card_image_of_injective _ (MulAction.injective g),hcard]
    rw [←hc]
    exact basis_mem_chains (F := F) ρ (s.image (g • ·)) (Set.subset_univ _)
      (by simpa using hind g (s : Set V) hi)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (chains (F := F) ρ Set.univ k).add_mem ihx ihy
  | smul a x hx ih => simpa using (chains (F := F) ρ Set.univ k).smul_mem a ih

def chainSubrepresentation (k : ℕ) : Subrepresentation (ambientAction (V := V) G) where
  toSubmodule := chains (F := F) ρ Set.univ k
  apply_mem_toSubmodule g := fun {_} hx => labelMap_chains G ρ hind g k hx

def chainRep (k : ℕ) : Rep ℚ G := Rep.of (chainSubrepresentation G (ρ := ρ) hind k).toRepresentation

end
end SourceBurnside.Stability.Frames

end

end OAI
