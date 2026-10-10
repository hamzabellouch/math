import Mathlib

namespace OAI

 

noncomputable section

namespace Honeycomb

abbrev Cell := ℤ × ℤ

structure Vertex where
  i : ℤ
  j : ℤ
  isR : Bool
  deriving DecidableEq

 

structure Edge where
  i : ℤ
  j : ℤ
  kind : Fin 3
  deriving DecidableEq

def Edge.p (e : Edge) : Vertex := ⟨e.i, e.j, false⟩

def Edge.r (e : Edge) : Vertex :=
  ⟨e.i - if e.kind = 1 then 1 else 0,
   e.j - if e.kind = 2 then 1 else 0, true⟩

def Edge.ends (e : Edge) : Sym2 Vertex := s(e.p, e.r)

def h : ℂ := ⟨Real.sqrt 3, 0⟩
def v : ℂ := ⟨Real.sqrt 3 / 2, 3 / 2⟩

def cellPosition (t : Cell) : ℂ := (t.1 : ℂ) * h + (t.2 : ℂ) * v

 
def position (a : Vertex) : ℂ :=
  cellPosition (a.i, a.j) + if a.isR then (h + v) / 3 else 0

def cyclicSucc {n : ℕ} (k : Fin n) : Fin n :=
  ⟨(k.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩

 

def IsSimpleCycle (s : Finset Edge) : Prop :=
  ∃ (n : ℕ), 3 ≤ n ∧ ∃ a : Fin n → Vertex, Function.Injective a ∧
    s.image Edge.ends = Finset.univ.image (fun k => s(a k, a (cyclicSucc k)))

structure EmbeddedPolygon where
  edges : Finset Edge
  isCycle : IsSimpleCycle edges

@[ext] theorem EmbeddedPolygon.ext {p q : EmbeddedPolygon} (h : p.edges = q.edges) :
    p = q := by
  cases p
  cases q
  cases h
  rfl

theorem EmbeddedPolygon.edges_nonempty (p : EmbeddedPolygon) : p.edges.Nonempty := by
  obtain ⟨n, hn, a, _, ha⟩ := p.isCycle
  have hn0 : 0 < n := by omega
  have hu : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
  have hh := hu.image (fun k => s(a k, a (cyclicSucc k)))
  rw [← ha] at hh
  exact Finset.image_nonempty.mp hh

def Vertex.translate (t : Cell) (a : Vertex) : Vertex :=
  ⟨a.i + t.1, a.j + t.2, a.isR⟩

def Edge.translate (t : Cell) (e : Edge) : Edge :=
  ⟨e.i + t.1, e.j + t.2, e.kind⟩

@[simp] theorem Edge.translate_zero (e : Edge) : Edge.translate 0 e = e := by
  cases e
  simp [Edge.translate]

@[simp] theorem Edge.translate_translate (t u : Cell) (e : Edge) :
    Edge.translate t (Edge.translate u e) = Edge.translate (t + u) e := by
  cases e
  simp [Edge.translate, add_left_comm, add_comm]

theorem Edge.translate_injective (t : Cell) : Function.Injective (Edge.translate t) := by
  intro e f h
  have hh := congrArg (Edge.translate (-t)) h
  simpa using hh

@[simp] theorem Edge.p_translate (t : Cell) (e : Edge) :
    (Edge.translate t e).p = Vertex.translate t e.p := rfl

@[simp] theorem Edge.r_translate (t : Cell) (e : Edge) :
    (Edge.translate t e).r = Vertex.translate t e.r := by
  dsimp [Edge.r, Edge.translate, Vertex.translate]
  congr 1 <;> omega

@[simp] theorem position_translate (t : Cell) (a : Vertex) :
    position (Vertex.translate t a) = position a + cellPosition t := by
  simp only [position, Vertex.translate, cellPosition, Int.cast_add]
  ring_nf

def translateEdges (t : Cell) (s : Finset Edge) : Finset Edge :=
  s.image (Edge.translate t)

@[simp] theorem translateEdges_zero (s : Finset Edge) : translateEdges 0 s = s := by
  have hh : Edge.translate (0 : Cell) = id := funext Edge.translate_zero
  simp [translateEdges, hh]

@[simp] theorem translateEdges_translate (t u : Cell) (s : Finset Edge) :
    translateEdges t (translateEdges u s) = translateEdges (t + u) s := by
  simp only [translateEdges, Finset.image_image]
  congr 1
  funext e
  exact Edge.translate_translate t u e

@[simp] theorem translateEdges_card (t : Cell) (s : Finset Edge) :
    (translateEdges t s).card = s.card :=
  Finset.card_image_of_injective _ (Edge.translate_injective t)

 
def vertices (s : Finset Edge) : Finset Vertex := s.image Edge.p ∪ s.image Edge.r

def pointSet (s : Finset Edge) : Set ℂ := position '' (vertices s : Set Vertex)

def embeddedDiameter (s : Finset Edge) : ℝ := Metric.diam (pointSet s)

@[simp] theorem vertices_translate (t : Cell) (s : Finset Edge) :
    vertices (translateEdges t s) = (vertices s).image (Vertex.translate t) := by
  simp [vertices, translateEdges, Finset.image_union, Finset.image_image, Function.comp_def]

theorem pointSet_translate (t : Cell) (s : Finset Edge) :
    pointSet (translateEdges t s) = (fun z => z + cellPosition t) '' pointSet s := by
  simp only [pointSet, vertices_translate, Finset.coe_image, Set.image_image]
  simp only [position_translate]

theorem embeddedDiameter_translate (t : Cell) (s : Finset Edge) :
    embeddedDiameter (translateEdges t s) = embeddedDiameter s := by
  rw [embeddedDiameter, pointSet_translate]
  exact (show Isometry (fun z : ℂ => z + cellPosition t) from
    fun z w => by simp [edist_dist, dist_eq_norm]).diam_image _

 
def TranslationEquivalent (p q : EmbeddedPolygon) : Prop :=
  ∃ t : Cell, translateEdges t p.edges = q.edges

instance polygonSetoid : Setoid EmbeddedPolygon where
  r := TranslationEquivalent
  iseqv := {
    refl := fun p => ⟨0, translateEdges_zero _⟩
    symm := by
      intro p q h
      obtain ⟨t, ht⟩ := h
      refine ⟨-t, ?_⟩
      rw [← ht]
      simp
    trans := by
      intro p q r h₁ h₂
      obtain ⟨t, ht⟩ := h₁
      obtain ⟨u, hu⟩ := h₂
      refine ⟨u + t, ?_⟩
      rw [← translateEdges_translate, ht, hu]
  }

 
abbrev Polygon := Quotient polygonSetoid

def length : Polygon → ℕ := Quotient.lift (fun p => p.edges.card) (by
  intro p q h
  obtain ⟨t, ht⟩ := h
  rw [← ht, translateEdges_card])

def diameter : Polygon → ℝ := Quotient.lift (fun p => embeddedDiameter p.edges) (by
  intro p q h
  obtain ⟨t, ht⟩ := h
  rw [← ht, embeddedDiameter_translate])

 
def xStar : ℝ := (Real.sqrt (2 + Real.sqrt 2))⁻¹

def weight (γ : Polygon) : ℝ := xStar ^ length γ

def massTerm (r : ℝ) (γ : Polygon) : ℝ :=
  if r ≤ diameter γ then weight γ else 0

def lengthTerm (r : ℝ) (γ : Polygon) : ℝ :=
  if r ≤ diameter γ then (length γ : ℝ) * weight γ else 0

def secondMomentTerm (r : ℝ) (γ : Polygon) : ℝ :=
  if diameter γ ≤ r then (length γ : ℝ) ^ 2 * weight γ else 0

 
def A (r : ℝ) : ℝ := ∑' γ : Polygon, massTerm r γ

 
def P (r : ℝ) : ℝ := ∑' γ : Polygon, lengthTerm r γ

 
def M2 (r : ℝ) : ℝ := ∑' γ : Polygon, secondMomentTerm r γ

 

theorem Edge.ends_injective : Function.Injective Edge.ends := by
  rintro ⟨ei, ej, ek⟩ ⟨fi, fj, fk⟩ hh
  rcases Sym2.eq_iff.mp hh with ⟨hp, hr⟩ | ⟨hp, _⟩
  · have hi := congrArg Vertex.i hp
    have hj := congrArg Vertex.j hp
    dsimp [Edge.p] at hi hj
    subst fi
    subst fj
    have hk : ek = fk := by
      have hri := congrArg Vertex.i hr
      have hrj := congrArg Vertex.j hr
      dsimp [Edge.r] at hri hrj
      clear hh hp hr
      fin_cases ek <;> fin_cases fk <;> simp at hri hrj ⊢ <;> omega
    cases hk
    rfl
  · have hf := congrArg Vertex.isR hp
    simp [Edge.p, Edge.r] at hf

theorem diameter_nonneg (γ : Polygon) : 0 ≤ diameter γ := by
  induction γ using Quotient.inductionOn with
  | h p => exact Metric.diam_nonneg

theorem xStar_pos : 0 < xStar := by
  unfold xStar
  positivity

theorem xStar_lt_one : xStar < 1 := by
  have hh : 1 < Real.sqrt (2 + Real.sqrt 2) := by
    apply (Real.lt_sqrt (by norm_num)).2
    have h2 := Real.sqrt_nonneg (2 : ℝ)
    linarith
  exact inv_lt_one_of_one_lt₀ hh

theorem weight_pos (γ : Polygon) : 0 < weight γ := pow_pos xStar_pos _

theorem weight_nonneg (γ : Polygon) : 0 ≤ weight γ := (weight_pos γ).le

theorem massTerm_nonneg (r : ℝ) (γ : Polygon) : 0 ≤ massTerm r γ := by
  have hw := weight_nonneg γ
  unfold massTerm
  split_ifs <;> positivity

theorem lengthTerm_nonneg (r : ℝ) (γ : Polygon) : 0 ≤ lengthTerm r γ := by
  have hw := weight_nonneg γ
  unfold lengthTerm
  split_ifs <;> positivity

theorem secondMomentTerm_nonneg (r : ℝ) (γ : Polygon) : 0 ≤ secondMomentTerm r γ := by
  have hw := weight_nonneg γ
  unfold secondMomentTerm
  split_ifs <;> positivity

theorem A_nonneg (r : ℝ) : 0 ≤ A r := tsum_nonneg (massTerm_nonneg r)
theorem P_nonneg (r : ℝ) : 0 ≤ P r := tsum_nonneg (lengthTerm_nonneg r)
theorem M2_nonneg (r : ℝ) : 0 ≤ M2 r := tsum_nonneg (secondMomentTerm_nonneg r)

 

def anchor (γ : Polygon) : Edge := γ.out.edges_nonempty.choose

theorem anchor_mem (γ : Polygon) : anchor γ ∈ γ.out.edges :=
  γ.out.edges_nonempty.choose_spec

def anchorCell (γ : Polygon) : Cell := ((anchor γ).i, (anchor γ).j)

def anchoredEdges (γ : Polygon) : Finset Edge :=
  translateEdges (-anchorCell γ) γ.out.edges

theorem anchoredEdges_injective : Function.Injective anchoredEdges := by
  intro γ δ hh
  have hshift := congrArg (translateEdges (anchorCell δ)) hh
  simp only [anchoredEdges, translateEdges_translate, add_neg_cancel,
    translateEdges_zero] at hshift
  have hq : (⟦γ.out⟧ : Polygon) = ⟦δ.out⟧ :=
    Quotient.sound ⟨anchorCell δ + -anchorCell γ, hshift⟩
  simpa only [Quotient.out_eq] using hq

theorem embeddedDiameter_out (γ : Polygon) :
    embeddedDiameter γ.out.edges = diameter γ := by
  change diameter (Quotient.mk _ γ.out) = diameter γ
  rw [Quotient.out_eq]

theorem anchoredEdges_diameter (γ : Polygon) :
    embeddedDiameter (anchoredEdges γ) = diameter γ := by
  rw [anchoredEdges, embeddedDiameter_translate, embeddedDiameter_out]

theorem pointSet_finite (s : Finset Edge) : (pointSet s).Finite :=
  (vertices s).finite_toSet.image position

theorem p_mem_pointSet {e : Edge} {s : Finset Edge} (he : e ∈ s) :
    position e.p ∈ pointSet s := by
  exact ⟨e.p, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩), rfl⟩

theorem zero_mem_anchored_pointSet (γ : Polygon) :
    0 ∈ pointSet (anchoredEdges γ) := by
  have he : Edge.translate (-anchorCell γ) (anchor γ) ∈ anchoredEdges γ :=
    Finset.mem_image.mpr ⟨anchor γ, anchor_mem γ, rfl⟩
  have hp := p_mem_pointSet he
  simpa [Edge.translate, anchorCell, Edge.p, position, cellPosition] using hp

theorem norm_position_p_le_diameter (γ : Polygon) {e : Edge}
    (he : e ∈ anchoredEdges γ) : ‖position e.p‖ ≤ diameter γ := by
  have hd := Metric.dist_le_diam_of_mem
    (pointSet_finite (anchoredEdges γ)).isBounded
    (p_mem_pointSet he) (zero_mem_anchored_pointSet γ)
  rw [dist_zero_right] at hd
  change ‖position e.p‖ ≤ embeddedDiameter (anchoredEdges γ) at hd
  rwa [anchoredEdges_diameter] at hd

@[simp] theorem position_p_re (e : Edge) :
    (position e.p).re = (e.i : ℝ) * Real.sqrt 3 + (e.j : ℝ) * (Real.sqrt 3 / 2) := by
  simp [position, Edge.p, cellPosition, h, v]

@[simp] theorem position_p_im (e : Edge) :
    (position e.p).im = (e.j : ℝ) * (3 / 2) := by
  simp [position, Edge.p, cellPosition, h, v]

 
theorem edge_coordinate_bound {e : Edge} {r : ℝ} (hr : ‖position e.p‖ ≤ r) :
    |(e.i : ℝ)| ≤ 2 * r ∧ |(e.j : ℝ)| ≤ 2 * r := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr
  have hy : |(e.j : ℝ) * (3 / 2)| ≤ r := by
    simpa using (Complex.abs_im_le_norm (position e.p)).trans hr
  have hj : |(e.j : ℝ)| ≤ r := by
    rw [abs_le] at hy ⊢
    constructor <;> linarith
  have hx : |(e.i : ℝ) * Real.sqrt 3 + (e.j : ℝ) * (Real.sqrt 3 / 2)| ≤ r := by
    simpa using (Complex.abs_re_le_norm (position e.p)).trans hr
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs1 : 1 ≤ Real.sqrt 3 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  have hs2 : Real.sqrt 3 ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    norm_num
  have hjs : |(e.j : ℝ) * (Real.sqrt 3 / 2)| ≤ r := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 3 / 2)]
    calc
      |(e.j : ℝ)| * (Real.sqrt 3 / 2) ≤ r * 1 :=
        mul_le_mul hj (by linarith) (by positivity) hr0
      _ = r := mul_one _
  have his : |(e.i : ℝ) * Real.sqrt 3| ≤ 2 * r := by
    calc
      |(e.i : ℝ) * Real.sqrt 3| =
          |((e.i : ℝ) * Real.sqrt 3 + (e.j : ℝ) * (Real.sqrt 3 / 2)) -
            (e.j : ℝ) * (Real.sqrt 3 / 2)| := by ring_nf
      _ ≤ |(e.i : ℝ) * Real.sqrt 3 + (e.j : ℝ) * (Real.sqrt 3 / 2)| +
            |(e.j : ℝ) * (Real.sqrt 3 / 2)| := abs_sub _ _
      _ ≤ 2 * r := by linarith
  refine ⟨?_, by linarith⟩
  calc
    |(e.i : ℝ)| ≤ |(e.i : ℝ)| * Real.sqrt 3 := le_mul_of_one_le_right (abs_nonneg _) hs1
    _ = |(e.i : ℝ) * Real.sqrt 3| := by rw [abs_mul, abs_of_nonneg hs0]
    _ ≤ 2 * r := his

 
def edgeBox (b : ℤ) : Finset Edge :=
  ((Finset.Icc (-b) b ×ˢ Finset.Icc (-b) b) ×ˢ (Finset.univ : Finset (Fin 3))).image
    (fun t => ⟨t.1.1, t.1.2, t.2⟩)

theorem mem_edgeBox {b : ℤ} {e : Edge} :
    e ∈ edgeBox b ↔ (-b ≤ e.i ∧ e.i ≤ b) ∧ (-b ≤ e.j ∧ e.j ≤ b) := by
  simp only [edgeBox, Finset.mem_image, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_univ, and_true]
  constructor
  · rintro ⟨⟨⟨i, j⟩, k⟩, hh, he⟩
    cases he
    exact hh
  · intro hh
    exact ⟨((e.i, e.j), e.kind), hh, by cases e; rfl⟩

theorem anchoredEdges_subset_box {γ : Polygon} {r : ℝ} (hr : diameter γ ≤ r) :
    anchoredEdges γ ⊆ edgeBox ⌈2 * r⌉ := by
  intro e he
  have hh := edge_coordinate_bound ((norm_position_p_le_diameter γ he).trans hr)
  have hceil := Int.le_ceil (2 * r)
  have hi : |(e.i : ℝ)| ≤ (⌈2 * r⌉ : ℤ) := hh.1.trans hceil
  have hj : |(e.j : ℝ)| ≤ (⌈2 * r⌉ : ℤ) := hh.2.trans hceil
  rw [abs_le] at hi hj
  apply mem_edgeBox.mpr
  constructor <;> constructor
  · exact_mod_cast hi.1
  · exact_mod_cast hi.2
  · exact_mod_cast hj.1
  · exact_mod_cast hj.2

 
theorem finite_diameter_le (r : ℝ) : {γ : Polygon | diameter γ ≤ r}.Finite := by
  apply Set.Finite.of_injOn (f := anchoredEdges)
    (t := ↑(edgeBox ⌈2 * r⌉).powerset)
  · intro γ hγ
    exact Finset.mem_powerset.mpr (anchoredEdges_subset_box hγ)
  · exact anchoredEdges_injective.injOn
  · exact Finset.finite_toSet _

theorem summable_diameter_truncation (r : ℝ) (f : Polygon → ℝ) :
    Summable (fun γ => if diameter γ ≤ r then f γ else 0) := by
  apply summable_of_hasFiniteSupport
  apply (finite_diameter_le r).subset
  intro γ hγ
  by_contra hh
  exact hγ (ite_eq_right hh)

theorem summable_secondMomentTerm (r : ℝ) : Summable (secondMomentTerm r) :=
  summable_diameter_truncation r (fun γ => (length γ : ℝ) ^ 2 * weight γ)

 
theorem M2_monotone : Monotone M2 := by
  intro r s hrs
  apply (summable_secondMomentTerm r).tsum_le_tsum _ (summable_secondMomentTerm s)
  intro γ
  have hw := weight_nonneg γ
  unfold secondMomentTerm
  split_ifs with h₁ h₂ h₂
  · exact le_rfl
  · exact False.elim (h₂ (h₁.trans hrs))
  · positivity
  · exact le_rfl

 

instance : Countable Edge := by
  have hinj : Function.Injective (fun e : Edge => (e.i, e.j, e.kind)) := by
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hh
    simpa only [Prod.mk.injEq, Edge.mk.injEq] using hh
  exact hinj.countable

instance : Countable EmbeddedPolygon := by
  have hinj : Function.Injective EmbeddedPolygon.edges := by
    intro p q hpq
    exact EmbeddedPolygon.ext hpq
  exact hinj.countable

theorem polygon_countable : Countable Polygon := inferInstance

theorem length_pos (γ : Polygon) : 0 < length γ := by
  induction γ using Quotient.inductionOn with
  | h p => exact Finset.card_pos.mpr p.edges_nonempty

def hexagonEdges : Finset Edge :=
  {⟨0, 0, 0⟩, ⟨1, 0, 1⟩, ⟨1, 0, 2⟩, ⟨1, -1, 0⟩, ⟨1, -1, 1⟩, ⟨0, 0, 2⟩}

 
def hexagon : EmbeddedPolygon where
  edges := hexagonEdges
  isCycle := by
    refine ⟨6, by omega, ![⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨1, 0, false⟩,
      ⟨1, -1, true⟩, ⟨1, -1, false⟩, ⟨0, -1, true⟩], ?_, ?_⟩
    · decide
    · decide

theorem hexagon_length : length ⟦hexagon⟧ = 6 := by decide

instance : Nonempty Polygon := ⟨⟦hexagon⟧⟩

 
theorem Edge.unit_length (e : Edge) : dist (position e.p) (position e.r) = 1 := by
  rw [dist_eq_norm, Complex.norm_def]
  suffices hh : Complex.normSq (position e.p - position e.r) = 1 by
    rw [hh, Real.sqrt_one]
  rcases e with ⟨i, j, k⟩
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases k <;>
    simp [Complex.normSq_apply, Edge.p, Edge.r, position, cellPosition, h, v] <;>
    ring_nf <;> nlinarith

 
theorem position_injective : Function.Injective position := by
  rintro ⟨i, j, b⟩ ⟨i', j', b'⟩ hh
  have hx := congrArg Complex.re hh
  have hy := congrArg Complex.im hh
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  cases b <;> cases b' <;>
    simp [position, cellPosition, h, v] at hx hy
  · have hj : j = j' := hy
    subst j'
    have hi : i = i' := by
      exact_mod_cast (mul_right_cancel₀ hs
        (show (i : ℝ) * Real.sqrt 3 = (i' : ℝ) * Real.sqrt 3 by linarith))
    subst i'
    rfl
  · have hbad : 3 * j = 3 * j' + 1 := by
      exact_mod_cast (show 3 * (j : ℝ) = 3 * (j' : ℝ) + 1 by linarith)
    omega
  · have hbad : 3 * j + 1 = 3 * j' := by
      exact_mod_cast (show 3 * (j : ℝ) + 1 = 3 * (j' : ℝ) by linarith)
    omega
  · have hj : j = j' := hy
    subst j'
    have hi : i = i' := by
      exact_mod_cast (mul_right_cancel₀ hs
        (show (i : ℝ) * Real.sqrt 3 = (i' : ℝ) * Real.sqrt 3 by linarith))
    subst i'
    rfl

end Honeycomb

end

end OAI
