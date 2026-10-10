import Mathlib

namespace OAI

/-! Strict honeycomb bridges and their finite length classes. -/



noncomputable section
open scoped ENNReal
open Filter

namespace HoneycombActual

structure Vertex where
  col : ℤ
  row : ℤ
  up : Bool
  deriving DecidableEq

def up (i j : ℤ) : Vertex := ⟨i, j, true⟩
def down (i j : ℤ) : Vertex := ⟨i, j, false⟩

def UpDownAdj (v w : Vertex) : Prop :=
  v.up = true ∧ w.up = false ∧
    ((w.col = v.col ∧ w.row + 1 = v.row) ∨
     (w.col = v.col ∧ w.row = v.row) ∨
     (w.col + 1 = v.col ∧ w.row = v.row))

def Adj (v w : Vertex) : Prop := UpDownAdj v w ∨ UpDownAdj w v

def rowSpacing : ℝ := Real.sqrt 3 / 2

def position (v : Vertex) : ℂ :=
  if v.up then
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1/2,
      rowSpacing * ((v.row : ℝ) + 1/3)⟩
  else
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1,
      rowSpacing * ((v.row : ℝ) + 2/3)⟩

def port (i j : ℤ) : ℂ :=
  ⟨(i : ℝ) + (j : ℝ) / 2 + 1/2, rowSpacing * (j : ℝ)⟩

structure Bridge where
  height : ℕ
  terminal : ℤ
  vertices : List Vertex
  height_pos : 0 < height
  self_avoiding : vertices.Nodup
  connected : vertices.IsChain Adj
  initiates : vertices.head? = some (up 0 0)
  terminates : vertices.getLast? = some (down terminal ((height : ℤ) - 1))
  in_strip : ∀ v ∈ vertices, 0 ≤ v.row ∧ v.row < (height : ℤ)

namespace Bridge

def length (b : Bridge) : ℕ := b.vertices.length

def endpointDistance (b : Bridge) : ℝ :=
  dist (port 0 0) (port b.terminal b.height)

def trace (b : Bridge) : Set ℂ :=
  {port 0 0, port b.terminal b.height} ∪ (position '' {v | v ∈ b.vertices})

def diameter (b : Bridge) : ℝ := Metric.diam b.trace

def crosses (r : ℕ) (e : Vertex × Vertex) : Bool :=
  decide ((e.1.row < (r : ℤ) ∧ (r : ℤ) ≤ e.2.row) ∨
          (e.2.row < (r : ℤ) ∧ (r : ℤ) ≤ e.1.row))

def crossingCount (b : Bridge) (r : ℕ) : ℕ :=
  (b.vertices.zip b.vertices.tail).countP (crosses r)

def Irreducible (b : Bridge) : Prop :=
  ∀ r : ℕ, 0 < r → r < b.height → b.crossingCount r ≠ 1

end Bridge

def rho : ℝ := (Real.sqrt (2 + Real.sqrt 2))⁻¹

def weight (b : Bridge) : ℝ≥0∞ := ENNReal.ofReal (rho ^ b.length)

def criticalMass (P : Bridge → Prop) : ℝ≥0∞ := by
  classical
  exact ∑' b : Bridge, if P b then weight b else 0

def bridgeMass (h : ℕ) : ℝ≥0∞ :=
  if h = 0 then 1 else criticalMass (fun b => b.height = h)

def lengthReward (h : ℕ) : ℝ≥0∞ := by
  classical
  exact ∑' b : Bridge, if b.height = h then (b.length : ℝ≥0∞) * weight b else 0

def uniformLengthProbability (n : ℕ) (P : Bridge → Prop) : ℝ :=
  (Nat.card {b : Bridge // b.length = n ∧ P b} : ℝ) /
  (Nat.card {b : Bridge // b.length = n} : ℝ)

def FiniteBridgeEstimates : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (∃ h₀ : ℕ, 0 < h₀ ∧ ∀ h : ℕ, h₀ ≤ h →
      ENNReal.ofReal (c * (h : ℝ) ^ (-(1/4 : ℝ))) ≤ bridgeMass h ∧
      bridgeMass h ≤ ENNReal.ofReal (C * (h : ℝ) ^ (-(1/4 : ℝ))) ∧
      lengthReward h ≤ ENNReal.ofReal (C * (h : ℝ) ^ (13/12 : ℝ)) ∧
      ENNReal.ofReal (c * (h : ℝ) ^ (-(1/4 : ℝ))) ≤
        criticalMass (fun b => b.height = h ∧ c * (h : ℝ) ^ (4/3 : ℝ) ≤ b.length)) ∧
    (∀ h : ℕ, 0 < h → ∀ x : ℝ, 1 ≤ x →
      criticalMass (fun b => b.height = h ∧ x < b.diameter) ≤
        ENNReal.ofReal (C * x ^ (-(1/4 : ℝ)))) ∧
    (∀ h : ℕ, bridgeMass h ≠ ⊤ ∧ lengthReward h ≠ ⊤)

def ExactLengthSpatialLaw : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Tendsto (fun m : ℕ => uniformLengthProbability (2*m) (fun b =>
      (2*m : ℝ) ^ ((3/4 : ℝ) - ξ) ≤ b.endpointDistance ∧
      b.endpointDistance ≤ b.diameter ∧
      b.diameter ≤ (2*m : ℝ) ^ ((3/4 : ℝ) + ξ))) atTop (nhds 1)

theorem rho_pos : 0 < rho := by
  unfold rho
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem Adj.side_ne {v w : Vertex} (h : Adj v w) : v.up ≠ w.up := by
  rcases h with ⟨hv, hw, _⟩ | ⟨hw, hv, _⟩ <;> simp [hv, hw]

theorem chain_length_parity (v : Vertex) (xs : List Vertex)
    (h : (v :: xs).IsChain Adj) (z : Vertex)
    (hz : (v :: xs).getLast? = some z) :
    (v :: xs).length % 2 = 0 ↔ v.up ≠ z.up := by
  induction xs generalizing v with
  | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hz
      subst z
      simp
  | cons w xs ih =>
      obtain ⟨hvw, hw⟩ := List.isChain_cons_cons.mp h
      have hcol := Adj.side_ne hvw
      have hlast : (w :: xs).getLast? = some z := by simpa using hz
      have hp := ih w hw hlast
      simp only [List.length_cons] at hp ⊢
      cases hv : v.up <;> cases hw' : w.up <;> cases hz' : z.up <;>
        simp_all <;> omega

theorem Bridge.even_length (b : Bridge) : Even b.length := by
  have hh := b.initiates
  cases hlist : b.vertices with
  | nil => simp [hlist] at hh
  | cons v xs =>
      have hv : v = up 0 0 := by simpa [hlist] using hh
      subst v
      have hc : (up 0 0 :: xs).IsChain Adj := by simpa [hlist] using b.connected
      have ht : (up 0 0 :: xs).getLast? =
          some (down b.terminal ((b.height : ℤ) - 1)) := by
        simpa [hlist] using b.terminates
      have hp := (chain_length_parity (up 0 0) xs hc _ ht).mpr (by simp [up, down])
      exact even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero (by simpa [Bridge.length, hlist] using hp))

def zigzagTwo : Bridge where
  height := 1
  terminal := 0
  vertices := [up 0 0, down 0 0]
  height_pos := by decide
  self_avoiding := by simp [up, down]
  connected := by simp [List.isChain_cons_cons, Adj, UpDownAdj, up, down]
  initiates := rfl
  terminates := by rfl
  in_strip := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> norm_num [up, down]

def zigzagFour : Bridge where
  height := 1
  terminal := 1
  vertices := [up 0 0, down 0 0, up 1 0, down 1 0]
  height_pos := by decide
  self_avoiding := by simp [up, down]
  connected := by simp [List.isChain_cons_cons, Adj, UpDownAdj, up, down]
  initiates := rfl
  terminates := by rfl
  in_strip := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> norm_num [up, down]

theorem Bridge.irreducible_of_height_one (b : Bridge) (h : b.height = 1) :
    b.Irreducible := by
  intro r hr hrh
  omega

theorem zigzagTwo_irreducible : zigzagTwo.Irreducible :=
  zigzagTwo.irreducible_of_height_one rfl

theorem zigzagFour_irreducible : zigzagFour.Irreducible :=
  zigzagFour.irreducible_of_height_one rfl

theorem weight_pos (b : Bridge) : 0 < weight b := by
  exact ENNReal.ofReal_pos.mpr (pow_pos rho_pos _)

theorem weight_le_criticalMass (P : Bridge → Prop) (b : Bridge) (h : P b) :
    weight b ≤ criticalMass P := by
  classical
  unfold criticalMass
  have ht : (if P b then weight b else 0) ≤
      ∑' a : Bridge, if P a then weight a else 0 :=
    ENNReal.le_tsum (f := fun bridge : Bridge => if P bridge then weight bridge else 0) b
  simpa only [ite_eq_left h] using ht

def halfLengthMass (m : ℕ) : ℝ≥0∞ :=
  criticalMass (fun b => b.Irreducible ∧ b.length = 2*m)

theorem halfLengthMass_one_pos : 0 < halfLengthMass 1 := by
  have h : zigzagTwo.Irreducible ∧ zigzagTwo.length = 2*1 :=
    ⟨zigzagTwo_irreducible, rfl⟩
  exact (weight_pos zigzagTwo).trans_le (weight_le_criticalMass _ _ h)

theorem halfLengthMass_two_pos : 0 < halfLengthMass 2 := by
  have h : zigzagFour.Irreducible ∧ zigzagFour.length = 2*2 :=
    ⟨zigzagFour_irreducible, rfl⟩
  exact (weight_pos zigzagFour).trans_le (weight_le_criticalMass _ _ h)

def SpanOne (w : ℕ → ℝ≥0∞) : Prop :=
  AddSubgroup.closure {z : ℤ | ∃ m n : ℕ, 0 < w m ∧ 0 < w n ∧
    z = (m : ℤ) - (n : ℤ)} = ⊤

theorem actual_halfLength_span_one : SpanOne halfLengthMass := by
  apply top_unique
  intro z _
  have hOne : (1 : ℤ) ∈ AddSubgroup.closure
      {z : ℤ | ∃ m n : ℕ, 0 < halfLengthMass m ∧ 0 < halfLengthMass n ∧
        z = (m : ℤ) - (n : ℤ)} := by
    apply AddSubgroup.subset_closure
    exact ⟨2, 1, halfLengthMass_two_pos, halfLengthMass_one_pos, by norm_num⟩
  simpa using AddSubgroup.zsmul_mem _ hOne z

def neighbors (v : Vertex) : Finset Vertex :=
  if v.up then
    {down v.col (v.row-1), down v.col v.row, down (v.col-1) v.row}
  else
    {up v.col (v.row+1), up v.col v.row, up (v.col+1) v.row}

theorem mem_neighbors_iff (v w : Vertex) : w ∈ neighbors v ↔ Adj v w := by
  rcases v with ⟨i, j, s⟩
  rcases w with ⟨k, l, t⟩
  cases s <;> cases t <;>
    simp [neighbors, Adj, UpDownAdj, up, down, Vertex.mk.injEq] <;> omega

def walkLists (v : Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[v]}
  | n+1 => (neighbors v).biUnion (fun w => (walkLists w n).image (List.cons v))

theorem isChain_mem_walkLists (v : Vertex) (xs : List Vertex)
    (h : (v :: xs).IsChain Adj) : v :: xs ∈ walkLists v xs.length := by
  induction xs generalizing v with
  | nil => simp [walkLists]
  | cons w xs ih =>
      obtain ⟨hvw, hc⟩ := List.isChain_cons_cons.mp h
      change v :: w :: xs ∈
        (neighbors v).biUnion (fun a => (walkLists a xs.length).image (List.cons v))
      exact Finset.mem_biUnion.mpr ⟨w, (mem_neighbors_iff v w).mpr hvw,
        Finset.mem_image.mpr ⟨w :: xs, ih w hc, rfl⟩⟩

theorem Bridge.vertices_mem_walkLists (b : Bridge) :
    b.vertices ∈ walkLists (up 0 0) (b.length - 1) := by
  have hh := b.initiates
  cases hv : b.vertices with
  | nil => simp [hv] at hh
  | cons v xs =>
      have heq : v = up 0 0 := by simpa [hv] using hh
      subst v
      simpa [Bridge.length, hv] using
        isChain_mem_walkLists (up 0 0) xs (by simpa [hv] using b.connected)

theorem Bridge.length_pos (b : Bridge) : 0 < b.length := by
  have hh := b.initiates
  cases hv : b.vertices with
  | nil => simp [hv] at hh
  | cons v xs => simp [Bridge.length, hv]

theorem Bridge.vertices_injective : Function.Injective Bridge.vertices := by
  intro b c heq
  rcases b with ⟨h, t, vs, hp, hs, hc, hi, ht, hv⟩
  rcases c with ⟨h', t', vs', hp', hs', hc', hi', ht', hv'⟩
  dsimp at heq
  subst vs'
  have he : down t ((h : ℤ)-1) = down t' ((h' : ℤ)-1) :=
    Option.some.inj (ht.symm.trans ht')
  have het := congrArg Vertex.col he
  have heh := congrArg Vertex.row he
  dsimp [down] at het heh
  have heh' : h = h' := by omega
  subst t'
  subst h'
  rfl

instance finiteBridgeLength (n : ℕ) : Finite {b : Bridge // b.length = n} := by
  let f : {b : Bridge // b.length = n} →
      {l : List Vertex // l ∈ walkLists (up 0 0) (n-1)} := fun b =>
    ⟨b.val.vertices, by simpa [b.property] using b.val.vertices_mem_walkLists⟩
  apply Finite.of_injective f
  intro b c heq
  apply Subtype.ext
  apply Bridge.vertices_injective
  exact congrArg Subtype.val heq

instance finiteBridgeLengthEvent (n : ℕ) (P : Bridge → Prop) :
    Finite {b : Bridge // b.length = n ∧ P b} := by
  let f : {b : Bridge // b.length = n ∧ P b} →
      {b : Bridge // b.length = n} := fun b => ⟨b.val, b.property.1⟩
  apply Finite.of_injective f
  intro b c heq
  apply Subtype.ext
  exact congrArg (fun a : {b : Bridge // b.length = n} => a.val) heq

theorem exactLengthMass_eq (n : ℕ) (P : Bridge → Prop) :
    criticalMass (fun b => b.length = n ∧ P b) =
      (Nat.card {b : Bridge // b.length = n ∧ P b} : ℝ≥0∞) *
        ENNReal.ofReal (rho ^ n) := by
  classical
  let := Fintype.ofFinite {b : Bridge // b.length = n ∧ P b}
  have hsub : criticalMass (fun b => b.length = n ∧ P b) =
      ∑' b : {b : Bridge // b.length = n ∧ P b}, weight b.val := by
    calc
      criticalMass (fun b => b.length = n ∧ P b) =
          ∑' b : Bridge, {b : Bridge | b.length = n ∧ P b}.indicator weight b := by
        unfold criticalMass
        apply tsum_congr
        intro b
        by_cases hb : b.length = n ∧ P b <;> simp [hb]
      _ = _ := (tsum_subtype {b : Bridge | b.length = n ∧ P b} weight).symm
  rw [hsub]
  have hweights : (fun b : {b : Bridge // b.length = n ∧ P b} => weight b.val) =
      fun _ => ENNReal.ofReal (rho ^ n) := by
    funext b
    simp only [weight, b.property.1]
  rw [hweights, tsum_fintype]
  simp [Nat.card_eq_fintype_card, nsmul_eq_mul]

theorem lengthMass_eq (n : ℕ) :
    criticalMass (fun b => b.length = n) =
      (Nat.card {b : Bridge // b.length = n} : ℝ≥0∞) *
        ENNReal.ofReal (rho ^ n) := by
  classical
  let := Fintype.ofFinite {b : Bridge // b.length = n}
  have hsub : criticalMass (fun b => b.length = n) =
      ∑' b : {b : Bridge // b.length = n}, weight b.val := by
    calc
      criticalMass (fun b => b.length = n) =
          ∑' b : Bridge, {b : Bridge | b.length = n}.indicator weight b := by
        unfold criticalMass
        apply tsum_congr
        intro b
        by_cases hb : b.length = n <;> simp [hb]
      _ = _ := (tsum_subtype {b : Bridge | b.length = n} weight).symm
  rw [hsub]
  have hweights : (fun b : {b : Bridge // b.length = n} => weight b.val) =
      fun _ => ENNReal.ofReal (rho ^ n) := by
    funext b
    simp only [weight, b.property]
  rw [hweights, tsum_fintype]
  simp [Nat.card_eq_fintype_card, nsmul_eq_mul]

theorem lengthMass_ne_top (n : ℕ) : criticalMass (fun b => b.length = n) ≠ ⊤ := by
  rw [lengthMass_eq]
  exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top

theorem uniformLengthProbability_eq_critical_ratio (n : ℕ) (P : Bridge → Prop) :
    uniformLengthProbability n P =
      (criticalMass (fun b => b.length = n ∧ P b) /
        criticalMass (fun b => b.length = n)).toReal := by
  rw [exactLengthMass_eq, lengthMass_eq, ENNReal.toReal_div]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (le_of_lt (pow_pos rho_pos n))]
  exact (mul_div_mul_right _ _ (ne_of_gt (pow_pos rho_pos n))).symm

theorem Bridge.halfLength_pos (b : Bridge) : 0 < b.length / 2 := by
  obtain ⟨k, hk⟩ := b.even_length
  have hp := b.length_pos
  omega

theorem Bridge.twice_halfLength (b : Bridge) : 2 * (b.length / 2) = b.length := by
  obtain ⟨k, hk⟩ := b.even_length
  omega

theorem halfLengthMass_eq_pushforward (m : ℕ) :
    halfLengthMass m = criticalMass (fun b => b.Irreducible ∧ b.length / 2 = m) := by
  unfold halfLengthMass
  congr 1
  funext b
  have he := b.twice_halfLength
  exact propext (by constructor <;> rintro ⟨hI, hL⟩ <;> exact ⟨hI, by omega⟩)

theorem halfLengthMass_zero : halfLengthMass 0 = 0 := by
  classical
  rw [halfLengthMass_eq_pushforward]
  unfold criticalMass
  calc
    _ = ∑' _ : Bridge, (0 : ℝ≥0∞) := by
      apply tsum_congr
      intro b
      split_ifs with hb
      · have hp := b.halfLength_pos
        omega
      · rfl
    _ = 0 := tsum_zero

def rowVertex (k : ℕ) : Vertex :=
  if k % 2 = 0 then up ((k / 2 : ℕ) : ℤ) 0 else down ((k / 2 : ℕ) : ℤ) 0

theorem rowVertex_injective : Function.Injective rowVertex := by
  intro k l h
  have hc := congrArg Vertex.col h
  have hs := congrArg Vertex.up h
  by_cases hk : k % 2 = 0 <;> by_cases hl : l % 2 = 0 <;>
    simp [rowVertex, hk, hl, up, down] at hc hs <;> omega

theorem rowVertex_adj (k : ℕ) : Adj (rowVertex k) (rowVertex (k+1)) := by
  by_cases hk : k % 2 = 0
  · have hk' : (k+1) % 2 ≠ 0 := by omega
    have he : (k+1) / 2 = k / 2 := by omega
    simp [rowVertex, hk, hk', Adj, UpDownAdj, up, down, he]
  · have hk' : (k+1) % 2 = 0 := by omega
    have he : (k+1) / 2 = k / 2 + 1 := by omega
    simp [rowVertex, hk, hk', Adj, UpDownAdj, up, down, he]

def rowZigzag (m : ℕ) (hm : 0 < m) : Bridge where
  height := 1
  terminal := m - 1
  vertices := List.ofFn (fun i : Fin (2*m) => rowVertex i.val)
  height_pos := by decide
  self_avoiding := List.nodup_ofFn.mpr (rowVertex_injective.comp Fin.val_injective)
  connected := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.getElem_ofFn]
    exact rowVertex_adj i
  initiates := by
    rw [List.head?_eq_getElem?]
    simp [show 0 < 2*m by omega, rowVertex]
  terminates := by
    rw [List.getLast?_eq_getElem?]
    have hn : 2*m-1 < 2*m := by omega
    have hp : (2*m-1) % 2 ≠ 0 := by omega
    have hq : (2*m-1) / 2 = m-1 := by omega
    simp only [List.length_ofFn, List.getElem?_ofFn, dite_eq_left hn]
    simp only [rowVertex, hp, ite_false, hq]
    norm_num [Nat.cast_sub (by omega : 1 ≤ m)]
  in_strip := by
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    simp [rowVertex, up, down]
    split_ifs <;> simp

theorem rowZigzag_length (m : ℕ) (hm : 0 < m) : (rowZigzag m hm).length = 2*m := by
  simp [Bridge.length, rowZigzag]

theorem rowZigzag_irreducible (m : ℕ) (hm : 0 < m) : (rowZigzag m hm).Irreducible := by
  intro r hr hr'
  change r < 1 at hr'
  omega

theorem nonempty_bridgeLength (m : ℕ) (hm : 0 < m) :
    Nonempty {b : Bridge // b.length = 2*m} :=
  ⟨⟨rowZigzag m hm, rowZigzag_length m hm⟩⟩

theorem card_bridgeLength_pos (m : ℕ) (hm : 0 < m) :
    0 < Nat.card {b : Bridge // b.length = 2*m} := by
  let := nonempty_bridgeLength m hm
  exact Nat.card_pos

theorem Bridge.trace_finite (b : Bridge) : b.trace.Finite := by
  exact (Set.toFinite _).union (b.vertices.finite_toSet.image position)

theorem Bridge.endpointDistance_le_diameter (b : Bridge) :
    b.endpointDistance ≤ b.diameter := by
  apply Metric.dist_le_diam_of_mem b.trace_finite.isBounded <;> simp [trace]

def IrreducibleNormalization : Prop := criticalMass Bridge.Irreducible = 1

def lengthLaplaceReward (u : ℝ) : ℝ≥0∞ := by
  classical
  exact ∑' b : Bridge, if b.Irreducible then
    weight b * ENNReal.ofReal (1 - Real.exp (-u * (b.length : ℝ))) else 0

def ActualLengthTailBound : Prop :=
  ∃ C n₀ : ℝ, 0 < C ∧ 0 < n₀ ∧ ∀ n : ℝ, n₀ ≤ n →
    criticalMass (fun b => b.Irreducible ∧ n < (b.length : ℝ)) ≤
      ENNReal.ofReal (C * n ^ (-(9/16 : ℝ)))

def ActualLengthLaplaceLower : Prop :=
  ∃ c u₀ : ℝ, 0 < c ∧ 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ →
    ENNReal.ofReal (c * u ^ (9/16 : ℝ)) ≤ lengthLaplaceReward u

def ActualLengthLaplaceUpper : Prop :=
  ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ →
    lengthLaplaceReward u ≤ ENNReal.ofReal (C * u ^ (9/16 : ℝ))

end HoneycombActual

end

end OAI
