import OAI.Analysis.SeparableQuotients.Parameters

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open CoherentClosures PathCoding
open scoped ENNReal Classical
abbrev Γ := OmegaOne.{0}
abbrev Array := Γ →₀ ℚ

inductive Family where
  | pure : ℕ → Family
  | mixed : Family
  deriving DecidableEq

def Family.s : Family → ℕ
  | .pure k => k+2
  | .mixed => 2

lemma Family.s_ge_two (f : Family) : 2 ≤ f.s := by cases f <;> simp [Family.s]

def Family.q (f : Family) : ℝ := Parameters.q f.s

def Family.L (f : Family) (j : ℕ) : ℕ := Parameters.L f.s (j-1)
def Family.m (f : Family) (j : ℕ) : ℕ := Parameters.m f.s (j-1)

lemma Family.m_pos (f : Family) (j : ℕ) : 0 < f.m j := Parameters.m_pos _ _

/-- Succession refers to the full supports, in both orders in mixed mode. -/
def Successive (f : Family) (x y : Array) : Prop :=
  ∀ a ∈ x.support, ∀ b ∈ y.support,
    a < b ∧ (f = .mixed → Colors.color a < Colors.color b)

lemma Successive.disjoint {f : Family} {x y : Array} (h : Successive f x y) :
    Disjoint x.support y.support := by
  apply Finset.disjoint_left.mpr
  intro a hx hy
  exact (lt_irrefl a) (h a hx a hy).1

structure Crop where
  ordinal : Set Γ
  ordinal_convex : Set.OrdConnected ordinal
  colors : Set ℕ
  colors_convex : Set.OrdConnected colors

def Crop.set (A : Crop) : Family → Set Γ
  | .pure _ => A.ordinal
  | .mixed => A.ordinal ∩ Colors.color ⁻¹' A.colors

def restrict (A : Set Γ) (x : Array) : Array := x.filter (· ∈ A)

@[simp] lemma restrict_apply (A : Set Γ) (x : Array) (a : Γ) :
    restrict A x a = if a ∈ A then x a else 0 := Finsupp.filter_apply _ _ _

/-- A specified Type I expression. Child norming membership is imposed at its
construction stage, outside this data structure. -/
structure TypeI (f : Family) where
  weight : ℕ
  weight_pos : 1 ≤ weight
  length : ℕ
  length_pos : 1 ≤ length
  length_le : length ≤ f.L weight
  child : Fin length → Array
  child_nonzero : ∀ h, child h ≠ 0
  successive : ∀ h i, h < i → Successive f (child h) (child i)

def TypeI.value {f : Family} (e : TypeI f) : Array :=
  (1 / (f.m e.weight : ℚ)) • ∑ h, e.child h

/-- Exactly the finite prefix conditions, with unused raw entries ignored.
Padding raw data beyond length imposes no mathematical restriction. -/
structure PrefixValid (P : RawPath) (length : ℕ) : Prop where
  successive : ∀ i j, i < j → j < length → ∀ a ∈ (P.piece i).support,
    ∀ b ∈ (P.piece j).support, a < b
  metadata_strict : ∀ i j, i < j → j < length → P.metadata i < P.metadata j
  metadata_pos : ∀ i, i < length → 1 ≤ P.metadata i
  weight_pos : ∀ i, i < length → 1 ≤ P.weight i
  weight_le_metadata : ∀ i, i < length → P.weight i ≤ P.metadata i
  rho_bound : ∀ n, n < length → ∀ a b, a ∈ P.support n → b ∈ P.support n → a ≤ b →
    rho a b ≤ P.metadata n
  rule : ∀ n, n+1 < length → P.weight (n+1) = sigma (P.code n)

lemma PrefixValid.weight_strict {P : RawPath} {len : ℕ} (h : PrefixValid P len) :
    StrictMono (fun i : Fin len => P.weight i) := by
  cases len with
  | zero => intro i; exact i.elim0
  | succ len =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    change P.weight i < P.weight ((i : ℕ)+1)
    rw [h.rule i (by omega)]
    exact (h.weight_le_metadata i (by omega)).trans_lt
      ((P.metadata_le_codeBound i).trans_lt (codeBound_lt_sigma _))

structure FinitePath (f : Family) where
  raw : RawPath
  length : ℕ
  length_pos : 1 ≤ length
  valid : PrefixValid raw length
  piece : Fin length → TypeI f
  value_eq : ∀ i, (piece i).value = raw.piece i
  weight_eq : ∀ i, (piece i).weight = raw.weight i
  mixed_successive : ∀ (i j : Fin length), i < j →
    Successive f (raw.piece i) (raw.piece j)

def FinitePath.value {f : Family} (P : FinitePath f) : Array := ∑ i : Fin P.length, P.raw.piece i

def FinitePath.active {f : Family} (P : FinitePath f) (A : Crop) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin P.length => restrict (A.set f) (P.raw.piece i) ≠ 0)).image
    (fun i : Fin P.length => P.raw.weight i)

structure TypeII (f : Family) where
  length : ℕ
  path : Fin length → FinitePath f
  crop : Fin length → Crop
  coefficient : Fin length → ℚ
  bound : ∑ b, |(coefficient b : ℝ)| ^ f.q ≤ 1
  disjoint_active : Pairwise (fun b c =>
    Disjoint ((path b).active (crop b)) ((path c).active (crop c)))

def TypeII.value {f : Family} (e : TypeII f) : Array :=
  ∑ b, e.coefficient b • restrict ((e.crop b).set f) (e.path b).value

/-- Each stage retains previous stages and adjoins expressions whose Type I children belong to previous stages, with uncropped path data. -/
def stage (base : Set Array) (f : Family) : ℕ → Set Array
  | 0 => base
  | n+1 => stage base f n ∪
      {x | ∃ e : TypeI f, e.value = x ∧ ∀ h, e.child h ∈ stage base f n} ∪
      {x | ∃ e : TypeII f, e.value = x ∧
        ∀ b i h, ((e.path b).piece i).child h ∈ stage base f n}

def pureBase (k : ℕ) : Set Array :=
  {x | x = 0 ∨ ∃ a, Colors.color a = k ∧
    (x = Finsupp.single a 1 ∨ x = Finsupp.single a (-1))}

def Pure (k : ℕ) : Set Array := ⋃ n, stage (pureBase k) (.pure k) n

def Full : Set Array := ⋃ n, stage (⋃ k, Pure k) .mixed n

lemma stage_mono (base : Set Array) (f : Family) : Monotone (stage base f) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  exact Or.inl (Or.inl hx)

lemma pure_subset_full (k : ℕ) : Pure k ⊆ Full := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨k, hx⟩⟩

lemma coordinate_mem (a : Γ) : Finsupp.single a 1 ∈ Full := by
  apply pure_subset_full (Colors.color a)
  exact Set.mem_iUnion.mpr ⟨0, Or.inr ⟨a, rfl, Or.inl rfl⟩⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open CoherentClosures PathCoding
open scoped Classical

lemma successive_coefficient_unique {f : Family} {n : ℕ} (v : Fin n → Array)
    (h : ∀ i j, i < j → Successive f (v i) (v j)) {a : Γ} {i j : Fin n}
    (hi : v i a ≠ 0) (hj : v j a ≠ 0) : i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact Finset.disjoint_left.mp (h i j hij).disjoint
      (Finsupp.mem_support_iff.mpr hi) (Finsupp.mem_support_iff.mpr hj)
  · exact Finset.disjoint_left.mp (h j i hij).disjoint
      (Finsupp.mem_support_iff.mpr hj) (Finsupp.mem_support_iff.mpr hi)

lemma TypeI.coefficient_bound {f : Family} (e : TypeI f)
    (h : ∀ i a, |(e.child i a : ℝ)| ≤ 1) (a : Γ) :
    |(e.value a : ℝ)| ≤ 1 / (f.m e.weight : ℝ) := by
  classical
  have hm : 0 < (f.m e.weight : ℝ) := by exact_mod_cast f.m_pos _
  have hsum : |∑ i, (e.child i a : ℝ)| ≤ 1 := by
    by_cases hex : ∃ i, e.child i a ≠ 0
    · obtain ⟨i, hi⟩ := hex
      rw [Finset.sum_eq_single i]
      · exact h i a
      · intro j _ hji
        have hz : e.child j a = 0 := by
          by_contra hj
          exact hji (successive_coefficient_unique e.child e.successive hj hi)
        simp [hz]
      · simp
    · push Not at hex
      simp [hex]
  have heq : (e.value a : ℝ) = (1 / (f.m e.weight : ℝ)) * ∑ i, (e.child i a : ℝ) := by
    simp [TypeI.value, Finsupp.smul_apply, smul_eq_mul]
  rw [heq, abs_mul, abs_of_pos (one_div_pos.mpr hm)]
  simpa using mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hm))

/-- A coordinate meets at most one original path piece. -/
def FinitePath.hitIndex {f : Family} (P : FinitePath f) (a : Γ) : Fin P.length :=
  if h : ∃ i : Fin P.length, P.raw.piece i a ≠ 0 then h.choose
  else ⟨0, P.length_pos⟩

lemma FinitePath.value_at_hit {f : Family} (P : FinitePath f) (a : Γ) :
    P.value a = P.raw.piece (P.hitIndex a) a := by
  classical
  by_cases hex : ∃ i : Fin P.length, P.raw.piece i a ≠ 0
  · have hi : P.raw.piece (P.hitIndex a) a ≠ 0 := by
      simpa only [FinitePath.hitIndex, dite_eq_left hex] using hex.choose_spec
    change (∑ i : Fin P.length, P.raw.piece i) a = _
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single (P.hitIndex a)]
    · intro j _ hj
      by_contra hne
      exact hj (successive_coefficient_unique (fun i : Fin P.length => P.raw.piece i)
        P.mixed_successive hne hi)
    · simp
  · push Not at hex
    simp [FinitePath.value, hex]

lemma FinitePath.hit_weight_active {f : Family} (P : FinitePath f) (A : Crop) (a : Γ)
    (ha : restrict (A.set f) P.value a ≠ 0) :
    P.raw.weight (P.hitIndex a) ∈ P.active A := by
  classical
  have hAc : a ∈ A.set f := by
    by_contra hn
    simp [hn] at ha
  have hv : P.raw.piece (P.hitIndex a) a ≠ 0 := by
    simpa [hAc, P.value_at_hit] using ha
  apply Finset.mem_image.mpr
  refine ⟨P.hitIndex a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  intro hz
  have hz' := congrArg (fun x : Array => x a) hz
  exact hv (by simpa [hAc] using hz')

end SeparableQuotient.Norming

end

end OAI
