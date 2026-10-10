import Mathlib
import OAI.Probability.LatticeSurface.Geometry.TriangularCover

namespace OAI

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

def latticeDist (x y : Vertex) : ℝ :=
  max (max |(x.1 : ℝ) - y.1| |(x.2 : ℝ) - y.2|)
    |((x.1 : ℝ) - y.1) + ((x.2 : ℝ) - y.2)|

def box (L : ℕ) : Finset Vertex :=
  (Finset.Icc 0 (L : ℤ)) ×ˢ (Finset.Icc 0 (L : ℤ))

def interior (L : ℕ) : Finset Vertex :=
  (Finset.Icc 1 ((L : ℤ) - 1)) ×ˢ (Finset.Icc 1 ((L : ℤ) - 1))

abbrev Filling (L : ℕ) := {x : Vertex // x ∈ interior L} → ℝ

noncomputable def filledHeight (L : ℕ) (s : Vertex → ℝ) (a : Filling L)
    (x : Vertex) : ℝ :=
  if hx : x ∈ interior L then a ⟨x, hx⟩ else s x

def fillingPolytope (L : ℕ) (s : Vertex → ℝ) : Set (Filling L) :=
  {a | ∀ x ∈ box L, ∀ y ∈ box L, Adj x y →
    |filledHeight L s a x - filledHeight L s a y| ≤ 1}

noncomputable def fillingVolume (L : ℕ) (s : Vertex → ℝ) : ℝ≥0∞ :=
  volume (fillingPolytope L s)

noncomputable def logFillingVolume (L : ℕ) (s : Vertex → ℝ) : WithBot ℝ :=
  if fillingVolume L s = 0 then ⊥ else
    (Real.log (fillingVolume L s).toReal : ℝ)

noncomputable def positiveLogVolume (L : ℕ) (s : Vertex → ℝ) : ℝ :=
  Real.log (fillingVolume L s).toReal

def faceCenter (L : ℕ) (side : Fin 4) : Vertex :=
  match side.val with
  | 0 => (0, (L / 2 : ℕ))
  | 1 => ((L : ℤ), (L / 2 : ℕ))
  | 2 => ((L / 2 : ℕ), 0)
  | _ => ((L / 2 : ℕ), (L : ℤ))

def compressedNeighbor (L : ℕ) (side : Fin 4) : Vertex :=
  match side.val with
  | 0 => (0, (L / 2 : ℕ) + 1)
  | 1 => ((L : ℤ), (L / 2 : ℕ) - 1)
  | 2 => ((L / 2 : ℕ) + 1, 0)
  | _ => ((L / 2 : ℕ) - 1, (L : ℤ))

def ConvexGood (L k₀ : ℕ) (δ δ₀ s₀ : ℝ) (h : Vertex → ℝ) : Prop :=
  (∀ x ∈ box L, ∀ y ∈ box L, Adj x y → |h x - h y| ≤ 1 - δ) ∧
  (∀ x ∈ box L, ∀ y ∈ box L, (k₀ : ℝ) ≤ latticeDist x y →
    |h x - h y| ≤ (1 - δ₀) * latticeDist x y) ∧
  (∀ side, s₀ ≤ |h (compressedNeighbor L side) - h (faceCenter L side)|)

lemma adj_symm {x y : Vertex} (h : Adj x y) : Adj y x := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  simp only [Adj, Prod.mk.injEq] at h ⊢
  omega

lemma adj_ne {x y : Vertex} (h : Adj x y) : x ≠ y := by
  intro hxy
  subst y
  rcases x with ⟨a,b⟩
  simp only [Adj, Prod.mk.injEq] at h
  omega

def latticeGraph : SimpleGraph Vertex where
  Adj := Adj
  symm := ⟨fun _ _ => adj_symm⟩
  loopless := ⟨fun _ h => adj_ne h rfl⟩

abbrev BoxVertex (L : ℕ) := {x : Vertex // x ∈ box L}

def boxGraph (L : ℕ) : SimpleGraph (BoxVertex L) := latticeGraph.induce (↑(box L))

@[simp] lemma boxGraph_adj {L : ℕ} (x y : BoxVertex L) :
    (boxGraph L).Adj x y ↔ Adj x.val y.val := Iff.rfl

@[simp] lemma mem_box {L : ℕ} {x : Vertex} :
    x ∈ box L ↔ (0 ≤ x.1 ∧ x.1 ≤ (L : ℤ)) ∧ (0 ≤ x.2 ∧ x.2 ≤ (L : ℤ)) := by
  simp [box]

instance box_nonempty (L : ℕ) : Nonempty (BoxVertex L) :=
  ⟨⟨(0,0), by simp⟩⟩

def intDist (x y : Vertex) : ℤ :=
  max (max |x.1-y.1| |x.2-y.2|) |(x.1-y.1)+(x.2-y.2)|

lemma intDist_nonneg (x y : Vertex) : 0 ≤ intDist x y :=
  (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))

lemma intDist_eq_zero_iff (x y : Vertex) : intDist x y = 0 ↔ x = y := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  simp only [intDist, Prod.mk.injEq, abs_eq_max_neg]
  omega

lemma intDist_cast (x y : Vertex) : (intDist x y : ℝ) = latticeDist x y := by
  simp [intDist, latticeDist, max_assoc]

lemma geodesic_step {x y : Vertex} (hne : x ≠ y) :
    ∃ z : Vertex, Adj x z ∧
      (min x.1 y.1 ≤ z.1 ∧ z.1 ≤ max x.1 y.1) ∧
      (min x.2 y.2 ≤ z.2 ∧ z.2 ≤ max x.2 y.2) ∧
      intDist z y + 1 = intDist x y := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  change (a,b) ≠ (c,d) at hne
  rcases lt_trichotomy a c with hac | hac | hac
  · by_cases hdb : d < b
    · refine ⟨(a+1,b-1), ?_, ?_, ?_, ?_⟩
      · simp [Adj]
      · dsimp; omega
      · dsimp; omega
      · simp only [intDist, abs_eq_max_neg]; omega
    · refine ⟨(a+1,b), ?_, ?_, ?_, ?_⟩
      · simp [Adj]
      · dsimp; omega
      · dsimp; omega
      · simp only [intDist, abs_eq_max_neg]; omega
  · subst c
    rcases lt_trichotomy b d with hbd | hbd | hbd
    · refine ⟨(a,b+1), ?_, ?_, ?_, ?_⟩
      · simp [Adj]
      · dsimp; omega
      · dsimp; omega
      · simp only [intDist, abs_eq_max_neg]; omega
    · exact False.elim (hne (by simp [hbd]))
    · refine ⟨(a,b-1), ?_, ?_, ?_, ?_⟩
      · simp [Adj]
      · dsimp; omega
      · dsimp; omega
      · simp only [intDist, abs_eq_max_neg]; omega
  · by_cases hbd : b < d
    · refine ⟨(a-1,b+1), ?_, ?_, ?_, ?_⟩
      · simp [Adj]
      · dsimp; omega
      · dsimp; omega
      · simp only [intDist, abs_eq_max_neg]; omega
    · refine ⟨(a-1,b), ?_, ?_, ?_, ?_⟩
      · simp [Adj]
      · dsimp; omega
      · dsimp; omega
      · simp only [intDist, abs_eq_max_neg]; omega

lemma box_geodesic (L : ℕ) (x y : BoxVertex L) :
    ∃ p : (boxGraph L).Walk x y, (p.length : ℤ) = intDist x.val y.val := by
  suffices ∀ n (x y : BoxVertex L), (intDist x.val y.val).toNat = n →
      ∃ p : (boxGraph L).Walk x y, (p.length : ℤ) = intDist x.val y.val from
    this _ x y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn
    by_cases hxy : x = y
    · subst y
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      simp [intDist]
    · have hne : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
      obtain ⟨z,hxz,hz1,hz2,hd⟩ := geodesic_step hne
      have hz : z ∈ box L := by
        have hxb := mem_box.mp x.property
        have hyb := mem_box.mp y.property
        apply mem_box.mpr
        constructor <;> constructor <;> omega
      let z' : BoxVertex L := ⟨z,hz⟩
      have hlt : (intDist z y.val).toNat < n := by
        have := intDist_nonneg z y.val
        have := intDist_nonneg x.val y.val
        omega
      obtain ⟨p,hp⟩ := ih _ hlt z' y rfl
      refine ⟨SimpleGraph.Walk.cons (show (boxGraph L).Adj x z' from hxz) p, ?_⟩
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      change (p.length : ℤ) + 1 = _
      rw [hp]
      exact hd

lemma box_connected (L : ℕ) : (boxGraph L).Connected := by
  constructor
  intro x y
  obtain ⟨p,_⟩ := box_geodesic L x y
  exact ⟨p⟩

lemma latticeDist_triangle (x y z : Vertex) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  apply max_le
  · apply max_le
    · exact (abs_sub_le (x.1 : ℝ) y.1 z.1).trans
        (add_le_add ((le_max_left _ _).trans (le_max_left _ _))
          ((le_max_left _ _).trans (le_max_left _ _)))
    · exact (abs_sub_le (x.2 : ℝ) y.2 z.2).trans
        (add_le_add ((le_max_right _ _).trans (le_max_left _ _))
          ((le_max_right _ _).trans (le_max_left _ _)))
  · calc
      |((x.1 : ℝ) - z.1) + ((x.2 : ℝ) - z.2)| =
          |(((x.1 : ℝ)-y.1)+((x.2 : ℝ)-y.2)) +
            (((y.1 : ℝ)-z.1)+((y.2 : ℝ)-z.2))| := by congr 1; ring
      _ ≤ |((x.1 : ℝ)-y.1)+((x.2 : ℝ)-y.2)| +
          |((y.1 : ℝ)-z.1)+((y.2 : ℝ)-z.2)| := abs_add_le _ _
      _ ≤ _ := add_le_add (le_max_right _ _) (le_max_right _ _)

lemma intDist_adj {x y : Vertex} (hxy : Adj x y) : intDist x y = 1 := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  simp only [Adj, Prod.mk.injEq] at hxy
  simp only [intDist, abs_eq_max_neg]
  omega

lemma latticeDist_adj {x y : Vertex} (hxy : Adj x y) : latticeDist x y = 1 := by
  rw [←intDist_cast, intDist_adj hxy]
  norm_num

lemma latticeDist_walk_le {L : ℕ} {x y : BoxVertex L} (p : (boxGraph L).Walk x y) :
    latticeDist x.val y.val ≤ (p.length : ℝ) := by
  induction p with
  | nil => simp [latticeDist]
  | @cons x y z hxy p ih =>
    calc
      latticeDist x.val z.val ≤ latticeDist x.val y.val + latticeDist y.val z.val :=
        latticeDist_triangle _ _ _
      _ ≤ 1 + (p.length : ℝ) := add_le_add (le_of_eq (latticeDist_adj hxy)) ih
      _ = ((SimpleGraph.Walk.cons hxy p).length : ℝ) := by simp; ring

lemma box_dist (L : ℕ) (x y : BoxVertex L) :
    ((boxGraph L).dist x y : ℝ) = latticeDist x.val y.val := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := box_geodesic L x y
    have hpr : (p.length : ℝ) = latticeDist x.val y.val := by
      rw [←intDist_cast]
      exact_mod_cast hp
    rw [←hpr]
    exact_mod_cast (boxGraph L).dist_le p
  · obtain ⟨p,hp⟩ := (box_connected L).exists_walk_length_eq_dist x y
    simpa only [hp] using latticeDist_walk_le p

lemma scaled_edge_bound_walk {L : ℕ} {h : Vertex → ℝ} {c : ℝ}
    (hh : ∀ x ∈ box L, ∀ y ∈ box L, Adj x y → |h x-h y| ≤ c)
    {x y : BoxVertex L} (p : (boxGraph L).Walk x y) :
    |h x.val-h y.val| ≤ c * (p.length : ℝ) := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
    calc
      |h x.val-h z.val| ≤ |h x.val-h y.val|+|h y.val-h z.val| := abs_sub_le _ _ _
      _ ≤ c + c * (p.length : ℝ) :=
        add_le_add (hh _ x.property _ y.property hxy) ih
      _ = c*((SimpleGraph.Walk.cons hxy p).length : ℝ) := by simp; ring

lemma near_global_bound {L : ℕ} {h : Vertex → ℝ} {c : ℝ}
    (hh : ∀ x ∈ box L, ∀ y ∈ box L, Adj x y → |h x-h y| ≤ c)
    {x y : Vertex} (hx : x ∈ box L) (hy : y ∈ box L) :
    |h x-h y| ≤ c*latticeDist x y := by
  obtain ⟨p,hp⟩ := box_geodesic L ⟨x,hx⟩ ⟨y,hy⟩
  have hpr : (p.length : ℝ) = latticeDist x y := by
    rw [←intDist_cast]
    exact_mod_cast hp
  simpa only [hpr] using scaled_edge_bound_walk hh p

end TriangularLipschitz

end

end OAI
