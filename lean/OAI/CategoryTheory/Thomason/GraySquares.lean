import Mathlib
import OAI.CategoryTheory.Thomason.DimensionOne

namespace OAI

/-! Gray Squares. -/

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayComposition
open DirectedComplex DirectedComplex.Table GlobeComplex

abbrev G (n : ℕ) : OmegaCategory.{u} := (complex n).nu
abbrev T (n : ℕ) : OmegaCategory.{u} := (complex n).cylinder.nu
abbrev face (n k : ℕ) (b : Bool) : G.{u} k ⟶ G.{u} n := (faceMap n k b).nu
abbrev tensorFace (n k : ℕ) (b : Bool) : T.{u} k ⟶ T.{u} n := (faceMap n k b).cylinder.nu
abbrev endpoint (n : ℕ) (b : Bool) : G.{u} n ⟶ T.{u} n := ((complex n).cylinderEndpoint b).nu
abbrev projection (n : ℕ) : T.{u} n ⟶ G.{u} n := (complex n).cylinderProjection.nu

lemma endpoint_natural (n k : ℕ) (a b : Bool) :
    endpoint.{u} k b ≫ tensorFace.{u} n k a = face.{u} n k a ≫ endpoint.{u} n b := by
  exact congrArg Hom.nu ((faceMap n k a).cylinder_endpoint b)
lemma projection_natural (n k : ℕ) (a : Bool) :
    tensorFace.{u} n k a ≫ projection.{u} n = projection.{u} k ≫ face.{u} n k a := by
  exact congrArg Hom.nu ((faceMap n k a).cylinder_projection)

abbrev P (n k : ℕ) : OmegaCategory.{u} := pushout (face.{u} n k true) (face.{u} n k false)

abbrev Q (n k : ℕ) : OmegaCategory.{u} := pushout (tensorFace.{u} n k true) (tensorFace.{u} n k false)
abbrev i₀ (n k : ℕ) : G.{u} n ⟶ P.{u} n k := pushout.inl _ _
abbrev i₁ (n k : ℕ) : G.{u} n ⟶ P.{u} n k := pushout.inr _ _
abbrev j₀ (n k : ℕ) : T.{u} n ⟶ Q.{u} n k := pushout.inl _ _
abbrev j₁ (n k : ℕ) : T.{u} n ⟶ Q.{u} n k := pushout.inr _ _

def cutEndpoint (n k : ℕ) (b : Bool) : P.{u} n k ⟶ Q.{u} n k :=
  pushout.desc (endpoint.{u} n b ≫ j₀.{u} n k) (endpoint.{u} n b ≫ j₁.{u} n k) (by
    rw [← Category.assoc, ← endpoint_natural.{u}, Category.assoc,
      ← Category.assoc (face.{u} n k false), ← endpoint_natural.{u}, Category.assoc,
      pushout.condition])
def cutProjection (n k : ℕ) : Q.{u} n k ⟶ P.{u} n k :=
  pushout.desc (projection.{u} n ≫ i₀.{u} n k) (projection.{u} n ≫ i₁.{u} n k) (by
    rw [← Category.assoc, projection_natural.{u}, Category.assoc,
      ← Category.assoc (tensorFace.{u} n k false), projection_natural.{u}, Category.assoc,
      pushout.condition])

lemma face_top (n k : ℕ) (b : Bool) :
    (face.{u} n k b).map (topTable k) = truncate k b (topTable n) := by
  change (faceMap.{u} n k b).nu.map (topTable k) = _
  erw [faceMap_nu, lift_top]

lemma top_composable (n k : ℕ) :
    (P.{u} n k).target k ((i₀.{u} n k).map (topTable n)) =
      (P.{u} n k).source k ((i₁.{u} n k).map (topTable n)) := by
  erw [← (i₀.{u} n k).map_target, ← (i₁.{u} n k).map_source]
  have h := congrArg (fun f : G.{u} k ⟶ P.{u} n k => f.map (topTable k))
    (pushout.condition (f := face.{u} n k true) (g := face.{u} n k false))
  change (i₀.{u} n k).map ((face.{u} n k true).map (topTable k)) =
    (i₁.{u} n k).map ((face.{u} n k false).map (topTable k)) at h
  rw [face_top.{u}, face_top.{u}] at h
  exact h

def compositeCell (n k : ℕ) : (P.{u} n k).Cell :=
  (P.{u} n k).comp k ((i₀.{u} n k).map (topTable n)) ((i₁.{u} n k).map (topTable n))
    (top_composable.{u} n k)
lemma compositeCell_bounded (n k : ℕ) (hkn : k < n) :
    (P.{u} n k).source n (compositeCell.{u} n k) = compositeCell.{u} n k := by
  unfold compositeCell
  rw [(P.{u} n k).source_comp_gt n k hkn _ _ _ ((P.{u} n k).source_composable hkn (top_composable.{u} n k))]
  apply (P.{u} n k).comp_congr_cells
  · erw [← (i₀.{u} n k).map_source]
    change (i₀.{u} n k).map (truncate n false (topTable n)) = _
    rw [topTable_bounded]
  · erw [← (i₁.{u} n k).map_source]
    change (i₁.{u} n k).map (truncate n false (topTable n)) = _
    rw [topTable_bounded]

def composition (n k : ℕ) (hkn : k < n) : G.{u} n ⟶ P.{u} n k :=
  GlobeComplex.lift (compositeCell.{u} n k) (compositeCell_bounded.{u} n k hkn)

def CooperationExists (n k : ℕ) (hkn : k < n) : Prop :=
  ∃ γ : T.{u} n ⟶ Q.{u} n k,
    (∀ b, endpoint.{u} n b ≫ γ = composition.{u} n k hkn ≫ cutEndpoint.{u} n k b) ∧
    γ ≫ cutProjection.{u} n k = projection.{u} n ≫ composition.{u} n k hkn

def FirstMixedCooperation : Prop := CooperationExists.{u} 2 0 (by decide)
end Thomason.GrayComposition

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayTwo
open DirectedComplex DirectedComplex.Table GlobeComplex

@[ext] structure Coordinates where
  vertex : Bool → Fin 4 → ℤ
  edge : Bool → Fin 6 → ℤ
  face : Bool → Fin 4 → ℤ
  volume : ℤ

namespace Coordinates

def IsValid (x : Coordinates) : Prop :=
  (∀ b i, 0 ≤ x.vertex b i) ∧
  (∀ b i, 0 ≤ x.edge b i) ∧
  (∀ b i, 0 ≤ x.face b i) ∧
  0 ≤ x.volume ∧
  (∀ b, x.vertex b 0 + x.vertex b 1 + x.vertex b 2 + x.vertex b 3 = 1) ∧
  (∀ b,
    x.vertex true 0 - x.vertex false 0 = -x.edge b 0 - x.edge b 1 - x.edge b 4 ∧
    x.vertex true 1 - x.vertex false 1 = x.edge b 0 + x.edge b 1 - x.edge b 5 ∧
    x.vertex true 2 - x.vertex false 2 = -x.edge b 2 - x.edge b 3 + x.edge b 4 ∧
    x.vertex true 3 - x.vertex false 3 = x.edge b 2 + x.edge b 3 + x.edge b 5) ∧
  (∀ b,
    x.edge true 0 - x.edge false 0 = -x.face b 0 + x.face b 2 ∧
    x.edge true 1 - x.edge false 1 = x.face b 0 + x.face b 3 ∧
    x.edge true 2 - x.edge false 2 = -x.face b 1 - x.face b 2 ∧
    x.edge true 3 - x.edge false 3 = x.face b 1 - x.face b 3 ∧
    x.edge true 4 - x.edge false 4 = -x.face b 2 - x.face b 3 ∧
    x.edge true 5 - x.edge false 5 = x.face b 2 + x.face b 3) ∧
  (x.face true 0 - x.face false 0 = -x.volume ∧
    x.face true 1 - x.face false 1 = x.volume ∧
    x.face true 2 - x.face false 2 = -x.volume ∧
    x.face true 3 - x.face false 3 = x.volume)

end Coordinates

abbrev K : DirectedComplex.{u} := (complex 2).cylinder

def coordinates (t : Table K.{u}) : Coordinates where
  vertex b := ![(t.row 0 b).1.val ⟨false⟩, (t.row 0 b).1.val ⟨true⟩,
    (t.row 0 b).2.val ⟨false⟩, (t.row 0 b).2.val ⟨true⟩]
  edge b := ![(t.row 1 b).1.val ⟨false⟩, (t.row 1 b).1.val ⟨true⟩,
    (t.row 1 b).2.1.val ⟨false⟩, (t.row 1 b).2.1.val ⟨true⟩,
    (t.row 1 b).2.2.val ⟨false⟩, (t.row 1 b).2.2.val ⟨true⟩]
  face b := ![(t.row 2 b).1.val ⟨false⟩, (t.row 2 b).2.1.val ⟨false⟩,
    (t.row 2 b).2.2.val ⟨false⟩, (t.row 2 b).2.2.val ⟨true⟩]
  volume := (t.row 3 false).2.2.val ⟨false⟩

lemma row_above (t : Table K.{u}) (p : ℕ) (hp : 3 < p) (b : Bool) :
    t.row p b = 0 := by
  cases p with
  | zero => omega
  | succ p =>
    apply Prod.ext
    · exact chain_zero (by omega) _
    · apply Prod.ext
      · exact chain_zero (by omega) _
      · exact chain_zero (by omega) _

lemma bounded (t : Table K.{u}) : truncate 3 false t = t :=
  dimension_of_rows_above_zero t (row_above t)

lemma coordinates_valid (t : Table K.{u}) : (coordinates t).IsValid := by
  have pv (b : Bool) := t.positive 0 b
  have pe (b : Bool) := t.positive 1 b
  have pf (b : Bool) := t.positive 2 b
  have ph := t.positive 3 false
  refine ⟨?_, ?_, ?_, ph.2.2 false, ?_, ?_, ?_, ?_⟩
  · intro b i
    fin_cases i
    · exact (pv b).1 false
    · exact (pv b).1 true
    · exact (pv b).2 false
    · exact (pv b).2 true
  · intro b i
    fin_cases i
    · exact (pe b).1 false
    · exact (pe b).1 true
    · exact (pe b).2.1 false
    · exact (pe b).2.1 true
    · exact (pe b).2.2 false
    · exact (pe b).2.2 true
  · intro b i
    fin_cases i
    · exact (pf b).1 false
    · exact (pf b).2.1 false
    · exact (pf b).2.2 false
    · exact (pf b).2.2 true
  · intro b
    have h := t.augmentation b
    change ((t.row 0 b).1.val ⟨false⟩ + (t.row 0 b).1.val ⟨true⟩) +
      ((t.row 0 b).2.val ⟨false⟩ + (t.row 0 b).2.val ⟨true⟩) = 1 at h
    dsimp [coordinates]
    omega
  · intro b
    have h₀ := congrArg (fun c : K.Chain 0 => c.1.val ⟨false⟩) (t.boundary 0 b)
    have h₁ := congrArg (fun c : K.Chain 0 => c.1.val ⟨true⟩) (t.boundary 0 b)
    have h₂ := congrArg (fun c : K.Chain 0 => c.2.val ⟨false⟩) (t.boundary 0 b)
    have h₃ := congrArg (fun c : K.Chain 0 => c.2.val ⟨true⟩) (t.boundary 0 b)
    change ((t.row 1 b).1.val ⟨false⟩ + (t.row 1 b).1.val ⟨true⟩) * (-1) -
      (t.row 1 b).2.2.val ⟨false⟩ =
      (t.row 0 true).1.val ⟨false⟩ - (t.row 0 false).1.val ⟨false⟩ at h₀
    change ((t.row 1 b).1.val ⟨false⟩ + (t.row 1 b).1.val ⟨true⟩) * 1 -
      (t.row 1 b).2.2.val ⟨true⟩ =
      (t.row 0 true).1.val ⟨true⟩ - (t.row 0 false).1.val ⟨true⟩ at h₁
    change ((t.row 1 b).2.1.val ⟨false⟩ + (t.row 1 b).2.1.val ⟨true⟩) * (-1) +
      (t.row 1 b).2.2.val ⟨false⟩ =
      (t.row 0 true).2.val ⟨false⟩ - (t.row 0 false).2.val ⟨false⟩ at h₂
    change ((t.row 1 b).2.1.val ⟨false⟩ + (t.row 1 b).2.1.val ⟨true⟩) * 1 +
      (t.row 1 b).2.2.val ⟨true⟩ =
      (t.row 0 true).2.val ⟨true⟩ - (t.row 0 false).2.val ⟨true⟩ at h₃
    dsimp [coordinates]
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  · intro b
    have h₀ := congrArg (fun c : K.Chain 1 => c.1.val ⟨false⟩) (t.boundary 1 b)
    have h₁ := congrArg (fun c : K.Chain 1 => c.1.val ⟨true⟩) (t.boundary 1 b)
    have h₂ := congrArg (fun c : K.Chain 1 => c.2.1.val ⟨false⟩) (t.boundary 1 b)
    have h₃ := congrArg (fun c : K.Chain 1 => c.2.1.val ⟨true⟩) (t.boundary 1 b)
    have h₄ := congrArg (fun c : K.Chain 1 => c.2.2.val ⟨false⟩) (t.boundary 1 b)
    have h₅ := congrArg (fun c : K.Chain 1 => c.2.2.val ⟨true⟩) (t.boundary 1 b)
    change ((t.row 2 b).1.val ⟨false⟩ + (t.row 2 b).1.val ⟨true⟩) * (-1) -
      (-1) * (t.row 2 b).2.2.val ⟨false⟩ =
      (t.row 1 true).1.val ⟨false⟩ - (t.row 1 false).1.val ⟨false⟩ at h₀
    change ((t.row 2 b).1.val ⟨false⟩ + (t.row 2 b).1.val ⟨true⟩) * 1 -
      (-1) * (t.row 2 b).2.2.val ⟨true⟩ =
      (t.row 1 true).1.val ⟨true⟩ - (t.row 1 false).1.val ⟨true⟩ at h₁
    change ((t.row 2 b).2.1.val ⟨false⟩ + (t.row 2 b).2.1.val ⟨true⟩) * (-1) +
      (-1) * (t.row 2 b).2.2.val ⟨false⟩ =
      (t.row 1 true).2.1.val ⟨false⟩ - (t.row 1 false).2.1.val ⟨false⟩ at h₂
    change ((t.row 2 b).2.1.val ⟨false⟩ + (t.row 2 b).2.1.val ⟨true⟩) * 1 +
      (-1) * (t.row 2 b).2.2.val ⟨true⟩ =
      (t.row 1 true).2.1.val ⟨true⟩ - (t.row 1 false).2.1.val ⟨true⟩ at h₃
    change ((t.row 2 b).2.2.val ⟨false⟩ + (t.row 2 b).2.2.val ⟨true⟩) * (-1) =
      (t.row 1 true).2.2.val ⟨false⟩ - (t.row 1 false).2.2.val ⟨false⟩ at h₄
    change ((t.row 2 b).2.2.val ⟨false⟩ + (t.row 2 b).2.2.val ⟨true⟩) * 1 =
      (t.row 1 true).2.2.val ⟨true⟩ - (t.row 1 false).2.2.val ⟨true⟩ at h₅
    have hz₀ := top_target_zero 2 (t.row 2 b).1
    have hz₁ := top_target_zero 2 (t.row 2 b).2.1
    dsimp [coordinates]
    norm_num at h₀ h₁ h₂ h₃ h₄ h₅
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  · have h₀ := congrArg (fun c : K.Chain 2 => c.1.val ⟨false⟩) (t.boundary 2 false)
    have h₁ := congrArg (fun c : K.Chain 2 => c.2.1.val ⟨false⟩) (t.boundary 2 false)
    have h₂ := congrArg (fun c : K.Chain 2 => c.2.2.val ⟨false⟩) (t.boundary 2 false)
    have h₃ := congrArg (fun c : K.Chain 2 => c.2.2.val ⟨true⟩) (t.boundary 2 false)
    change ((t.row 3 false).1.val ⟨false⟩ + (t.row 3 false).1.val ⟨true⟩) * 0 -
      1 * (t.row 3 false).2.2.val ⟨false⟩ =
      (t.row 2 true).1.val ⟨false⟩ - (t.row 2 false).1.val ⟨false⟩ at h₀
    change ((t.row 3 false).2.1.val ⟨false⟩ + (t.row 3 false).2.1.val ⟨true⟩) * 0 +
      1 * (t.row 3 false).2.2.val ⟨false⟩ =
      (t.row 2 true).2.1.val ⟨false⟩ - (t.row 2 false).2.1.val ⟨false⟩ at h₁
    change ((t.row 3 false).2.2.val ⟨false⟩ + (t.row 3 false).2.2.val ⟨true⟩) * (-1) =
      (t.row 2 true).2.2.val ⟨false⟩ - (t.row 2 false).2.2.val ⟨false⟩ at h₂
    change ((t.row 3 false).2.2.val ⟨false⟩ + (t.row 3 false).2.2.val ⟨true⟩) * 1 =
      (t.row 2 true).2.2.val ⟨true⟩ - (t.row 2 false).2.2.val ⟨true⟩ at h₃
    have hz := top_target_zero 2 (t.row 3 false).2.2
    dsimp [coordinates]
    norm_num at h₀ h₁ h₂ h₃
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega

lemma coordinates_injective : Function.Injective (coordinates.{u}) := by
  intro s t h
  have hv (b i) := congrArg (fun x : Coordinates => x.vertex b i) h
  have he (b i) := congrArg (fun x : Coordinates => x.edge b i) h
  have hf (b i) := congrArg (fun x : Coordinates => x.face b i) h
  have hh := congrArg Coordinates.volume h
  ext p b
  rcases p with _ | _ | _ | _ | p
  · apply Prod.ext
    · apply Subtype.ext; funext ⟨a⟩; cases a
      · exact hv b 0
      · exact hv b 1
    · apply Subtype.ext; funext ⟨a⟩; cases a
      · exact hv b 2
      · exact hv b 3
  · apply Prod.ext
    · apply Subtype.ext; funext ⟨a⟩; cases a
      · exact he b 0
      · exact he b 1
    · apply Prod.ext
      · apply Subtype.ext; funext ⟨a⟩; cases a
        · exact he b 2
        · exact he b 3
      · apply Subtype.ext; funext ⟨a⟩; cases a
        · exact he b 4
        · exact he b 5
  · apply Prod.ext
    · apply Subtype.ext; funext ⟨a⟩; cases a
      · exact hf b 0
      · exact (top_target_zero 2 _).trans (top_target_zero 2 _).symm
    · apply Prod.ext
      · apply Subtype.ext; funext ⟨a⟩; cases a
        · exact hf b 1
        · exact (top_target_zero 2 _).trans (top_target_zero 2 _).symm
      · apply Subtype.ext; funext ⟨a⟩; cases a
        · exact hf b 2
        · exact hf b 3
  · have hs : (s.row 3 b).2.2.val ⟨false⟩ = (s.row 3 false).2.2.val ⟨false⟩ := by
      cases b
      · rfl
      · exact congrArg (fun c : K.Chain 3 => c.2.2.val ⟨false⟩) (row_top_fixed s (bounded s)).symm
    have ht : (t.row 3 b).2.2.val ⟨false⟩ = (t.row 3 false).2.2.val ⟨false⟩ := by
      cases b
      · rfl
      · exact congrArg (fun c : K.Chain 3 => c.2.2.val ⟨false⟩) (row_top_fixed t (bounded t)).symm
    apply Prod.ext
    · exact (chain_zero (n := 2) (p := 3) (by decide) _).trans
        (chain_zero (n := 2) (p := 3) (by decide) _).symm
    · apply Prod.ext
      · exact (chain_zero (n := 2) (p := 3) (by decide) _).trans
          (chain_zero (n := 2) (p := 3) (by decide) _).symm
      · apply Subtype.ext; funext ⟨a⟩; cases a
        · exact hs.trans (hh.trans ht.symm)
        · exact (top_target_zero 2 _).trans (top_target_zero 2 _).symm
  · rw [row_above s _ (by omega), row_above t _ (by omega)]

end Thomason.GrayTwo

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayTwo
open DirectedComplex DirectedComplex.Table GlobeComplex

namespace Coordinates

def lower (p : ℕ) (hp : p < 2) (a b : ℤ) : Chain.{u} 2 p :=
  ⟨fun c => if c.down then b else a, by
    rintro c (hc | ⟨hc, _⟩) <;> omega⟩

def top (a : ℤ) : Chain.{u} 2 2 :=
  ⟨fun c => if c.down then 0 else a, by
    rintro c (hc | ⟨_, hc⟩)
    · omega
    · simp [hc]⟩

def row (x : Coordinates) : (p : ℕ) → Bool → K.{u}.Chain p
  | 0, b => (lower 0 (by decide) (x.vertex b 0) (x.vertex b 1),
      lower 0 (by decide) (x.vertex b 2) (x.vertex b 3))
  | 1, b => (lower 1 (by decide) (x.edge b 0) (x.edge b 1),
      lower 1 (by decide) (x.edge b 2) (x.edge b 3),
      lower 0 (by decide) (x.edge b 4) (x.edge b 5))
  | 2, b => (top (x.face b 0), top (x.face b 1),
      lower 1 (by decide) (x.face b 2) (x.face b 3))
  | 3, _ => (0, 0, top x.volume)
  | p + 4, _ => 0

lemma row_above (x : Coordinates) {p : ℕ} (hp : 3 < p) (b : Bool) :
    row.{u} x p b = 0 := by
  rcases p with _ | _ | _ | _ | p <;> first | omega | rfl

lemma row_positive (x : Coordinates) (hx : x.IsValid) (p : ℕ) (b : Bool) :
    row.{u} x p b ∈ K.positive p := by
  rcases hx with ⟨hv, he, hf, hm, _⟩
  rcases p with _ | _ | _ | _ | p
  · refine ⟨?_, ?_⟩ <;> intro c <;> cases c
    · exact hv b 0
    · exact hv b 1
    · exact hv b 2
    · exact hv b 3
  · refine ⟨?_, ?_, ?_⟩ <;> intro c <;> cases c
    · exact he b 0
    · exact he b 1
    · exact he b 2
    · exact he b 3
    · exact he b 4
    · exact he b 5
  · refine ⟨?_, ?_, ?_⟩ <;> intro c <;> cases c
    · exact hf b 0
    · exact le_rfl
    · exact hf b 1
    · exact le_rfl
    · exact hf b 2
    · exact hf b 3
  · refine ⟨(complex.{u} 2).positive 3 |>.zero_mem,
      (complex.{u} 2).positive 3 |>.zero_mem, ?_⟩
    intro c; cases c
    · exact hm
    · exact le_rfl
  · exact (K.positive _).zero_mem

lemma row_boundary (x : Coordinates) (hx : x.IsValid) (p : ℕ) (b : Bool) :
    K.d p (row.{u} x (p+1) b) = row x p true - row x p false := by
  rcases hx with ⟨_, _, _, _, _, hb, hc, hd⟩
  have hb' := hb b
  have hc' := hc b
  rcases p with _ | _ | _ | _ | p
  · apply Prod.ext
    · apply Subtype.ext; funext ⟨a⟩; cases a
      · change (x.edge b 0 + x.edge b 1) * (-1) - x.edge b 4 =
          x.vertex true 0 - x.vertex false 0
        omega
      · change (x.edge b 0 + x.edge b 1) * 1 - x.edge b 5 =
          x.vertex true 1 - x.vertex false 1
        omega
    · apply Subtype.ext; funext ⟨a⟩; cases a
      · change (x.edge b 2 + x.edge b 3) * (-1) + x.edge b 4 =
          x.vertex true 2 - x.vertex false 2
        omega
      · change (x.edge b 2 + x.edge b 3) * 1 + x.edge b 5 =
          x.vertex true 3 - x.vertex false 3
        omega
  · apply Prod.ext
    · apply Subtype.ext; funext ⟨a⟩; cases a
      · change (x.face b 0 + 0) * (-1) - (-1) * x.face b 2 =
          x.edge true 0 - x.edge false 0
        omega
      · change (x.face b 0 + 0) * 1 - (-1) * x.face b 3 =
          x.edge true 1 - x.edge false 1
        omega
    · apply Prod.ext
      · apply Subtype.ext; funext ⟨a⟩; cases a
        · change (x.face b 1 + 0) * (-1) + (-1) * x.face b 2 =
            x.edge true 2 - x.edge false 2
          omega
        · change (x.face b 1 + 0) * 1 + (-1) * x.face b 3 =
            x.edge true 3 - x.edge false 3
          omega
      · apply Subtype.ext; funext ⟨a⟩; cases a
        · change (x.face b 2 + x.face b 3) * (-1) =
            x.edge true 4 - x.edge false 4
          omega
        · change (x.face b 2 + x.face b 3) * 1 =
            x.edge true 5 - x.edge false 5
          omega
  · apply Prod.ext
    · apply Subtype.ext; funext ⟨a⟩; cases a
      · change (0 + 0) * 0 - 1 * x.volume = x.face true 0 - x.face false 0
        omega
      · change (0 + 0) * 0 - 1 * 0 = (0 : ℤ) - 0
        omega
    · apply Prod.ext
      · apply Subtype.ext; funext ⟨a⟩; cases a
        · change (0 + 0) * 0 + 1 * x.volume = x.face true 1 - x.face false 1
          omega
        · change (0 + 0) * 0 + 1 * 0 = (0 : ℤ) - 0
          omega
      · apply Subtype.ext; funext ⟨a⟩; cases a
        · change (x.volume + 0) * (-1) = x.face true 2 - x.face false 2
          omega
        · change (x.volume + 0) * 1 = x.face true 3 - x.face false 3
          omega
  · change K.d 3 0 = row x 3 true - row x 3 false
    rw [map_zero]
    change (0 : K.Chain 3) = (0, 0, top x.volume) - (0, 0, top x.volume)
    exact (sub_self _).symm
  · rw [row_above x (by omega), row_above x (by omega), row_above x (by omega),
      map_zero, sub_self]

def table (x : Coordinates) (hx : x.IsValid) : Table K.{u} where
  row := row x
  positive := row_positive x hx
  boundary := row_boundary x hx
  augmentation b := by
    change (x.vertex b 0 + x.vertex b 1) + (x.vertex b 2 + x.vertex b 3) = 1
    have h := hx.2.2.2.2.1 b
    omega
  bounded := ⟨3, fun p hp b => row_above x hp b⟩

@[simp] lemma coordinates_table (x : Coordinates) (hx : x.IsValid) :
    coordinates (table.{u} x hx) = x := by
  apply Coordinates.ext
  · funext b i; fin_cases i <;> rfl
  · funext b i; fin_cases i <;> rfl
  · funext b i; fin_cases i <;> rfl
  · rfl

end Coordinates

@[simp] lemma table_coordinates (t : Table K.{u}) :
    (coordinates t).table (coordinates_valid t) = t := by
  apply coordinates_injective
  exact Coordinates.coordinates_table _ _

def coordinatesEquiv : Table K.{u} ≃ {x : Coordinates // x.IsValid} where
  toFun t := ⟨coordinates t, coordinates_valid t⟩
  invFun x := x.val.table x.property
  left_inv := table_coordinates
  right_inv x := Subtype.ext (Coordinates.coordinates_table.{u} x.val x.property)

end Thomason.GrayTwo

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayTwo
open DirectedComplex DirectedComplex.Table GlobeComplex

def code (i : Fin 23) : Coordinates :=
  match i.val with
  | 0 =>
    { vertex _b := ![1, 0, 0, 0]
      edge _b := ![0, 0, 0, 0, 0, 0]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 1 =>
    { vertex b := (if b then ![0, 1, 0, 0] else ![1, 0, 0, 0])
      edge _b := ![0, 1, 0, 0, 0, 0]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 2 =>
    { vertex b := (if b then ![0, 1, 0, 0] else ![1, 0, 0, 0])
      edge b := (if b then ![0, 1, 0, 0, 0, 0] else ![1, 0, 0, 0, 0, 0])
      face _b := ![1, 0, 0, 0]
      volume := 0 }
  | 3 =>
    { vertex b := (if b then ![0, 1, 0, 0] else ![1, 0, 0, 0])
      edge _b := ![1, 0, 0, 0, 0, 0]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 4 =>
    { vertex b := (if b then ![0, 0, 1, 0] else ![1, 0, 0, 0])
      edge _b := ![0, 0, 0, 0, 1, 0]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 5 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![1, 0, 0, 0])
      edge _b := ![0, 0, 0, 1, 1, 0]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 6 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![1, 0, 0, 0])
      edge b := (if b then ![0, 1, 0, 0, 0, 1] else ![0, 0, 0, 1, 1, 0])
      face _b := ![0, 0, 0, 1]
      volume := 0 }
  | 7 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![1, 0, 0, 0])
      edge b := (if b then ![0, 0, 0, 1, 1, 0] else ![0, 0, 1, 0, 1, 0])
      face _b := ![0, 1, 0, 0]
      volume := 0 }
  | 8 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![1, 0, 0, 0])
      edge _b := ![0, 0, 1, 0, 1, 0]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 9 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![1, 0, 0, 0])
      edge b := (if b then ![0, 1, 0, 0, 0, 1] else ![0, 0, 1, 0, 1, 0])
      face _b := ![0, 1, 0, 1]
      volume := 0 }
  | 10 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![1, 0, 0, 0])
      edge b := (if b then ![0, 1, 0, 0, 0, 1] else ![0, 0, 1, 0, 1, 0])
      face b := (if b then ![0, 1, 0, 1] else ![1, 0, 1, 0])
      volume := 1 }
  | 11 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![1, 0, 0, 0])
      edge b := (if b then ![0, 1, 0, 0, 0, 1] else ![0, 0, 1, 0, 1, 0])
      face _b := ![1, 0, 1, 0]
      volume := 0 }
  | 12 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![1, 0, 0, 0])
      edge b := (if b then ![1, 0, 0, 0, 0, 1] else ![0, 0, 1, 0, 1, 0])
      face _b := ![0, 0, 1, 0]
      volume := 0 }
  | 13 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![1, 0, 0, 0])
      edge _b := ![0, 1, 0, 0, 0, 1]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 14 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![1, 0, 0, 0])
      edge b := (if b then ![0, 1, 0, 0, 0, 1] else ![1, 0, 0, 0, 0, 1])
      face _b := ![1, 0, 0, 0]
      volume := 0 }
  | 15 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![1, 0, 0, 0])
      edge _b := ![1, 0, 0, 0, 0, 1]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 16 =>
    { vertex _b := ![0, 1, 0, 0]
      edge _b := ![0, 0, 0, 0, 0, 0]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 17 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![0, 1, 0, 0])
      edge _b := ![0, 0, 0, 0, 0, 1]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 18 =>
    { vertex _b := ![0, 0, 1, 0]
      edge _b := ![0, 0, 0, 0, 0, 0]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 19 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![0, 0, 1, 0])
      edge _b := ![0, 0, 0, 1, 0, 0]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | 20 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![0, 0, 1, 0])
      edge b := (if b then ![0, 0, 0, 1, 0, 0] else ![0, 0, 1, 0, 0, 0])
      face _b := ![0, 1, 0, 0]
      volume := 0 }
  | 21 =>
    { vertex b := (if b then ![0, 0, 0, 1] else ![0, 0, 1, 0])
      edge _b := ![0, 0, 1, 0, 0, 0]
      face _b := ![0, 0, 0, 0]
      volume := 0 }
  | _ =>
    { vertex _b := ![0, 0, 0, 1]
      edge _b := ![0, 0, 0, 0, 0, 0]
      face _b := ![0, 0, 0, 0]
      volume := 0 }

lemma code_valid (i : Fin 23) : (code i).IsValid := by
  revert i
  unfold Coordinates.IsValid
  decide

lemma forall_fin4 (P : Fin 4 → Prop) : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩ i
    fin_cases i <;> assumption

lemma forall_fin6 (P : Fin 6 → Prop) :
    (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩
  · rintro ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ i
    fin_cases i <;> assumption

lemma vec_val_five {α : Type*} (a b c d e f : α) :
    ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl

end Thomason.GrayTwo

end

noncomputable section
universe u v w z


namespace Thomason.GrayTwo

lemma vertex_0 (x : Coordinates) (hx : x.IsValid) (b : Bool)
    (h : x.vertex b 0 = 1) : x.vertex b = ![1, 0, 0, 0] := by
  have hp := hx.1 b
  have ha := hx.2.2.2.2.1 b
  simp only [forall_fin4] at hp
  simp only [funext_iff, forall_fin4]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
  repeat' constructor <;> omega

lemma vertex_1 (x : Coordinates) (hx : x.IsValid) (b : Bool)
    (h : x.vertex b 1 = 1) : x.vertex b = ![0, 1, 0, 0] := by
  have hp := hx.1 b
  have ha := hx.2.2.2.2.1 b
  simp only [forall_fin4] at hp
  simp only [funext_iff, forall_fin4]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
  repeat' constructor <;> omega

lemma vertex_2 (x : Coordinates) (hx : x.IsValid) (b : Bool)
    (h : x.vertex b 2 = 1) : x.vertex b = ![0, 0, 1, 0] := by
  have hp := hx.1 b
  have ha := hx.2.2.2.2.1 b
  simp only [forall_fin4] at hp
  simp only [funext_iff, forall_fin4]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
  repeat' constructor <;> omega

lemma vertex_3 (x : Coordinates) (hx : x.IsValid) (b : Bool)
    (h : x.vertex b 3 = 1) : x.vertex b = ![0, 0, 0, 1] := by
  have hp := hx.1 b
  have ha := hx.2.2.2.2.1 b
  simp only [forall_fin4] at hp
  simp only [funext_iff, forall_fin4]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
  repeat' constructor <;> omega

end Thomason.GrayTwo

end

end OAI
