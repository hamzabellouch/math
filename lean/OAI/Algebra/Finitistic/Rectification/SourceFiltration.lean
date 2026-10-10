import OAI.Algebra.Finitistic.Rectification.InducedDiagram
import OAI.Algebra.Finitistic.Rectification.TotalFunctorial

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))

/-- Source at least one: the actual D1 and D2 vertex terms and D1 arrow terms. -/
abbrev F1₀ := t.V₁ ⊞ t.V₂
abbrev F1₁ := ⨁ t.V
def Z : BiComplex k B where
  X _ := ModuleCat.of _ PUnit
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

def p1 : F1₁ t ⟶ F1₀ t :=
  biproduct.desc fun b => t.pb₁ b ≫ biprod.inl - t.pb₂ b ≫ biprod.inr

def h1 : Homotopy ((0 : Z ⟶ F1₁ t) ≫ p1 t) 0 where
  hom _ _ := 0
  zero _ _ _ := rfl
  comm _ := by simp [dNext, prevD]

/-- Source zero quotient: retain precisely the path-multiplication terms. -/
def p0 : (⨁ t.U) ⟶ t.V₀ := biproduct.desc t.pa₀

def q0 : t.L₂ ⟶ (⨁ t.U) :=
  biproduct.desc fun r => ∑ a, ∑ b, t.qa r a b ≫ biproduct.ι t.U a

theorem q0_p0 : q0 t ≫ p0 t = 0 := by
  apply biproduct.hom_ext'
  intro r
  simpa [q0, p0, Preadditive.sum_comp] using t.first r

def h0 : Homotopy (q0 t ≫ p0 t) 0 where
  hom _ _ := 0
  zero _ _ _ := rfl
  comm n := by rw [q0_p0]; simp [dNext, prevD]

omit [Fintype R] in
@[reassoc] theorem in_p : (biprod.inr : F1₁ t ⟶ t.L₁) ≫ t.p =
    p1 t ≫ (biprod.inr : F1₀ t ⟶ t.L₀) := by
  apply biproduct.hom_ext'
  intro b
  simp [AssemblyData.p, p1, AssemblyData.in₁, AssemblyData.in₂,
    Preadditive.sub_comp]

omit [Fintype R] in
@[reassoc] theorem p_out : t.p ≫ (biprod.fst : t.L₀ ⟶ t.V₀) =
    (biprod.fst : t.L₁ ⟶ ⨁ t.U) ≫ p0 t := by
  apply biprod.hom_ext' <;> apply biproduct.hom_ext' <;> intro a <;>
    simp [AssemblyData.p, p0, AssemblyData.in₀, AssemblyData.in₁,
      AssemblyData.in₂, Preadditive.sub_comp]

@[reassoc] theorem q_out : t.q ≫ (biprod.fst : t.L₁ ⟶ ⨁ t.U) = q0 t := by
  apply biproduct.hom_ext'
  intro r
  simp [AssemblyData.q, q0, Preadditive.sum_comp, Preadditive.add_comp]

variable (h : Homotopy (t.q ≫ t.p) 0)
/-- The original summand inclusion, as a triple preserving the specified homotopy. -/
def include1 : MapData (p1 t) 0 (h1 t) t.p t.q h where
  f₀ := biprod.inr
  f₁ := biprod.inr
  f₂ := 0
  commP := in_p t
  commQ := by simp
  commH i j := by simp [h1]

/-- Projection onto the actual source-zero quotient. The condition only records
that the supplied homotopy increases source index; it is proved for Section4 inputs below. -/
def quotient0 (hh : ∀ i j, h.hom i j ≫ (biprod.fst : t.L₀ ⟶ t.V₀).f j = 0) :
    MapData t.p t.q h (p0 t) (q0 t) (h0 t) where
  f₀ := biprod.fst
  f₁ := biprod.fst
  f₂ := 𝟙 _
  commP := (p_out t).symm
  commQ := by simpa using (q_out t).symm
  commH i j := by simpa [h0] using (hh i j).symm

/-- The second filtration step and its source-one quotient. -/
def p2 : Z (k := k) (B := B) ⟶ t.V₂ := 0

def h2 : Homotopy ((0 : Z ⟶ Z) ≫ p2 t) 0 where
  hom _ _ := 0
  zero _ _ _ := rfl
  comm _ := by simp [p2, dNext, prevD]

def pGrade1 : F1₁ t ⟶ t.V₁ := biproduct.desc t.pb₁

def hGrade1 : Homotopy ((0 : Z ⟶ F1₁ t) ≫ pGrade1 t) 0 where
  hom _ _ := 0
  zero _ _ _ := rfl
  comm _ := by simp [dNext, prevD]

def include2 : MapData (p2 t) 0 (h2 t) (p1 t) 0 (h1 t) where
  f₀ := biprod.inr
  f₁ := 0
  f₂ := 𝟙 _
  commP := by simp [p2]
  commQ := by simp
  commH i j := by simp [h1, h2]

def quotient1 : MapData (p1 t) 0 (h1 t) (pGrade1 t) 0 (hGrade1 t) where
  f₀ := biprod.fst
  f₁ := 𝟙 _
  f₂ := 𝟙 _
  commP := by
    rw [Category.id_comp]
    apply biproduct.hom_ext'
    intro b
    simp [p1, pGrade1, Preadditive.sub_comp]
  commQ := by simp
  commH i j := by simp [h1, hGrade1]

/-- Changing the endpoint proofs does not change a homotopy's components. -/
theorem cast_hom {X Y : BiComplex k B} {a b a' b' : X ⟶ Y}
    (ha : a = a') (hb : b = b') (e : Homotopy a b = Homotopy a' b')
    (v : Homotopy a b) : (cast e v).hom = v.hom := by
  subst a'
  subst b'
  rfl

variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

theorem induced_h_out (i j : ℤ) :
    (nullHomotopy s D₀ D₁ D₂ f g H).hom i j ≫
      (biprod.fst : L0Prime s D₀ D₁ D₂ f g ⟶
        (inducedData s D₀ D₁ D₂ f g).V₀).f j = 0 := by
  classical
  unfold nullHomotopy
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [cast_hom (by simp [AssemblyData.composite]) (by simp)]
  rw [cast_hom (ha := ?_) (hb := ?_)]
  rotate_left
  · simp
  · simp
  change ((-1 : k) • h s D₀ D₁ D₂ f g H i j) ≫ _ = 0
  rw [Linear.smul_comp]
  suffices h s D₀ D₁ D₂ f g H i j ≫
      (biprod.fst : L0Prime s D₀ D₁ D₂ f g ⟶
        (inducedData s D₀ D₁ D₂ f g).V₀).f j = 0 by rw [this, smul_zero]
  rw [h_formula, Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro r _
  dsimp only [AssemblyData.in₂]
  erw [Category.assoc, Category.assoc, ← comp_f, Category.assoc, biprod.inr_fst,
    CategoryTheory.Limits.comp_zero]

/-- Actual Section 4 source filtration inclusion; no decomposition is assumed. -/
abbrev inducedInclude1 := include1 (inducedData s D₀ D₁ D₂ f g)
  (nullHomotopy s D₀ D₁ D₂ f g H)
/-- Actual Section 4 source quotient; homotopy compatibility is proved above. -/
abbrev inducedQuotient0 := quotient0 (inducedData s D₀ D₁ D₂ f g)
  (nullHomotopy s D₀ D₁ D₂ f g H) (induced_h_out s D₀ D₁ D₂ f g H)
end ExternalTensor.Section4.SourceFiltration

end

end OAI
