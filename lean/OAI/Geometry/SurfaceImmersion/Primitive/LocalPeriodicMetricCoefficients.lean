import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicExpansionStep

namespace OAI

/-! Coefficients of the pullback metric of the finite periodic ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}



/-- The coefficient A_i=U_{i,x}+U_{i+1,theta}; index zero stores U_1. -/
def xCoefficient (dx : A) (U : ℕ → Family O E) (i : ℕ) : Family O E :=
  (U (i - 1)).slow dx + (U i).angle

/-- The coefficient B_i=U_{i,y}; index zero stores U_1. -/
def yCoefficient (dy : A) (U : ℕ → Family O E) (i : ℕ) : Family O E :=
  (U (i - 1)).slow dy

def xxQuadratic (dx : A) (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  ∑ i ∈ Finset.Ico 1 r, (xCoefficient dx U i).inner (xCoefficient dx U (r - i))

def xyQuadratic (dx dy : A) (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  ∑ i ∈ Finset.Ico 1 r, (xCoefficient dx U i).inner (yCoefficient dy U (r - i))

def yyQuadratic (dy : A) (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  ∑ i ∈ Finset.Ico 1 r, (yCoefficient dy U i).inner (yCoefficient dy U (r - i))

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

def xxCoefficient (dx : A) (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  (2 : ℝ) • g.longitudinal.inner (xCoefficient dx U r) + xxQuadratic dx U r

def xyCoefficient (dx : A) (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  g.longitudinal.inner (yCoefficient dy U r) +
  g.transverse.inner (xCoefficient dx U r) + xyQuadratic dx dy U r

def yyCoefficient (U : ℕ → Family O E) (r : ℕ) : Family O ℝ :=
  (2 : ℝ) • g.transverse.inner (yCoefficient dy U r) + yyQuadratic dy U r

end Geometry

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xCoefficient_congr {dx : A} {U W : ℕ → Family O E} {i : ℕ}
    (h₁ : U (i - 1) = W (i - 1)) (h₂ : U i = W i) :
    xCoefficient dx U i = xCoefficient dx W i := by
  simp only [xCoefficient, h₁, h₂]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yCoefficient_congr {dy : A} {U W : ℕ → Family O E} {i : ℕ}
    (h : U (i - 1) = W (i - 1)) : yCoefficient dy U i = yCoefficient dy W i := by
  simp only [yCoefficient, h]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xxQuadratic_congr {dx : A} {U W : ℕ → Family O E} {r : ℕ}
    (h : ∀ i < r, U i = W i) : xxQuadratic dx U r = xxQuadratic dx W r := by
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  rw [xCoefficient_congr (h _ (by omega)) (h _ hir),
    xCoefficient_congr (h _ (by omega)) (h _ (by omega))]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xyQuadratic_congr {dx dy : A} {U W : ℕ → Family O E} {r : ℕ}
    (h : ∀ i < r, U i = W i) : xyQuadratic dx dy U r = xyQuadratic dx dy W r := by
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  rw [xCoefficient_congr (h _ (by omega)) (h _ hir),
    yCoefficient_congr (h _ (by omega))]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yyQuadratic_congr {dy : A} {U W : ℕ → Family O E} {r : ℕ}
    (h : ∀ i < r - 1, U i = W i) : yyQuadratic dy U r = yyQuadratic dy W r := by
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  rw [yCoefficient_congr (h _ (by omega)), yCoefficient_congr (h _ (by omega))]

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
