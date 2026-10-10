import Mathlib
import OAI.Analysis.MatrixSigning.Potential.FacePotential

namespace OAI

open Matrix

namespace CurrentKS.Schedule

def movementBudget (n : ℕ) (ε : ℚ) : ℚ :=
  let s₀ := ε/40000
  let J := 1+(3*(n:ℚ))^2/s₀
  let E₀ := 2*J^2*(1+3*(n:ℚ))^2
  max 1 (max (48*E₀/23) (4*(1+9*(n:ℚ)^2)))

def threshold (n : ℕ) (ε lam : ℚ) : ℚ := lam/(512*(movementBudget n ε)^2)

lemma movementBudget_one_le (n : ℕ) (ε : ℚ) : 1 ≤ movementBudget n ε := le_max_left _ _

lemma movementBudget_pos (n : ℕ) (ε : ℚ) : 0 < movementBudget n ε :=
  lt_of_lt_of_le (by norm_num) (movementBudget_one_le n ε)

lemma threshold_pos (n : ℕ) (ε : ℚ) {lam : ℚ} (hlam : 0 < lam) : 0 < threshold n ε lam := by
  unfold threshold
  have hp := movementBudget_pos n ε
  positivity

lemma threshold_le_one (n : ℕ) (ε : ℚ) {lam : ℚ} (hlam : lam ≤ 1) : threshold n ε lam ≤ 1 := by
  unfold threshold
  have hp := movementBudget_pos n ε
  have h1 := movementBudget_one_le n ε
  apply (div_le_one (by positivity)).mpr
  nlinarith

lemma threshold_relation (n : ℕ) (ε lam : ℚ) :
    lam=512*threshold n ε lam*(movementBudget n ε)^2 := by
  have hp := (movementBudget_pos n ε).ne'
  unfold threshold
  field_simp

def stepSize (a M σ : ℚ) : ℚ := min (σ/4) (min (a/(4*M)) (1/4))
def stencilSize (n : ℕ) (a M σ : ℚ) : ℚ := min (σ/8) (min 1 (a/(64*M*n)))
def meshSize (n : ℕ) (a M s : ℚ) : ℚ := s*a/(4096*M*n)

lemma stepSize_spec {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    0 < stepSize a M σ ∧ stepSize a M σ ≤ σ/4 ∧ stepSize a M σ ≤ 1/4 ∧
      M*stepSize a M σ ≤ a/4 := by
  have hp : 0 < a/(4*M) := by positivity
  have hs : stepSize a M σ ≤ a/(4*M) := min_le_right _ _ |>.trans (min_le_left _ _)
  refine ⟨by unfold stepSize;positivity,min_le_left _ _,
    (min_le_right _ _).trans (min_le_right _ _),?_⟩
  have hh := (le_div_iff₀ (show (0:ℚ) < 4*M by positivity)).mp hs
  linarith

lemma stencilSize_spec {n : ℕ} (hn : 0 < n) {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    0 < stencilSize n a M σ ∧ stencilSize n a M σ ≤ σ/8 ∧
    stencilSize n a M σ ≤ 1 ∧ stencilSize n a M σ ≤ a/(64*M*n) := by
  have hnr : (0:ℚ) < n := by exact_mod_cast hn
  refine ⟨by unfold stencilSize;positivity,min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),(min_le_right _ _).trans (min_le_right _ _)⟩

lemma meshSize_spec {n : ℕ} (hn : 0 < n) {a M s : ℚ} (ha : 0 < a) (hM : 0 < M) (hs : 0 < s) :
    0 < meshSize n a M s ∧ (n:ℚ)*meshSize n a M s/2 ≤ s*(a/(1024*M))/8 := by
  have hnr : (0:ℚ) < n := by exact_mod_cast hn
  refine ⟨by unfold meshSize;positivity,?_⟩
  unfold meshSize
  apply le_of_eq
  field_simp
  ring

lemma schedule_radius {n : ℕ} (hn : 0 < n) {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    stepSize a M σ+2*stencilSize n a M σ ≤ σ/2 := by
  have hs := (stepSize_spec ha hM hσ).2.1
  have hh := (stencilSize_spec hn ha hM hσ).2.1
  linarith

open CurrentKS.State

def coarseBudgetQ (d n : ℕ) (ε σ : ℚ) : ℚ :=
  200+((d:ℚ)+1)+|ε|+(200/ε)*((d:ℚ)+1)+200*((d:ℚ)+1)+
    (((d:ℚ)+1)+n)+384*n*(1+800/σ^3)

def valueCurve2Q (d n : ℕ) (ε σ : ℚ) : ℚ :=
  let B := coarseBudgetQ d n ε σ
  let Jb := 10^18*((d:ℚ)+1)*(1+ε⁻¹)^4
  let D := 300*B^5
  (1+|ε| *(2*((d:ℚ)+1)))*(Jb*D*(1+Jb*D)^2)

def valueCurve3Q (d n : ℕ) (ε σ : ℚ) : ℚ :=
  let B := coarseBudgetQ d n ε σ
  let Jb := 10^18*((d:ℚ)+1)*(1+ε⁻¹)^4
  let D := 300*B^5
  (1+|ε| *(2*((d:ℚ)+1)))*
    (Jb*D*((1+Jb*D)^3+3*(1+Jb*D)*(Jb*D*(1+Jb*D)^2)))

def curveBudget (d n : ℕ) (ε σ lam : ℚ) : ℚ :=
  1+valueCurve2Q d n ε σ+valueCurve3Q d n ε σ+|lam| *(n:ℚ)*(1+800/σ^3)

lemma coarseBudgetQ_cast (d n : ℕ) (ε σ : ℚ) :
    (coarseBudgetQ d n ε σ:ℝ)=coarseBudget d n (ε:ℝ) (σ:ℝ) := by
  simp only [coarseBudgetQ,coarseBudget,Rat.cast_add,Rat.cast_mul,Rat.cast_div,
    Rat.cast_pow,Rat.cast_natCast,Rat.cast_abs,Rat.cast_ofNat,Rat.cast_one]

lemma curveBudget_cast (d n : ℕ) (ε σ lam : ℚ) :
    (curveBudget d n ε σ lam:ℝ)=potentialCurveBound d n (ε:ℝ) (σ:ℝ) (lam:ℝ) := by
  simp only [curveBudget,potentialCurveBound,valueCurve2Q,valueCurve3Q,
    valueCurve2Bound,valueCurve3Bound,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_abs,Rat.cast_inv,Rat.cast_one,Rat.cast_ofNat,coarseBudgetQ_cast]

lemma curveBudget_one_le (d n : ℕ) {ε σ : ℚ} (hε : 0 < ε) (hσ : 0 < σ) (lam : ℚ) :
    1 ≤ curveBudget d n ε σ lam := by
  have hεr : (0:ℝ) < ε := by exact_mod_cast hε
  have hσr : (0:ℝ) < σ := by exact_mod_cast hσ
  have hh := valueCurve_bounds_nonneg (d:=d) (N:=n) hεr hσr
  have hl : (0:ℝ) ≤ |(lam:ℝ)| *(n:ℝ)*(1+800/(σ:ℝ)^3) := by positivity
  have hc : (1:ℝ) ≤ potentialCurveBound d n (ε:ℝ) (σ:ℝ) (lam:ℝ) := by
    unfold potentialCurveBound
    linarith
  rw [←curveBudget_cast] at hc
  exact_mod_cast hc

end CurrentKS.Schedule

end OAI
