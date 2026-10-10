import OAI.NumberTheory.TotientAsymptotic.FordSimplexEmbedding

namespace OAI

/-!
The fixed-deviation consequence of Ford, *The distribution of totients*,
arXiv:1104.3264v2 (2013), Lemma 6.1, (6.6)--(6.8), pp. 30--31.
We use deviation 1/40 only. For the lower tail take
`theta = (1/40)/(1-1/40)` in (6.6); for the upper tail take
`theta = -(1/40)/(1+1/40)` in (6.7) or (6.8), splitting at
`-i*lambda_i/L`. The uniform bounds (6.4) give positive absolute
constants in `exp (-c*(L-i))`. Letting the terminal cutoff decrease to
zero and rescaling the simplex gives precisely the input below.
The transfer from Ford's terminal coefficient 1 to our coefficient a_1
is proved here using `shrinkLast`, rather than assumed in this input.
-/

noncomputable section
open MeasureTheory

namespace TotientAsymptotic

def fordSimplexCenter (N : ℕ) (B : ℝ) (i : Fin (N+2)) : ℝ :=
  B*rho^(i.val+1)*(1-(i.val+1 : ℝ)/(N+2))

def fordCoordinateBad (N : ℕ) (B : ℝ) (i : Fin (N+2)) : Set (Fin (N+2) → ℝ) :=
  {u | (1/40 : ℝ) < |u i/fordSimplexCenter N B i-1|}

def FordCoordinateConcentrationInput : Prop :=
  ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ N ≥ N₀, ∀ B : ℝ, 0 < B → ∀ i : Fin (N+2), i.val < N →
      (volume (fordSimplex N B ∩ fordCoordinateBad N B i)).toReal ≤
        C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (fordSimplex N B)).toReal

lemma measurableSet_fordCoordinateBad (N : ℕ) (B : ℝ) (i : Fin (N+2)) :
    MeasurableSet (fordCoordinateBad N B i) := by
  apply measurableSet_lt measurable_const
  exact ((measurable_pi_apply i).div_const _ |>.sub_const 1).abs

lemma prefixRegion_volume_ne_top {N : ℕ} (hN : 0 < N) (B : ℝ) :
    volume (prefixRegion N B 0 0) ≠ ⊤ := by
  rw [volume_prefixRegion_explicit _ hN]
  exact ENNReal.ofReal_ne_top

theorem simplex_coordinate_concentration (hford : FordCoordinateConcentrationInput) :
    ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ N ≥ N₀, ∀ B : ℝ, 0 < B → ∀ i : Fin (N+2), i.val < N →
      (volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i)).toReal ≤
        C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (prefixRegion (N+2) B 0 0)).toReal := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := hford
  have ha := a_pos (j := 1) le_rfl
  refine ⟨C/a 1, c, N₀, div_pos hC ha, hc, ?_⟩
  intro N hN B hB i hi
  have hlast : i ≠ Fin.last (N+1) := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_last] at hh
    omega
  have hbound := shrinkLast_volume_bound
    (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i)
    (fordCoordinateBad N B i) (measurableSet_fordCoordinateBad N B i)
    (fun _ hu => hu.1) (fun u hu => by
      change (1/40 : ℝ) < |shrinkLast N u i/fordSimplexCenter N B i-1|
      rw [shrinkLast_preserves_prefix N u i hlast]
      exact hu.2)
  have hfin : volume (fordSimplex N B ∩ fordCoordinateBad N B i) ≠ ⊤ :=
    ne_top_of_le_ne_top (prefixRegion_volume_ne_top (by omega) B)
      (measure_mono (fun _ hu => hu.1.1))
  have hrightfin : ENNReal.ofReal ((a 1)⁻¹)*volume (fordSimplex N B ∩ fordCoordinateBad N B i) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hreal := ENNReal.toReal_mono hrightfin hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)] at hreal
  have hvol : (volume (fordSimplex N B)).toReal ≤ (volume (prefixRegion (N+2) B 0 0)).toReal := by
    exact ENNReal.toReal_mono (prefixRegion_volume_ne_top (by omega) B)
      (measure_mono (fun _ hu => hu.1))
  calc
    _ ≤ (a 1)⁻¹*(volume (fordSimplex N B ∩ fordCoordinateBad N B i)).toReal := hreal
    _ ≤ (a 1)⁻¹*(C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (fordSimplex N B)).toReal) :=
      mul_le_mul_of_nonneg_left (hconc N hN B hB i hi) (inv_nonneg.mpr ha.le)
    _ ≤ (a 1)⁻¹*(C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (prefixRegion (N+2) B 0 0)).toReal) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvol (by positivity)) (inv_nonneg.mpr ha.le)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
