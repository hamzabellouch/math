import OAI.Geometry.Immersion.ClosedSurface.FreeCharts

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RootMean Set Filter

lemma FreeBudget.slowSize_nonneg {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    {c : SupportedFreeChart F φ ψ S} {u : Base → ℝ} {τ s : ℝ} {q m : ℕ}
    (b : FreeBudget c u τ s q m) : 0 ≤ b.slowSize := by
  have hc := freeModeConstant_nonneg 4 m q b.nonnegK
  have hc' := b.nonnegC
  have hn := b.nonnegN
  have hj := zero_le_one.trans b.oneLEJ
  unfold FreeBudget.slowSize FreeBudget.seedConstant
  positivity

lemma FreeBudget.size_nonneg {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    {c : SupportedFreeChart F φ ψ S} {u : Base → ℝ} {τ s : ℝ} {q m : ℕ}
    (b : FreeBudget c u τ s q m) : 0 ≤ b.size := by
  have hc := freeModeConstant_nonneg 4 m q b.nonnegK
  have hc' := b.nonnegC
  have hn := b.nonnegN
  have hj := zero_le_one.trans b.oneLEJ
  unfold FreeBudget.size FreeBudget.seedConstant
  positivity


lemma weighted_quadraticAmplitude {n : ℕ} {ι : Type*} {φ : ι → Base → ℝ}
    {Z : ι → Field n} {τ s C P : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hZ : ∀ i, ContDiff ℝ ∞ (Z i))
    (hbZ : ∀ i, WeightedBound univ s (m + 1) C (Z i))
    (hpφ : ∀ i v, ‖v‖ ≤ 1 → WeightedBound univ s m P (coordDeriv v (φ i))) :
    ∀ l, WeightedBound univ s m
      ((n : ℝ) * (2 ^ m * ((1 + 2 ^ m * P) * C / τ) * ((1 + 2 ^ m * P) * C / τ)))
      (quadraticAmplitude τ φ Z l) := by
  have hh (i j) := weighted_phaseCrossTensor isOpen_univ hτ hs hτs hC hC hP
    (hφ i).contDiffOn (hφ j).contDiffOn (hZ i).contDiffOn (hZ j).contDiffOn
    (hbZ i) (hbZ j) (hpφ i) (hpφ j)
  intro l
  rcases l with i | ⟨i,j,b⟩
  · exact (hh i i).1
  · cases b
    · exact (hh i j).1
    · exact (hh i j).2



theorem weighted_free_quadraticAmplitude {ι : Type*} [Fintype ι]
    {F : RField 4} {φ ψ u : ι → Base → ℝ} {S : ι → Set Base}
    (c : ∀ i, SupportedFreeChart F (φ i) (ψ i) (S i))
    {δ τ s P : ℝ} (hδ : 0 ≤ δ) (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s)
    (hs1 : s ≤ 1) (hP : 0 ≤ P) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) {q m : ℕ}
    (b : ∀ i, FreeBudget (c i) (u i) τ s q (m + 1))
    (hpφ : ∀ i v, ‖v‖ ≤ 1 → WeightedBound univ s m P (coordDeriv v (φ i))) :
    let C := ∑ i, (b i).slowSize
    ∀ l, WeightedBound univ s m
      ((4 * 2 ^ m * ((1 + 2 ^ m * P) * C) ^ 2) * δ ^ 2)
      (quadraticAmplitude τ φ (fun i => (c i).amplitude (u i) δ τ q) l) := by
  classical
  dsimp only
  have hsum : 0 ≤ ∑ i, (b i).slowSize := Finset.sum_nonneg fun i _ => (b i).slowSize_nonneg
  have hb (i) := (c i).amplitude_bound hδ hτ hs hτs hs1 (b i)
  have hb' (i) : WeightedBound univ s (m + 1)
      ((∑ i, (b i).slowSize) * (δ * τ)) ((c i).amplitude (u i) δ τ q) := by
    exact (hb i).mono_const (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => (b j).slowSize_nonneg) (Finset.mem_univ i))
      (mul_nonneg hδ hτ.le))
  have hsm i := ((c i).amplitude_smooth (b i).smoothAmplitude δ τ q).1
  have hh := weighted_quadraticAmplitude hτ hs hτs (mul_nonneg hsum (mul_nonneg hδ hτ.le))
    hP hφ hsm hb' hpφ
  intro l
  convert hh l using 1
  field_simp
  ring



structure ForcedGeometryBudget {n : ℕ} {F : RField n} {φ : Base → ℝ} {S : Set Base}
    (c : SupportedSolveChart F φ S) (τ s : ℝ) (q m : ℕ) where
  K : ℝ
  J : ℝ
  D : ℝ
  E : ℝ
  T : ℝ
  nonnegK : 0 ≤ K
  oneLEJ : 1 ≤ J
  nonnegD : 0 ≤ D
  oneLEE : 1 ≤ E
  nonnegT : 0 ≤ T
  coefficients : ReconstructionCoefficientBound (fun p => complexify (F (c.e p)))
    c.V s (m + q + 1) K
  coordinate : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ c.U,
    ‖iteratedFDerivWithin ℝ j c.χ c.U p‖ ≤ J
  coordinateDerivative : ∀ v, ‖v‖ ≤ 1 → WeightedBound c.U τ m D (coordDeriv v c.χ)
  inverseCoordinate : ∀ j, 1 ≤ j → j ≤ m + q + 1 → ∀ p ∈ c.V,
    ‖iteratedFDerivWithin ℝ j c.e c.V p‖ ≤ E
  inverseDerivative : ∀ v, ‖v‖ ≤ 1 → WeightedBound c.V s (m + q + 1) T (coordDeriv v c.e)

def ForcedGeometryBudget.forcingFactor {n : ℕ} {F : RField n} {φ : Base → ℝ} {S : Set Base}
    {c : SupportedSolveChart F φ S} {τ s : ℝ} {q m : ℕ}
    (b : ForcedGeometryBudget c τ s q m) : ℝ :=
  4 * (2 ^ (m + q + 1) * (2 ^ (m + q + 1) *
    ((m + q + 1).factorial : ℝ) * b.E ^ (m + q + 1) * b.T) * b.T)

lemma ForcedGeometryBudget.forcingFactor_nonneg {n : ℕ} {F : RField n}
    {φ : Base → ℝ} {S : Set Base} {c : SupportedSolveChart F φ S} {τ s : ℝ} {q m : ℕ}
    (b : ForcedGeometryBudget c τ s q m) : 0 ≤ b.forcingFactor := by
  have he := zero_le_one.trans b.oneLEE
  have ht := b.nonnegT
  unfold ForcedGeometryBudget.forcingFactor
  positivity



def ForcedGeometryBudget.toSolveBudget {n : ℕ} {F : RField n} {φ : Base → ℝ} {S : Set Base}
    {c : SupportedSolveChart F φ S} {τ s C : ℝ} {q m : ℕ}
    (b : ForcedGeometryBudget c τ s q m) (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    {A : Base → ComplexTensor} (hA : ContDiff ℝ ∞ A)
    (hbA : WeightedBound univ s (m + q + 1) C A) : SolveBudget c A τ s q m where
  K := b.K
  C := b.forcingFactor * C
  J := b.J
  D := b.D
  nonnegK := b.nonnegK
  nonnegC := mul_nonneg b.forcingFactor_nonneg hC
  oneLEJ := b.oneLEJ
  nonnegD := b.nonnegD
  smoothA := contDiffOn_coordinateTarget c.domain.isOpen hA.contDiffOn c.smoothe (mapsTo_univ _ _)
  coefficients := b.coefficients
  coordinate := b.coordinate
  coordinateDerivative := b.coordinateDerivative
  forcing := by
    have hc := hbA.comp_coordinates c.domain.isOpen.uniqueDiffOn isOpen_univ.uniqueDiffOn hs hs1
      b.oneLEE hC c.smoothe hA.contDiffOn (mapsTo_univ _ _) b.inverseCoordinate
    have hC' : 0 ≤ ((m + q + 1).factorial : ℝ) * C * b.E ^ (m + q + 1) := by
      have he := zero_le_one.trans b.oneLEE
      positivity
    have hh := weighted_complexPullbackField_apply c.domain.isOpen hs hC' b.nonnegT
      (hA.contDiffOn.comp c.smoothe (mapsTo_univ _ _)) c.smoothe hc b.inverseDerivative
    convert hh using 1 <;> first | rfl | unfold ForcedGeometryBudget.forcingFactor; ring

end ClosedSurfaceR4.RealModes

end

end OAI
