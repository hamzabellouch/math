import OAI.Probability.UnimodularPercolation.Kernel.TraceBounds

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
namespace BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq

structure PublishedSimpleGraph (G : BondGraph V E) : Prop where
  injective : Function.Injective G
  loopless : ∀ e x, G e ≠ s(x, x)
  connected : Connected G
  locallyFinite : LocallyFinite G
  quasiTransitive : QuasiTransitive G

noncomputable def triangleDiagram (G : BondGraph V E) (p : unitInterval) (x : V) : ℝ≥0∞ :=
  ∑' ab : V × V, ENNReal.ofReal
    (twoPoint G p x ab.1 * twoPoint G p ab.1 ab.2 * twoPoint G p ab.2 x)

noncomputable def graphDistance (G : BondGraph V E) (x y : V) : ℕ :=
  (openSimpleGraph G Set.univ).dist x y

def ExponentialDecay (G : BondGraph V E) (p : unitInterval) : Prop :=
  ∃ A a : ℝ, 0 < A ∧ 0 < a ∧ ∀ x y,
    twoPoint G p x y ≤ A * Real.exp (-a * graphDistance G x y)

noncomputable def pexp (G : BondGraph V E) : unitInterval :=
  sSup {p | ExponentialDecay G p}

def PowerTail (f : ℕ → ℝ) (exponent : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 0 < n →
    c * (n : ℝ) ^ (-exponent) ≤ f n ∧ f n ≤ C * (n : ℝ) ^ (-exponent)

def volumeEvent (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | (n : ℕ∞) ≤ (cluster G ω x).encard}

def intrinsicRadiusEvent (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ y ∈ cluster G ω x, n ≤ (openSimpleGraph G ω).dist x y}

def extrinsicRadiusEvent (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ y ∈ cluster G ω x, n ≤ graphDistance G x y}

noncomputable def criticalTail (G : BondGraph V E)
    (A : V → ℕ → Set (Set E)) (x : V) (n : ℕ) : ℝ :=
  (law (pc G) (A x n)).toReal

def CriticalTailLaws (G : BondGraph V E) : Prop :=
  ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2) ∧
    PowerTail (criticalTail G (intrinsicRadiusEvent G) x) 1 ∧
    PowerTail (criticalTail G (extrinsicRadiusEvent G) x) 1

def SusceptibilityLaw (G : BondGraph V E) : Prop :=
  ∀ x, ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
    ∀ p : unitInterval, p < pc G → (pc G : ℝ) - p < δ →
      c / ((pc G : ℝ) - p) ≤ susceptibility G p x ∧
      susceptibility G p x ≤ C / ((pc G : ℝ) - p)

noncomputable def percolationProbability (G : BondGraph V E) (p : unitInterval)
    (x : V) : ℝ := (law p {ω | (cluster G ω x).Infinite}).toReal

def PercolationProbabilityLaw (G : BondGraph V E) : Prop :=
  ∀ x, ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
    ∀ p : unitInterval, pc G < p → (p : ℝ) - pc G < δ →
      c * ((p : ℝ) - pc G) ≤ percolationProbability G p x ∧
      percolationProbability G p x ≤ C * ((p : ℝ) - pc G)

theorem triangle_hasSum
    (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x : V) :
    HasSum (fun ab : V × V =>
      twoPoint G p x ab.1 * twoPoint G p ab.1 ab.2 * twoPoint G p ab.2 x)
      (matrixCoeff (T ^ 3) x x).re := by
  have ht := hT.positiveRealMatrix G p T
  have hs := ht.triple_hasSum ht ht x x
  rw [show T * T * T = T ^ 3 by simp only [pow_succ, pow_zero, one_mul]] at hs
  simpa only [HasKernel.matrixCoeff_re G p T hT] using hs

theorem triangleDiagram_eq_matrix
    (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x : V) :
    triangleDiagram G p x = ENNReal.ofReal (matrixCoeff (T ^ 3) x x).re := by
  have hs := triangle_hasSum G p T hT x
  unfold triangleDiagram
  have hn (ab : V × V) :
      0 ≤ twoPoint G p x ab.1 * twoPoint G p ab.1 ab.2 * twoPoint G p ab.2 x :=
    mul_nonneg (mul_nonneg (twoPoint_nonneg G p x ab.1)
      (twoPoint_nonneg G p ab.1 ab.2)) (twoPoint_nonneg G p ab.2 x)
  exact (ENNReal.ofReal_tsum_of_nonneg hn hs.summable).symm.trans
    (congrArg ENNReal.ofReal hs.tsum_eq)

theorem triangleDiagram_le_norm_cube
    (G : BondGraph V E) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (x : V) :
    triangleDiagram G p x ≤ ENNReal.ofReal (‖T‖ ^ 3) := by
  rw [triangleDiagram_eq_matrix G p T hT x]
  apply ENNReal.ofReal_le_ofReal
  apply (Complex.re_le_norm _).trans
  have hc : ‖matrixCoeff (T ^ 3) x x‖ ≤ ‖T ^ 3‖ := by
    change ‖(T ^ 3) (lp.single 2 x (1 : ℂ)) x‖ ≤ ‖T ^ 3‖
    apply (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
      ((T ^ 3) (lp.single 2 x (1 : ℂ))) x).trans
    simpa only [lp.norm_single (by norm_num : 0 < (2 : ENNReal)), norm_one, mul_one] using
      (T ^ 3).le_opNorm (lp.single 2 x (1 : ℂ))
  exact hc.trans (norm_pow_le' T (by norm_num : 0 < (3 : ℕ)))

theorem triangleDiagram_le_operatorNorm_cube
    (G : BondGraph V E) (p : unitInterval) (h : OperatorBounded G p) (x : V) :
    triangleDiagram G p x ≤ operatorNorm G p ^ 3 := by
  classical
  obtain ⟨T, hT⟩ := h
  rw [operatorNorm_of_hasKernel hT, ← ENNReal.ofReal_pow (norm_nonneg T)]
  exact triangleDiagram_le_norm_cube G p T hT x

theorem triangleDiagram_lt_top_of_bounded
    (G : BondGraph V E) (p : unitInterval) (h : OperatorBounded G p) (x : V) :
    triangleDiagram G p x < ⊤ := by
  classical
  obtain ⟨T, hT⟩ := h
  exact (triangleDiagram_le_norm_cube G p T hT x).trans_lt ENNReal.ofReal_lt_top

theorem critical_triangle_of_mainConclusion
    (G : BondGraph V E) (h : MainConclusion G) (x : V) :
    triangleDiagram G (pc G) x ≤ operatorNorm G (pc G) ^ 3 ∧
      triangleDiagram G (pc G) x < ⊤ := by
  have hb := (operatorNorm_lt_top_iff G (pc G)).mp h.2.1
  exact ⟨triangleDiagram_le_operatorNorm_cube G (pc G) hb x,
    triangleDiagram_lt_top_of_bounded G (pc G) hb x⟩

def HutchcroftExponentialInput (G : BondGraph V E) : Prop :=
  PublishedSimpleGraph G → ∀ p : unitInterval, 0 < p → p < ptwo G →
    ∀ T : Hilbert V →L[ℂ] Hilbert V, HasKernel G p T → ∀ x y,
      twoPoint G p x y ≤ 2 * ‖T‖ *
        Real.exp (-(graphDistance G x y : ℝ) / (Real.exp 1 * ‖T‖))

theorem exponentialDecay_zero [Countable E] (G : BondGraph V E) :
    ExponentialDecay G 0 := by
  classical
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    simp [graphDistance]
  · rw [twoPoint_zero, ite_eq_right hxy]
    positivity

theorem exponentialDecay_of_publishedInput [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G)
    (hpub : HutchcroftExponentialInput G)
    (p : unitInterval) (hp : p < ptwo G) : ExponentialDecay G p := by
  classical
  by_cases hp0 : p = 0
  · simpa only [hp0] using exponentialDecay_zero G
  have hp_pos : 0 < p := lt_of_le_of_ne bot_le (Ne.symm hp0)
  obtain ⟨q, hq, hpq⟩ := lt_sSup_iff.mp hp
  obtain ⟨T, hT⟩ := operatorBounded_of_le G hpq.le hq
  have hnorm : 0 < ‖T‖ := by
    let x : V := Classical.arbitrary V
    have hcol := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
      (T (lp.single 2 x (1 : ℂ))) x
    rw [hT x x, twoPoint_self, Complex.ofReal_one, norm_one] at hcol
    have hop := T.le_opNorm (lp.single 2 x (1 : ℂ))
    norm_num [lp.norm_single] at hop
    exact zero_lt_one.trans_le (hcol.trans hop)
  refine ⟨2 * ‖T‖, (Real.exp 1 * ‖T‖)⁻¹, by positivity, by positivity, ?_⟩
  intro x y
  convert hpub hgraph p hp_pos hp T hT x y using 1
  congr 2
  simp only [div_eq_mul_inv, neg_mul, mul_neg, mul_comm]

theorem ptwo_le_pexp_of_publishedInput [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G)
    (hpub : HutchcroftExponentialInput G) : ptwo G ≤ pexp G := by
  apply le_of_forall_lt_imp_le_of_dense
  intro p hp
  exact le_sSup (exponentialDecay_of_publishedInput G hgraph hpub p hp)

theorem exponential_threshold_of_mainConclusion [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G)
    (hpub : HutchcroftExponentialInput G) (hmain : MainConclusion G) :
    pc G < ptwo G ∧ ptwo G ≤ pexp G :=
  ⟨hmain.2.2.1, ptwo_le_pexp_of_publishedInput G hgraph hpub⟩

theorem law_restrict_finite_cluster (G : BondGraph V E) (p : unitInterval) (x : V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) (A : Set (Set E)) :
    law p {ω | ω ∈ A ∧ (cluster G ω x).Finite} = law p A := by
  apply measure_congr
  filter_upwards [hfin] with ω hω
  exact propext (and_iff_left hω)

noncomputable def criticalFiniteTail (G : BondGraph V E)
    (A : V → ℕ → Set (Set E)) (x : V) (n : ℕ) : ℝ :=
  (law (pc G) {ω | ω ∈ A x n ∧ (cluster G ω x).Finite}).toReal

theorem criticalFiniteTail_eq (G : BondGraph V E)
    (A : V → ℕ → Set (Set E)) (x : V)
    (hfin : ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite) :
    criticalFiniteTail G A x = criticalTail G A x := by
  funext n
  unfold criticalFiniteTail criticalTail
  rw [law_restrict_finite_cluster G (pc G) x hfin (A x n)]

def HutchcroftCriticalVolumeInput (G : BondGraph V E) : Prop :=
  PublishedSimpleGraph G → pc G < ptwo G → ∀ x,
    PowerTail (criticalFiniteTail G (volumeEvent G) x) (1 / 2)

def HutchcroftCriticalRadiiInput (G : BondGraph V E) : Prop :=
  PublishedSimpleGraph G → pc G < ptwo G → ∀ x,
    PowerTail (criticalFiniteTail G (intrinsicRadiusEvent G) x) 1 ∧
    PowerTail (criticalFiniteTail G (extrinsicRadiusEvent G) x) 1

theorem criticalTailLaws_of_publishedInputs (G : BondGraph V E)
    (hgraph : PublishedSimpleGraph G)
    (hvolume : HutchcroftCriticalVolumeInput G)
    (hradii : HutchcroftCriticalRadiiInput G)
    (hgap : pc G < ptwo G)
    (hfin : ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite) :
    CriticalTailLaws G := by
  intro x
  obtain ⟨hi, he⟩ := hradii hgraph hgap x
  have hv := hvolume hgraph hgap x
  rw [criticalFiniteTail_eq G (volumeEvent G) x (hfin x)] at hv
  rw [criticalFiniteTail_eq G (intrinsicRadiusEvent G) x (hfin x)] at hi
  rw [criticalFiniteTail_eq G (extrinsicRadiusEvent G) x (hfin x)] at he
  exact ⟨hv, hi, he⟩

def HutchcroftFirstMomentInput (G : BondGraph V E) : Prop :=
  PublishedSimpleGraph G → pc G < ptwo G → ∀ x,
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ p : unitInterval, p < pc G → (pc G : ℝ) - p < δ →
        c / ((pc G : ℝ) - p) ≤ ∫ ω, ((cluster G ω x).ncard : ℝ) ∂law p ∧
        (∫ ω, ((cluster G ω x).ncard : ℝ) ∂law p) ≤ C / ((pc G : ℝ) - p)

theorem susceptibilityLaw_of_publishedInput [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G)
    (hpub : HutchcroftFirstMomentInput G) (hgap : pc G < ptwo G) :
    SusceptibilityLaw G := by
  intro x
  obtain ⟨c, C, δ, hc, hC, hδ, hb⟩ := hpub hgraph hgap x
  refine ⟨c, C, δ, hc, hC, hδ, ?_⟩
  intro p hp hnear
  rw [(susceptibility_eq_integral G hgraph.locallyFinite hgraph.quasiTransitive p hp x).2]
  exact hb p hp hnear

def TrianglePercolationProbabilityInput (G : BondGraph V E) : Prop :=
  PublishedSimpleGraph G → (∀ x, triangleDiagram G (pc G) x < ⊤) →
    PercolationProbabilityLaw G

theorem percolationProbabilityLaw_of_publishedInput
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G)
    (hpub : TrianglePercolationProbabilityInput G)
    (hbounded : OperatorBounded G (pc G)) : PercolationProbabilityLaw G :=
  hpub hgraph (triangleDiagram_lt_top_of_bounded G (pc G) hbounded)

theorem meanFieldLaws_of_publishedInputs [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hgraph : PublishedSimpleGraph G)
    (hfirst : HutchcroftFirstMomentInput G)
    (htheta : TrianglePercolationProbabilityInput G)
    (hvolume : HutchcroftCriticalVolumeInput G)
    (hradii : HutchcroftCriticalRadiiInput G)
    (hmain : MainConclusion G)
    (hfin : ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite) :
    SusceptibilityLaw G ∧ PercolationProbabilityLaw G ∧ CriticalTailLaws G := by
  have hb := (operatorNorm_lt_top_iff G (pc G)).mp hmain.2.1
  exact ⟨susceptibilityLaw_of_publishedInput G hgraph hfirst hmain.2.2.1,
    percolationProbabilityLaw_of_publishedInput G hgraph htheta hb,
    criticalTailLaws_of_publishedInputs G hgraph hvolume hradii hmain.2.2.1 hfin⟩

end BenjaminiSchramm
end Percolation

end OAI
