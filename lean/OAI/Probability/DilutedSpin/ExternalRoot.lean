import OAI.Probability.DilutedSpin.ActualLowIncrement
import OAI.Probability.DilutedSpin.ConcreteReservoir
import OAI.Probability.DilutedSpin.ExternalTaylor
import OAI.Probability.DilutedSpin.FullRootPalm

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot
open scoped NNReal BigOperators Topology
variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

lemma integrable_scoreError (π : Measure (K×ℕ → ℝ)) [IsProbabilityMeasure π]
    (M : Model p) (C H : ℝ)
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1) (j : K×ℕ) (N : ℕ) :
    Integrable (scoreError ν Q m D E M C H j N) π := by
  apply Integrable.div_const
  apply integrable_parameterError
  · intro k y
    exact measurable_energy _ _ (fun σ => measurable_boundedPotential C σ) (measurable_clipReal H) k _
  · intro i; exact (probeLow_lt_high i.2).le
  · intro i; exact probe_interval_quarter i.2
  · intro i; exact extractionProbe_abs_le_quarter i.2
  · intro i x y; exact hD _ _ _
  · intro i x y; exact hE _ _ _

noncomputable def spinFactor (u : K×ℕ → ℝ) (i : K×ℕ) (σ : Spin) (y : FinitePath (A i.1) (L+1)) : ℝ :=
  1+extractionProbe i.2*D i.1 σ y+boundParameter (probeLow i.2) (probeHigh i.2) (u i)*E i.1 σ y

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
    [∀ q, Fintype (A q)] in
lemma measurable_spinFactor (i : K×ℕ) (σ : Spin) (y : FinitePath (A i.1) (L+1)) :
    Measurable (fun u => spinFactor D E u i σ y) :=
  measurable_const.add (((measurable_boundParameter _ _).comp (measurable_pi_apply i)).mul_const _)

lemma abs_log_affine_le {d e t u : ℝ} (hD : |d| ≤ 1) (hE : |e| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) : |Real.log (1+t*d+u*e)| ≤ 1 := by
  have htd : |t*d| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg t,abs_nonneg d]
  have hue : |u*e| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg u,abs_nonneg e]
  have hlo : 1/2 ≤ 1+t*d+u*e := by linarith [(abs_le.mp htd).1,(abs_le.mp hue).1]
  have hhi : 1+t*d+u*e ≤ 3/2 := by linarith [(abs_le.mp htd).2,(abs_le.mp hue).2]
  have hpos : 0 < 1+t*d+u*e := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hinv : (1+t*d+u*e)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ hpos).mpr
    linarith
  have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
    [∀ q, Fintype (A q)] in
lemma spinFactor_log_bound
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
    (u : K×ℕ → ℝ) (i : K×ℕ) (σ : Spin) (y : FinitePath (A i.1) (L+1)) :
    |Real.log (spinFactor D E u i σ y)| ≤ 1 := by
  apply abs_log_affine_le (hD _ _ _) (hE _ _ _) (extractionProbe_abs_le_quarter _)
  have hu := probe_interval_quarter i.2 (boundParameter_mem (probeLow_lt_high i.2).le (u i))
  exact abs_le.mpr ⟨by linarith [hu.1],hu.2⟩

/-- The increment of the actual quenched physical system with the complete
Poisson dictionary, not a pressure-rate proxy. Its size is N+1. -/
noncomputable def increment (M : Model p) (N : ℕ) (u : K×ℕ → ℝ) : ℝ :=
  SizeCoupling.perturbedMean (N := N+2) M.disorder.toMeasure M.field.toMeasure ν id id
    (fun i => Q i.1) m (spinFactor D E u) (M.alpha*(N+2)) (scoreRate (N+2)) -
  SizeCoupling.perturbedMean (N := N+1) M.disorder.toMeasure M.field.toMeasure ν id id
    (fun i => Q i.1) m (spinFactor D E u) (M.alpha*(N+1)) (scoreRate (N+1))

omit [DecidableEq K] in
lemma integrable_increment (π : Measure (K×ℕ → ℝ)) [IsProbabilityMeasure π]
    (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hm : ∀ l, 0 < m l) (hend : m (Fin.last L) = 1)
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1) (N : ℕ) :
    Integrable (increment ν Q m D E M N) π := by
  have hi (k : ℕ) := (SizeCoupling.parameter_average_negligible (N := k+1) π ν M hθ hh
    (fun i => Q i.1) m hm hend (spinFactor D E) (measurable_spinFactor D E)
    (spinFactor_log_bound D E hD hE) (scoreRate (k+1))).1
  change Integrable (fun u => increment ν Q m D E M N u) π
  simpa only [increment,Pi.sub_def,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    Nat.add_assoc,Nat.reduceAdd,add_assoc,one_add_one_eq_two] using (hi (N+1)).sub (hi N)

omit [DecidableEq K] in
lemma low_averaged_increment (π : Measure (K×ℕ → ℝ)) [IsProbabilityMeasure π]
    (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hm : ∀ l, 0 < m l) (hend : m (Fin.last L) = 1)
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∃ N, n ≤ N ∧ (∫ u, increment ν Q m D E M N u ∂π) ≤ Filter.liminf (pressure M) Filter.atTop+ε :=
  by
    simpa only [increment,Nat.cast_add,Nat.cast_ofNat] using
      SizeCoupling.actual_low_averaged_increments π ν M hθ hh (fun i => Q i.1) m hm hend
        (spinFactor D E) (measurable_spinFactor D E) (spinFactor_log_bound D E hD hE) hε n

omit [DecidableEq K] in
lemma uniform_increment (M : Model p) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H) (hm : ∀ l, 0 < m l)
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
    (N : ℕ) (u : K×ℕ → ℝ) :
    |increment ν Q m D E M N u| ≤ Real.log 2+H+(2*p+1)*C*M.alpha+3 := by
  simpa only [increment,Nat.add_assoc,Nat.reduceAdd,Nat.cast_add,Nat.cast_one,
    Nat.cast_ofNat,add_assoc,one_add_one_eq_two,mul_one] using
    SizeCoupling.actual_uniform_increment_ae (N := N+1) ν M hC hH hθ hh (fun i => Q i.1) m hm
      (spinFactor D E u) (by norm_num : (0:ℝ) ≤ 1) (spinFactor_log_bound D E hD hE u)

end DilutedSpinGlass.ConcreteReservoir
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- A fresh independent insertion, retaining every original mark in `z`.
The arguments `old` and `new` are intentionally distinct. -/
noncomputable def rootExternalTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old new E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (z : FullRootState Y X I M) (i : I) : ℝ :=
  packRoot (fun h k x n y => externalTreeScore S a T Q m (base h k x) (rootArray n y) i old (new i) (E i) f) z

noncomputable def rootExternalCoefficient (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (j : ℕ) (z : FullRootState Y X I M) (i : I) : ℝ :=
  packRoot (fun h k x n y => externalCoefficient S a T Q m (base h k x) (rootArray n y) i old (D i) (E i) f j) z

lemma measurable_rootExternalTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old new E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × I => rootExternalTreeScore S a T Q m base old new E f z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro i
  dsimp only [rootExternalTreeScore]
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  exact measurable_externalTreeScore S a T Q m
    (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) i old (new i) (E i) f (hb k)

lemma measurable_rootExternalCoefficient (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j : Fin L, m j.succ ≠ 0)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (j : ℕ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × I => rootExternalCoefficient S a T Q m base old D E f j z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro i
  dsimp only [rootExternalCoefficient]
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  exact measurable_externalCoefficient S a T Q m hm
    (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) i old (D i) (E i) f j (hb k)

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν η : Measure I) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

noncomputable def externalAverage (t u : ℝ) : ℝ :=
  ∫ z : FullRootState Y X I M × I, rootExternalTreeScore S a T Q (fun j => m j.succ) base old
    (fun i x y => 1+t*D i x y+u*E i x y) E f z.1 z.2 ∂(fullRootLaw ξ μ ν r s).prod η

noncomputable def externalCoefficientAverage (j : ℕ) : ℝ :=
  ∫ z : FullRootState Y X I M × I, rootExternalCoefficient S a T Q m base old D E f j z.1 z.2
    ∂(fullRootLaw ξ μ ν r s).prod η

variable (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)

include hE hf hb in
lemma integrable_rootExternalTreeScore (new : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hA : ∀ i x y, 1/2 ≤ new i x y) :
    Integrable (fun z : FullRootState Y X I M × I =>
      rootExternalTreeScore S a T Q (fun j => m j.succ) base old new E f z.1 z.2)
      ((fullRootLaw ξ μ ν r s).prod η) := by
  apply Integrable.of_bound (measurable_rootExternalTreeScore S a T Q _ base old new E f hb).aestronglyMeasurable (2*B)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs]
    exact abs_externalTreeScore_le S a T Q _ (base z.1.1 z.1.2.1.1 z.1.2.1.2)
      (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old (new z.2) (E z.2) f hf (hE z.2) (hA z.2))

include hmono hpos hroot hend hB hf hD hE hb hm in
lemma integrable_rootExternalCoefficient (j : ℕ) :
    Integrable (fun z : FullRootState Y X I M × I => rootExternalCoefficient S a T Q m base old D E f j z.1 z.2)
      ((fullRootLaw ξ μ ν r s).prod η) := by
  apply Integrable.of_bound (measurable_rootExternalCoefficient S a T Q m hm base old D E f j hb).aestronglyMeasurable
    (B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) j/(j.factorial:ℝ))
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs]
    exact externalCoefficient_bound S a T Q m hmono hpos hroot hend
      (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old (D z.2) (E z.2) f hB hf (hD z.2) (hE z.2) j)

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (S : PrescribedTree L) (a b : S.Leaf) (d : ℕ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hV : ∀ x i, |V x i| ≤ 1)
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
include hb hV

lemma integrable_rootPair_square : Integrable (fun z =>
    (S.sampleLaw (rootTower T Q (fun j => m j.succ) base old z)).expect (fun x =>
      FiniteLaw.dot (rootVector V z (S.pathAt a x)) (rootVector V z (S.pathAt b x))^2)) μ := by
  apply integrable_rootTreeMean T Q (fun j => m j.succ) base old hb S
    (fun x => FiniteLaw.dot (V (x a)) (V (x b))^2) μ
  intro x
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_one_iff_abs_le_one _).mpr (FiniteLaw.abs_dot_le_one _ _ (hV _) (hV _))

lemma integrable_rootPair_history : Integrable (fun z =>
    pairObservableHistory (rootTower T Q (fun j => m j.succ) base old z) m S a d
      (fun x y => FiniteLaw.dot (rootVector V z x) (rootVector V z y))
      (fun x => FiniteLaw.dot (rootVector V z (S.pathAt a x)) (rootVector V z (S.pathAt b x)))) μ := by
  exact integrable_rootPairObservable T Q m base old S a d
    (fun x y => FiniteLaw.dot (V x) (V y)) (fun x => FiniteLaw.dot (V (x a)) (V (x b)))
    hb μ (by norm_num : (0:ℝ) ≤ 1)
    (fun x y => FiniteLaw.abs_dot_le_one _ _ (hV x) (hV y))
    (fun x => FiniteLaw.abs_dot_le_one _ _ (hV _) (hV _))

/-- Nonnegative three-copy control for the actual random-reservoir root law.
No integrability side conditions or covariance estimates are assumed. -/
theorem root_model_decorrelation_bound (hd : d < L) (hab : splitDepth S a b = d)
    (v : S.Internal) (hav : freshSplitDepth S v a = d) (hbv : freshSplitDepth S v b = d)
    (huniq : ∀ c, splitDepth S a c = d → c = b)
    (hm : Monotone m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last L) = 1) :
    (-gamma S m v)*(∫ z, rootConditionalEnergy T Q (fun j => m j.succ) base old d V z ∂μ) ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
      pairRootCovariance μ (rootAlphabet (Ω := Ω) (A := A)) L d N
        (rootTower T Q (fun j => m j.succ) base old) (rootVector V) m S a b := by
  apply root_decorrelation_bound μ (rootAlphabet (Ω := Ω) (A := A)) L d N
    (rootTower T Q (fun j => m j.succ) base old) (rootVector V) m S a b hd hab v hav hbv hm hp hend
  · intro z x i; exact hV _ i
  · intro z c hc x; rw [huniq c hc]
  · exact integrable_rootConditionalEnergy T Q (fun j => m j.succ) base old d V hb μ hd hV
  · exact integrable_rootPair_square T Q m base old S a b V hb hV μ
  · exact integrable_rootPair_history T Q m base old S a b d V hb hV μ

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
