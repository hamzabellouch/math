import OAI.Probability.DilutedSpin.ConvexBounds

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass
open MeasureTheory Set

theorem measurableEmbedding_sigmaMk {I : Type*} {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] (i : I) :
    MeasurableEmbedding (Sigma.mk i : X i → Sigma X) where
  injective := sigma_mk_injective
  measurable := measurable_sigmaMk i
  measurableSet_image' := by
    intro s hs
    change MeasurableSet[⨅ j, (inferInstance : MeasurableSpace (X j)).map (Sigma.mk j)] _
    rw [MeasurableSpace.measurableSet_iInf]
    intro j
    change MeasurableSet ((Sigma.mk j) ⁻¹' (Sigma.mk i '' s))
    by_cases h : j = i
    · subst j
      rw [Set.preimage_image_eq _ sigma_mk_injective]
      exact hs
    · have he : ((Sigma.mk j) ⁻¹' (Sigma.mk i '' s)) = ∅ := by
        ext x
        simp only [mem_preimage,mem_image,mem_empty_iff_false,iff_false,not_exists]
        intro y hy
        exact h (congrArg Sigma.fst hy.2).symm
      rw [he]
      exact MeasurableSet.empty

/-- Countable disjoint root laws retain joint parameter measurability. -/
theorem measurable_sigmaProd {I : Type*} [Countable I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    {f : (i : I) → X i → A → Y}
    (hf : ∀ i, Measurable (fun z : X i × A => f i z.1 z.2)) :
    Measurable (fun z : Sigma X × A => f z.1.1 z.1.2 z.2) := by
  intro s hs
  have he : (fun z : Sigma X × A => f z.1.1 z.1.2 z.2) ⁻¹' s =
      ⋃ i, (Prod.map (Sigma.mk i) id) '' ((fun z : X i × A => f i z.1 z.2) ⁻¹' s) := by
    ext z
    rcases z with ⟨⟨i,x⟩,a⟩
    constructor
    · intro h
      exact mem_iUnion.mpr ⟨i, ⟨(x,a),h,rfl⟩⟩
    · intro h
      rcases mem_iUnion.mp h with ⟨j,w,hw,he⟩
      have hh : (fun z : Sigma X × A => f z.1.1 z.1.2 z.2) (Prod.map (Sigma.mk j) id w) ∈ s := hw
      rw [he] at hh
      exact hh
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  exact ((measurableEmbedding_sigmaMk i).prodMap MeasurableEmbedding.id).measurableSet_image'
    (hf i hs)

end DilutedSpinGlass

namespace DilutedSpinGlass.KernelTower
open MeasureTheory ProbabilityTheory
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_correctedPerturbLog {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    {base : X → FinitePath Ω L → ℝ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hbase : ∀ y, Measurable (fun x => base x y))
    (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u) :
    Measurable (fun x => correctedPerturbLog T m (base x) (D x) (E x) (t x) (u x)) := by
  apply (measurable_backwardLog L T m (measurable_perturbLog hbase hD hE ht hu)).add
  exact (hu.pow_const 2).const_mul _

theorem measurable_correctedPerturbScore {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    {base : X → FinitePath Ω L → ℝ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hbase : ∀ y, Measurable (fun x => base x y))
    (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u) :
    Measurable (fun x => correctedPerturbScore T m (base x) (D x) (E x) (t x) (u x)) := by
  apply (measurable_path_expect L T m (measurable_perturbLog hbase hD hE ht hu)
    (measurable_perturbScore hD hE ht hu)).add
  exact hu.const_mul _

omit [MeasurableSpace X] in
theorem correctedPerturbScore_bound {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    |correctedPerturbScore T m base D E t u| ≤ 3*n := by
  unfold correctedPerturbScore
  have h1 := (law L (tilt L T m (perturbLog base D E t u))).abs_expect_le
    (perturbScore_bound D E hD hE ht hu)
  have h3 : |4*(n:ℝ)*u| ≤ (n : ℝ) := by
    rw [abs_mul,abs_of_nonneg (by positivity)]
    nlinarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have h4 := abs_add_le
    ((law L (tilt L T m (perturbLog base D E t u))).expect (perturbScore D E t u)) (4*n*u)
  linarith

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)

theorem familyPoisson_count_memLp :
    MemLp (fun z : Sigma X => (z.1 : ℝ)) 2 (familyLaw (poissonMeasure r) ν) := by
  apply familyPoisson_memLp_linear ν r (fun _ => measurable_const) (A := 0) (B := 1)
  intro n x
  simp

theorem familyPoisson_count_variance :
    variance (fun z : Sigma X => (z.1 : ℝ)) (familyLaw (poissonMeasure r) ν) = r := by
  rw [variance_eq_integral (familyPoisson_count_memLp ν r).aemeasurable,
    familyPoisson_count_mean]
  rw [integral_familyLaw (poissonMeasure r) ν (fun n _ => ((n : ℝ)-r)^2)
    (fun _ => measurable_const) ((familyPoisson_count_memLp ν r).sub (memLp_const (r : ℝ))).integrable_sq]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,poisson_variance]

theorem familyPoisson_count_deviation :
    (∫ z : Sigma X, |(z.1 : ℝ)-r| ∂familyLaw (poissonMeasure r) ν) ≤ Real.sqrt r := by
  have h := integral_deviation_le_sqrt_variance (familyLaw (poissonMeasure r) ν)
    (familyPoisson_count_memLp ν r)
  rwa [familyPoisson_count_mean,familyPoisson_count_variance] at h

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {X Ω : ℕ → Type} [∀ n, MeasurableSpace (X n)] [∀ n, Fintype (Ω n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)
    (L : ℕ) (T : ∀ n, KernelTower (Ω n) L) (m : Fin L → ℝ)
    (base : ∀ n, X n → FinitePath (Ω n) L → ℝ)
    (D E : ∀ n, X n → Fin n → FinitePath (Ω n) L → ℝ)

/-- The convex concentration estimate instantiated with the literal corrected
score of the marked hierarchy and its random-dimensional Poisson root law.
The variance premise is precisely the separate Efron--Stein/count estimate. -/
theorem poisson_corrected_score_root_bound
    (hm : ∀ i, 0 < m i)
    (hb : ∀ n y, Measurable (fun x => base n x y))
    (hD : ∀ n q y, Measurable (fun x => D n x q y))
    (hE : ∀ n q y, Measurable (fun x => E n x q y))
    (hDb : ∀ n x q y, |D n x q y| ≤ 1)
    (hEb : ∀ n x q y, |E n x q y| ≤ 1)
    {t a b ρ V : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4))
    (hLp : ∀ u ∈ Ioo (-(1:ℝ)/4) (1/4), MemLp (fun z : Sigma X =>
      KernelTower.correctedPerturbLog (T z.1) m (base z.1 z.2) (D z.1 z.2) (E z.1 z.2) t u)
        2 (familyLaw (poissonMeasure r) ν))
    (hv : ∀ u ∈ Icc (a-ρ) (b+ρ), variance (fun z : Sigma X =>
      KernelTower.correctedPerturbLog (T z.1) m (base z.1 z.2) (D z.1 z.2) (E z.1 z.2) t u)
        (familyLaw (poissonMeasure r) ν) ≤ V) :
    (∫ u in a..b, (∫ z : Sigma X,
      |KernelTower.correctedPerturbScore (T z.1) m (base z.1 z.2) (D z.1 z.2) (E z.1 z.2) t u -
        ∫ w : Sigma X, KernelTower.correctedPerturbScore (T w.1) m (base w.1 w.2)
          (D w.1 w.2) (E w.1 w.2) t u ∂familyLaw (poissonMeasure r) ν|
      ∂familyLaw (poissonMeasure r) ν))/(b-a) ≤
        4*Real.sqrt V/ρ+12*ρ*(r : ℝ)/(b-a) := by
  let F (z : Sigma X) (u : ℝ) :=
    KernelTower.correctedPerturbLog (T z.1) m (base z.1 z.2) (D z.1 z.2) (E z.1 z.2) t u
  let G (z : Sigma X) (u : ℝ) :=
    KernelTower.correctedPerturbScore (T z.1) m (base z.1 z.2) (D z.1 z.2) (E z.1 z.2) t u
  have hFm (u : ℝ) : Measurable (fun z => F z u) := measurable_sigmaUncurry (fun n =>
    KernelTower.measurable_correctedPerturbLog (T n) m (hb n) (hD n) (hE n)
      measurable_const measurable_const)
  have hGm : Measurable (fun z : Sigma X × ℝ => G z.1 z.2) := by
    apply measurable_sigmaProd (f := fun n x u =>
      KernelTower.correctedPerturbScore (T n) m (base n x) (D n x) (E n x) t u)
    intro n
    exact KernelTower.measurable_correctedPerturbScore (T n) m
      (fun y => (hb n y).comp measurable_fst) (fun q y => (hD n q y).comp measurable_fst)
      (fun q y => (hE n q y).comp measurable_fst) measurable_const measurable_snd
  have hfc (z : Sigma X) : ConvexOn ℝ (Ioo (-(1:ℝ)/4) (1/4)) (F z) :=
    (KernelTower.correctedPerturbLog_convex (T z.1) m hm (base z.1 z.2)
      (D z.1 z.2) (E z.1 z.2) (hDb z.1 z.2) (hEb z.1 z.2) ht).subset
      Ioo_subset_Icc_self (convex_Ioo _ _)
  have hu (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) : |u| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [h.1],h.2.le⟩
  have hbound (z : Sigma X) (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :
      |G z u| ≤ 3*(z.1 : ℝ) := KernelTower.correctedPerturbScore_bound
    (T z.1) m (base z.1 z.2) (D z.1 z.2) (E z.1 z.2) (hDb z.1 z.2) (hEb z.1 z.2) ht (hu u h)
  have hd (z : Sigma X) (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :
      HasDerivAt (F z) (G z u) u := by
    apply KernelTower.hasDerivAt_correctedPerturbLog _ _ (fun i => ne_of_gt (hm i))
    intro q y
    have hh := KernelTower.perturb_factor_lower (D z.1 z.2) (E z.1 z.2)
      (hDb z.1 z.2) (hEb z.1 z.2) ht (hu u h) q y
    linarith
  have hh := root_derivative_integral_bound (familyLaw (poissonMeasure r) ν)
    isOpen_Ioo (convex_Ioo _ _) hFm hGm hfc hLp
    ((familyPoisson_count_integrable ν r).const_mul 3) hbound hd hab hρ hJ hv
  rw [integral_const_mul,familyPoisson_count_mean] at hh
  convert hh using 1; ring

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {I : Type*} [MeasurableSpace I] (μ : Measure I) [IsProbabilityMeasure μ]

/-- Efron--Stein plus the independent Poisson count, on the genuine dependent
root probability law used by the derivative concentration estimate. -/
theorem familyPoisson_variance_le (r : ℝ≥0)
    {F : (n : ℕ) → RootPath I n → ℝ} {A B C D : ℝ}
    (hF : ∀ n, Measurable (F n)) (hb : ∀ n x, |F n x| ≤ A+B*n)
    (hD : 0 ≤ D)
    (hrep : ∀ n (i : Fin n) x y, |F n x-F n (replaceRoot n x i y)| ≤ C)
    (hadd : ∀ n x y, |F (n+1) (x,y)-F n y| ≤ D) :
    variance (fun z : Sigma (RootPath I) => F z.1 z.2)
      (familyLaw (poissonMeasure r) (fun n => rootLaw n (fun _ => μ))) ≤
        (C^2/2+D^2)*(r : ℝ) := by
  let ν := fun n => rootLaw n (fun _ : Fin n => μ)
  have hLp := familyPoisson_memLp_linear ν r hF hb
  have hmean : (∫ z : Sigma (RootPath I), F z.1 z.2 ∂familyLaw (poissonMeasure r) ν) =
      ∫ n, rootAverage μ F n ∂poissonMeasure r :=
    integral_familyLaw (poissonMeasure r) ν F hF (hLp.integrable (by norm_num))
  rw [variance_eq_integral hLp.aemeasurable]
  change (∫ z : Sigma (RootPath I),
    (F z.1 z.2-(∫ z : Sigma (RootPath I), F z.1 z.2 ∂familyLaw (poissonMeasure r) ν))^2
    ∂familyLaw (poissonMeasure r) ν) ≤ _
  rw [integral_familyLaw (poissonMeasure r) ν
    (fun n x => (F n x-(∫ z : Sigma (RootPath I), F z.1 z.2 ∂familyLaw (poissonMeasure r) ν))^2)
    (fun n => ((hF n).sub measurable_const).pow_const 2)
    ((hLp.sub (memLp_const _)).integrable_sq),hmean]
  exact poisson_random_root_variance μ r hF hb hD hrep hadd

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω A I : Type} [Fintype Ω] [Fintype A] [MeasurableSpace I] {L : ℕ}

/-- The random-count convex correction has its own addition/deletion cost.
Replacement of an existing root point is unaffected. -/
theorem correctedMarkedRoot_family_variance
    (μ : Measure I) [IsProbabilityMeasure μ] (r : ℝ≥0)
    (T : KernelTower Ω L) (Q : Fin L → FiniteLaw A)
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ)
    (factor : I → FinitePath Ω L → FinitePath A L → ℝ)
    (hfmeas : ∀ x y, Measurable (fun i => factor i x y)) {B C : ℝ}
    (hb : ∀ y, |base y| ≤ B) (hC : 0 ≤ C)
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) (c : ℝ) :
    variance (fun z : Sigma (RootPath I) =>
      markedRoot T Q m base (rootArray z.1 z.2) factor+c*z.1)
      (familyLaw (poissonMeasure r) (fun n => rootLaw n (fun _ => μ))) ≤
        (2*C^2+(C+|c|)^2)*(r : ℝ) := by
  let F := fun n (x : RootPath I n) => markedRoot T Q m base (rootArray n x) factor+c*n
  have hF (n : ℕ) : Measurable (F n) :=
    (measurable_markedRoot T Q m base factor hfmeas n).add measurable_const
  have hbound (n : ℕ) (x : RootPath I n) : |F n x| ≤ B+(C+|c|)*n := by
    dsimp only [F]
    have h := markedRoot_uniform_bound T Q m hm base factor hb hf n x
    calc
      _ ≤ |markedRoot T Q m base (rootArray n x) factor|+|c*(n:ℝ)| := abs_add_le _ _
      _ ≤ B+C*n+|c| * n := by rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]; linarith
      _ = B+(C+|c|)*n := by ring
  have hrep (n : ℕ) (i : Fin n) (x : RootPath I n) (y : I) :
      |F n x-F n (replaceRoot n x i y)| ≤ 2*C := by
    dsimp only [F]
    rw [add_sub_add_right_eq_sub,rootArray_replace,abs_sub_comm]
    apply markedRoot_update_bound T Q m hm
    intro z w
    have h := abs_sub (Real.log (factor y z w)) (Real.log (factor (rootArray n x i) z w))
    linarith [hf y z w,hf (rootArray n x i) z w]
  have hadd (n : ℕ) (x : I) (y : RootPath I n) : |F (n+1) (x,y)-F n y| ≤ C+|c| := by
    change |markedRoot T Q m base (Fin.cons x (rootArray n y)) factor+c*(n+1:ℕ)-
      (markedRoot T Q m base (rootArray n y) factor+c*n)| ≤ _
    rw [Nat.cast_add,Nat.cast_one]
    have h := markedRoot_cons_bound T Q m hm base (rootArray n y) x factor (hf x)
    calc
      _ = |markedRoot T Q m base (Fin.cons x (rootArray n y)) factor-
        markedRoot T Q m base (rootArray n y) factor+c| := by congr 1; ring
      _ ≤ |markedRoot T Q m base (Fin.cons x (rootArray n y)) factor-
        markedRoot T Q m base (rootArray n y) factor|+|c| := abs_add_le _ _
      _ ≤ C+|c| := add_le_add h le_rfl

  have h := familyPoisson_variance_le μ r hF hbound (add_nonneg hC (abs_nonneg c)) hrep hadd
  convert h using 1; ring

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

noncomputable def rootDeviation (f : X → ℝ) : ℝ := ∫ x, |f x-∫ y, f y ∂μ| ∂μ

omit [IsProbabilityMeasure μ] in
theorem rootDeviation_nonneg (f : X → ℝ) : 0 ≤ rootDeviation μ f :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem rootDeviation_add_le {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    rootDeviation μ (f+g) ≤ rootDeviation μ f+rootDeviation μ g := by
  unfold rootDeviation
  simp only [Pi.add_apply]
  rw [integral_add hf hg]
  have hi := integral_mono ((hf.add hg).sub (integrable_const _)).abs
    (((hf.sub (integrable_const _)).abs).add ((hg.sub (integrable_const _)).abs))
    (fun x => (show |f x+g x-((∫ y, f y ∂μ)+(∫ y, g y ∂μ))| ≤
      |f x-(∫ y, f y ∂μ)|+|g x-(∫ y, g y ∂μ)| by
        have heq : f x+g x-((∫ y, f y ∂μ)+(∫ y, g y ∂μ)) =
            (f x-(∫ y, f y ∂μ))+(g x-(∫ y, g y ∂μ)) := by ring
        rw [heq]
        exact abs_add_le _ _))
  have hr := integral_add (hf.sub (integrable_const (∫ y, f y ∂μ))).abs
    (hg.sub (integrable_const (∫ y, g y ∂μ))).abs
  dsimp only [Pi.add_apply,Pi.sub_apply] at hr hi
  rw [hr] at hi
  exact hi

omit [IsProbabilityMeasure μ] in
theorem rootDeviation_smul (c : ℝ) (f : X → ℝ) :
    rootDeviation μ (fun x => c*f x) = |c| * rootDeviation μ f := by
  simp only [rootDeviation,integral_const_mul,← mul_sub,abs_mul]

theorem rootDeviation_sub_le {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    rootDeviation μ (f-g) ≤ rootDeviation μ f+rootDeviation μ g := by
  have h := rootDeviation_add_le μ hf (hg.const_mul (-1))
  rw [rootDeviation_smul] at h
  have heq : f-g = f+(fun x => (-1:ℝ)*g x) := by
    ext x
    simp [sub_eq_add_neg]
  rw [heq]
  simpa only [abs_neg,abs_one,one_mul] using h

end DilutedSpinGlass

namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory Set
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem measurable_rootDeviation {G : X → ℝ → ℝ}
    (hG : Measurable (fun z : X × ℝ => G z.1 z.2)) :
    Measurable (fun u => rootDeviation μ (fun x => G x u)) := by
  have hk : Measurable (fun u => ∫ x, G x u ∂μ) :=
    (hG.stronglyMeasurable.integral_prod_left').measurable
  exact ((hG.sub (hk.comp measurable_snd)).abs.stronglyMeasurable.integral_prod_left').measurable

theorem rootDeviation_bound {f B : X → ℝ} (hf : Measurable f)
    (hB : Integrable B μ) (hb : ∀ x, |f x| ≤ B x) :
    rootDeviation μ f ≤ 2*(∫ x, B x ∂μ) := by
  have hi : Integrable f μ := hB.mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  have hh := integral_mono ((hi.sub (integrable_const _)).abs)
    (hB.add (integrable_const |∫ x, f x ∂μ|))
      (fun x => (abs_sub _ _).trans (add_le_add (hb x) le_rfl))
  simp only [Pi.add_apply,integral_add hB (integrable_const _),integral_const,
    probReal_univ,smul_eq_mul,one_mul] at hh
  have hav : |∫ x, f x ∂μ| ≤ ∫ x, B x ∂μ :=
    (abs_integral_le_integral_abs).trans (integral_mono hi.abs hB hb)
  simp only [Pi.sub_apply] at hh
  dsimp only [rootDeviation]
  linarith

theorem intervalIntegrable_rootDeviation {G : X → ℝ → ℝ}
    (hG : Measurable (fun z : X × ℝ => G z.1 z.2)) {B : X → ℝ}
    (hB : Integrable B μ) {a b : ℝ} (hab : a ≤ b)
    (hb : ∀ x u, u ∈ Icc a b → |G x u| ≤ B x) :
    IntervalIntegrable (fun u => rootDeviation μ (fun x => G x u)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply Measure.integrableOn_of_bounded
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measurable_rootDeviation μ hG).aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro u hu
  rw [Real.norm_eq_abs,abs_of_nonneg (rootDeviation_nonneg μ _)]
  exact rootDeviation_bound μ (hG.comp (measurable_id.prodMk measurable_const)) hB
    (fun x => hb x u ⟨hu.1.le,hu.2⟩)

end DilutedSpinGlass

end

end OAI
