import OAI.Probability.DilutedSpin.ExternalRoot
import OAI.Probability.DilutedSpin.PhysicalPairConnection

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

noncomputable def pairOverlap (S : PrescribedTree (L+1)) (a b : S.Leaf)
    (read : Site N → FinitePath Ω (L+1) → Spin) (x : S.Leaf → FinitePath Ω (L+1)) : ℝ :=
  FiniteLaw.dot (readVector read (x a)) (readVector read (x b))

omit [Fintype Ω] in
lemma pairOverlap_bound (S : PrescribedTree (L+1)) (a b : S.Leaf)
    (read : Site N → FinitePath Ω (L+1) → Spin) (x) : |pairOverlap S a b read x| ≤ 1 :=
  FiniteLaw.abs_dot_le_one _ _ (readVector_bound read _) (readVector_bound read _)

variable (S : PrescribedTree (L+1)) (a b : S.Leaf) (T : KernelTower Ω (L+1))
    (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L (Site N)) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Site N → FinitePath Ω (L+1) → Spin) (d : ℕ)
    (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (Labels L (Site N))) [IsProbabilityMeasure ν] (rate score : ℝ≥0)
include hb

lemma shapeCovariance_pair :
    shapeCovariance ξ μ ν (siteLaw N) rate score S a T m base old read (pairSplitTest d) true
      (pairOverlap S a b read) =
    pairRootCovariance (fullRootLaw ξ μ ν rate score)
      (rootAlphabet (Ω := Ω) (A := fun i : Labels L (Site N) => Alphabet i.1.1))
      (L+1) d (max N 1) (rootTower T (fun i => prior i.1.1) (fun j => m j.succ) base old)
      (rootVector (readVector read)) m S a b := by
  unfold shapeCovariance
  rw [shapeAverage_pair S a T m base old read d _ hb (by norm_num : (0:ℝ) ≤ 1)
      (pairOverlap_bound S a b read) ξ μ ν rate score,
    shapeAverage_pair S a T m base old read d _ hb (by norm_num : (0:ℝ) ≤ 1)
      (fun _ => by simp : ∀ _, |(1:ℝ)| ≤ 1) ξ μ ν rate score]
  rfl

lemma integrable_overlap_square (rootμ : Measure (FullRootState Y X (Labels L (Site N)) M))
    [IsFiniteMeasure rootμ] : Integrable (fun z =>
      (S.sampleLaw (rootTower T (fun i => prior i.1.1) (fun j => m j.succ) base old z)).expect
      (fun x => FiniteLaw.dot (rootVector (readVector read) z (S.pathAt a x))
        (rootVector (readVector read) z (S.pathAt b x))^2)) rootμ := by
  apply integrable_rootTreeMean T (fun i => prior i.1.1) (fun j => m j.succ) base old hb
    S (fun x => pairOverlap S a b read x ^ 2) rootμ
  intro x
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_one_iff_abs_le_one _).mpr (pairOverlap_bound S a b read x)

/-- Physical singleton covariance bound. The only tree assumptions here are
positional: exactly one eligible second leaf, and an actual common fork. All
root integrability obligations are discharged for the true reservoir. -/
theorem shape_energy_bound (hd : d < L+1) (hab : splitDepth S a b = d)
    (v : S.Internal) (hav : freshSplitDepth S v a = d) (hbv : freshSplitDepth S v b = d)
    (huniq : ∀ c, splitDepth S a c = d → c = b)
    (hm : Monotone m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last (L+1)) = 1) :
    (-gamma S m v) * (∫ z,
      rootConditionalEnergy T (fun i => prior i.1.1) (fun j => m j.succ) base old d (readVector read) z
        ∂fullRootLaw ξ μ ν rate score) ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
      shapeCovariance ξ μ ν (siteLaw N) rate score S a T m base old read (pairSplitTest d) true
        (pairOverlap S a b read) := by
  have hi := root_model_decorrelation_bound T (fun i => prior i.1.1) m base old S a b d
    (readVector read) hb (readVector_bound read) (fullRootLaw ξ μ ν rate score)
    hd hab v hav hbv huniq hm hp hend
  have he := shapeCovariance_pair S a b T m base old read d hb ξ μ ν rate score
  exact hi.trans_eq (congrArg (fun x => (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+x) he.symm)

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
