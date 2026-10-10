import OAI.Probability.DilutedSpin.QSubsetDeviation

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance physicalShapeErrorDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
variable {p L : ℕ}

noncomputable def physicalTreeDeviation (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) : ℝ :=
  overlapDeviation
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

lemma physicalTreeDeviation_le_variance (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) {t : ℝ} (ht : 0<t) :
    physicalTreeDeviation M C H N L u T ≤ physicalTreeVariance M C H N L u T/(2*t)+t/2 := by
  unfold physicalTreeDeviation physicalTreeVariance
  exact root_overlapDeviation_le_variance _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i) ht

noncomputable def physicalShapeDeviation (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) : ℝ :=
  shapeDeviation
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

lemma physicalShapeDeviation_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) :
    0 ≤ physicalShapeDeviation M C H N L u T := shapeDeviation_nonneg _ _ _ _ _

lemma physicalShapeDeviation_qExpect_le (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) {t : ℝ} (ht : 0<t) (k : ℕ) :
    qExpect (grid (L+1) 0 (L+1)) (physicalShapeDeviation M C H N L u) k (single (L+1)) ≤
      (2:ℝ)^(k+1)*(qExpect (grid (L+1) 0 (L+1))
        (subtreePotential (k+1) (physicalTreeVariance M C H N L u)) k (single (L+1))/(2*t)+t/2) := by
  apply qExpect_shapeDeviation_le _ _ _ _ _ (physicalTreeVariance_nonneg M C H N L u) ht
  exact fun T => physicalTreeDeviation_le_variance M C H N L u T ht

/-- The complete finite-shape MAD error for the actual selected reservoir tends
 to zero. This is the error required by the empirical pattern comparison. -/
theorem physicalShapeError_tendsto (M : Model p) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (k : ℕ) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (physicalShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))) atTop)
      atTop (𝓝 0) := by
  apply doubleLimit_young _ (fun L n => qExpect (grid (L+1) 0 (L+1))
    (subtreePotential (k+1) (physicalTreeVariance M C H (Ns L n+1) L (us L n)))
    k (single (L+1))) ((2:ℝ)^(k+1)) (by positivity)
  · intro L n
    exact qExpect_nonneg _ (grid_strictMono (by omega)).monotone grid_nonneg
      _ (physicalShapeDeviation_nonneg _ _ _ _ _ _) _ _
  · intro L
    exact qExpect_subtree_bounded (k+1) k _ (fun _ _ => physicalTreeVariance_le_one _ _ _ _ _ _ _)
  · intro t ht L n
    exact physicalShapeDeviation_qExpect_le _ _ _ _ _ _ ht k
  · exact physicalSubtree_limsup_tendsto M C H Ns us hcontrol (k+1) k

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped Topology BigOperators
namespace FiniteLaw
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (Q : (z : Z) → FiniteLaw (Ω z))
    (f : (z : Z) → Ω z → ℝ)
lemma mixedDeviation_le_two (hf : ∀ z x, |f z x|≤1) : mixedDeviation μ Ω Q f≤2 := by
  have he : |∫ z, (Q z).expect (f z) ∂μ|≤1 :=
    abs_integral_le_bound (fun z => (Q z).abs_expect_le (hf z))
  apply (le_abs_self _).trans
  apply abs_integral_le_bound
  intro z
  apply (Q z).abs_expect_le
  intro x
  rw [abs_abs]
  exact (abs_sub _ _).trans (by linarith [hf z x])
end FiniteLaw
namespace PrescribedTree
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}
lemma shapeDeviation_bound (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (S : PrescribedTree n)
    (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ)
    (hV : ∀ z y i, |V z y i|≤1) : shapeDeviation μ Ω S K V≤(2:ℝ)^S.leaves*2 := by
  classical
  unfold shapeDeviation
  calc
    _ ≤ ∑ _A : Finset S.Leaf, (2:ℝ) := by
      apply Finset.sum_le_sum
      intro A _
      split_ifs
      · exact FiniteLaw.mixedDeviation_le_two μ _ _ _
          (fun z w => subsetOverlap_bound S A (V z) (hV z) w)
      · norm_num
    _ = _ := by simp [card_leaf]

lemma qExpect_shape_bound {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (F : PrescribedTree n → ℝ) (hF : ∀ S, F S≤(2:ℝ)^S.leaves*2)
    (k : ℕ) : qExpect m F k (single n) ≤ (2:ℝ)^(k+1)*2 := by
  have hh := qExpect_mono_leaves m hm hpos F (fun _ => (2:ℝ)^(k+1)*2) k (single n)
    (fun S hS => by simpa only [hS,leaves_single,Nat.add_comm 1 k] using hF S)
  simpa only [qExpect_const m hroot hend] using hh
end PrescribedTree

lemma limsup_le_of_vanishing_error (f g e : ℕ → ℝ)
    (hf : ∀ n, 0≤f n) (hg : IsBoundedUnder (·≤·) atTop g)
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ n, f n≤g n+e n) :
    limsup f atTop≤limsup g atTop := by
  have hle (t : ℝ) (ht : 0<t) : limsup f atTop≤limsup g atTop+2*t := by
    have hgf : ∀ᶠ n in atTop, g n<limsup g atTop+t :=
      eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ht) hg
    have hef : ∀ᶠ n in atTop, e n<t := he.eventually (Iio_mem_nhds ht)
    apply limsup_le_of_le (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall hf).frequently))
    filter_upwards [hgf,hef] with n hgn hen
    linarith [h n]
  have hc : ContinuousAt (fun t : ℝ => limsup g atTop+2*t) 0 := by fun_prop
  have hh := ge_of_tendsto (hc.continuousWithinAt.tendsto (s := Set.Ioi 0))
    (eventually_nhdsWithin_of_forall (fun t ht => hle t ht))
  simpa using hh
end DilutedSpinGlass

end

end OAI
