import OAI.MathematicalPhysics.Boltzmann.Branching.HalfGaussianMoment
import OAI.MathematicalPhysics.Boltzmann.Branching.HotCanonicalFamily
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPhysicalSource
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedHotRegularity
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetSolutions
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetStability
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Jets.AnnularEnvelopes
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreMomentBound
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum

namespace OAI

section

/-! # Countably labeled periodic copies of the finite cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

instance : Countable JetLattice.Label := Function.Injective.countable
  (f := fun i : JetLattice.Label => (i.annulus,i.positive,i.lattice)) (by
    intro i j h
    cases i; cases j
    simpa using h)

def displacement (n : JetLattice.Lattice) : Space :=
  (JetLattice.transverseShift n,JetLattice.axialShift n)

def color (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (i : JetLattice.Label) (p : JetPrototype.Phase) : ℝ :=
  if i.annulus < N then
    JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive) (shift (displacement i.lattice) p) / H q p.2
  else 0

def seed (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (p : JetPrototype.Phase) : ℝ :=
  ∑' i, color s₀ η K α γ d₀ q N i p

theorem measurable_color (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (i : JetLattice.Label) :
    Measurable (color s₀ η K α γ d₀ q N i) := by
  unfold color
  split_ifs
  · exact ((JetDatum.term_measurable s₀ η K α γ d₀ _).comp (measurable_shift _)).div
      ((ChartKernel.measurable_H q).comp measurable_snd)
  · exact measurable_const

theorem measurable_seed (s₀ η K α γ d₀ q : ℝ) (N : ℕ) : Measurable (seed s₀ η K α γ d₀ q N) :=
  Measurable.tsum (measurable_color s₀ η K α γ d₀ q N)

theorem color_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ q : ℝ) (N : ℕ) (i : JetLattice.Label) (p : JetPrototype.Phase) :
    0 ≤ color s₀ η K α γ d₀ q N i p := by
  unfold color
  split_ifs
  · exact div_nonneg (JetDatum.term_nonneg hs₀ hK hd₀ η α γ _ _) (H_nonneg _ _)
  · exact le_rfl

private theorem in_enlargement {s₀ η K α γ d₀ q : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) {i : JetLattice.Label} {p : JetPrototype.Phase}
    (hp : color s₀ η K α γ d₀ q N i p ≠ 0) :
    PlaneChart.join p.1.1 p.1.2 ∈ JetLattice.spatialEnlargement s₀ η 0 i := by
  have hi : i.annulus < N := by
    by_contra h
    exact hp (by simp only [color,ite_eq_right h])
  have hn : JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
      (shift (displacement i.lattice) p) ≠ 0 := by
    intro h
    exact hp (by simp only [color,ite_eq_left hi,h,zero_div])
  have hsp := JetSupport.initial_spatial_support η K α γ
    (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) i.positive hn
  constructor
  · rw [PlaneChart.transverse_join]
    apply Metric.mem_cthickening_of_dist_le _ _ _ _ hsp.1
    simpa [shift,displacement,jetScale] using (enlargementWidth_pos hη
      (DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1))).le
  · have hax : |p.1.2-JetLattice.axialShift i.lattice| < 1/8 := hsp.2
    change |axial (PlaneChart.join p.1.1 p.1.2)-JetLattice.axialShift i.lattice| ≤ _
    rw [PlaneChart.axial_join]
    linarith

theorem color_disjoint {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ)
    (p : JetPrototype.Phase) (i j : JetLattice.Label) (hij : i ≠ j)
    (hi : color s₀ η K α γ d₀ q N i p ≠ 0) : color s₀ η K α γ d₀ q N j p = 0 := by
  by_contra hj
  exact hij (JetLattice.common_point_label hs₀ hsmax hη hηmax (by norm_num : (0:ℝ) ≤ 1/32)
    (in_enlargement hs₀ hη hi) (in_enlargement hs₀ hη hj))

theorem color_summable {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ) (p : JetPrototype.Phase) :
    Summable (fun i => color s₀ η K α γ d₀ q N i p) :=
  JetSeries.summable_single_support (color_disjoint hs₀ hsmax hη hηmax K α γ d₀ q N p)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Finite weighted bounds for the countably labeled periodic seed -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem coefficient_le_amplitude {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K)
    (hd₀ : 0 ≤ d₀) (η : ℝ) {N : ℕ} (i : JetDatum.Index)
    (hi : i ∈ JetFiniteGaussian.indices N) :
    JetFiniteGaussian.coefficient s₀ η K d₀ i.1 ≤ JetFiniteGaussian.amplitude s₀ η K d₀ N := by
  classical
  have h : JetFiniteGaussian.coefficient s₀ η K d₀ i.1 ≤
      ∑ j ∈ JetFiniteGaussian.indices N, JetFiniteGaussian.coefficient s₀ η K d₀ j.1 :=
    Finset.single_le_sum (fun (j : JetDatum.Index) _ =>
      JetFiniteGaussian.coefficient_nonneg hs₀ hK hd₀ η j.1) hi
  exact h.trans (le_add_of_nonneg_left zero_le_one)

theorem color_bound {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (γ q : ℝ) (N : ℕ) (i : JetLattice.Label) (p : JetPrototype.Phase) :
    color s₀ η K α γ d₀ q N i p ≤ WeightedFiniteSeed.amplitude s₀ η K d₀ N := by
  classical
  unfold color
  split_ifs with hi
  · apply (div_le_iff₀ (H_pos q p.2)).mpr
    have hmem : (i.annulus,i.positive) ∈ JetFiniteGaussian.indices N := by
      simp [JetFiniteGaussian.indices,hi]
    have hcoef := coefficient_le_amplitude hs₀ hK hd₀.le η (i.annulus,i.positive) hmem
    calc
      _ ≤ JetFiniteGaussian.coefficient s₀ η K d₀ i.annulus * JetGaussianMoments.kernel 2 p.2 :=
        JetFiniteGaussian.term_bound hs₀ hsmax hη hK hd₀ hwidth hα hαmax γ
          (i.annulus,i.positive) (WeightedTranslation.shift (displacement i.lattice) p)
      _ ≤ JetFiniteGaussian.amplitude s₀ η K d₀ N * JetGaussianMoments.kernel 2 p.2 :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
      _ ≤ JetFiniteGaussian.amplitude s₀ η K d₀ N * (tiltConstant*H q p.2) :=
        mul_le_mul_of_nonneg_left (JetGaussianEscape.gaussian_le_hot q p.2)
          (JetFiniteGaussian.amplitude_pos hs₀ hK hd₀.le η N).le
      _ = _ := by unfold WeightedFiniteSeed.amplitude; ring
  · exact (WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N).le

theorem seed_bounds {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (γ q : ℝ) (N : ℕ) (p : JetPrototype.Phase) :
    0 ≤ seed s₀ η K α γ d₀ q N p ∧
      seed s₀ η K α γ d₀ q N p ≤ WeightedFiniteSeed.amplitude s₀ η K d₀ N := by
  classical
  refine ⟨tsum_nonneg (fun i => color_nonneg hs₀ hK hd₀.le η α γ q N i p),?_⟩
  by_cases h : ∃ i, color s₀ η K α γ d₀ q N i p ≠ 0
  · obtain ⟨i,hi⟩ := h
    unfold seed
    rw [tsum_eq_single i (fun j hj => color_disjoint hs₀ hsmax hη hηmax K α γ d₀ q N p i j hj.symm hi)]
    exact color_bound hs₀ hsmax hη.le hK hd₀ hwidth hα hαmax γ q N i p
  · have hz (i) : color s₀ η K α γ d₀ q N i p = 0 := not_ne_iff.mp (not_exists.mp h i)
    simp only [seed,hz,tsum_zero]
    exact (WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N).le

theorem finite_sum_le_seed {s₀ η K d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (α γ q : ℝ) (N : ℕ) (u : Finset JetLattice.Label) (p : JetPrototype.Phase) :
    ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤ seed s₀ η K α γ d₀ q N p :=
  (color_summable hs₀ hsmax hη hηmax K α γ d₀ q N p).sum_le_tsum u
    (fun i _ => color_nonneg hs₀ hK hd₀ η α γ q N i p)

theorem physical_color_le {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ q : ℝ) (N : ℕ) (i : JetLattice.Label) (p : JetPrototype.Phase) :
    H q p.2*color s₀ η K α γ d₀ q N i p ≤
      JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive) (WeightedTranslation.shift (displacement i.lattice) p) := by
  unfold color
  split_ifs
  · rw [mul_div_cancel₀ _ (H_pos q p.2).ne']
  · simp only [mul_zero]
    exact JetDatum.term_nonneg hs₀ hK hd₀ η α γ _ _

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Exact periodicity of the labeled initial datum -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def relabel (n : JetLattice.Lattice) : JetLattice.Label ≃ JetLattice.Label where
  toFun i := ⟨i.annulus,i.positive,i.lattice+n⟩
  invFun i := ⟨i.annulus,i.positive,i.lattice-n⟩
  left_inv i := by cases i; simp
  right_inv i := by cases i; simp

theorem displacement_add (m n : JetLattice.Lattice) :
    displacement (m+n) = displacement m+displacement n := by
  apply Prod.ext
  · ext k
    simp [displacement,JetLattice.transverseShift]
  · simp [displacement,JetLattice.axialShift]

theorem shift_shift (y z : Space) (p : JetPrototype.Phase) :
    shift y (shift z p) = shift (y+z) p := by
  apply Prod.ext
  · dsimp [shift]
    abel
  · rfl

theorem color_shift (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (n : JetLattice.Lattice)
    (i : JetLattice.Label) (p : JetPrototype.Phase) :
    color s₀ η K α γ d₀ q N i (shift (displacement n) p) =
      color s₀ η K α γ d₀ q N (relabel n i) p := by
  change (if i.annulus < N then
    JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
      (shift (displacement i.lattice) (shift (displacement n) p)) / VelocityWeight.H q p.2 else 0) =
    (if i.annulus < N then
    JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
      (shift (displacement (i.lattice+n)) p) / VelocityWeight.H q p.2 else 0)
  rw [displacement_add,shift_shift]

theorem seed_periodic (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (n : JetLattice.Lattice)
    (p : JetPrototype.Phase) :
    seed s₀ η K α γ d₀ q N (shift (displacement n) p) = seed s₀ η K α γ d₀ q N p := by
  unfold seed
  simp_rw [color_shift]
  exact (relabel n).tsum_eq (fun i => color s₀ η K α γ d₀ q N i p)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The periodic finite cold seed equals the manuscript datum in the central cube -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

private theorem integer_zero_of_close {x : ℝ} {n : ℤ}
    (hx : x ∈ TorusChart.interval) (hn : |x-(n:ℝ)| < 1/4) : n = 0 := by
  by_contra h
  have hi := JetLattice.integer_distance h
  have ha : |x| ≤ 1/2 := abs_le.mpr ⟨hx.1.le,hx.2⟩
  have ht := abs_add_le ((n:ℝ)-x) x
  rw [sub_add_cancel,abs_sub_comm] at ht
  simp only [Int.cast_zero,sub_zero] at hi
  linarith

theorem term_shift_lattice_zero {s₀ η K α γ d₀ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    {i : JetDatum.Index} {n : JetLattice.Lattice} {y : Velocity} {v : Velocity}
    (hy : y ∈ TorusChart.cube)
    (hp : JetDatum.term s₀ η K α γ d₀ i
      (shift (displacement n) (JetPeriodicDatum.spatialMap y,v)) ≠ 0) : n = 0 := by
  have hsp := JetSupport.initial_spatial_support η K α γ _ _ i.2 hp
  have hnorm : ‖(transverse y-JetLattice.transverseShift n)‖ < s₀ := by
    have hh := hsp.1.1.2
    change ‖transverse y-JetLattice.transverseShift n‖ <
      Real.exp η*jetScale s₀ η i.1-gapCoefficient η*jetScale s₀ η i.1^2 at hh
    have hg : 0 ≤ gapCoefficient η*jetScale s₀ η i.1^2 :=
      mul_nonneg (gapCoefficient_pos hη).le (sq_nonneg _)
    rw [outerRadius_eq] at hh
    have hb := scale_antitone hs₀.le hη.le (Nat.zero_le i.1)
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at hb
    linarith
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · apply integer_zero_of_close (hy (Fin.last 2))
    have hz : |y (Fin.last 2)-(n (Fin.last 2):ℝ)| < 1/8 := hsp.2
    linarith
  · apply integer_zero_of_close (hy j.castSucc)
    have hc := PiLp.norm_apply_le (transverse y-JetLattice.transverseShift n) j
    change ‖y j.castSucc-(n j.castSucc:ℝ)‖ ≤ _ at hc
    rw [Real.norm_eq_abs] at hc
    exact (hc.trans_lt hnorm).trans_le (by linarith)

theorem color_central {s₀ η K α γ d₀ q : ℝ} (N : ℕ) (i : JetDatum.Index)
    (p : JetPrototype.Phase) :
    color s₀ η K α γ d₀ q N ⟨i.1,i.2,0⟩ p =
      (if i.1 < N then JetDatum.term s₀ η K α γ d₀ i p else 0)/H q p.2 := by
  have hz : displacement 0 = 0 := by
    apply Prod.ext
    · ext j; simp [displacement,JetLattice.transverseShift]
    · simp [displacement,JetLattice.axialShift]
  have hshift : shift (displacement 0) p = p := by rw [hz]; apply Prod.ext <;> simp [shift]
  simp only [color,hshift]
  split_ifs <;> simp

theorem seed_on_cube {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ)
    {y : Velocity} (hy : y ∈ TorusChart.cube) (v : Velocity) :
    seed s₀ η K α γ d₀ q N (JetPeriodicDatum.spatialMap y,v) =
      JetTruncation.truncated s₀ η K α γ d₀ N (JetPeriodicDatum.spatialMap y,v)/H q v := by
  classical
  let p : JetPrototype.Phase := (JetPeriodicDatum.spatialMap y,v)
  have hlat (i : JetLattice.Label) (hi : color s₀ η K α γ d₀ q N i p ≠ 0) : i.lattice = 0 := by
    have hN : i.annulus < N := by
      by_contra hn
      exact hi (by simp only [color,ite_eq_right hn])
    have ht : JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
        (shift (displacement i.lattice) p) ≠ 0 := by
      intro ht
      exact hi (by simp only [color,ite_eq_left hN,ht,zero_div])
    exact term_shift_lattice_zero hs₀ hsmax hη hy ht
  by_cases hex : ∃ j : JetDatum.Index, j.1 < N ∧ JetDatum.term s₀ η K α γ d₀ j p ≠ 0
  · obtain ⟨j,hjN,hj⟩ := hex
    let i : JetLattice.Label := ⟨j.1,j.2,0⟩
    have hi : color s₀ η K α γ d₀ q N i p ≠ 0 := by
      rw [color_central,ite_eq_left hjN]
      exact div_ne_zero hj (H_pos q v).ne'
    have hseed : seed s₀ η K α γ d₀ q N p = color s₀ η K α γ d₀ q N i p :=
      tsum_eq_single i (fun k hk => color_disjoint hs₀ hsmax hη hηmax K α γ d₀ q N p i k hk.symm hi)
    have htrunc : JetTruncation.truncated s₀ η K α γ d₀ N p = JetDatum.term s₀ η K α γ d₀ j p := by
      unfold JetTruncation.truncated
      rw [tsum_eq_single j]
      · exact ite_eq_left hjN
      · intro k hk
        rw [JetDatum.term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p j k hk.symm hj]
        simp
    change seed s₀ η K α γ d₀ q N p = JetTruncation.truncated s₀ η K α γ d₀ N p/H q v
    rw [hseed,htrunc,color_central,ite_eq_left hjN]
  · have htrunc : JetTruncation.truncated s₀ η K α γ d₀ N p = 0 := by
      calc
        _ = ∑' j : JetDatum.Index, (0:ℝ) := tsum_congr (fun j => ?_)
        _ = 0 := tsum_zero
      by_cases hjN : j.1 < N
      · have hj : JetDatum.term s₀ η K α γ d₀ j p = 0 := by
          by_contra hj
          exact hex ⟨j,hjN,hj⟩
        rw [ite_eq_left hjN,hj]
      · exact ite_eq_right hjN
    have hseed : seed s₀ η K α γ d₀ q N p = 0 := by
      calc
        _ = ∑' i : JetLattice.Label, (0:ℝ) := tsum_congr (fun i => ?_)
        _ = 0 := tsum_zero
      by_contra hi
      have hl := hlat i hi
      have he : i = ⟨i.annulus,i.positive,0⟩ := by cases i; simp_all
      rw [he] at hi
      rw [color_central N (i.annulus,i.positive) p] at hi
      by_cases hN : i.annulus < N
      · rw [ite_eq_left hN] at hi
        have ht : JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive) p ≠ 0 :=
          fun h => hi (by rw [h,zero_div])
        exact hex ⟨(i.annulus,i.positive),hN,ht⟩
      · exact hi (by rw [ite_eq_right hN,zero_div])
    change seed s₀ η K α γ d₀ q N p = JetTruncation.truncated s₀ η K α γ d₀ N p/H q v
    rw [hseed,htrunc,zero_div]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Periodicity of the full cold family and its hot remainder -/

noncomputable section

open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem coldLimit_shift {s₀ η K α γ d₀ q b L T : ℝ} {N : ℕ}
    {F : ℝ × JetPrototype.Phase → ℝ} (n : JetLattice.Lattice)
    (hF : pull (displacement n) F = F) (i : JetLattice.Label) :
    pull (displacement n) (coldLimit q b L T F (color s₀ η K α γ d₀ q N i)) =
      coldLimit q b L T F (color s₀ η K α γ d₀ q N (relabel n i)) := by
  rw [← coldLimit_pull,hF]
  congr 1
  funext p
  exact color_shift s₀ η K α γ d₀ q N n i p

theorem coldSum_shift {s₀ η K α γ d₀ q b L T : ℝ} {N : ℕ}
    {F : ℝ × JetPrototype.Phase → ℝ} (n : JetLattice.Lattice)
    (hF : pull (displacement n) F = F) (u : ℝ × JetPrototype.Phase) :
    (∑' i, coldLimit q b L T F (color s₀ η K α γ d₀ q N i)
      (u.1,shift (displacement n) u.2)) =
      ∑' i, coldLimit q b L T F (color s₀ η K α γ d₀ q N i) u := by
  have h (i : JetLattice.Label) : coldLimit q b L T F (color s₀ η K α γ d₀ q N i)
      (u.1,shift (displacement n) u.2) =
      coldLimit q b L T F (color s₀ η K α γ d₀ q N (relabel n i)) u :=
    congrFun (coldLimit_shift n hF i) u
  simp_rw [h]
  exact (relabel n).tsum_eq (fun i => coldLimit q b L T F (color s₀ η K α γ d₀ q N i) u)

theorem hotRemainder_shift {s₀ η K α γ d₀ q b L T : ℝ} {N : ℕ}
    {F : ℝ × JetPrototype.Phase → ℝ} (n : JetLattice.Lattice)
    (hF : pull (displacement n) F = F) :
    pull (displacement n) (hotRemainder q b L T F (color s₀ η K α γ d₀ q N)) =
      hotRemainder q b L T F (color s₀ η K α γ d₀ q N) := by
  funext u
  change F (u.1,shift (displacement n) u.2)-_ = F u-_
  rw [coldSum_shift n hF u]
  exact congrArg (fun a => a-∑' i, coldLimit q b L T F (color s₀ η K α γ d₀ q N i) u)
    (congrFun hF u)

theorem hotForcing_shift {s₀ η K α γ d₀ q b L T : ℝ} {N : ℕ}
    {F : ℝ × JetPrototype.Phase → ℝ} (n : JetLattice.Lattice)
    (hF : pull (displacement n) F = F) :
    pull (displacement n) (hotForcing q b L T F (color s₀ η K α γ d₀ q N)) =
      hotForcing q b L T F (color s₀ η K α γ d₀ q N) := by
  have hf : pull (displacement n) (forcing q b L F) = forcing q b L F := by
    rw [← forcing_pull,hF]
  funext u
  change forcing q b L F (u.1,shift (displacement n) u.2)-_ = forcing q b L F u-_
  rw [show forcing q b L F (u.1,shift (displacement n) u.2) = forcing q b L F u from congrFun hf u]
  congr 1
  have h (i) : coldForcing q b L F (coldLimit q b L T F (color s₀ η K α γ d₀ q N i))
      (u.1,shift (displacement n) u.2) =
      coldForcing q b L F (coldLimit q b L T F (color s₀ η K α γ d₀ q N (relabel n i))) u := by
    have he := coldForcing_pull q b L (displacement n) F
      (coldLimit q b L T F (color s₀ η K α γ d₀ q N i))
    rw [hF,coldLimit_shift n hF i] at he
    exact (congrFun he u).symm
  simp_rw [h]
  exact (relabel n).tsum_eq (fun i => coldForcing q b L F (coldLimit q b L T F (color s₀ η K α γ d₀ q N i)) u)

theorem familyReplacement_shift {s₀ η K α γ d₀ q b L T : ℝ} {N : ℕ}
    {F : ℝ × JetPrototype.Phase → ℝ} (n : JetLattice.Lattice)
    (hF : pull (displacement n) F = F) :
    pull (displacement n) (HotCanonical.familyReplacement F
      (fun i => coldLimit q b L T F (color s₀ η K α γ d₀ q N i))) =
      HotCanonical.familyReplacement F (fun i => coldLimit q b L T F (color s₀ η K α γ d₀ q N i)) := by
  funext u
  simp only [pull, HotCanonical.familyReplacement, HotCanonical.replacement,
    PhaseEssSup.canonical]
  rw [coldSum_shift n hF u,show F (u.1,shift (displacement n) u.2) = F u from congrFun hF u]

theorem remainderForcing_shift {s₀ η K α γ d₀ q b L T : ℝ} {N : ℕ}
    {F G : ℝ × JetPrototype.Phase → ℝ} (n : JetLattice.Lattice)
    (hF : pull (displacement n) F = F) (hG : pull (displacement n) G = G) :
    pull (displacement n) (remainderForcing q b L G
      (fun i => coldLimit q b L T F (color s₀ η K α γ d₀ q N i))) =
      remainderForcing q b L G (fun i => coldLimit q b L T F (color s₀ η K α γ d₀ q N i)) := by
  have hf : pull (displacement n) (forcing q b L G) = forcing q b L G := by
    rw [← forcing_pull,hG]
  funext u
  change forcing q b L G (u.1,shift (displacement n) u.2)-_ = forcing q b L G u-_
  rw [show forcing q b L G (u.1,shift (displacement n) u.2) = forcing q b L G u from congrFun hf u]
  congr 1
  have h (i) : coldForcing q b L G (coldLimit q b L T F (color s₀ η K α γ d₀ q N i))
      (u.1,shift (displacement n) u.2) =
      coldForcing q b L G (coldLimit q b L T F (color s₀ η K α γ d₀ q N (relabel n i))) u := by
    have he := coldForcing_pull q b L (displacement n) G
      (coldLimit q b L T F (color s₀ η K α γ d₀ q N i))
    rw [hG,coldLimit_shift n hF i] at he
    exact (congrFun he u).symm
  simp_rw [h]
  exact (relabel n).tsum_eq (fun i => coldForcing q b L G (coldLimit q b L T F (color s₀ η K α γ d₀ q N i)) u)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual labeled periodic approximation on a common local interval -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def initial (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (h₀ : JetPrototype.Phase → ℝ) (p : JetPrototype.Phase) : ℝ :=
  seed s₀ η K α γ d₀ q N p+h₀ p

theorem initial_color_bounds {s₀ η K d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (α γ q : ℝ) (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p) :
    (∀ i p, 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ initial s₀ η K α γ d₀ q N h₀ p) ∧
    (∀ u : Finset JetLattice.Label, ∀ p,
      ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤ initial s₀ η K α γ d₀ q N h₀ p) := by
  have hf (u : Finset JetLattice.Label) (p) : ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤
      initial s₀ η K α γ d₀ q N h₀ p :=
    (finite_sum_le_seed hs₀ hsmax hη hηmax hK hd₀ α γ q N u p).trans (le_add_of_nonneg_right (hh₀ p))
  refine ⟨?_,hf⟩
  intro i p
  classical
  exact ⟨color_nonneg hs₀ hK hd₀ η α γ q N i p,by simpa using hf {i} p⟩

theorem exists_periodic_solution {s₀ η K d₀ α q b B : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 < d₀) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hq : q < 2) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (γ : ℝ) (N : ℕ) {h₀ : JetPrototype.Phase → ℝ}
    (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p ∧ h₀ p ≤ B)
    (hper : ∀ n p, h₀ (shift (displacement n) p) = h₀ p) :
    let A := WeightedFiniteSeed.amplitude s₀ η K d₀ N+B
    let T := WeightedLocalControl.lifespan q b A
    let L := WeightedLocalControl.damping q b A
    ∃ F : ℝ × JetPrototype.Phase → ℝ, Measurable F ∧
      (∀ z, 0 ≤ F z ∧ F z ≤ 2*A) ∧
      (∀ z, F z = PositiveIntegral.value T L JetBarrier.flight
        (initial s₀ η K α γ d₀ q N h₀) (WeightedLocal.forcing q b L F) z) ∧
      (∀ n z, F (z.1,shift (displacement n) z.2) = F z) := by
  dsimp only
  let A := WeightedFiniteSeed.amplitude s₀ η K d₀ N+B
  have hA : 0 < A := add_pos_of_pos_of_nonneg (WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N) hB
  have hi (p) : 0 ≤ initial s₀ η K α γ d₀ q N h₀ p ∧
      initial s₀ η K α γ d₀ q N h₀ p ≤ A := by
    have hs := seed_bounds hs₀ hsmax hη hηmax hK hd₀ hwidth hα hαmax γ q N p
    exact ⟨add_nonneg hs.1 (hh₀ p).1, add_le_add hs.2 (hh₀ p).2⟩
  obtain ⟨F,hFm,hF,hFeq⟩ := WeightedLocalControl.exists_solution hq hb hA
    ((measurable_seed s₀ η K α γ d₀ q N).add hh₀m) hi
  refine ⟨F,hFm,hF,hFeq,?_⟩
  intro n z
  have hseed (p : JetPrototype.Phase) :
      initial s₀ η K α γ d₀ q N h₀ (shift (displacement n) p) =
        initial s₀ η K α γ d₀ q N h₀ p :=
    congrArg₂ (fun a b : ℝ => a+b) (seed_periodic s₀ η K α γ d₀ q N n p) (hper n p)
  have he := solution_covariance hq hb (WeightedLocalControl.bounds hb hA).1
    (WeightedLocalControl.lifespan_pos hb hA).le (by positivity : 0 ≤ 2*A)
    (le_refl _) (WeightedLocalControl.small hb hA) hFm hF hFeq (displacement n)
    hseed
  exact congrFun he z

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The labeled periodic cold family of the constructed total solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.JetCopyDatum

def cold (s₀ η K α γ d₀ q b L T : ℝ) (N : ℕ)
    (F : ℝ × JetPrototype.Phase → ℝ) (i : JetLattice.Label) : ℝ × JetPrototype.Phase → ℝ :=
  coldLimit q b L T F (color s₀ η K α γ d₀ q N i)

theorem cold_envelope {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hTmax : T ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight
      (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) z)
    (i : JetLattice.Label) {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    physical q (cold s₀ η K α γ d₀ q b L T N F i) (t,p) ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
        (WeightedTranslation.shift (displacement i.lattice) p) := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
  exact WeightedJetComparison.shifted_limit_le hq hb hL hT hR hloss hK hα hγ hs
    (mul_pos hd₀ (pow_pos hs _)) hTmax
    (JetEscapedEnvelope.epsilon_small hK hd₀.le hs (JetEscapedTotal.scale_bound hs₀ hη _) hsmall)
    η i.positive (displacement i.lattice) hFm (measurable_color s₀ η K α γ d₀ q N i) hF
    ((initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀).1 i) hF₀ hFeq
    (physical_color_le hs₀ hK hd₀.le η α γ q N i) ht p

theorem cold_family_summable {s₀ η K d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (α γ : ℝ) (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight
      (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) z)
    (z : ℝ × JetPrototype.Phase) :
    Summable (fun i => cold s₀ η K α γ d₀ q b L T N F i z) ∧
      (∑' i, cold s₀ η K α γ d₀ q b L T N F i z) ≤ F z := by
  obtain ⟨hci,hcf⟩ := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀ α γ q N hh₀
  exact WeightedLocal.cold_family_summable hq hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hci hF₀ hcf hFeq z

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform hot gain from one main cold jet and a weighted remainder -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetHotGain

theorem remainder_bound (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d₀ t q R D : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (ht : 0 < t) (htmax : t ≤ 1 / 32) (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 ≤ D)
    (η : ℝ) (a : Bool) (x : Space) {f c : Velocity → ℝ}
    (hfm : Measurable f) (hcm : Measurable c)
    (hc : ∀ w, 0 ≤ c w) (hcf : ∀ w, c w ≤ f w)
    (hf : ∀ w, f w ≤ R * H q w)
    (hcU : ∀ w, c w ≤ JetSupersolution.U η K α γ s (d₀*s^10) t a (x,w))
    (hrem : ∀ w, f w - c w ≤ D * H q w) (b : ℝ) :
    ∀ᵐ v : Velocity, CollisionCutoff.gain b f v - CollisionCutoff.gain b c v ≤
      (2*D*JetMainGain.coefficient K α γ q / (s+t) +
        D^2*HotApplication.realBound q) * H q v := by
  filter_upwards [HotRepresentative.ae_good hcarleman hq₁ hq₂,
    JetMainGain.gain_bound hcarleman hK hα hγ hs hsmax hd₀ hd₀max ht htmax hq₁ hq₂ η a x]
      with v hv hjet
  have hci := MixedRealGain.integrable_of_le hcm (ChartKernel.measurable_H q)
    hc (H_nonneg q) hcU (fun _ => le_rfl) v hjet.1
  have hcmix := (MixedRealGain.gain_mono hcm (ChartKernel.measurable_H q)
    hc (H_nonneg q) hcU (fun _ => le_rfl) v hjet.1).trans hjet.2
  have h := HotGainRemainder.gain_difference_le hv hD hfm hcm hc hcf hf hrem hci hcmix b
  convert h using 1
  ring

end BoltzmannNonuniqueness.JetHotGain

end

end

section

/-! # Selection of the unique possible main color in the periodic family -/

noncomputable section

open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem outside_iff_not_mem (s₀ η t : ℝ) (x : Velocity) (i : Label) :
    JetLatticeTail.outside η (jetScale s₀ η i.annulus) t i.positive x i.lattice ↔
      x ∉ spatialEnlargement s₀ η t i := Iff.rfl

theorem main_or_outside {s₀ η t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (htmax : t ≤ 1/32) (N : ℕ) (x : Velocity) :
    (∃ i : Label, i.annulus < N ∧ x ∈ spatialEnlargement s₀ η t i ∧
      ∀ j : Label, j.annulus < N → j ≠ i →
        JetLatticeTail.outside η (jetScale s₀ η j.annulus) t j.positive x j.lattice) ∨
    (∀ i : Label, i.annulus < N →
      JetLatticeTail.outside η (jetScale s₀ η i.annulus) t i.positive x i.lattice) := by
  classical
  by_cases h : ∃ i : Label, i.annulus < N ∧ x ∈ spatialEnlargement s₀ η t i
  · obtain ⟨i,hi,hx⟩ := h
    refine Or.inl ⟨i,hi,hx,?_⟩
    intro j _ hji
    rw [outside_iff_not_mem]
    intro hj
    exact hji (common_point_label hs₀ hsmax hη hηmax htmax hj hx)
  · right
    intro i hi
    rw [outside_iff_not_mem]
    exact fun hx => h ⟨i,hi,hx⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The escaped-family estimate in the actual label indexing -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

def coordinates : Label ≃ ℕ × (Bool × Lattice) where
  toFun i := (i.annulus,i.positive,i.lattice)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv i := by cases i; rfl
  right_inv p := rfl

theorem tsum_labels (f : Label → ℝ≥0∞) :
    (∑' i, f i) = ∑' j : ℕ, ∑' a : Bool, ∑' n : Lattice, f ⟨j,a,n⟩ := by
  rw [← coordinates.symm.tsum_eq f]
  change (∑' p : ℕ × (Bool × Lattice), f ⟨p.1,p.2.1,p.2.2⟩) = _
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_prod']

def escaped (s₀ η t : ℝ) (N : ℕ) (x : Velocity) (f : Label → ℝ) (i : Label) : ℝ :=
  by
    classical
    exact if i.annulus < N ∧ JetLatticeTail.outside η (jetScale s₀ η i.annulus) t i.positive x i.lattice
      then f i else 0

theorem escaped_bound {s₀ η K α γ d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (A q : ℝ) (N : ℕ)
    (f : Label → ℝ) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (hf : ∀ i, 0 ≤ f i) (hfs : Summable f)
    (hfU : ∀ i, i.annulus < N → f i ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,v)) :
    (∑' i, escaped s₀ η t N x f i) ≤
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A*VelocityWeight.H q v := by
  classical
  have hnon (i) : 0 ≤ escaped s₀ η t N x f i := by
    unfold escaped
    split_ifs
    · exact hf i
    · exact le_rfl
  have hle (i) : escaped s₀ η t N x f i ≤ f i := by
    unfold escaped
    split_ifs
    · exact le_rfl
    · exact hf i
  have hsum : Summable (escaped s₀ η t N x f) := Summable.of_nonneg_of_le hnon hle hfs
  have h := JetEscapedEnvelope.real_power hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    ht htmax hsmall A q (fun j _ _ => j < N) (fun j a n => f ⟨j,a,n⟩) x v hx
    (fun j a n hj => hfU ⟨j,a,n⟩ hj)
  have he : (∑' i, ENNReal.ofReal (escaped s₀ η t N x f i)) =
      JetEscapedEnvelope.escapedSum s₀ η t x (fun j _ _ => j < N) (fun j a n => f ⟨j,a,n⟩) := by
    rw [tsum_labels]
    unfold escaped JetEscapedEnvelope.escapedSum
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,apply_ite ENNReal.ofReal,ENNReal.ofReal_zero]
  rw [← he, ← ENNReal.ofReal_tsum_of_nonneg hnon hsum] at h
  have hB : 0 ≤ JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*
      t^A*VelocityWeight.H q v := by
    have hc := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α (JetEscapedEnvelope.exponent A)
    exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg ht.le A)) (VelocityWeight.H_nonneg q v)
  simpa only [ENNReal.toReal_ofReal (tsum_nonneg hnon),ENNReal.toReal_ofReal hB] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Removing the unique main color leaves precisely the escaped family -/

noncomputable section

open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem sum_sub_main {s₀ η t : ℝ} {N : ℕ} {x : Velocity} {f : Label → ℝ}
    (hfs : Summable f) (hzero : ∀ j : Label, ¬j.annulus < N → f j = 0)
    (i : Label) (hi : x ∈ spatialEnlargement s₀ η t i)
    (hout : ∀ j : Label, j.annulus < N → j ≠ i →
      JetLatticeTail.outside η (jetScale s₀ η j.annulus) t j.positive x j.lattice) :
    (∑' j, f j)-f i = ∑' j, escaped s₀ η t N x f j := by
  classical
  have he (j : Label) : (if j=i then 0 else f j) = escaped s₀ η t N x f j := by
    by_cases hji : j=i
    · subst j
      have hn : ¬JetLatticeTail.outside η (jetScale s₀ η i.annulus) t i.positive x i.lattice :=
        fun h => (outside_iff_not_mem s₀ η t x i).mp h hi
      simp [escaped,hn]
    · by_cases hj : j.annulus < N
      · simp [escaped,hji,hj,hout j hj hji]
      · simp only [ite_eq_right hji,hzero j hj,escaped,hj,false_and,ite_false]
  rw [hfs.tsum_eq_add_tsum_ite i]
  simp_rw [he]
  ring

theorem sum_all_escaped {s₀ η t : ℝ} {N : ℕ} {x : Velocity} {f : Label → ℝ}
    (hzero : ∀ j : Label, ¬j.annulus < N → f j = 0)
    (hout : ∀ j : Label, j.annulus < N →
      JetLatticeTail.outside η (jetScale s₀ η j.annulus) t j.positive x j.lattice) :
    (∑' j, f j) = ∑' j, escaped s₀ η t N x f j := by
  apply tsum_congr
  intro j
  by_cases hj : j.annulus < N
  · simp [escaped,hj,hout j hj]
  · simp only [escaped,hj,false_and,ite_false,hzero j hj]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Weighted tails and absent labels of the actual cold family -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cold_zero (s₀ η K α γ d₀ q b L T : ℝ) (N : ℕ)
    (F : ℝ × JetPrototype.Phase → ℝ) (i : Label) (hi : ¬i.annulus < N) :
    cold s₀ η K α γ d₀ q b L T N F i = 0 := by
  have hseed : color s₀ η K α γ d₀ q N i = 0 := by
    funext p
    simp only [color,ite_eq_right hi,Pi.zero_apply]
  unfold cold
  rw [hseed,WeightedLocal.coldLimit_zero]

theorem normalized_escaped_bound {s₀ η K α γ d₀ t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (A q : ℝ) (N : ℕ)
    (f : Label → ℝ) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (hf : ∀ i, 0 ≤ f i) (hfs : Summable f)
    (hfU : ∀ i, i.annulus < N → VelocityWeight.H q v*f i ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,v)) :
    (∑' i, escaped s₀ η t N x f i) ≤
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A := by
  have h := escaped_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max ht htmax hsmall A q N
    (fun i => VelocityWeight.H q v*f i) x v hx
    (fun i => mul_nonneg (VelocityWeight.H_nonneg q v) (hf i))
    (hfs.mul_left (VelocityWeight.H q v)) hfU
  have he (i) : escaped s₀ η t N x (fun j => VelocityWeight.H q v*f j) i =
      VelocityWeight.H q v*escaped s₀ η t N x f i := by
    unfold escaped
    split_ifs <;> simp only [mul_zero]
  simp_rw [he] at h
  rw [tsum_mul_left] at h
  have hh : VelocityWeight.H q v*(∑' i, escaped s₀ η t N x f i) ≤
      VelocityWeight.H q v*(JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A) :=
    h.trans_eq (mul_comm _ _)
  exact (mul_le_mul_iff_of_pos_left (VelocityWeight.H_pos q v)).mp hh

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Separating the main cold color from escaped colors and the hot cap -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem remainder_at_main {s₀ η t z e : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (htmax : t ≤ 1/32) (N : ℕ) (x : Velocity) (i : Label)
    (hi : x ∈ spatialEnlargement s₀ η t i)
    (F : Velocity → ℝ) (c : Label → Velocity → ℝ)
    (hcs : ∀ w, Summable (fun j => c j w))
    (hzero : ∀ j, ¬j.annulus < N → ∀ w, c j w = 0)
    (hhot : ∀ w, F w-(∑' j, c j w) ≤ z)
    (htail : ∀ w, (∑' j, escaped s₀ η t N x (fun k => c k w) j) ≤ e) :
    ∀ w, F w-c i w ≤ z+e := by
  have hout (j : Label) (_hj : j.annulus < N) (hji : j ≠ i) :
      JetLatticeTail.outside η (jetScale s₀ η j.annulus) t j.positive x j.lattice := by
    apply (outside_iff_not_mem s₀ η t x j).mpr
    intro hj
    exact hji (common_point_label hs₀ hsmax hη hηmax htmax hj hi)
  intro w
  have he := sum_sub_main (hcs w) (fun j hj => hzero j hj w) i hi hout
  linarith only [he,hhot w,htail w]

theorem frequency_at_main {s₀ η K α γ d₀ q t z e V : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (ht : 0 < t) (htmax : t ≤ 1/32) (hq : q < 2) (hz : 0 ≤ z) (he : 0 ≤ e)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ) (x : Velocity) (i : Label) (hi : x ∈ spatialEnlargement s₀ η t i)
    {F : Velocity → ℝ} (hFm : Measurable F) (hFn : ∀ w, 0 ≤ F w)
    (c : Label → Velocity → ℝ) (hcs : ∀ w, Summable (fun j => c j w))
    (hzero : ∀ j, ¬j.annulus < N → ∀ w, c j w = 0)
    (hhot : ∀ᵐ w, F w-(∑' j, c j w) ≤ z)
    (htail : ∀ w, (∑' j, escaped s₀ η t N x (fun k => c k w) j) ≤ e)
    (hcU : ∀ w, H q w*c i w ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
      (JetSpatialBox.shifted x i.lattice,w)) (b : ℝ) {v : Velocity}
    (hv : ‖v-JetBarrier.centerVelocity α γ (jetScale s₀ η i.annulus) t i.positive
      (JetSpatialBox.shifted x i.lattice)‖ ≤ d₀*jetScale s₀ η i.annulus^10)
    (hvV : ‖v‖ ≤ V) :
    CollisionCutoff.frequency b (fun w => H q w*F w) v ≤
      4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9+
        (z+e)*weightFrequencyConstant q V := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
  have hout (j : Label) (_hj : j.annulus < N) (hji : j ≠ i) :
      JetLatticeTail.outside η (jetScale s₀ η j.annulus) t j.positive x j.lattice := by
    apply (outside_iff_not_mem s₀ η t x j).mpr
    intro hj
    exact hji (common_point_label hs₀ hsmax hη hηmax htmax hj hi)
  have hrem : ∀ᵐ w, F w-c i w ≤ z+e := by
    filter_upwards [hhot] with w hw
    have he := sum_sub_main (hcs w) (fun j hj => hzero j hj w) i hi hout
    linarith only [he,hw,htail w]
  have hupper : ∀ᵐ w, H q w*F w ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
      (JetSpatialBox.shifted x i.lattice,w)+(z+e)*H q w := by
    filter_upwards [hrem] with w hw
    have hh := mul_le_mul_of_nonneg_left hw (H_nonneg q w)
    nlinarith only [hh,hcU w]
  have hf := JetSupersolution.core_add_weight_frequency_bound_ae hK hs (by positivity) hα hγ
    ht (htmax.trans (by norm_num))
    (JetEscapedEnvelope.epsilon_small hK hd₀.le hs (JetEscapedTotal.scale_bound hs₀ hη _) hsmall)
    hq (add_nonneg hz he) η b i.positive (JetSpatialBox.shifted x i.lattice)
    ((ChartKernel.measurable_H q).mul hFm) (fun w => mul_nonneg (H_nonneg q w) (hFn w))
    hupper hv hvV
  convert hf using 1
  dsimp only [jetScale]
  field_simp

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Every retained free-core flight stays in its own main color -/

noncomputable section

open Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem color_initial_core {s₀ η K α γ d₀ q : ℝ} {N : ℕ} {i : Label}
    {p : JetPrototype.Phase} (hp : color s₀ η K α γ d₀ q N i p ≠ 0) :
    JetPrototype.density η K α γ (jetScale s₀ η i.annulus)
      (d₀*jetScale s₀ η i.annulus^10) i.positive (shift (displacement i.lattice) p) ≠ 0 := by
  have hi : i.annulus < N := by
    by_contra hi
    exact hp (by simp only [color,ite_eq_right hi])
  intro hz
  apply hp
  simp only [color,ite_eq_left hi,JetDatum.term,hz,zero_div]

theorem shifted_flight_position (t : ℝ) (p : JetPrototype.Phase) (n : Lattice) :
    JetSpatialBox.shifted (PlaneChart.join (JetBarrier.flight t p).1.1
      (JetBarrier.flight t p).1.2) n = (JetBarrier.flight t (shift (displacement n) p)).1 := by
  apply Prod.ext
  · simp only [JetSpatialBox.shifted,PlaneChart.transverse_join]
    change (p.1.1+t • VelocityWeight.transverse p.2)-transverseShift n =
      (p.1.1-transverseShift n)+t • VelocityWeight.transverse p.2
    abel
  · change (p.1.2+t*VelocityWeight.axial p.2)-axialShift n =
      (p.1.2-axialShift n)+t*VelocityWeight.axial p.2
    ring

theorem central_enlargement_coordinates {s₀ η t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (htmax : t ≤ 1/32)
    {i : Label} (hi0 : i.lattice = 0) {x : Velocity}
    (hx : x ∈ spatialEnlargement s₀ η t i) : ∀ k, |x k| ≤ 1 := by
  have htzero : transverseShift (0 : Lattice) = 0 := by ext k; simp [transverseShift]
  have hy := hx.1
  have hz := hx.2
  rw [hi0,htzero,sub_zero] at hy
  have hz' : |VelocityWeight.axial x| ≤ 1/8+2*t+1/16 := by
    simpa only [hi0,axialShift,Pi.zero_apply,Int.cast_zero,sub_zero] using hz
  have hyt := enlargement_inside_baseBall hs₀ hη i.annulus i.positive hy
  rw [Metric.mem_ball,dist_zero_right] at hyt
  have hsquare := VelocityWeight.norm_sq_split x
  have hxnorm : ‖x‖ ≤ 1 := by
    have hysq : ‖VelocityWeight.transverse x‖^2 ≤ (1/8:ℝ)^2 := by
      nlinarith [norm_nonneg (VelocityWeight.transverse x)]
    have hzabs : |VelocityWeight.axial x| ≤ 1/4 := by linarith only [hz',htmax]
    have hzsq : (VelocityWeight.axial x)^2 ≤ (1/4:ℝ)^2 := by
      nlinarith [sq_abs (VelocityWeight.axial x),abs_nonneg (VelocityWeight.axial x)]
    nlinarith [norm_nonneg x]
  intro k
  have hk : |x k| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x k
  exact hk.trans hxnorm

theorem color_flight_geometry {s₀ η K α γ d₀ q t : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (ht : 0 ≤ t) (i : Label) (p : JetPrototype.Phase)
    (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
    (hwidth : t*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
    (hp : color s₀ η K α γ d₀ q N i p ≠ 0) :
    PlaneChart.join (JetBarrier.flight t p).1.1 (JetBarrier.flight t p).1.2 ∈
      spatialEnlargement s₀ η t i ∧
    ‖p.2-JetBarrier.centerVelocity α γ (jetScale s₀ η i.annulus) t i.positive
      (JetSpatialBox.shifted (PlaneChart.join (JetBarrier.flight t p).1.1
        (JetBarrier.flight t p).1.2) i.lattice)‖ ≤ d₀*jetScale s₀ η i.annulus^10 ∧
    ‖p.2‖ ≤ 2 := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
  have hd : 0 < d₀*jetScale s₀ η i.annulus^10 := by positivity
  have hcore := color_initial_core hp
  have hy := JetSupport.free_core_transverse ht hd hwidth K α γ i.positive hcore
  have hz := JetSupport.free_core_axial ht hd hdmax hα hαmax η K γ
    (jetScale s₀ η i.annulus) i.positive hcore
  constructor
  · change (JetSpatialBox.shifted (PlaneChart.join (JetBarrier.flight t p).1.1
      (JetBarrier.flight t p).1.2) i.lattice).1 ∈ _ ∧
      |(JetSpatialBox.shifted (PlaneChart.join (JetBarrier.flight t p).1.1
        (JetBarrier.flight t p).1.2) i.lattice).2| ≤ _
    rw [shifted_flight_position]
    exact ⟨hy,hz⟩
  constructor
  · rw [shifted_flight_position]
    exact (JetCoreFlight.error_lt_width hd hα hγ hs ht η K i.positive hcore).le
  · exact (JetSupport.density_support_two hd hdmax hα hαmax η K γ
      (jetScale s₀ η i.annulus) i.positive hcore).le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Spatial localization of the unique cold core in the central periodic cube -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem enlargement_central_lattice {s₀ η t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (htmax : t ≤ 1/32)
    {x : Velocity} (hx : x ∈ TorusChart.cube) {i : Label}
    (hi : x ∈ spatialEnlargement s₀ η t i) : i.lattice = 0 := by
  have hn := enlargement_inside_baseBall hs₀ hη i.annulus i.positive hi.1
  rw [Metric.mem_ball,dist_zero_right] at hn
  have hclose {r : ℝ} {n : ℤ} (hr : r ∈ TorusChart.interval)
      (h : |r-(n:ℝ)| ≤ 1/4) : n = 0 := by
    by_contra hne
    have hd := integer_distance hne
    have ha : |r| ≤ 1/2 := abs_le.mpr ⟨hr.1.le,hr.2⟩
    have hb := abs_add_le ((n:ℝ)-r) r
    rw [sub_add_cancel,abs_sub_comm] at hb
    simp only [Int.cast_zero,sub_zero] at hd
    linarith
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · apply hclose (hx (Fin.last 2))
    have hb := hi.2
    change |x (Fin.last 2)-(i.lattice (Fin.last 2):ℝ)| ≤ 1/8+2*t+1/16 at hb
    linarith
  · apply hclose (hx j.castSucc)
    have hb := PiLp.norm_apply_le (transverse x-transverseShift i.lattice) j
    change ‖x j.castSucc-(i.lattice j.castSucc:ℝ)‖ ≤ _ at hb
    rw [Real.norm_eq_abs] at hb
    linarith

theorem enlargement_central_shell {s₀ η t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (htmax : t ≤ 1/32)
    {x : Velocity} (hx : x ∈ TorusChart.cube) {i : Label}
    (hi : x ∈ spatialEnlargement s₀ η t i) :
    transverse x ∈ AnnularEnvelope.shell s₀ η i.annulus := by
  have hz := enlargement_central_lattice hs₀ hsmax hη htmax hx hi
  have he := hi.1
  rw [hz] at he
  have hshift : transverseShift (0 : Lattice) = 0 := by ext k; simp [transverseShift]
  rw [hshift,sub_zero] at he
  exact enlargement_subset_annulus hη (DatumBounds.scale_pos hs₀ _) i.positive he

theorem main_coefficient_le {s₀ η t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (ht : 0 ≤ t) (htmax : t ≤ 1/32)
    {N : ℕ} {x : Velocity} (hx : x ∈ TorusChart.cube) {i : Label}
    (hiN : i.annulus < N) (hi : x ∈ spatialEnlargement s₀ η t i) :
    1/(jetScale s₀ η i.annulus+t) ≤
      AnnularEnvelope.finiteEnvelope s₀ η (Finset.range N) t (transverse x) := by
  have hs (j : ℕ) : 0 < jetScale s₀ η j := DatumBounds.scale_pos hs₀ _
  have hn (j : ℕ) (_hj : j ∈ Finset.range N) :
      0 ≤ AnnularEnvelope.term s₀ η j t (transverse x) := by
    apply indicator_nonneg
    intro _ _
    exact div_nonneg zero_le_one (add_nonneg ht (hs j).le)
  have he := Finset.single_le_sum hn (Finset.mem_range.mpr hiN)
  have hshell := enlargement_central_shell hs₀ hsmax hη htmax hx hi
  simpa only [AnnularEnvelope.finiteEnvelope,AnnularEnvelope.term,indicator_of_mem hshell,add_comm] using he

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Annular half-Gaussian moment bound for the periodic geometric decomposition -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

def escapedConstant (s₀ η K α d₀ : ℝ) : ℝ :=
  JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0)

theorem cell_moment_bound {s₀ η K α γ d₀ q t Z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hq : q < 2) (hZ : 0 ≤ Z)
    (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ) (x : Velocity) (hx : x ∈ TorusChart.cube)
    (F : Velocity → ℝ) (c : Label → Velocity → ℝ)
    (hcm : ∀ i, Measurable (c i)) (hcn : ∀ i v, 0 ≤ c i v)
    (hcs : ∀ v, Summable (fun i => c i v))
    (hzero : ∀ i, ¬i.annulus < N → ∀ v, c i v = 0)
    (hU : ∀ i v, H q v*c i v ≤ JetSupersolution.U η K α γ (jetScale s₀ η i.annulus)
      (d₀*jetScale s₀ η i.annulus^10) t i.positive (JetSpatialBox.shifted x i.lattice,v))
    (hhot : ∀ᵐ v, F v-∑' i, c i v ≤ Z) :
    moment (fun v => H q v*F v) ≤ ENNReal.ofReal
      ((Z+escapedConstant s₀ η K α d₀)*hotConstant q+
        JetEnvelopeGain.momentConstant K α γ*
          AnnularEnvelope.finiteEnvelope s₀ η (Finset.range N) t (transverse x)) := by
  let E := escapedConstant s₀ η K α d₀
  have hE : 0 ≤ E := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _
  have hZE : 0 ≤ Z+E := add_nonneg hZ hE
  have hx1 (k) : |x k| ≤ 1 := by
    have h := hx k
    exact (abs_le.mpr ⟨h.1.le,h.2⟩).trans (by norm_num)
  have he (v) : (∑' i, escaped s₀ η t N x (fun j => c j v) i) ≤ E := by
    simpa only [Real.rpow_zero,mul_one,E,escapedConstant] using
      normalized_escaped_bound hs₀ hsmax hη hηmax hK hα.le hαmax hγ.le hd₀ hd₀max ht htmax
        hsmall 0 q N (fun j => c j v) x v hx1 (fun i => hcn i v) (hcs v)
        (fun i _ => hU i v)
  have hmeas : Measurable (fun v => (Z+E)*H q v) := by unfold H singularity; fun_prop
  have hnonneg (v) : 0 ≤ (Z+E)*H q v := mul_nonneg hZE (H_nonneg q v)
  have hbase := hot_moment hq hZE
  have henvnonneg : 0 ≤ JetEnvelopeGain.momentConstant K α γ*
      AnnularEnvelope.finiteEnvelope s₀ η (Finset.range N) t (transverse x) := by
    apply mul_nonneg (JetEnvelopeGain.momentConstant_nonneg hK α γ)
    apply Finset.sum_nonneg
    intro j _
    apply indicator_nonneg
    intro _ _
    exact div_nonneg zero_le_one (add_nonneg ht.le (DatumBounds.scale_pos hs₀ _).le)
  rcases main_or_outside hs₀ hsmax hη hηmax htmax N x with ⟨i,hiN,hi,hout⟩ | hout
  · have hdom : ∀ᵐ v, H q v*F v ≤ (Z+E)*H q v+H q v*c i v := by
      filter_upwards [hhot] with v hv
      have hs := sum_sub_main (hcs v) (fun j hj => hzero j hj v) i hi hout
      have hc := he v
      have hn : F v ≤ Z+E+c i v := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hn (H_nonneg q v)]
    have him : Measurable (fun v => H q v*c i v) := by unfold H singularity; fun_prop
    have hin (v) : 0 ≤ H q v*c i v := mul_nonneg (H_nonneg q v) (hcn i v)
    have hb := (moment_le_exponential him hin).trans
      (JetEnvelopeGain.dominated_exponential_moment hK hα hγ (DatumBounds.scale_pos hs₀ _)
        ((JetEscapedTotal.scale_bound hs₀ hη _).trans hsmax) hd₀ hd₀max ht htmax η i.positive
        (JetSpatialBox.shifted x i.lattice) (hU i))
    have hcoef := mul_le_mul_of_nonneg_left (main_coefficient_le hs₀ hsmax hη ht.le htmax hx hiN hi)
      (JetEnvelopeGain.momentConstant_nonneg hK α γ)
    have hcore : moment (fun v => H q v*c i v) ≤ ENNReal.ofReal
        (JetEnvelopeGain.momentConstant K α γ*AnnularEnvelope.finiteEnvelope s₀ η
          (Finset.range N) t (transverse x)) := by
      apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
      simpa only [div_eq_mul_inv,one_mul,jetScale] using hcoef
    calc
      _ ≤ moment (fun v => (Z+E)*H q v+H q v*c i v) := moment_mono_ae hdom
      _ = _ := moment_add hmeas hnonneg hin
      _ ≤ _ := add_le_add (le_of_eq hbase) hcore
      _ = _ := (ENNReal.ofReal_add (mul_nonneg hZE (hotConstant_nonneg q)) henvnonneg).symm
  · have hdom : ∀ᵐ v, H q v*F v ≤ (Z+E)*H q v := by
      filter_upwards [hhot] with v hv
      have hs := sum_all_escaped (fun j hj => hzero j hj v) hout
      have hc := he v
      have hn : F v ≤ Z+E := by rw [hs] at hv; linarith
      nlinarith [mul_le_mul_of_nonneg_left hn (H_nonneg q v)]
    calc
      _ ≤ moment (fun v => (Z+E)*H q v) := moment_mono_ae hdom
      _ = _ := hbase
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right henvnonneg)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Reduction of every spatial point to a bounded fundamental cell -/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem spatialMap_surjective : Function.Surjective JetPeriodicDatum.spatialMap := by
  intro y
  refine ⟨split.symm (y.2,y.1),?_⟩
  have h := split.apply_symm_apply (y.2,y.1)
  rw [split_apply] at h
  exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

theorem exists_shift_in_cell (y : JetPrototype.Space) :
    ∃ (n : JetLattice.Lattice) (x : Velocity), (∀ k, |x k| ≤ 1) ∧
      y-displacement n = JetPeriodicDatum.spatialMap x := by
  obtain ⟨v,hv⟩ := spatialMap_surjective y
  let n : JetLattice.Lattice := fun k => ⌊v k⌋
  let x : Velocity := WithLp.toLp 2 (fun k => v k-(n k : ℝ))
  refine ⟨n,x,?_,?_⟩
  · intro k
    change |v k-(⌊v k⌋ : ℝ)| ≤ 1
    exact abs_le.mpr ⟨by linarith [Int.floor_le (v k)],by linarith [Int.lt_floor_add_one (v k)]⟩
  · rw [← hv]
    apply Prod.ext
    · apply (WithLp.ext_iff 2).mpr
      funext k
      rfl
    · rfl

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
