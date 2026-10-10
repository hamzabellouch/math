import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Periodic
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryMotion

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry.BoxLayout
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

def solid (A : BoxLayout ι) (i : ι) : Set Space :=
  Icc (A.center i - A.width i) (A.center i + A.width i)

omit [Fintype ι] in
lemma mem_solid {A : BoxLayout ι} {i : ι} {x : Space} : x ∈ A.solid i ↔
    ∀ k, A.center i k - A.width i k ≤ x k ∧ x k ≤ A.center i k + A.width i k := by
  simp only [solid, mem_Icc, Pi.le_def, Pi.sub_apply, Pi.add_apply]
  exact forall_and.symm

def affineMap (A B : BoxLayout ι) (i : ι) (x : Space) : Space :=
  fun k => B.center i k + B.width i k / A.width i k * (x k - A.center i k)

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}

def fieldCenter (m : BoxMotion A B safe η) (i : ι) (t : ℝ) : Space :=
  m.center (2 * t - 1 / 2) i

def fieldScale (m : BoxMotion A B safe η) (i : ι) (t : ℝ) : Space :=
  fun k => m.width (2 * t - 1 / 2) i k / A.width i k

def velocity (m : BoxMotion A B safe η) : Velocity :=
  familyVelocity (fun i => -A.width i) A.width m.fieldCenter m.fieldScale η

def path (m : BoxMotion A B safe η) (i : ι) (x : Space) : ℝ → Space :=
  affinePath (m.fieldCenter i) (m.fieldScale i) (x - A.center i)

lemma fieldCenter_smooth (m : BoxMotion A B safe η) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (m.fieldCenter i) :=
  (contDiff_pi.mp m.smooth_center i).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma fieldScale_smooth (m : BoxMotion A B safe η) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (m.fieldScale i) := by
  apply contDiff_pi.mpr
  intro k
  exact (((contDiff_pi.mp (contDiff_pi.mp m.smooth_width i) k).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))).div_const _

lemma fieldScale_pos (m : BoxMotion A B safe η) (i : ι) (t : ℝ) (k : Fin 3) :
    0 < m.fieldScale i t k := div_pos (m.positive _ _ _) (m.positive_start _ _)

lemma fieldScale_det (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    ∏ k, m.fieldScale i t k = 1 := by
  simp only [fieldScale, Finset.prod_div_distrib, m.volume]
  exact div_self (ne_of_gt (Finset.prod_pos (fun k _ => m.positive_start i k)))

lemma velocity_jointSmooth (m : BoxMotion A B safe η) : JointSmooth m.velocity :=
  familyVelocity_jointSmooth m.fieldCenter_smooth m.fieldScale_smooth
    (fun i t k => (m.fieldScale_pos i t k).ne') _ _ _

lemma velocity_divergence (m : BoxMotion A B safe η) (t : ℝ) (x : Space) :
    div m.velocity t x = 0 :=
  familyVelocity_divergence m.fieldCenter_smooth m.fieldScale_smooth
    (fun i t k => (m.fieldScale_pos i t k).ne') _ _ _ _ _

lemma lowerEndpoint_eq (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    lowerEndpoint (-A.width i) (m.fieldCenter i) (m.fieldScale i) t =
      m.center (2 * t - 1 / 2) i - m.width (2 * t - 1 / 2) i := by
  ext k
  dsimp [lowerEndpoint, fieldCenter, fieldScale]
  field_simp [(m.positive_start i k).ne']
  ring

lemma upperEndpoint_eq (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    lowerEndpoint (A.width i) (m.fieldCenter i) (m.fieldScale i) t =
      m.center (2 * t - 1 / 2) i + m.width (2 * t - 1 / 2) i := by
  ext k
  dsimp [lowerEndpoint, fieldCenter, fieldScale]
  rw [div_mul_cancel₀ _ (m.positive_start i k).ne']

lemma enlarged_disjoint (m : BoxMotion A B safe η) (t : ℝ) :
    Pairwise fun i j => Disjoint
      (closedEnlargement (lowerEndpoint (-A.width i) (m.fieldCenter i) (m.fieldScale i) t)
        (lowerEndpoint (A.width i) (m.fieldCenter i) (m.fieldScale i) t) (2 * η))
      (closedEnlargement (lowerEndpoint (-A.width j) (m.fieldCenter j) (m.fieldScale j) t)
        (lowerEndpoint (A.width j) (m.fieldCenter j) (m.fieldScale j) t) (2 * η)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rw [m.lowerEndpoint_eq, m.upperEndpoint_eq, mem_closedEnlargement] at hi hj
  obtain ⟨k, hk⟩ := m.separation (2 * t - 1 / 2) i j hij
  have hbound : |m.center (2 * t - 1 / 2) i k - m.center (2 * t - 1 / 2) j k| ≤
      m.width (2 * t - 1 / 2) i k + m.width (2 * t - 1 / 2) j k + 4 * η := by
    apply abs_le.mpr
    have hi' := hi k
    have hj' := hj k
    dsimp at hi' hj'
    constructor <;> linarith
  exact hk.not_ge hbound

lemma path_start (m : BoxMotion A B safe η) (i : ι) (x : Space) : m.path i x 0 = x := by
  ext k
  have hc := m.start_center (-(1 / 2)) (by norm_num)
  have hw := m.start_width (-(1 / 2)) (by norm_num)
  simp only [path, affinePath, fieldCenter, fieldScale, mul_zero, zero_sub, Pi.sub_apply]
  rw [hc, hw, div_self (m.positive_start i k).ne', one_mul]
  ring

lemma path_end (m : BoxMotion A B safe η) (i : ι) (x : Space) :
    m.path i x 1 = A.affineMap B i x := by
  ext k
  change m.center (2 * 1 - 1 / 2) i k +
    m.width (2 * 1 - 1 / 2) i k / A.width i k * (x k - A.center i k) = _
  rw [m.end_center _ (by norm_num), m.end_width _ (by norm_num)]
  rfl

omit [Fintype ι] in
lemma reference_mem {i : ι} {x : Space} (hx : x ∈ A.solid i) :
    x - A.center i ∈ Icc (-A.width i) (A.width i) := by
  rw [BoxLayout.mem_solid] at hx
  constructor <;> intro k <;> dsimp <;> linarith [(hx k).1, (hx k).2]

lemma path_hasDerivAt (m : BoxMotion A B safe η) (hη : 0 < η)
    {i : ι} {x : Space} (hx : x ∈ A.solid i) (t : ℝ) :
    HasDerivAt (m.path i x) (m.velocity t (m.path i x t)) t := by
  have hz := reference_mem hx
  have hplateau := affinePath_mem_plateau (c := m.fieldCenter i) hη hz (m.fieldScale_pos i t)
  unfold path
  rw [velocity, familyVelocity_eq_on_plateau hη i hplateau (m.enlarged_disjoint t)]
  exact affinePath_hasDerivAt hη (m.fieldCenter_smooth i) (m.fieldScale_smooth i)
    (m.fieldScale_pos i) (m.fieldScale_det i) hz t

lemma path_guarded (m : BoxMotion A B safe η) {i : ι} (hi : i ∈ safe)
    {x : Space} (hx : x ∈ A.solid i) (t : ℝ) : m.path i x t ∉ observer := by
  intro hobs
  have hob : m.path i x t 0 < 2 := (Set.mem_pi.mp hobs 0 (Set.mem_univ _)).2
  have hg := m.guard (2 * t - 1 / 2) i hi
  have hz := (reference_mem hx).1 0
  have hp := m.fieldScale_pos i t 0
  have hmul := mul_le_mul_of_nonneg_left hz hp.le
  change m.fieldScale i t 0 * (-A.width i 0) ≤
    m.fieldScale i t 0 * (x - A.center i) 0 at hmul
  have hlow : m.center (2 * t - 1 / 2) i 0 - m.width (2 * t - 1 / 2) i 0 ≤ m.path i x t 0 := by
    have he := congrFun (m.lowerEndpoint_eq i t) 0
    change m.fieldCenter i t 0 + m.fieldScale i t 0 * (-A.width i 0) =
      m.center (2 * t - 1 / 2) i 0 - m.width (2 * t - 1 / 2) i 0 at he
    change _ ≤ m.fieldCenter i t 0 + m.fieldScale i t 0 * (x - A.center i) 0
    rw [← he]
    linarith
  exact (lt_of_lt_of_le hg hlow).not_gt hob

lemma fieldCenter_before (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : t ≤ 1 / 4) :
    m.fieldCenter i t = A.center i := by
  unfold fieldCenter
  rw [m.start_center _ (by linarith)]

lemma fieldScale_before (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : t ≤ 1 / 4) :
    m.fieldScale i t = 1 := by
  ext k
  change m.width (2 * t - 1 / 2) i k / A.width i k = 1
  rw [m.start_width _ (by linarith), div_self (m.positive_start i k).ne']

lemma fieldCenter_after (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : 3 / 4 ≤ t) :
    m.fieldCenter i t = B.center i := by
  unfold fieldCenter
  rw [m.end_center _ (by linarith)]

lemma fieldScale_after (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : 3 / 4 ≤ t) :
    m.fieldScale i t = fun k => B.width i k / A.width i k := by
  unfold fieldScale
  rw [m.end_width _ (by linarith)]

lemma velocity_collars (m : BoxMotion A B safe η) : TimeCollars m.velocity := by
  intro t ht
  apply familyVelocity_zero
  · intro i
    rcases ht with ht | ht
    · have he : m.fieldCenter i =ᶠ[𝓝 t] fun _ => A.center i := by
        filter_upwards [Iio_mem_nhds ht] with s hs using m.fieldCenter_before i hs.le
      rw [he.deriv_eq, deriv_const]
    · have he : m.fieldCenter i =ᶠ[𝓝 t] fun _ => B.center i := by
        filter_upwards [Ioi_mem_nhds ht] with s hs using m.fieldCenter_after i hs.le
      rw [he.deriv_eq, deriv_const]
  · intro i k
    rcases ht with ht | ht
    · have he : (fun s => m.fieldScale i s k) =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        rw [m.fieldScale_before i hs.le]
        rfl
      rw [he.deriv_eq, deriv_const]
    · have he : (fun s => m.fieldScale i s k) =ᶠ[𝓝 t] fun _ => B.width i k / A.width i k := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        rw [m.fieldScale_after i hs.le]
      rw [he.deriv_eq, deriv_const]

lemma bounded_geometry (m : BoxMotion A B safe η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t i k,
      |m.center t i k| ≤ C ∧ |m.width t i k| ≤ C := by
  obtain ⟨Cc, hc⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    m.smooth_center.continuous.continuousOn
  obtain ⟨Cw, hw⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    m.smooth_width.continuous.continuousOn
  have hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i k,
      |m.center t i k| ≤ max 0 (max Cc Cw) ∧
      |m.width t i k| ≤ max 0 (max Cc Cw) := by
    intro t ht i k
    constructor
    · exact (norm_le_pi_norm (m.center t i) k).trans
        ((norm_le_pi_norm (m.center t) i).trans ((hc t ht).trans
          ((le_max_left _ _).trans (le_max_right _ _))))
    · exact (norm_le_pi_norm (m.width t i) k).trans
        ((norm_le_pi_norm (m.width t) i).trans ((hw t ht).trans
          ((le_max_right _ _).trans (le_max_right _ _))))
  refine ⟨max 0 (max Cc Cw), le_max_left _ _, fun t i k => ?_⟩
  by_cases ht : t ≤ 0
  · simpa only [m.start_center t ht, m.start_width t ht,
      m.start_center 0 le_rfl, m.start_width 0 le_rfl] using hh 0 ⟨le_rfl, by norm_num⟩ i k
  · by_cases ht' : 1 ≤ t
    · simpa only [m.end_center t ht', m.end_width t ht',
        m.end_center 1 le_rfl, m.end_width 1 le_rfl] using hh 1 ⟨by norm_num, le_rfl⟩ i k
    · exact hh t ⟨le_of_not_ge ht, le_of_not_ge ht'⟩ i k

lemma velocity_compact_support (m : BoxMotion A B safe η) (hη : 0 < η) :
    ∃ K : Set Space, IsCompact K ∧ SpatiallySupported K m.velocity := by
  obtain ⟨C, hC, hb⟩ := m.bounded_geometry
  let K : Set Space := Icc (fun _ => -(2 * C + 2 * η)) (fun _ => 2 * C + 2 * η)
  refine ⟨K, isCompact_Icc, fun t x hx => image_eq_zero_of_notMem_tsupport ?_⟩
  intro ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp (tsupport_familyVelocity_subset
    (fun i => -A.width i) A.width m.fieldCenter m.fieldScale hη t ht)
  rw [m.lowerEndpoint_eq, m.upperEndpoint_eq, mem_closedEnlargement] at hi
  apply hx
  constructor <;> intro k
  · have hh := hi k
    have hbc := (abs_le.mp (hb (2 * t - 1 / 2) i k).1).1
    have hbw := (abs_le.mp (hb (2 * t - 1 / 2) i k).2).2
    dsimp at hh ⊢
    linarith [hh.1]
  · have hh := hi k
    have hbc := (abs_le.mp (hb (2 * t - 1 / 2) i k).1).2
    have hbw := (abs_le.mp (hb (2 * t - 1 / 2) i k).2).2
    dsimp at hh ⊢
    linarith [hh.2]

end BalancedTransport.Geometry.BoxMotion
end

end OAI
