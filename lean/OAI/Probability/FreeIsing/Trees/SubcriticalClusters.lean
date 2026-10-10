import OAI.Probability.FreeIsing.Trees.PathCylinders
import OAI.Probability.FreeIsing.Trees.RootedBroadcast
import OAI.Probability.FreeIsing.Trees.Shells

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace Problem367
namespace SubcriticalClusters

def DownwardOpen {d : ℕ} (p : ℝ) (U : TreeVertex d → ℝ)
    (r v : TreeVertex d) : Prop :=
  r.1 <+: v.1 ∧ ∀ k : ℕ, r.1.length < k → k ≤ v.1.length →
    U (ConnectedHull.takeVertex v k) ≤ p

def pathCoordinates {d : ℕ} (m : ℕ) (v : TreeVertex d) : Finset (TreeVertex d) :=
  (Finset.Ioc m v.1.length).image (ConnectedHull.takeVertex v)

lemma mem_pathCoordinates {d : ℕ} {m : ℕ} {v w : TreeVertex d} :
    w ∈ pathCoordinates m v ↔
      ∃ k : ℕ, m < k ∧ k ≤ v.1.length ∧ ConnectedHull.takeVertex v k = w := by
  classical
  simp only [pathCoordinates, Finset.mem_image, Finset.mem_Ioc]
  tauto

lemma card_pathCoordinates {d : ℕ} (m : ℕ) (v : TreeVertex d) :
    (pathCoordinates m v).card = v.1.length - m := by
  classical
  rw [pathCoordinates, Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj hij
    have hlen := congrArg (fun w : TreeVertex d => w.1.length) hij
    simpa only [ConnectedHull.prefix_length_eq v (Finset.mem_Ioc.mp hi).2,
      ConnectedHull.prefix_length_eq v (Finset.mem_Ioc.mp hj).2] using hlen

lemma uniform01_Iic {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniform01 (Iic p) = ENNReal.ofReal p := by
  have h := RootedBroadcast.biasedSpin_pos_mass hp0 hp1
  have heq : (RootedBroadcast.biasedSpin p) ⁻¹' {IsingSpin.pos} = Iic p := by
    ext x
    simp [RootedBroadcast.biasedSpin]
  rwa [heq] at h

lemma path_open_mass {d : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (v : TreeVertex d) :
    labelMeasure d {U | ∀ k : ℕ, m < k → k ≤ v.1.length →
      U (ConnectedHull.takeVertex v k) ≤ p} =
      (ENNReal.ofReal p) ^ (v.1.length - m) := by
  classical
  have heq : {U : TreeVertex d → ℝ | ∀ k : ℕ, m < k → k ≤ v.1.length →
      U (ConnectedHull.takeVertex v k) ≤ p} =
      Set.pi (pathCoordinates m v : Set (TreeVertex d)) (fun _ => Iic p) := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Set.mem_Iic]
    constructor
    · intro h w hw
      obtain ⟨k, hk, hkv, rfl⟩ := mem_pathCoordinates.mp hw
      exact h k hk hkv
    · intro h k hk hkv
      exact h _ (mem_pathCoordinates.mpr ⟨k, hk, hkv, rfl⟩)
  rw [heq, labelMeasure, Measure.infinitePi_pi _ (fun _ _ => measurableSet_Iic)]
  simp only [uniform01_Iic hp0 hp1, Finset.prod_const, card_pathCoordinates]

lemma downwardOpen_mass_le {d : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r v : TreeVertex d) :
    labelMeasure d {U | DownwardOpen p U r v} ≤
      (ENNReal.ofReal p) ^ (v.1.length - r.1.length) := by
  rw [← path_open_mass hp0 hp1 r.1.length v]
  exact measure_mono (fun _ h => h.2)

theorem ae_finite_of_depth_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : Ω → TreeVertex d → Prop) (m : ℕ) (p : ℝ≥0∞)
    (hp : (d - 1 : ℕ) * p < 1) (hptop : p ≠ ∞)
    (hdepth : ∀ ω v, R ω v → m ≤ v.1.length)
    (hprob : ∀ v, μ {ω | R ω v} ≤ p ^ (v.1.length - m)) :
    ∀ᵐ ω ∂μ, {v | R ω v}.Finite := by
  classical
  let A : ℕ → Set Ω := fun k => ⋃ v : TreeShell d (m + k + 1), {ω | R ω v.1}
  have hA (k : ℕ) : μ (A k) ≤
      (d : ℝ≥0∞) * (d - 1 : ℕ) ^ m * p * (((d - 1 : ℕ) : ℝ≥0∞) * p) ^ k := by
    calc
      μ (A k) ≤ ∑ v : TreeShell d (m + k + 1), μ {ω | R ω v.1} :=
        measure_iUnion_fintype_le μ _
      _ ≤ ∑ _v : TreeShell d (m + k + 1), p ^ (k + 1) := by
        apply Finset.sum_le_sum
        intro v _
        have hlen : v.1.1.length - m = k + 1 := by have := v.2; omega
        simpa only [hlen] using hprob v.1
      _ = (d : ℝ≥0∞) * (d - 1 : ℕ) ^ m * p *
          (((d - 1 : ℕ) : ℝ≥0∞) * p) ^ k := by
        simp only [Finset.sum_const, Finset.card_univ, card_treeShell_succ,
          nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow]
        rw [pow_add, pow_succ, mul_pow]
        ring
  have hsum : (∑' k, μ (A k)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hA)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by simp) (by simp)) hptop
    · exact ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hp))
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  apply (finite_treeBall d (m + N)).subset
  intro v hv
  show v.1.length ≤ m + N
  by_contra hlen
  have hm := hdepth ω v hv
  let k := v.1.length - m - 1
  have hnk : N ≤ k := by omega
  have hvlen : v.1.length = m + k + 1 := by omega
  exact hN k hnk (Set.mem_iUnion.mpr ⟨⟨v, hvlen⟩, hv⟩)

theorem ae_finite_downwardOpen {d : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : (d - 1 : ℕ) * p < 1)
    (r : TreeVertex d) :
    ∀ᵐ U ∂labelMeasure d, {v | DownwardOpen p U r v}.Finite := by
  apply ae_finite_of_depth_bound (labelMeasure d) (fun U v => DownwardOpen p U r v)
    r.1.length (ENNReal.ofReal p) _ ENNReal.ofReal_ne_top
    (fun _ _ h => h.1.length_le) (downwardOpen_mass_le hp0 hp1 r)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_lt_one]
  exact hp

theorem ae_all_finite_downwardOpen {d : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : (d - 1 : ℕ) * p < 1) :
    ∀ᵐ U ∂labelMeasure d, ∀ r : TreeVertex d,
      {v | DownwardOpen p U r v}.Finite := by
  exact ae_all_iff.2 (ae_finite_downwardOpen hp0 hp1 hp)

lemma pathCoordinates_ne_nil {d : ℕ} {m : ℕ} {v w : TreeVertex d}
    (hw : w ∈ pathCoordinates m v) : w.1 ≠ [] := by
  obtain ⟨k, hk, hkv, rfl⟩ := mem_pathCoordinates.mp hw
  intro hnil
  have hlen := ConnectedHull.prefix_length_eq v hkv
  rw [hnil, List.length_nil] at hlen
  omega

lemma path_event_eq_cylinder {d : ℕ} {Ω : Type*} (U : Ω → TreeVertex d → ℝ)
    (p : ℝ) (m : ℕ) (v : TreeVertex d) :
    {ω | ∀ k : ℕ, m < k → k ≤ v.1.length →
      U ω (ConnectedHull.takeVertex v k) ≤ p} =
    {ω | ∀ w ∈ pathCoordinates m v, U ω w ≤ p} := by
  ext ω
  constructor
  · intro h w hw
    obtain ⟨k, hk, hkv, rfl⟩ := mem_pathCoordinates.mp hw
    exact h k hk hkv
  · intro h k hk hkv
    exact h _ (mem_pathCoordinates.mpr ⟨k, hk, hkv, rfl⟩)

theorem ae_all_finite_downwardOpen_of_cylinder_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → TreeVertex d → ℝ) {p : ℝ}
    (hp : (d - 1 : ℕ) * p < 1) (_hp0 : 0 ≤ p)
    (hCylinder : ∀ S : Finset (TreeVertex d), (∀ v ∈ S, v.1 ≠ []) →
      μ {ω | ∀ v ∈ S, U ω v ≤ p} ≤ (ENNReal.ofReal p) ^ S.card) :
    ∀ᵐ ω ∂μ, ∀ r : TreeVertex d, {v | DownwardOpen p (U ω) r v}.Finite := by
  apply ae_all_iff.2
  intro r
  have hsmall : ((d - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal p < 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_lt_one]
    exact hp
  apply ae_finite_of_depth_bound μ (fun ω v => DownwardOpen p (U ω) r v)
    r.1.length (ENNReal.ofReal p) hsmall ENNReal.ofReal_ne_top
    (fun _ _ h => h.1.length_le)
  intro v
  calc
    μ {ω | DownwardOpen p (U ω) r v} ≤
        μ {ω | ∀ k : ℕ, r.1.length < k → k ≤ v.1.length →
          U ω (ConnectedHull.takeVertex v k) ≤ p} := measure_mono (fun _ h => h.2)
    _ = μ {ω | ∀ w ∈ pathCoordinates r.1.length v, U ω w ≤ p} :=
      congrArg μ (path_event_eq_cylinder U p r.1.length v)
    _ ≤ (ENNReal.ofReal p) ^ (pathCoordinates r.1.length v).card :=
      hCylinder _ (fun _ hw => pathCoordinates_ne_nil hw)
    _ = (ENNReal.ofReal p) ^ (v.1.length - r.1.length) := by
      rw [card_pathCoordinates]

lemma measurableSet_downwardOpen {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {U : Ω → TreeVertex d → ℝ} (hU : ∀ v, Measurable (fun ω => U ω v))
    (p : ℝ) (r v : TreeVertex d) :
    MeasurableSet {ω | DownwardOpen p (U ω) r v} := by
  by_cases hpre : r.1 <+: v.1
  · simp only [DownwardOpen, hpre, true_and]
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k : ℕ =>
      MeasurableSet.iInter fun _ : r.1.length < k =>
        MeasurableSet.iInter fun _ : k ≤ v.1.length =>
          measurableSet_le (hU _) measurable_const
  · simp only [DownwardOpen, hpre, false_and, Set.ofPred_false, MeasurableSet.empty]

end SubcriticalClusters
end Problem367

end

end OAI
