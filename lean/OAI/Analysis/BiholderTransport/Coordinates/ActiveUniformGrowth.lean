import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.CompactConfigurations

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def activeCoordinates (v : M → ℝ) (a : M) (K : Set M) : Set (Model n × Model n) :=
  (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)) ''
      {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ activeLogs v z.1 ∧ z.1 ∈ K}

def activeConfiguration (v : M → ℝ) (a : M) (K : Set M) (T : ℝ) (ι : Type*) [Fintype ι] :=
  {q : EnvelopeData (Model n) ι | (∀ i, (q.1.1,q.1.2 i) ∈ activeCoordinates v a K) ∧
    (∀ i, 0 ≤ q.2.1 i) ∧ (∑ i, q.2.1 i = 1) ∧ q.2.2 ∈ Icc 0 T}

lemma WeakMTW.active_configurations_uniform_growth
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a : M} {K : Set M} (hK : IsCompact K)
    (hKa : K ⊆ (extChartAt 𝓘(ℝ,Model n) a).source)
    {ι : Type*} [Fintype ι] [Nonempty ι] {T : ℝ} (hT : T < 1)
    (hID : ∀ x ∈ K, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      ∀ t ∈ Icc (0:ℝ) T, t • p ∈ injectivityDomain x) :
    ∃ b > 0, ∀ᶠ h : Model n in 𝓝 0,
      ∀ q ∈ activeConfiguration v a K T ι,
        b * ‖h‖^2 ≤ q.2.2 *
          (cTransform v (movingNormal a (q.1.1,h)) -
            cTransform v ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) +
          movingNormalCost a q.1.1 (q.2.2 • ∑ i, q.2.1 i • q.1.2 i) h -
          movingNormalCost a q.1.1 (q.2.2 • ∑ i, q.2.1 i • q.1.2 i) 0 := by
  classical
  obtain ⟨s,hTs,hs1⟩ := exists_between (max_lt (show (0:ℝ)<1 by norm_num) hT)
  have hs : 0 < s := (le_max_left 0 T).trans_lt hTs
  have hTs' : T < s := (le_max_right 0 T).trans_lt hTs
  let Q := activeConfiguration (n := n) v a K T ι
  have hQ : IsCompact Q := compact_common_base_configurations
    (isCompact_active_coordinates hv hK hKa) T
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  have hmem (q : Q) (i : ι) := mem_active_coordinates hKa (q.2.1 i)
  have hbase (q : Q) : q.1.1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target :=
    (hmem q (Classical.arbitrary ι)).1
  have H := hmtw.compact_scaled_envelope_growth a s hs hs1
    (fun q : Q => q.1) continuous_subtype_val hbase
    (fun q i => q.2.2.1 i) (fun q => q.2.2.2.1)
    (fun q => q.2.2.2.2.1) (fun q => q.2.2.2.2.2.trans_lt hTs')
    (fun q i => (hmem q i).2.1.1) (fun q p hp => hID _
      (hmem q (Classical.arbitrary ι)).2.2 p
      ((convexHull_mono (by rintro _ ⟨i,rfl⟩; exact (hmem q i).2.1)) hp)
      _ q.2.2.2.2)
  obtain ⟨b,hb,H⟩ := H
  refine ⟨b,hb,?_⟩
  filter_upwards [H] with h hh q hq
  obtain ⟨i,hi⟩ := hh ⟨q,hq⟩
  have hp := (hmem ⟨q,hq⟩ i).2.1
  have hsup := active_split_lower_support hv hp.1 hp.2 hs hs1
    (movingNormal a (q.1.1,h))
  have he : riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
      (s • chartFiberInverse a q.1.1 (q.1.2 i)) = movingNormal a (q.1.1,s • q.1.2 i) := by
    rw [movingNormal_eq (hbase ⟨q,hq⟩),map_smul]
  rw [he] at hsup
  have hsup' := mul_le_mul_of_nonneg_left hsup hq.2.2.2.1
  unfold scaledNormalEnvelope movingNormalCost at hi
  rw [movingNormal_zero (hbase ⟨q,hq⟩)] at hi
  change b * ‖h‖^2 ≤ _
  unfold movingNormalCost
  rw [movingNormal_zero (hbase ⟨q,hq⟩)]
  nlinarith [show q.2.2 * (-(cost (movingNormal a (q.1.1,h))
      (movingNormal a (q.1.1,s • q.1.2 i)) -
        cost ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
          (movingNormal a (q.1.1,s • q.1.2 i))) / s) =
      -(q.2.2 / s) * (cost (movingNormal a (q.1.1,h))
        (movingNormal a (q.1.1,s • q.1.2 i)) -
          cost ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
            (movingNormal a (q.1.1,s • q.1.2 i))) by ring]

end WeakMTWTransport

end

end OAI
