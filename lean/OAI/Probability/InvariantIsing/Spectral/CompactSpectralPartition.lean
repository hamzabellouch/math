import OAI.Probability.InvariantIsing.Spectral.PositiveSpectralRounding
import OAI.Probability.InvariantIsing.Spectral.CompactSpectralQuantizers

namespace OAI

/-! Finite positive-mass spectral partitions for the compact-support approximation. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open scoped Topology Classical Function BigOperators

namespace InvariantIsing

def spectralBallWeight {n : ℕ} (ν : ProbabilityMeasure ℝ) (c r : Fin n → ℝ)
    (i : Option (Fin n)) : ℝ :=
  (ν : Measure ℝ).real (spectralBallCell (fun i => ball (c i) (r i)) i)

def spectralBallValue {n : ℕ} (c : Fin n → ℝ) (a : ℝ) (i : Option (Fin n)) : ℝ :=
  i.elim a c

structure CompactSpectralPartition (ν : ProbabilityMeasure ℝ) (a b δ : ℝ) where
  size : ℕ
  center : Fin size → ℝ
  radius : Fin size → ℝ
  center_mem : ∀ i, center i∈Icc a b
  radius_le : ∀ i, radius i ≤ δ
  null_boundary : ∀ i, (ν : Measure ℝ) (frontier (ball (center i) (radius i)))=0
  covers : (ν : Measure ℝ).support ⊆ ⋃ i, ball (center i) (radius i)
  lower : {i // 0 < spectralBallWeight ν center radius i}
  upper : {i // 0 < spectralBallWeight ν center radius i}
  lower_le : ∀ i : {i // 0 < spectralBallWeight ν center radius i},
    spectralBallValue center a lower ≤ spectralBallValue center a i
  le_upper : ∀ i : {i // 0 < spectralBallWeight ν center radius i},
    spectralBallValue center a i ≤ spectralBallValue center a upper

theorem exists_compact_spectral_partition (ν : ProbabilityMeasure ℝ) (a b δ : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (hδ : 0 < δ) :
    Nonempty (CompactSpectralPartition ν a b δ) := by
  obtain ⟨n,c,r,hc,hr,hn,hb⟩ := spectral_null_boundary_cover (ν : Measure ℝ)
    (ν : Measure ℝ).support hcompact δ hδ
  let S := spectralBallCell (fun i => ball (c i) (r i))
  let w := spectralBallWeight ν c r
  have hsum : ∑ i, w i=1 := spectralPartitionWeights_sum (ν : Measure ℝ) S
    (spectralBallCell_cover _) (spectralBallCell_disjoint _)
    (spectralBallCell_measurable _ (fun _ => measurableSet_ball))
  obtain ⟨i,hi⟩ := exists_pos_spectral_weight (fun _ => measureReal_nonneg) hsum
  let P := {i // 0 < w i}
  have he : (Finset.univ : Finset P).Nonempty := ⟨⟨i,hi⟩,Finset.mem_univ _⟩
  obtain ⟨lo,_,hlo⟩ := Finset.exists_min_image Finset.univ
    (fun i : P => spectralBallValue c a i) he
  obtain ⟨up,_,hup⟩ := Finset.exists_max_image Finset.univ
    (fun i : P => spectralBallValue c a i) he
  exact ⟨⟨n,c,r,(fun i => hbound (hc i)),(fun i => (hr i).2.le),hn,hb,lo,up,
    (fun i => hlo i (Finset.mem_univ i)),(fun i => hup i (Finset.mem_univ i))⟩⟩

namespace CompactSpectralPartition

variable {ν : ProbabilityMeasure ℝ} {a b δ : ℝ} (D : CompactSpectralPartition ν a b δ)

def cells : Option (Fin D.size) → Set ℝ :=
  spectralBallCell (fun i => ball (D.center i) (D.radius i))

def weight : Option (Fin D.size) → ℝ := spectralBallWeight ν D.center D.radius

def value : Option (Fin D.size) → ℝ := spectralBallValue D.center a

abbrev Positive := {i // 0 < D.weight i}

lemma weight_sum : ∑ i : D.Positive, D.weight i=1 :=
  positiveSpectralWeights_sum D.weight (fun _ => measureReal_nonneg)
    (spectralPartitionWeights_sum (ν : Measure ℝ) D.cells (spectralBallCell_cover _)
      (spectralBallCell_disjoint _) (spectralBallCell_measurable _ (fun _ => measurableSet_ball)))

def law : ProbabilityMeasure ℝ :=
  ⟨finiteSpectralMeasure (fun i : D.Positive => D.weight i) (fun i => D.value i),
    finiteSpectralMeasure_probability _ _ (fun _ => measureReal_nonneg) D.weight_sum⟩

def edge : ℝ := D.value D.upper

lemma value_mem (hab : a ≤ b) (i : Option (Fin D.size)) : D.value i∈Icc a b := by
  cases i with
  | none => exact ⟨le_rfl,hab⟩
  | some i => exact D.center_mem i

lemma residual_zero : (ν : Measure ℝ) (D.cells none)=0 :=
  spectralBallCell_residual_null (ν : Measure ℝ) _ (ν : Measure ℝ).support
    (ν : Measure ℝ).measure_compl_support D.covers

lemma law_eq_map : (D.law : Measure ℝ)=
    (ν : Measure ℝ).map (spectralBallQuantizer D.center D.radius a) := by
  change finiteSpectralMeasure (fun i : D.Positive => D.weight i) (fun i => D.value i)=_
  rw [finiteSpectralMeasure_positive D.weight D.value (fun _ => measureReal_nonneg)]
  exact (spectralPartition_pushforward (ν : Measure ℝ) D.cells (spectralBallCell_cover _)
    (spectralBallCell_disjoint _) (spectralBallCell_measurable _ (fun _ => measurableSet_ball))
    D.value).symm

lemma quantizer_close : ∀ᵐ x ∂(ν : Measure ℝ),
    dist (spectralBallQuantizer D.center D.radius a x) x ≤ δ := by
  filter_upwards [(ν : Measure ℝ).support_mem_ae] with x hx
  exact spectralBallQuantizer_close D.center D.radius a δ x D.radius_le (D.covers hx)

lemma endpoint_bounds (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support) :
    D.value D.lower-δ ≤ a ∧ b ≤ D.edge+δ :=
  positive_spectral_edge_bounds (ν : Measure ℝ) D.cells (spectralBallCell_cover _)
    D.value δ a b ha hb D.lower D.upper D.lower_le D.le_upper D.quantizer_close

lemma law_support (hab : a ≤ b) : ∀ᵐ x ∂(D.law : Measure ℝ), x∈Icc a D.edge := by
  exact ae_finiteSpectralMeasure _ _ (fun i : D.Positive =>
    ⟨(D.value_mem hab i).1,D.le_upper i⟩)

end CompactSpectralPartition
end InvariantIsing

end

end OAI
