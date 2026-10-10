import OAI.Geometry.Relativity.CKS.CollarFieldRegion
import OAI.Geometry.Relativity.CKS.SourcePhysicalTensor

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

 def rawExpansionValue (p : RawNullInput) : ℝ := 1+rz p.1^3*(rawD p.1).1
 def rawOrientedDomain : Set RawNullInput := rawPositiveDomain ∩ {p | 0<rawExpansionValue p}

lemma rawExpansionValue_continuousAt {p : RawNullInput} (hp : rawRegular p.1) :
    ContinuousAt rawExpansionValue p := by
  have hd := (rawD_smooth hp).continuousAt.fst.comp
    (continuous_fst.continuousAt : ContinuousAt (Prod.fst : RawNullInput → RawCollarInput) p)
  exact continuousAt_const.add ((by fun_prop : ContinuousAt (fun p : RawNullInput => rz p.1^3) p).mul hd)

lemma rawOrientedDomain_open : IsOpen rawOrientedDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hd := (rawExpansionValue_continuousAt hp.1.1.1).eventually
    (isOpen_Ioi.mem_nhds hp.2)
  filter_upwards [rawPositiveDomain_open.mem_nhds hp.1,hd] with q hq hqd
  exact ⟨hq,hqd⟩

lemma rawOrientedFamily_regular {K : Set MatrixScalarJet}
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) (B : ℝ) :
    rawReferenceFamily K B ⊆ rawOrientedDomain := by
  intro p hp
  refine ⟨rawPositiveFamily_regular hreg B hp,?_⟩
  change 0<1+rz p.1^3*(rawD p.1).1
  rw [hp.1.2]
  norm_num

lemma field_expansion_value (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point}
    (hf : f.RegularAt x) (h0 : determinant (fieldQ b f x) ≠ 0) :
    lapseDField (b 0) (fieldD b f) x=rawExpansionValue (thinRaw (fieldRaw b f x)) := by
  have hh := congrArg Prod.fst (field_rawD b hf h0)
  change fieldD b f x=(rawD (fieldRaw b f x).1).1 at hh
  change 1+b 0^3*fieldD b f x=1+b 0^3*(rawD (thinRaw (fieldRaw b f x)).1).1
  rw [thinD,hh]

theorem bounded_thin_oriented_fields {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      f.RegularAt x → matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r →
      positiveAngular (fieldQ b f x) ∧
      0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x ∧
      0 < lapseDField (b 0) (fieldD b f) x := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  obtain ⟨δ,hδ,hdom⟩ := (rawReferenceFamily_compact hK B).exists_cthickening_subset_open
    rawOrientedDomain_open (rawOrientedFamily_regular hreg B)
  refine ⟨max 1 (1/δ),le_max_left _ _,?_⟩
  intro b f x hf hq hb hbound r hr hz
  obtain ⟨_,hd⟩ := inverse_radius_threshold hδ hr
  have hh : |rz (thinRaw (fieldRaw b f x)).1| ≤ δ := by change |b 0| ≤ δ; rw [hz]; exact hd
  obtain ⟨hp,_⟩ := raw_reference_tube (p:=thinRaw (fieldRaw b f x)) hq
    (fieldRaw_thin_norm hB hb hbound) hh
  have h1 := hdom hp
  have hprim := (thinRaw_primitive_regular (fieldRaw b f x)).mp ⟨h1.1.1.1,h1.1.1.2.1⟩
  obtain ⟨hqr,hrad,_⟩ := field_primitive_regular b hf hprim
  refine ⟨?_,hrad,?_⟩
  · rw [field_angular_matrix b hf]
    exact h1.1.2
  · rw [field_expansion_value b hf hqr]
    exact h1.2

lemma fieldNormalizedLapse_positive {b : Fin 5 → ℝ} {f : CollarCoefficientFields} {x : Point}
    (hr : 0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x)
    (hd : 0 < lapseDField (b 0) (fieldD b f) x) :
    0<fieldNormalizedLapse b f x := by
  have he : ((b 0)^2+(1+(b 0)^3*fieldT b f x)^2-2*(b 0)^3*fieldF b f x)/(1+(b 0)^2)=
      lapseRadField (b 0) (fieldT b f) (fieldF b f) x := by
    unfold lapseRadField lapseVField
    have hz : 1+(b 0)^2 ≠ 0 := by positivity
    field_simp
    ring
  unfold fieldNormalizedLapse lapseNormalizedField
  rw [he]
  exact div_pos (Real.sqrt_pos.mpr hr) hd

end
end CKSAngularGeometry

end

end OAI
