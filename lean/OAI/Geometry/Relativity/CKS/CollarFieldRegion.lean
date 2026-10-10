import OAI.Geometry.Relativity.CKS.CollarThinConstraint

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma thinRaw_primitive_regular (p : RawNullInput) :
    (rawRegular (thinRaw p).1 ∧ rawLapseInput (thinRaw p).1 ∈ lapseCoefficientRegion) ↔
      (rawRegular p.1 ∧ rawLapseInput p.1 ∈ lapseCoefficientRegion) := by
  have hq : rawRegular (thinRaw p).1 ↔ rawRegular p.1 := by
    unfold rawRegular
    rw [thinQ]
  have hl : rawLapseInput (thinRaw p).1=rawLapseInput p.1 := by
    unfold rawLapseInput
    rw [thinT,thinF,thinD]
    rfl
  rw [hq,hl]

lemma field_primitive_regular (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point}
    (hf : f.RegularAt x)
    (hp : rawRegular (fieldRaw b f x).1 ∧ rawLapseInput (fieldRaw b f x).1 ∈ lapseCoefficientRegion) :
    determinant (fieldQ b f x) ≠ 0 ∧
    0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x ∧
    lapseDField (b 0) (fieldD b f) x ≠ 0 := by
  have hq : determinant (fieldQ b f x) ≠ 0 := by
    rw [field_angular_matrix b hf]
    exact hp.1
  refine ⟨hq,?_,?_⟩
  · have hh := congrArg Prod.fst (actual_lapseRadField (b 0) (fieldT_diff b hf)
      (fieldF_diff b hf) (rawD (fieldRaw b f x).1))
    rw [field_rawT b hf,field_rawF b hf] at hh
    change lapseRadField (b 0) (fieldT b f) (fieldF b f) x=
      (lapseRad (rawLapseInput (fieldRaw b f x).1)).1 at hh
    rw [hh]
    exact hp.2.1
  · have hh := congrArg Prod.fst (actual_lapseDField (b 0) (fieldD_diff b hf hq)
      (rawT (fieldRaw b f x).1) (rawF (fieldRaw b f x).1))
    rw [field_rawD b hf hq] at hh
    change lapseDField (b 0) (fieldD b f) x=(lapseD (rawLapseInput (fieldRaw b f x).1)).1 at hh
    rw [hh]
    exact hp.2.2

theorem bounded_thin_field_regions {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      f.RegularAt x → matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r →
      (determinant (fieldQ b f x) ≠ 0 ∧
        0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x ∧
        lapseDField (b 0) (fieldD b f) x ≠ 0) ∧
      (determinant (fieldQ (oldParams b) f x) ≠ 0 ∧
        0 < lapseRadField ((oldParams b) 0) (fieldT (oldParams b) f) (fieldF (oldParams b) f) x ∧
        lapseDField ((oldParams b) 0) (fieldD (oldParams b) f) x ≠ 0) := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  obtain ⟨δ,hδ,hdom⟩ := (rawReferenceFamily_compact hK B).exists_cthickening_subset_open
    rawNullDomain_open (rawReferenceFamily_regular hreg B)
  refine ⟨max 1 (1/δ),le_max_left _ _,?_⟩
  intro b f x hf hq hb hbound r hr hz
  obtain ⟨_,hd⟩ := inverse_radius_threshold hδ hr
  have hh : |rz (thinRaw (fieldRaw b f x)).1| ≤ δ := by change |b 0| ≤ δ; rw [hz]; exact hd
  obtain ⟨hp,hp₀⟩ := raw_reference_tube (p:=thinRaw (fieldRaw b f x)) hq
    (fieldRaw_thin_norm hB hb hbound) hh
  have h1 := hdom hp
  have h0 := hdom hp₀
  have h1' := (thinRaw_primitive_regular (fieldRaw b f x)).mp ⟨h1.1,h1.2.1⟩
  have h0' : rawRegular (thinRaw (fieldRaw (oldParams b) f x)).1 ∧
      rawLapseInput (thinRaw (fieldRaw (oldParams b) f x)).1 ∈ lapseCoefficientRegion := by
    rw [fieldRaw_old,thinRaw_old]
    exact ⟨h0.1,h0.2.1⟩
  exact ⟨field_primitive_regular b hf h1',field_primitive_regular (oldParams b) hf
    ((thinRaw_primitive_regular (fieldRaw (oldParams b) f x)).mp h0')⟩

theorem bounded_thin_coordinate_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B A : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      f.RegularAt x → matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r → 0 ≤ b 4 →
      (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
      f.metric 0 x 1 0=f.metric 0 x 0 1 → f.metric 1 x 1 0=f.metric 1 x 0 1 →
      coordinateDEC (fieldNullInput (oldParams b) f x) r → coordinateDEC (fieldNullInput b f x) r := by
  obtain ⟨R,hR,hh⟩ := bounded_thin_field_coordinate_DEC hK hreg hB hA
  obtain ⟨T,hT,ht⟩ := bounded_thin_field_regions hK (fun q hq => (hreg q hq).2.ne') hB
  refine ⟨max R T,hR.trans (le_max_left _ _),?_⟩
  intro b f x hf hq hb hbound r hr hz hw hparams hs₀ hs₁ hDEC
  obtain ⟨⟨hq₁,hr₁,hd₁⟩,⟨hq₀,hr₀,hd₀⟩⟩ := ht b f x hf hq hb hbound r
    ((le_max_right _ _).trans hr) hz
  have hsym (c : Fin 5 → ℝ) : fieldQ c f x 1 0=fieldQ c f x 0 1 := by
    change f.metric 0 x 1 0+(c 0^3*(1-c 1))*f.metric 1 x 1 0 =
      f.metric 0 x 0 1+(c 0^3*(1-c 1))*f.metric 1 x 0 1
    rw [hs₀,hs₁]
  exact hh b f x hf hq hb hbound r ((le_max_left _ _).trans hr) hz hw hparams
    (hsym b) (hsym (oldParams b)) hq₁ hq₀ hr₁ hr₀ hd₁ hd₀ hDEC

end
end CKSAngularGeometry

end

end OAI
