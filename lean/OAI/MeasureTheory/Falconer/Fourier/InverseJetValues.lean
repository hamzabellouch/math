import OAI.MeasureTheory.Falconer.Fourier.InverseJetSymbols
import OAI.MeasureTheory.Falconer.Estimates.InverseScalarPullout
import OAI.MeasureTheory.Falconer.Fourier.JetStateAmbient

namespace OAI

/-! # Exact values of the descriptor inverse factors

The additional label is the actual smooth angular multiplier. The other
labels are the original ambient descriptor masks, each occurring once.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol
variable {m K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

noncomputable def seedJet (f : DescriptorJetSymbol (m+1) K L F D) :
    DescriptorInverseLabel F → MaskJetIndex (m+3) :=
  Sum.elim (fun _ => MaskJetIndex.zero (m+3)) (fun b => f.jet b)

noncomputable def seedRadius (_f : DescriptorJetSymbol (m+1) K L F D)
    (N : ℕ) (σ : ℝ) : DescriptorInverseLabel F → ℝ :=
  Sum.elim (fun _ => D⁻¹) (fun b => descriptorMaskRadius N σ b)

noncomputable def seedMask (f : DescriptorJetSymbol (m+1) K L F D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3))) :
    DescriptorInverseLabel F → Space (m+3) → Space (m+3) → ℂ :=
  Sum.elim (fun _ _ => f.angular)
    (fun b x z => (descriptorAmbientMask Q ρ profile N σ J i b (S b) x z : ℂ))

 theorem seedMask_smooth (f : DescriptorJetSymbol (m+1) K L F D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (a : DescriptorInverseLabel F) (x : Space (m+3)) :
    ContDiff ℝ ∞ (f.seedMask Q ρ profile N σ J i S a x) := by
  cases a with
  | inl a => exact f.angular_smooth
  | inr b =>
    exact Complex.ofRealCLM.contDiff.comp
      (descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) x)

 theorem seedRadius_pos (f : DescriptorJetSymbol (m+1) K L F D) (hD : 0 < D)
    (N : ℕ) (σ : ℝ) (a : DescriptorInverseLabel F) : 0 < f.seedRadius N σ a := by
  cases a with
  | inl a => exact inv_pos.mpr hD
  | inr b => exact descriptorMaskRadius_pos N σ b

 theorem seedProduct (f : DescriptorJetSymbol (m+1) K L F D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (x z : Space (m+3)) :
    (∏ a : DescriptorInverseLabel F, (f.seedJet a).scaledValue (f.seedRadius N σ a)
      (f.seedMask Q ρ profile N σ J i S a x) z) =
      (∏ b ∈ F, normalizedAmbientDescriptorJet Q ρ profile N σ J i b (S b)
        (f.jet b).order (f.jet b).vectors x z : ℝ)*f.angular z := by
  have hzero : (f.seedJet (.inl ())).scaledValue (f.seedRadius N σ (.inl ()))
      (f.seedMask Q ρ profile N σ J i S (.inl ()) x) z = f.angular z := by
    change (MaskJetIndex.zero (m+3)).scaledValue D⁻¹ f.angular z = _
    rw [MaskJetIndex.scaledValue,MaskJetIndex.zero_value]
    change (1 : ℝ) • f.angular z = _
    exact one_smul ℝ _
  have hmask (b : {b // b ∈ F}) :
      (f.seedJet (.inr b)).scaledValue (f.seedRadius N σ (.inr b))
        (f.seedMask Q ρ profile N σ J i S (.inr b) x) z =
      (normalizedAmbientDescriptorJet Q ρ profile N σ J i b (S b)
        (f.jet b).order (f.jet b).vectors x z : ℂ) := by
    change (f.jet b).scaledValue (descriptorMaskRadius N σ b)
      (fun z => (descriptorAmbientMask Q ρ profile N σ J i b (S b) x z : ℂ)) z = _
    rw [MaskJetIndex.scaledValue_ofReal _ _ _
      (descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) x)]
    rfl
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique]
  rw [hzero]
  simp_rw [hmask]
  rw [Finset.prod_coe_sort F (fun b =>
    (normalizedAmbientDescriptorJet Q ρ profile N σ J i b (S b)
      (f.jet b).order (f.jet b).vectors x z : ℂ)),← Complex.ofReal_prod]
  ring

 theorem ambient_eq_seedProduct (f : DescriptorJetSymbol (m+1) K L F D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (A : ℝ) (x z : Space (m+3)) :
    f.ambient Q ρ profile N σ J i S A x z = f.spatial x*(A⁻¹ : ℝ)*
      (∏ a : DescriptorInverseLabel F, (f.seedJet a).scaledValue (f.seedRadius N σ a)
        (f.seedMask Q ρ profile N σ J i S a x) z) := by
  rw [f.seedProduct]
  rfl

end DescriptorJetSymbol

noncomputable def descriptorInverseSeparation {m KL KR L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (j : ℕ) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3))) :
    SmoothSeparation (Space (m+3)) (Space (m+3)) (Space (m+3)) :=
  seededJetSeparation m j (descriptorInverseSeed f g)
    (Sum.elim (f.seedRadius N σ) (g.seedRadius N σ))
    (f.seedMask Q ρ profile N σ J i S) (g.seedMask Q ρ profile N σ J i S)
    (f.seedMask_smooth Q ρ profile N σ J i S) (g.seedMask_smooth Q ρ profile N σ J i S)

theorem descriptorInverseSeparation_left {m KL KR L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (j : ℕ) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index)
    (x : Space (m+3)) (w : Sphere (m+3)) :
    (descriptorInverseSeparation f g j Q ρ profile N σ J i S).left a x w =
      (((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).coefficient w *
        (((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
          (.inl (.inl ()))).scaledValue D⁻¹ f.angular w) *
        descriptorJetProduct Q ρ profile N σ J i F id S
          (fun b => (f.inverseLeftJets g j a b).order)
          (fun b _ => (f.inverseLeftJets g j a b).vectors) x w := by
  let T := (MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j
  have hmask (b : {b // b ∈ F}) :
      ((T.term a).jet (.inl (.inr b))).scaledValue
        (f.seedRadius N σ (.inr b))
        (f.seedMask Q ρ profile N σ J i S (.inr b) x) w =
      normalizedDescriptorJet Q ρ profile N σ J i b (S b)
        (f.inverseLeftJets g j a b).order (f.inverseLeftJets g j a b).vectors x w := by
    change ((T.term a).jet (.inl (.inr b))).scaledValue (descriptorMaskRadius N σ b)
      (fun z => (descriptorAmbientMask Q ρ profile N σ J i b (S b) x z : ℂ)) w = _
    rw [MaskJetIndex.scaledValue_ofReal _ _ _
      (descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) x)]
    have hj : f.inverseLeftJets g j a b = (T.term a).jet (.inl (.inr b)) := by
      simp only [DescriptorJetSymbol.inverseLeftJets,dite_eq_left b.property]
      rfl
    rw [← hj]
    rfl
  change (T.term a).coefficient w *
    (∏ l : DescriptorInverseLabel F, ((T.term a).jet (.inl l)).scaledValue
      (f.seedRadius N σ l) (f.seedMask Q ρ profile N σ J i S l x) w) = _
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique]
  change (T.term a).coefficient w *
      (((T.term a).jet (.inl (.inl ()))).scaledValue D⁻¹ f.angular w *
        ∏ b : {b // b ∈ F}, ((T.term a).jet (.inl (.inr b))).scaledValue
          (f.seedRadius N σ (.inr b)) (f.seedMask Q ρ profile N σ J i S (.inr b) x) w) = _
  simp_rw [hmask]
  rw [Finset.prod_coe_sort F (fun b =>
    normalizedDescriptorJet Q ρ profile N σ J i b (S b)
      (f.inverseLeftJets g j a b).order (f.inverseLeftJets g j a b).vectors x w)]
  change _ = (T.term a).coefficient w *
    (((T.term a).jet (.inl (.inl ()))).scaledValue D⁻¹ f.angular w) * _
  exact (mul_assoc _ _ _).symm

theorem descriptorInverseSeparation_right {m KL KR L : ℕ}
    {F G : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol (m+1) KL L F D) (g : DescriptorJetSymbol (m+1) KR L G D)
    (j : ℕ) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (a : ((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).index)
    (x : Space (m+3)) (w : Sphere (m+3)) :
    (descriptorInverseSeparation f g j Q ρ profile N σ J i S).right a x w =
      (((((MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j).term a).jet
          (.inr (.inl ()))).scaledValue D⁻¹ g.angular w) *
        descriptorJetProduct Q ρ profile N σ J i G id S
          (fun b => (f.inverseRightJets g j a b).order)
          (fun b _ => (f.inverseRightJets g j a b).vectors) x w := by
  let T := (MaskJetExpansion.seed (descriptorInverseSeed f g)).inverse m j
  have hmask (b : {b // b ∈ G}) :
      ((T.term a).jet (.inr (.inr b))).scaledValue
        (g.seedRadius N σ (.inr b))
        (g.seedMask Q ρ profile N σ J i S (.inr b) x) w =
      normalizedDescriptorJet Q ρ profile N σ J i b (S b)
        (f.inverseRightJets g j a b).order (f.inverseRightJets g j a b).vectors x w := by
    change ((T.term a).jet (.inr (.inr b))).scaledValue (descriptorMaskRadius N σ b)
      (fun z => (descriptorAmbientMask Q ρ profile N σ J i b (S b) x z : ℂ)) w = _
    rw [MaskJetIndex.scaledValue_ofReal _ _ _
      (descriptorAmbientMask_contDiff Q ρ profile N σ J i b (S b) x)]
    have hj : f.inverseRightJets g j a b = (T.term a).jet (.inr (.inr b)) := by
      simp only [DescriptorJetSymbol.inverseRightJets,dite_eq_left b.property]
      rfl
    rw [← hj]
    rfl
  change (∏ l : DescriptorInverseLabel G, ((T.term a).jet (.inr l)).scaledValue
    (g.seedRadius N σ l) (g.seedMask Q ρ profile N σ J i S l x) w) = _
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique]
  change ((T.term a).jet (.inr (.inl ()))).scaledValue D⁻¹ g.angular w *
      (∏ b : {b // b ∈ G}, ((T.term a).jet (.inr (.inr b))).scaledValue
          (g.seedRadius N σ (.inr b)) (g.seedMask Q ρ profile N σ J i S (.inr b) x) w) = _
  simp_rw [hmask]
  rw [Finset.prod_coe_sort G (fun b =>
    normalizedDescriptorJet Q ρ profile N σ J i b (S b)
      (f.inverseRightJets g j a b).order (f.inverseRightJets g j a b).vectors x w)]
  rfl

namespace DescriptorJetSymbol

/-- Restoring both normalization constants recovers the original spatial
factor and every normalized descriptor jet exactly. -/
theorem value_normalized_angular_restore {n K L : ℕ} {F : Finset PolicyDescriptor}
    {D : ℝ} (u : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (q : Space (n+2) → ℂ)
    (hq : u.angular = normalizedAngular B q) (x : Space (n+2)) (w : Sphere (n+2)) :
    ((A*B : ℝ) : ℂ)*u.value Q ρ profile N σ J i S A x w =
      u.spatial x*q w*descriptorJetProduct Q ρ profile N σ J i F id S
        (fun b => (u.jet b).order) (fun b _ => (u.jet b).vectors) x w := by
  let P := descriptorJetProduct Q ρ profile N σ J i F id S
    (fun b => (u.jet b).order) (fun b _ => (u.jet b).vectors) x w
  have ha : (A : ℂ)*((A⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul,mul_inv_cancel₀ hA.ne',Complex.ofReal_one]
  have hb : (B : ℂ)*((B⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul,mul_inv_cancel₀ hB.ne',Complex.ofReal_one]
  change ((A*B : ℝ) : ℂ)*(P*(u.spatial x*((A⁻¹ : ℝ) : ℂ)*u.angular w)) =
    u.spatial x*q w*P
  rw [hq]
  simp only [normalizedAngular,Complex.real_smul,Complex.ofReal_mul]
  calc
    _ = ((A : ℂ)*((A⁻¹ : ℝ) : ℂ))*((B : ℂ)*((B⁻¹ : ℝ) : ℂ))*
        (u.spatial x*q w*P) := by ring
    _ = _ := by rw [ha,hb,one_mul,one_mul]

end DescriptorJetSymbol

end Falconer

end OAI
