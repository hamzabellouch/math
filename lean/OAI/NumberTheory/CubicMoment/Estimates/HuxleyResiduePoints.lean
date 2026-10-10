import OAI.NumberTheory.CubicMoment.Estimates.HuxleyFiniteDual

namespace OAI

/-! The literal residue sums as a finite set of reduced fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev HuxleyResidueIndex (Q : ℝ) :=
  Σ q : {q : Eisenstein // q ∈ nonzeroNormBall Q}, Residues q.val

abbrev huxleyResidueFintype {Q : ℝ} (q : {q : Eisenstein // q ∈ nonzeroNormBall Q}) :
    Fintype (Residues q.val) :=
  @Fintype.ofFinite _ (finite_residues (mem_nonzeroNormBall.mp q.property).2)

abbrev huxleyResidueIndexFintype (Q : ℝ) : Fintype (HuxleyResidueIndex Q) := by
  let _ (q : {q : Eisenstein // q ∈ nonzeroNormBall Q}) : Fintype (Residues q.val) := huxleyResidueFintype q
  exact inferInstance

def huxleyIndexLift {Q : ℝ} (p : HuxleyResidueIndex Q) : HuxleyLift :=
  ⟨p.1.val,residueRepresentative p.1.val p.2,0⟩

lemma huxleyIndexLift_injective (Q : ℝ) : Function.Injective (@huxleyIndexLift Q) := by
  rintro ⟨⟨q,hq⟩,x⟩ ⟨⟨r,hr⟩,y⟩ h
  have hqr : q = r := congrArg HuxleyLift.denominator h
  subst r
  have hxy : x = y := by
    have hn : residueRepresentative q x = residueRepresentative q y :=
      congrArg HuxleyLift.numerator h
    have hm := congrArg (Ideal.Quotient.mk (modulus q)) hn
    simpa only [residueRepresentative_spec] using hm
  subst y
  rfl

def huxleyResiduePointSet (Q : ℝ) : Finset HuxleyLift := by
  let _ : Fintype (HuxleyResidueIndex Q) := huxleyResidueIndexFintype Q
  exact (Finset.univ.filter (fun p : HuxleyResidueIndex Q => IsUnit p.2)).image huxleyIndexLift

lemma huxleyResiduePointSet_reduced (Q : ℝ) :
    ∀ p ∈ huxleyResiduePointSet Q, p.reduced Q := by
  let _ : Fintype (HuxleyResidueIndex Q) := huxleyResidueIndexFintype Q
  intro p hp
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
  have hq := mem_nonzeroNormBall.mp j.1.property
  exact huxleyLift_actual hq.2 hq.1 j.2 (Finset.mem_filter.mp hj).2 0

lemma huxleyResiduePointSet_shift (Q : ℝ) :
    ∀ p ∈ huxleyResiduePointSet Q, p.shift = 0 := by
  let _ : Fintype (HuxleyResidueIndex Q) := huxleyResidueIndexFintype Q
  intro p hp
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
  rfl

lemma huxleyResiduePointSet_sum (Q : ℝ) (f : HuxleyLift → ℝ) :
    (∑ p ∈ huxleyResiduePointSet Q, f p) =
      ∑ q ∈ nonzeroNormBall Q, ∑' x : Residues q,
        if IsUnit x then f ⟨q,residueRepresentative q x,0⟩ else 0 := by
  let _ (q : {q : Eisenstein // q ∈ nonzeroNormBall Q}) : Fintype (Residues q.val) := huxleyResidueFintype q
  let _ : Fintype (HuxleyResidueIndex Q) := huxleyResidueIndexFintype Q
  unfold huxleyResiduePointSet
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    rw [Fintype.sum_sigma]
    rw [← Finset.sum_coe_sort (nonzeroNormBall Q)]
    apply Finset.sum_congr rfl
    intro q hq
    rw [tsum_fintype]
    rfl
  · exact fun _ _ _ _ h => huxleyIndexLift_injective Q h

lemma huxleySieveMass_eq_points (Q Z : ℝ) (v : Eisenstein → ℂ) :
    huxleySieveMass Q Z v = ∑ p ∈ huxleyResiduePointSet Q,
      ‖∑ n ∈ nonzeroNormBall Z, v n*huxleyFrequencyPhase p.frequency n‖^2 := by
  rw [huxleyResiduePointSet_sum]
  unfold huxleySieveMass
  apply Finset.sum_congr rfl
  intro q hq
  unfold huxleyModulusMass
  apply tsum_congr
  intro x
  split_ifs <;> try rfl
  unfold additiveSievePolynomial
  congr 2
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  rw [huxleyPhase_eq_frequency]
  simp [HuxleyLift.frequency]

end CubicFirstMoment

end

end OAI
