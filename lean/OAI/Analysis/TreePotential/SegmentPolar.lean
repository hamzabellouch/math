import OAI.Analysis.TreePotential.SegmentBasic

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical
namespace BoundedTreePotentials.Segments


/-- The predual is the completion in the exact atom-testing norm. -/
def atomTests : TestFamily Node where
  carrier := Set.range Atom.profile
  zero_mem := ⟨Atom.zero, Atom.zero_profile⟩
  neg_mem g hg := by
    obtain ⟨A,rfl⟩ := hg
    exact ⟨A.neg, A.neg_profile⟩
  coeff_bound g hg v := by
    obtain ⟨A,rfl⟩ := hg
    exact A.profile_bound v
  singleton_mem v := by
    refine ⟨Atom.coordinate v, ?_⟩
    funext s
    rw [Atom.coordinate_profile]

def unitTests : TestFamily Node where
  carrier := {g | IsUnitTest g}
  zero_mem := unit_zero
  neg_mem _ hg := unit_neg hg
  coeff_bound _ hg := unit_coordinate hg
  singleton_mem v := by
    change IsUnitTest _
    exact unit_coordinate_test v

abbrev Predual := TestCompletion atomTests
abbrev Dual := StrongDual ℝ Predual

/-- The polar core is identified with the full continuous dual using block reflexivity and density. -/

abbrev DualCore := TestCompletion unitTests

lemma finitePairing_profile (A : Atom) (g : Node →₀ ℝ) :
    finitePairing A.profile g = A.pairing g := by
  unfold finitePairing Atom.profile Atom.pairing
  change (∑ v ∈ g.support, g v*(∑ S ∈ A.family, A.coeff S*(if v ∈ S.nodes then 1 else 0))) = _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hscale : (∑ v ∈ g.support, g v*(A.coeff S*(if v ∈ S.nodes then 1 else 0))) =
      A.coeff S*(∑ v ∈ g.support, if v ∈ S.nodes then g v else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    split_ifs <;> ring
  rw [hscale]
  congr 1
  rw [← Finset.sum_filter]
  unfold Segment.eval
  apply Finset.sum_subset
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v hv hnot
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    exact hnot (Finset.mem_filter.mpr ⟨hmem,hv⟩)

lemma predual_test_bound (g : Node →₀ ℝ) (F : Finset Segment) (hF : Incomparable F) :
    Real.sqrt (∑ S ∈ F, (S.eval g)^2) ≤ testNorm atomTests g := by
  let R := Real.sqrt (∑ S ∈ F, (S.eval g)^2)
  have hn : 0 ≤ ∑ S ∈ F, (S.eval g)^2 := Finset.sum_nonneg fun S _ => sq_nonneg _
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = ∑ S ∈ F, (S.eval g)^2 := Real.sq_sqrt hn
  by_cases hR0 : R=0
  · change R ≤ _
    rw [hR0]
    exact testNorm_nonneg _ _
  · have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    let A : Atom := ⟨F,hF,fun S => S.eval g/R,by
      simp only [div_pow, ← Finset.sum_div]
      rw [← hR2, div_self (pow_ne_zero _ hR0)]⟩
    have he : A.pairing g = R := by
      change (∑ S ∈ F, (S.eval g/R)*S.eval g)=R
      calc
        _ = (∑ S ∈ F, (S.eval g)^2)/R := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro S hS
          ring
        _ = R := by rw [← hR2]; field_simp
    have hh := finitePairing_le_testNorm atomTests ⟨A.profile,⟨A,rfl⟩⟩ g
    rw [finitePairing_profile, he, abs_of_nonneg hR] at hh
    exact hh

lemma predual_unit_iff (g : Node →₀ ℝ) : testNorm atomTests g ≤ 1 ↔ IsUnitTest g := by
  constructor
  · intro hg F hF
    have hh := (predual_test_bound g F hF).trans hg
    have hs := Real.sq_sqrt (show 0 ≤ ∑ S ∈ F, (S.eval g)^2 from Finset.sum_nonneg fun S _ => sq_nonneg _)
    nlinarith [Real.sqrt_nonneg (∑ S ∈ F, (S.eval g)^2)]
  · intro hg
    apply ciSup_le
    rintro ⟨f,A,hA⟩
    subst f
    rw [finitePairing_profile]
    exact A.pairing_bound hg

def segmentVector (S : Segment) : Node →₀ ℝ := ∑ v ∈ S.nodes, Finsupp.single v 1

@[simp] lemma segmentVector_apply (S : Segment) (v : Node) :
    segmentVector S v = if v ∈ S.nodes then 1 else 0 := by
  simp [segmentVector, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]

lemma finitePairing_segmentVector (S : Segment) (g : Node → ℝ) :
    finitePairing g (segmentVector S) = S.eval g := by
  simp [segmentVector, Segment.eval, finitePairing]

namespace Atom

def vector (A : Atom) : Node →₀ ℝ := ∑ S ∈ A.family, A.coeff S • segmentVector S

@[simp] lemma vector_apply (A : Atom) (v : Node) : A.vector v = A.profile v := by
  simp [vector, profile, Finsupp.finsetSum_apply, Finsupp.smul_apply]

lemma finitePairing_vector (A : Atom) (g : Node → ℝ) :
    finitePairing g A.vector = A.pairing g := by
  simp only [vector, map_sum, map_smul, finitePairing_segmentVector, smul_eq_mul, pairing]

def inCore (A : Atom) : DualCore := ((testVectorEquiv unitTests).symm A.vector : TestVector unitTests)

lemma norm_inCore (A : Atom) : ‖A.inCore‖ ≤ 1 := by
  rw [inCore, UniformSpace.Completion.norm_coe]
  change testNorm unitTests A.vector ≤ 1
  apply ciSup_le
  intro g
  rw [finitePairing_vector]
  exact A.pairing_bound g.property

@[simp] lemma zero_vector : zero.vector = 0 := by simp [vector, zero]
@[simp] lemma zero_inCore : zero.inCore = 0 := by simp [inCore]
@[simp] lemma neg_vector (A : Atom) : A.neg.vector = -A.vector := by
  ext v
  simp [neg_profile]
@[simp] lemma neg_inCore (A : Atom) : A.neg.inCore = -A.inCore := by
  simp [inCore, ← UniformSpace.Completion.coe_neg]

@[simp] lemma coordinate_vector (v : Node) : (coordinate v).vector = Finsupp.single v 1 := by
  ext w
  rw [vector_apply, coordinate_profile]
  simp only [Finsupp.single_apply]
  split_ifs <;> simp_all

def oneSegment (S : Segment) : Atom where
  family := {S}
  incomparable := by
    intro U hU V hV hne
    simp only [Finset.mem_singleton] at hU hV
    exact (hne (hU.trans hV.symm)).elim
  coeff := fun _ => 1
  budget := by simp

@[simp] lemma oneSegment_vector (S : Segment) : (oneSegment S).vector = segmentVector S := by
  simp [vector, oneSegment]

end Atom

lemma segmentVector_norm (S : Segment) :
    ‖((testVectorEquiv unitTests).symm (segmentVector S) : TestVector unitTests)‖ = 1 := by
  apply le_antisymm
  · simpa only [Atom.inCore, Atom.oneSegment_vector, UniformSpace.Completion.norm_coe]
      using (Atom.oneSegment S).norm_inCore
  · change 1 ≤ testNorm unitTests (segmentVector S)
    simpa only [segmentVector_apply, S.finish_mem, ↓reduceIte, abs_one]
      using coordinate_le_testNorm unitTests (segmentVector S) S.finish

/-- Normalizing the coefficients in an arbitrary family recovers the exact
unit-test condition from its (absolute, or equivalently signed) atom bounds. -/
lemma unit_iff_pairing_atoms (g : Node → ℝ) :
    IsUnitTest g ↔ ∀ A : Atom, |A.pairing g| ≤ 1 := by
  constructor
  · intro hg A
    exact A.pairing_bound hg
  · intro hg F hF
    let R := Real.sqrt (∑ S ∈ F, (S.eval g)^2)
    have hn : 0 ≤ ∑ S ∈ F, (S.eval g)^2 := Finset.sum_nonneg fun S _ => sq_nonneg _
    have hR : 0 ≤ R := Real.sqrt_nonneg _
    have hR2 : R^2 = ∑ S ∈ F, (S.eval g)^2 := Real.sq_sqrt hn
    by_cases hR0 : R=0
    · nlinarith
    · let A : Atom := ⟨F,hF,fun S => S.eval g/R,by
        simp only [div_pow, ← Finset.sum_div]
        rw [← hR2, div_self (pow_ne_zero _ hR0)]⟩
      have he : A.pairing g = R := by
        change (∑ S ∈ F, (S.eval g/R)*S.eval g)=R
        calc
          _ = (∑ S ∈ F, (S.eval g)^2)/R := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro S hS
            ring
          _ = R := by rw [← hR2]; field_simp
      have hh := hg A
      rw [he, abs_of_nonneg hR] at hh
      nlinarith

def coreLift : (Node →₀ ℝ) →ₗ[ℝ] DualCore :=
  UniformSpace.Completion.toComplL.toLinearMap.comp (testVectorEquiv unitTests).symm.toLinearMap

def functionalCoeffs (φ : DualCore →L[ℝ] ℝ) (v : Node) : ℝ := φ ((Atom.coordinate v).inCore)

lemma functional_coreLift (φ : DualCore →L[ℝ] ℝ) (z : Node →₀ ℝ) :
    φ (coreLift z) = finitePairing (functionalCoeffs φ) z := by
  have hz : z = ∑ v ∈ z.support, z v • Finsupp.single v 1 := by
    ext v
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]
  conv_lhs => rw [hz]
  simp only [map_sum, map_smul, smul_eq_mul, finitePairing_apply, functionalCoeffs,
    Atom.inCore, Atom.coordinate_vector]
  rfl

lemma functional_atom (φ : DualCore →L[ℝ] ℝ) (A : Atom) :
    φ A.inCore = A.pairing (functionalCoeffs φ) := by
  change φ (coreLift A.vector) = _
  rw [functional_coreLift, Atom.finitePairing_vector]

lemma Atom.pairing_smul (A : Atom) (c : ℝ) (g : Node → ℝ) :
    A.pairing (c • g) = c*A.pairing g := by
  unfold Atom.pairing
  simp only [Segment.eval_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  ring

lemma functional_atom_bound (φ : DualCore →L[ℝ] ℝ) {R : ℝ} (hR : 0 < R)
    (h : ∀ A : Atom, φ A.inCore ≤ R) (x : DualCore) : |φ x| ≤ R*‖x‖ := by
  have hab (A : Atom) : |φ A.inCore| ≤ R := by
    rw [abs_le]
    have hn := h A.neg
    rw [Atom.neg_inCore, map_neg] at hn
    exact ⟨by linarith, h A⟩
  let g := R⁻¹ • functionalCoeffs φ
  have hg : IsUnitTest g := by
    apply (unit_iff_pairing_atoms g).mpr
    intro A
    dsimp [g]
    rw [A.pairing_smul, abs_mul, abs_of_pos (inv_pos.mpr hR), ← functional_atom]
    have hh := mul_le_mul_of_nonneg_left (hab A) (inv_nonneg.mpr hR.le)
    simpa only [inv_mul_cancel₀ hR.ne'] using hh
  have hfin (w : TestVector unitTests) : |φ (w : DualCore)| ≤ R*‖(w : DualCore)‖ := by
    let z := testVectorEquiv unitTests w
    have h1 := finitePairing_le_testNorm unitTests ⟨g,hg⟩ z
    have he : finitePairing g z = R⁻¹*φ (coreLift z) := by
      rw [functional_coreLift]
      simp only [finitePairing_apply, g, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    rw [he, abs_mul, abs_of_pos (inv_pos.mpr hR)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hR.le
    have hc : coreLift z = (w : DualCore) := rfl
    rw [hc, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at h2
    rw [UniformSpace.Completion.norm_coe, norm_testVector_equiv]
    exact h2
  exact UniformSpace.Completion.induction_on x
    (isClosed_le (φ.continuous.abs) (continuous_const.mul continuous_norm)) hfin

/-- The atom-hull fact is proved directly in the completed dual core by
Hahn--Banach; no reflexivity or norm attainment is assumed here. -/
theorem core_atom_hull : Metric.closedBall (0 : DualCore) 1 =
    closure (convexHull ℝ (Set.range Atom.inCore)) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hn
    obtain ⟨φ,R,hR,hxR⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (Set.range Atom.inCore)).closure isClosed_closure hn
    have h0 : (0 : DualCore) ∈ closure (convexHull ℝ (Set.range Atom.inCore)) :=
      subset_closure (subset_convexHull ℝ _ ⟨Atom.zero, Atom.zero_inCore⟩)
    have hRpos : 0 < R := by simpa only [map_zero] using hR 0 h0
    have hb : ∀ A : Atom, φ A.inCore ≤ R := by
      intro A
      exact (hR _ (subset_closure (subset_convexHull ℝ _ ⟨A,rfl⟩))).le
    have hh := functional_atom_bound φ hRpos hb x
    have hxn : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hp := le_abs_self (φ x)
    nlinarith
  · apply closure_minimal _ Metric.isClosed_closedBall
    apply convexHull_min _ (convex_closedBall (0 : DualCore) 1)
    rintro x ⟨A,rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using A.norm_inCore

end BoundedTreePotentials.Segments

end

end OAI
