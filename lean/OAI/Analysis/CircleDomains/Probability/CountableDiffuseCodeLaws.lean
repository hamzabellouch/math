import OAI.Analysis.CircleDomains.Sobolev.FiniteSphericalArea
import OAI.Analysis.CircleDomains.Probability.PhysicalLastEntryLaw
import OAI.Analysis.CircleDomains.Topology.JordanCollarCountability
import OAI.Analysis.CircleDomains.Selection.LocalCodeMeetingBound
import OAI.Analysis.CircleDomains.Topology.CountableJordanCollars
import OAI.Analysis.CircleDomains.Topology.PuncturedSquareNeighborhood
import OAI.Analysis.CircleDomains.Probability.OccupationNeighborhood

namespace OAI

/-! The crossing contradiction for a family of actual positive code laws.
Pairwise dust contacts are countable; square occupation and hit bounds make
all remaining meetings small on a common member of the countable collar basis. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem countable_diffuse_code_laws {I : Type*} [LinearOrder I]
    (hcross : UnitDiskAlternatingContinua)
    (G U B E : Set Sphere) (hG : IsOpen G) (hU : IsOpen U)
    (hdisj : Disjoint U B) (hBU : Bᶜ ⊆ U)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (d : I → PathCodeData Sphere Sphere)
    (hGd : ∀ i, (d i).physicalDomain = G) (hUd : ∀ i, (d i).quotientDomain = U)
    (hBd : ∀ i, (d i).dust = B) (hEd : ∀ i, (d i).anchor = E)
    (hed : ∀ i, ∀ y : (d i).physicalDomain, ((d i).domainEquiv y).val = π y.val)
    (htarget : ∀ i, (d i).target ∈ B \ {OnePoint.infty})
    (hinj : Injective (fun i => (d i).target))
    (P : ∀ i, ProbabilityMeasure (BasePathCode (d i)))
    [∀ i, SigmaFinite (meanCodeOccupation (d i) (P i))]
    (g : I → Sphere → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (hocc : ∀ i, meanCodeOccupation (d i) (P i) = sphericalArea.withDensity (g i))
    (henergy : ∀ i, (∫⁻ x, g i x ^ 2 ∂sphericalArea) < ∞)
    (hhit : ∀ i, (∑' x : B, codeHitProbability (d i) (P i) x.val ^ 2) < ∞)
    (hcontacts : ∀ i j, i < j → ∃ D : Set Sphere, D.Countable ∧
      ∀ᵐ z ∂((P i : Measure (BasePathCode (d i))).prod (P j : Measure (BasePathCode (d j)))),
        range z.1.val.1 ∩ range z.2.val.1 ∩ (d i).dust ⊆ D)
    (K : Set (ℂ ≃ₜ ℂ)) (hK : K.Countable)
    (hgood : ∀ k ∈ K, frontier (quotientJordanDisk k) ⊆ U ∧
      π OnePoint.infty ∉ closure (quotientJordanDisk k) ∧ Disjoint E (quotientJordanDisk k))
    (hbasis : ∀ p ∈ B \ {OnePoint.infty}, ∀ O : Set Sphere, IsOpen O → p ∈ O →
      ∃ k ∈ K, p ∈ quotientJordanDisk k ∧ quotientJordanDisk k ⊆ O)
    (a : ℕ → ℝ≥0) (ha : ∀ n, 0 < a n) (hat : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (A : Set Sphere) (hKA : ∀ k ∈ K, π ⁻¹' quotientJordanDisk k ⊆ A)
    (hball : ∀ᶠ n in atTop, ∀ x ∈ A,
      sphericalArea (Metric.ball x (2 * a n)) ≤ C * (a n : ℝ≥0∞) ^ 2) : Countable I := by
  obtain ⟨δ, hδ, hbudget⟩ := exists_small_crossing_budget C hC
  have hδ2 : 0 < δ ^ 2 := ENNReal.pow_pos hδ 2
  have hu (i : I) : IsOpen (d i).quotientDomain := by simpa only [hUd i] using hU
  have hphys (i : I) : IsOpen (d i).physicalDomain := by simpa only [hGd i] using hG
  have hdb (i : I) : Disjoint (d i).quotientDomain (d i).dust := by
    simpa only [hUd i, hBd i] using hdisj
  have hri (i : I) : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ (d i).physicalDomainᶜ ∧ y ∈ connectedComponentIn (d i).physicalDomainᶜ x) := by
    simpa only [hGd i] using hr
  have hpB (i : I) : (d i).target ∈ (d i).dust := by
    simpa only [hBd i] using (htarget i).1
  have hpend (i : I) : (d i).target ∉ (d i).quotientDomain :=
    fun hi => disjoint_left.mp (hdb i) hi (hpB i)
  let Good (k : ℂ ≃ₜ ℂ) (i : I) : Prop :=
    (d i).target ∈ quotientJordanDisk k ∧
    (∫⁻ x in π ⁻¹' quotientJordanDisk k, g i x ^ 2 ∂sphericalArea) ≤ δ ^ 2 ∧
    countingSquareNorm (fun x : B =>
      if x.val ∈ quotientJordanDisk k ∧ x.val ≠ (d i).target
        then codeHitProbability (d i) (P i) x.val else 0) ≤ δ
  have hcover (i : I) : ∃ k ∈ K, Good k i := by
    obtain ⟨O, hO, hpO, hOE⟩ := exists_open_small_occupation_energy (d i) (hu i) (hphys i)
      (hdb i) π hπ (hed i) (P i) sphericalArea (g i) (hg i) (hocc i) (henergy i)
      (d i).target (hpB i) hδ2
    obtain ⟨V, hV, hpV, hVH⟩ := exists_open_punctured_square_norm
      (fun x : B => x.val) (fun x : B => codeHitProbability (d i) (P i) x.val)
      (hhit i) (d i).target hδ
    obtain ⟨k, hk, hpk, hsub⟩ := hbasis (d i).target (htarget i) (O ∩ V)
      (hO.inter hV) ⟨hpO, hpV⟩
    refine ⟨k, hk, hpk, ?_, ?_⟩
    · exact (lintegral_mono_set (preimage_mono (hsub.trans inter_subset_left))).trans hOE.le
    · apply (countingSquareNorm_mono ?_).trans hVH.le
      intro x
      by_cases hx : x.val ∈ quotientJordanDisk k ∧ x.val ≠ (d i).target
      · have hxV : x.val ∈ V ∧ x.val ≠ (d i).target := ⟨(hsub hx.1).2, hx.2⟩
        simp only [hx, hxV, le_refl]
      · simp only [hx, ite_false, zero_le]
  have hcount (k : ℂ ≃ₜ ℂ) (hk : k ∈ K) : {i | Good k i}.Countable := by
    let V := quotientJordanDisk k
    have hV : IsOpen V := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen k)
    obtain ⟨hfront, hinf, hE⟩ := hgood k hk
    apply countable_of_small_jordan_collar_meetings hcross {i | Good k i} k
      (fun i => BasePathCode (d i)) P (fun i => codePath (d i))
      (fun i => measurable_codePath (d i)) (fun i => (d i).target)
    · exact fun i hi => hi.1
    · intro i hi
      exact Eventually.of_forall fun z => ⟨fun hx => disjoint_left.mp hE
        ((hEd i) ▸ z.property.2.1.1) hx, z.property.2.1.2.1⟩
    · intro i hi
      exact physical_lastEntryLaw_nullSingletonClass (d i) (hu i) (hphys i) π hπ hclosed
        hsurj (hri i) (hed i) (hpend i) (P i) (g i) (hg i) (hocc i) (henergy i)
        V hV (by simpa only [hUd i] using hfront) (fun h => hinf (frontier_subset_closure h))
        (by simpa only [hEd i] using hE) hi.1
    · intro i hi j hj hij
      obtain ⟨D₀, hD₀, hcontact⟩ := hcontacts i j hij
      let D := insert (d i).target (insert (d j).target D₀)
      have hD : D.Countable := (hD₀.insert _).insert _
      have hc : ∀ᵐ z ∂((P i : Measure (BasePathCode (d i))).prod
          (P j : Measure (BasePathCode (d j)))),
          range z.1.val.1 ∩ range z.2.val.1 ∩ (d i).dust ⊆ D :=
        hcontact.mono fun z hz => hz.trans (subset_insert _ _ |>.trans (subset_insert _ _))
      have hpi : (d i).target ∈ D ∩ (V ∩ (d i).dust) :=
        ⟨mem_insert _ _, hi.1, hpB i⟩
      have hpj : (d j).target ∈ D ∩ (V ∩ (d i).dust) := by
        refine ⟨mem_insert_of_mem _ (mem_insert _ _), hj.1, ?_⟩
        simpa only [hBd i] using (htarget j).1
      have ht (i : I) (hi : Good k i) :
          countingSquareNorm (fun x : ↥(D ∩ (V ∩ B)) =>
            if x.val ≠ (d i).target then codeHitProbability (d i) (P i) x.val else 0) ≤ δ :=
        (punctured_square_norm_subtype_le (codeHitProbability (d i) (P i)) D V B
          (d i).target).trans hi.2.2
      have hb : ∀ᶠ n in atTop, ∀ x ∈ (d i).physicalDomain ∩ π ⁻¹' V,
          sphericalArea (Metric.ball x (2 * a n)) ≤ C * (a n : ℝ≥0∞) ^ 2 := by
        filter_upwards [hball] with n hn
        intro x hx
        exact hn x (hKA k hk hx.2)
      have hbU : (d i).dustᶜ ⊆ (d i).quotientDomain := by
        simpa only [hBd i, hUd i] using hBU
      have heG : (d j).physicalDomain = (d i).physicalDomain := (hGd j).trans (hGd i).symm
      have heI : (∫⁻ x in (d i).physicalDomain ∩ π ⁻¹' V,
          g i x ^ 2 ∂sphericalArea) ≤ δ ^ 2 :=
        (lintegral_mono_set inter_subset_right).trans hi.2.1
      have heJ : (∫⁻ x in (d i).physicalDomain ∩ π ⁻¹' V,
          g j x ^ 2 ∂sphericalArea) ≤ δ ^ 2 :=
        (lintegral_mono_set inter_subset_right).trans hj.2.1
      have hti : countingSquareNorm (fun x : ↥(D ∩ (V ∩ (d i).dust)) =>
          if x.val ≠ (d i).target then codeHitProbability (d i) (P i) x.val else 0) ≤ δ := by
        rw [hBd i]
        exact ht i hi
      have htj : countingSquareNorm (fun x : ↥(D ∩ (V ∩ (d i).dust)) =>
          if x.val ≠ (d j).target then codeHitProbability (d j) (P j) x.val else 0) ≤ δ := by
        rw [hBd i]
        exact ht j hj
      have hbound := local_code_meeting_bound (d i) (d j) (hu i) (hu j) (hphys i) heG hbU
        π hπ hclosed hsurj (hri i) (hed i) (hed j) (hpend i) (hpend j) (P i) (P j)
        sphericalArea (g i) (g j) (hg i) (hg j) (hocc i) (hocc j) V D hV hD hc
        (d i).target (d j).target hpi hpj (fun h => (ne_of_lt hij) (hinj h))
        a ha hat C δ hb heI heJ
        hti htj
      exact (mul_le_mul' (le_refl 4) hbound).trans_lt hbudget
  have hall : (univ : Set I) ⊆ ⋃ k ∈ K, {i | Good k i} := by
    intro i _
    obtain ⟨k, hk, hi⟩ := hcover i
    exact mem_iUnion₂.mpr ⟨k, hk, hi⟩
  exact Set.countable_univ_iff.mp ((hK.biUnion hcount).mono hall)

end CircleDomainRigidity

end

end OAI
