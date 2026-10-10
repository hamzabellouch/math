import OAI.Analysis.CircleDomains.Selection.OrderedHoleIntegration
import OAI.Analysis.CircleDomains.Modulus.DiskLinePayment

namespace OAI

/-! Distributional line error for constant-filled disjoint round disks.
The estimate charges only disks met by the line. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem filled_line_integration_through_disks
    {I : Type*} [Fintype I] (c : I → ℂ) (r value A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {y a b : ℝ} (hab : a < b)
    (ha : a ∈ diskLineDomain c r y) (hb : b ∈ diskLineDomain c r y)
    {f F ρ : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (diskLineDomain c r y))
    (hρ : Integrable ρ)
    (hmajor : ∀ x ∈ Icc a b ∩ diskLineDomain c r y, |deriv f x| ≤ ρ x)
    (hF : EqOn F (clipScalar ∘ f) (diskLineDomain c r y))
    (hfill : ∀ i x, (⟨x, y⟩ : ℂ) ∈ closedBall (c i) (r i) → F x = clipScalar (value i))
    (hcluster : ∀ i p u, (⟨p, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[diskLineDomain c r y] p) f → |u - value i| ≤ A i)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hzero : φ a = 0) (hone : φ b = 0)
    (hint : Integrable (fun x => F x * deriv φ x))
    (hdint : Integrable (fun x => deriv F x * φ x))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |φ x| ≤ C) :
    |(∫ x in a..b, F x * deriv φ x) + (∫ x in a..b, deriv F x * φ x)| ≤
      2 * C * ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
  classical
  let K := crossingChords c r y a b
  let H := K.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl
  have hmem (j : Fin K.card) : H j ∈ K := K.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ) rfl j
  have honto (z : ℝ × ℝ) (hz : z ∈ K) : ∃ j : Fin K.card, H j = z := by
    let z' : (K : Finset (ℝ ×ₗ ℝ)) := ⟨z, hz⟩
    refine ⟨(K.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).symm z', ?_⟩
    exact congrArg Subtype.val ((K.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).apply_symm_apply z')
  have hcover : (⋃ j, Icc (H j).1 (H j).2) = ⋃ z ∈ K, Icc z.1 z.2 := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨H j, hmem j, hj⟩
    · intro hx
      obtain ⟨z, hz, hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨j, rfl⟩ := honto z hz
      exact mem_iUnion.mpr ⟨j, hx⟩
  have howner (j : Fin K.card) : ∃ i, i ∈ crossingDisks c r y a b ∧
      horizontalChord (c i) (r i) y = H j := Finset.mem_image.mp (hmem j)
  choose owner howner heq using howner
  have hinside := crossingChords_inside c r hr
    (fun i hi => ha (mem_iUnion.mpr ⟨i, hi⟩))
    (fun i hi => hb (mem_iUnion.mpr ⟨i, hi⟩))
  have hsep := sorted_holes_separated K (fun z hz => (hinside z hz).2.1)
    (crossingChords_disjoint c r hr hdisj)
  let D := Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ
  have hDU : D ⊆ diskLineDomain c r y := by
    intro x hx
    apply (crossingChords_domain c r hr hx.1).mp
    change x ∈ (⋃ z ∈ K, Icc z.1 z.2)ᶜ
    rw [← hcover]
    exact hx.2
  have hD := isOpen_diskLineDomain c r y
  have hchord (j : Fin K.card) {x : ℝ} (hx : x ∈ Icc (H j).1 (H j).2) :
      (⟨x, y⟩ : ℂ) ∈ closedBall (c (owner j)) (r (owner j)) := by
    apply (mem_closedBall_iff_mem_horizontalChord _ (hr _) (crossingDisk_line_hit (howner j))).mpr
    simpa only [heq j] using hx
  have hpay := filled_integration_of_ordered_holes hab H
    (fun j => hinside _ (hmem j)) hsep (fun j => value (owner j))
    (fun j => chordToll c r A y a b (H j))
    (fun x hx => (hf.contDiffAt (hD.mem_nhds (hDU hx))).differentiableAt (by norm_num) |>.hasDerivAt)
    ((hf.continuousOn_deriv_of_isOpen hD le_rfl).mono hDU) hρ
    (fun x hx => hmajor x ⟨hx.1, hDU hx⟩)
    (hF.mono hDU) (fun j x hx => hfill _ x (hchord j hx))
    (by
      intro j p u hp hu
      exact (hcluster (owner j) p u (hchord j hp)
        (hu.mono (nhdsWithin_mono _ hDU))).trans (by
          simpa only [heq j] using le_chordToll c r A y a b hA (howner j)))
    hφ hzero hone hint hdint hC hbound (fun j => (hA _).trans (by
      simpa only [heq j] using le_chordToll c r A y a b hA (howner j)))
  have hsum : (∑ j : Fin K.card, chordToll c r A y a b (H j)) =
      ∑ z ∈ K, chordToll c r A y a b z := by
    apply Finset.sum_bij (fun j _ => H j)
    · exact fun j _ => hmem j
    · exact fun i _ j _ hij => H.injective hij
    · intro z hz
      obtain ⟨j, hj⟩ := honto z hz
      exact ⟨j, Finset.mem_univ _, hj⟩
    · exact fun _ _ => rfl
  have hpaid := hpay.trans_eq (congrArg (fun t : ℝ => 2 * C * t) hsum)
  exact hpaid.trans (mul_le_mul_of_nonneg_left
    (sum_chordToll_le_line_hits c r A y a b hA) (mul_nonneg (by norm_num) hC))

end CircleDomainRigidity

end OAI
