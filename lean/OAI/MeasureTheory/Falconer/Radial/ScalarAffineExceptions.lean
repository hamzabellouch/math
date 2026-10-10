import OAI.MeasureTheory.Falconer.Geometry.ScalarBallCandidates
import OAI.MeasureTheory.Falconer.Estimates.ScalarSumCells

namespace OAI

/-! Exceptional coefficient counts for separated scalar clusters. This is
 the finite real-variable separation estimate in the porous amplification
 argument; the coefficient distribution is the original finite set. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalar_affine_small_subset {μ R u v : ℝ} (hμ : 0 < μ)
    (hv : μ ≤ |v|) (hR : 0 ≤ R) (B : Finset ℝ) :
    B.filter (fun b => |u+b*v| ≤ R) ⊆
      B.filter (fun b => |b-(-u/v)| ≤ R/μ) := by
  intro b hb
  obtain ⟨hb,he⟩ := Finset.mem_filter.mp hb
  refine Finset.mem_filter.mpr ⟨hb,?_⟩
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv; linarith
  have hid : b-(-u/v) = (u+b*v)/v := by field_simp; ring
  rw [hid,abs_div]
  exact (div_le_div_of_nonneg_right he (abs_nonneg v)).trans
    (div_le_div_of_nonneg_left hR hμ hv)

 theorem scalar_affine_small_card {δ μ R K κ : ℝ} (hμ : 0 < μ)
    (hR : 0 ≤ R) (hscale : δ ≤ R/μ) (hscale1 : R/μ ≤ 1)
    (B : Finset ℝ)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass B u r ≤ K*r^κ*(B.card : ℝ))
    {u v : ℝ} (hv : μ ≤ |v|) :
    ((B.filter fun b => |u+b*v| ≤ R).card : ℝ) ≤
      K*(R/μ)^κ*(B.card : ℝ) := by
  calc
    _ ≤ scalarBallMass B (-u/v) (R/μ) := by
      change ((B.filter fun b => |u+b*v| ≤ R).card : ℝ) ≤
        ((B.filter fun b => |b-(-u/v)| ≤ R/μ).card : ℝ)
      exact_mod_cast Finset.card_le_card (scalar_affine_small_subset (u := u) hμ hv hR B)
    _ ≤ _ := hball _ _ hscale hscale1

noncomputable def scalarBadClusterCoefficients (B X Y : Finset ℝ) (R : ℝ) : Finset ℝ :=
  B.filter fun b => ∃ p ∈ X ×ˢ Y, ∃ q ∈ X ×ˢ Y,
    p ≠ q ∧ |(p.1+b*p.2)-(q.1+b*q.2)| ≤ R

 theorem scalar_bad_cluster_card {δ μ R K κ : ℝ} (hμ : 0 < μ)
    (hR : 0 ≤ R) (hRμ : R < μ) (hK : 0 ≤ K)
    (hscale : δ ≤ R/μ) (hscale1 : R/μ ≤ 1)
    (B X Y : Finset ℝ)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → μ ≤ |x-y|)
    (hY : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → μ ≤ |x-y|)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass B u r ≤ K*r^κ*(B.card : ℝ)) :
    ((scalarBadClusterCoefficients B X Y R).card : ℝ) ≤
      ((X.card : ℝ)*(Y.card : ℝ))^2 * (K*(R/μ)^κ*(B.card : ℝ)) := by
  let D := X ×ˢ Y
  let E := fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
    if pq.1 = pq.2 then (∅ : Finset ℝ) else
      B.filter fun b => |(pq.1.1+b*pq.1.2)-(pq.2.1+b*pq.2.2)| ≤ R
  have hn : 0 ≤ K*(R/μ)^κ*(B.card : ℝ) := by positivity
  have hE : ∀ pq ∈ D ×ˢ D,
      ((E pq).card : ℝ) ≤ K*(R/μ)^κ*(B.card : ℝ) := by
    rintro ⟨p,q⟩ hpq
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    obtain ⟨hpx,hpy⟩ := Finset.mem_product.mp hp
    obtain ⟨hqx,hqy⟩ := Finset.mem_product.mp hq
    by_cases heq : p = q
    · simpa [E,heq] using hn
    dsimp only [E]
    simp only [ite_eq_right heq]
    by_cases hy : p.2 = q.2
    · have hx : p.1 ≠ q.1 := by intro hx; exact heq (Prod.ext hx hy)
      have hsep := hX p.1 hpx q.1 hqx hx
      have hemp : (B.filter fun b => |(p.1+b*p.2)-(q.1+b*q.2)| ≤ R) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro b hb
        have hh := (Finset.mem_filter.mp hb).2
        have hid : (p.1+b*p.2)-(q.1+b*q.2) = p.1-q.1 := by rw [hy]; ring
        rw [hid] at hh
        linarith
      simpa only [hemp,Finset.card_empty,Nat.cast_zero] using hn
    · have hs := scalar_affine_small_card hμ hR hscale hscale1 B hball
        (u := p.1-q.1) (hY p.2 hpy q.2 hqy hy)
      have hid : (fun b : ℝ => |(p.1+b*p.2)-(q.1+b*q.2)| ≤ R) =
          (fun b : ℝ => |p.1-q.1+b*(p.2-q.2)| ≤ R) := by
        funext b; congr 2; ring
      have he : (B.filter fun b => |(p.1+b*p.2)-(q.1+b*q.2)| ≤ R) =
          (B.filter fun b => |p.1-q.1+b*(p.2-q.2)| ≤ R) := by
        ext b; simp only [Finset.mem_filter]; rw [congrFun hid b]
      simpa only [he] using hs
  have hsub : scalarBadClusterCoefficients B X Y R ⊆ (D ×ˢ D).biUnion E := by
    intro b hb
    obtain ⟨hb,p,hp,q,hq,hne,hsmall⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_biUnion.mpr ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,
      by simp only [E,ite_eq_right hne,Finset.mem_filter]; exact ⟨hb,hsmall⟩⟩
  calc
    _ ≤ (((D ×ˢ D).biUnion E).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ pq ∈ D ×ˢ D, ((E pq).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := D ×ˢ D) (t := E))
    _ ≤ ∑ _pq ∈ D ×ˢ D, K*(R/μ)^κ*(B.card : ℝ) := Finset.sum_le_sum hE
    _ = _ := by simp only [Finset.sum_const,Finset.card_product,D,nsmul_eq_mul,Nat.cast_mul]; ring

end Falconer

end OAI
