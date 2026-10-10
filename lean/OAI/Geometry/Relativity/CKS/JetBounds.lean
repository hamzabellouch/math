import OAI.Geometry.Relativity.CKS.MixedThreeJets

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma scalarJet_norm_components {u : ScalarJet} {B : ℝ} (h : ‖u‖ ≤ B) :
    |u.1| ≤ B ∧ (∀ a, |u.2.1 a| ≤ B) ∧ (∀ a b, |u.2.2 a b| ≤ B) := by
  obtain ⟨h0,h12⟩ := norm_prod_le_iff.mp h
  obtain ⟨h1,h2⟩ := norm_prod_le_iff.mp h12
  refine ⟨h0,?_,?_⟩
  · intro a; exact (norm_le_pi_norm _ a).trans h1
  · intro a b; exact (norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans h2)

lemma scalarJet_norm_of_components {u : ScalarJet} {B : ℝ} (hB : 0 ≤ B)
    (h0 : |u.1| ≤ B) (h1 : ∀ a, |u.2.1 a| ≤ B) (h2 : ∀ a b, |u.2.2 a b| ≤ B) :
    ‖u‖ ≤ B := by
  exact norm_prod_le_iff.mpr ⟨h0,norm_prod_le_iff.mpr
    ⟨(pi_norm_le_iff_of_nonneg hB).mpr h1,(pi_norm_le_iff_of_nonneg hB).mpr
    (fun a => (pi_norm_le_iff_of_nonneg hB).mpr (h2 a))⟩⟩

lemma productJet_norm {u v : ScalarJet} {U V : ℝ}
    (hU : ‖u‖ ≤ U) (hV : ‖v‖ ≤ V) : ‖productJet u v‖ ≤ 4*U*V := by
  have hU0 := (norm_nonneg u).trans hU
  have hV0 := (norm_nonneg v).trans hV
  obtain ⟨hu0,hu1,hu2⟩ := scalarJet_norm_components hU
  obtain ⟨hv0,hv1,hv2⟩ := scalarJet_norm_components hV
  have hb {a b : ℝ} (ha : |a| ≤ U) (hb : |b| ≤ V) : |a*b| ≤ U*V := by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hU0
  have hUV : 0 ≤ U*V := mul_nonneg hU0 hV0
  apply scalarJet_norm_of_components (by positivity)
  · exact (hb hu0 hv0).trans (by nlinarith)
  · intro a
    change |u.1*v.2.1 a+v.1*u.2.1 a| ≤ _
    have hs := abs_add_le (u.1*v.2.1 a) (v.1*u.2.1 a)
    have h := hb (hu1 a) hv0
    rw [mul_comm (u.2.1 a)] at h
    linarith [hb hu0 (hv1 a)]
  · intro a b
    change |u.1*v.2.2 a b+v.1*u.2.2 a b+u.2.1 a*v.2.1 b+v.2.1 a*u.2.1 b| ≤ _
    have h := hb (hu2 a b) hv0
    rw [mul_comm (u.2.2 a b)] at h
    have hh := hb (hu1 b) (hv1 a)
    rw [mul_comm (u.2.1 b)] at hh
    calc
      _ ≤ |u.1*v.2.2 a b|+|v.1*u.2.2 a b|+|u.2.1 a*v.2.1 b|+|v.2.1 a*u.2.1 b| := by
        exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ U*V+U*V+U*V+U*V := add_le_add (add_le_add (add_le_add (hb hu0 (hv2 a b)) h) (hb (hu1 a) (hv1 b))) hh
      _ = 4*U*V := by ring

lemma productThreeJet_norm {u v : ScalarThreeJet} {U V : ℝ}
    (hU : ‖u‖ ≤ U) (hV : ‖v‖ ≤ V) : ‖productThreeJet u v‖ ≤ 8*U*V := by
  have hU0 := (norm_nonneg u).trans hU
  have hV0 := (norm_nonneg v).trans hV
  obtain ⟨hu0,hu1⟩ := norm_prod_le_iff.mp hU
  obtain ⟨hv0,hv1⟩ := norm_prod_le_iff.mp hV
  apply norm_prod_le_iff.mpr
  constructor
  · exact (productJet_norm hu0 hv0).trans (by nlinarith [mul_nonneg hU0 hV0])
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    have hua : ‖u.2 a‖ ≤ U := (norm_le_pi_norm _ a).trans hu1
    have hva : ‖v.2 a‖ ≤ V := (norm_le_pi_norm _ a).trans hv1
    calc
      _ ≤ ‖productJet u.1 (v.2 a)‖+‖productJet v.1 (u.2 a)‖ := norm_add_le _ _
      _ ≤ 4*U*V+4*V*U := add_le_add (productJet_norm hu0 hva) (productJet_norm hv0 hua)
      _ = 8*U*V := by ring

end
end CKSMixedGeometry

end

end OAI
