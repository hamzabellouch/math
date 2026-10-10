import OAI.Geometry.NodalSets.Elliptic.EnvelopeContactJet
import OAI.Geometry.NodalSets.Elliptic.QuadraticFamily

namespace OAI

namespace Yau.Jets
open scoped ContDiff Topology
open MvPolynomial Filter
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma ContinuousPolyFamily.spatial_derivative_continuous {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (k : ℕ) :
    Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (reval (P z.1)) z.2) := by
  obtain ⟨s, hs⟩ := hp.2
  have he (t : T) : reval (P t) = polynomialFamily
      (fun d : s ↦ monomial d.val (1:ℂ)) (fun t d ↦ (P t).coeff d.val) t := by
    funext x
    rw [polynomial_sum_of_support_subset (P t) s (hs t)]
    simp [polynomialFamily, reval, Algebra.smul_def]
    exact (Finset.sum_attach s (fun d ↦ (P t).coeff d *
      eval (fun i ↦ (x i:ℂ)) (monomial d (1:ℂ)))).symm
  simp_rw [he]
  exact polynomialFamily_derivative_continuous
    (fun d : s ↦ monomial d.val (1:ℂ)) (fun t d ↦ (P t).coeff d.val)
    (fun d : s ↦ hp.1 d.val) k

def realTensorMap (k : ℕ) :
    (Coord [×k]→L[ℝ] ℂ) →L[ℝ] (Coord [×k]→L[ℝ] ℝ) :=
  ({ toFun := fun A ↦ Complex.reCLM.compContinuousMultilinearMap A
     map_add' := by intro A B; ext v; simp
     map_smul' := by intro c A; ext v; simp } :
    (Coord [×k]→L[ℝ] ℂ) →ₗ[ℝ] (Coord [×k]→L[ℝ] ℝ)).mkContinuous ‖Complex.reCLM‖
      (fun A ↦ Complex.reCLM.norm_compContinuousMultilinearMap_le A)

lemma ContinuousPolyFamily.real_spatial_derivative_continuous {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (k : ℕ) :
    Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (fun x ↦ (reval (P z.1) x).re) z.2) := by
  have he (t : T) (x : Coord) :
      iteratedFDeriv ℝ k (fun x ↦ (reval (P t) x).re) x =
        realTensorMap k (iteratedFDeriv ℝ k (reval (P t)) x) := by
    exact Complex.reCLM.iteratedFDeriv_comp_left (reval_contDiff _).contDiffAt
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))
  simp_rw [he]
  exact (realTensorMap k).continuous.comp (hp.spatial_derivative_continuous k)

lemma phase_gap_spatial_derivative_continuous {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (S : T → Coord → ℝ) (hS : ∀ t, ContDiff ℝ ∞ (S t))
    (hc : ∀ k, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (S z.1) z.2)) (k : ℕ) :
    Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k
      (fun x ↦ (reval (P z.1) x).re-S z.1 x) z.2) := by
  have he (t : T) (x : Coord) :
      iteratedFDeriv ℝ k (fun x ↦ (reval (P t) x).re-S t x) x =
        iteratedFDeriv ℝ k (fun x ↦ (reval (P t) x).re) x - iteratedFDeriv ℝ k (S t) x := by
    exact iteratedFDeriv_sub_apply
      ((Complex.reCLM.contDiff.comp (reval_contDiff _)).contDiffAt.of_le
        (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)))
      ((hS t).contDiffAt.of_le (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)))
  simp_rw [he]
  exact (hp.real_spatial_derivative_continuous k).sub (hc k)

theorem retained_phase_uniform_contact {s : Set T} (hs : IsCompact s)
    (P : T → CPoly) (hp : ContinuousPolyFamily P)
    (S : T → Coord → ℝ) (hS : ∀ t, ContDiff ℝ ∞ (S t))
    (hc : ∀ k, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (S z.1) z.2))
    (a b : T → ℝ) (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, b t ≠ 0)
    (hHc : ∀ i j, Continuous (fun t ↦ envelopeHessian (S t) i j))
    (hfirst : ∀ t ∈ s, ∀ x : Coord, fderiv ℝ (S t) 0 x = a t*x 0)
    (hkeep : ∀ t ∈ s, ∀ k, k ≤ 2 → homogeneousComponent k (P t) =
      initialPhaseJet (S t 0) (normalFrameVector (a t) (b t))
        (normalComplexHessian (a t) (b t) (envelopeHessian (S t))) k)
    (hstrict : ∀ t ∈ s, 0 < (a t)^2*envelopeHessian (S t) 0 0+
      (b t)^2*envelopeHessian (S t) 1 1) :
    ∃ c > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖x‖ ≤ 2*N^(-1/3:ℝ) → (reval (P t) x).re-S t x ≤ -c*‖x‖^2 := by
  have hj t ht := retained_phase_envelope_contact (P t) (S t) (hS t) (a t) (b t)
    (ha0 t) (hb0 t) (hfirst t ht) (hkeep t ht) (hstrict t ht)
  exact uniform_contact_from_second_jet hs (fun t x ↦ (reval (P t) x).re-S t x)
    (fun t ↦ (Complex.reCLM.contDiff.comp (reval_contDiff _)).sub (hS t))
    (phase_gap_spatial_derivative_continuous hp S hS hc 3)
    (fun t ↦ Yau.contactEta (a t) (b t) (envelopeHessian (S t) 0 0) (envelopeHessian (S t) 1 1))
    (contactEta_continuous a b _ ha hb hHc ha0).continuousOn
    (fun t ht ↦ Yau.contactEta_pos (ha0 t) (hstrict t ht))
    (fun t ht ↦ (hj t ht).1) (fun t ht ↦ (hj t ht).2.1) (fun t ht ↦ (hj t ht).2.2)

end
end Yau.Jets

end OAI
