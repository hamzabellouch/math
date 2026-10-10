import OAI.Geometry.Perimeter.Regularity.WeakHarmonicSmooth
import OAI.Geometry.Perimeter.Regularity.EllipticHodgeIdentity

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem curlTest_inner (u : VectorL2 n) {U : Set (Euc n)}
    (φ : SmoothLocalTest U) (a b : Euc n) :
    inner ℝ u (curlTestLp φ a b)=∫ x, inner ℝ (u x) (curlTest φ.val a b x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [curlTestLp_ae φ a b] with x hx
  rw [hx]

theorem curlTest_integrable_pairing (u : VectorL2 n) {U : Set (Euc n)}
    (φ : SmoothLocalTest U) (a b : Euc n) :
    Integrable (fun x ↦ inner ℝ (u x) (curlTest φ.val a b x)) volume := by
  apply (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) u (curlTestLp φ a b)).congr
  filter_upwards [curlTestLp_ae φ a b] with x hx
  rw [hx]

theorem div_curl_weak_harmonic {u : VectorL2 n} {U : Set (Euc n)}
    (hd : DivFreeLpOn u U) (hc : CurlFreeLpOn u U) (a : Euc n) :
    WeakHarmonicOn (fun x ↦ inner ℝ a (u x)) U := by
  intro ψ hψ hcψ hsψ
  let φ : SmoothLocalTest U := ⟨ψ,hψ,hcψ,hsψ⟩
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hi : Integrable (fun x ↦ inner ℝ (u x) (gradient (scalarDirection ψ a) x)) volume :=
    testGradient_integrable_pairing u (directionLocalTest φ a)
  have hi' (j : Fin n) : Integrable (fun x ↦ inner ℝ (u x)
      (curlTest (scalarDirection ψ (b j)) (b j) a x)) volume :=
    curlTest_integrable_pairing u (directionLocalTest φ (b j)) (b j) a
  calc
    (∫ x, inner ℝ a (u x)*divergence (gradient ψ) x)=
      ∫ x, inner ℝ (u x) (gradient (scalarDirection ψ a) x)+
        ∑ j : Fin n, inner ℝ (u x) (curlTest (scalarDirection ψ (b j)) (b j) a x) := by
      congr 1
      funext x
      rw [real_inner_comm,mul_comm,←real_inner_smul_right,div_curl_test_identity hψ]
      simp only [inner_add_right,inner_sum,b]
    _ = (∫ x, inner ℝ (u x) (gradient (scalarDirection ψ a) x))+
        ∑ j : Fin n, ∫ x, inner ℝ (u x) (curlTest (scalarDirection ψ (b j)) (b j) a x) := by
      rw [integral_add hi (integrable_finsetSum Finset.univ (fun j _ ↦ hi' j)),
        integral_finsetSum Finset.univ (fun j _ ↦ hi' j)]
    _ = 0 := by
      rw [show (∫ x, inner ℝ (u x) (gradient (scalarDirection ψ a) x))=0 from hd (directionLocalTest φ a)]
      simp only [zero_add]
      apply Finset.sum_eq_zero
      intro j _
      exact (curlTest_inner u (directionLocalTest φ (b j)) (b j) a).symm.trans (hc _ _ _)

theorem vectorLp_component_locallyIntegrable (u : VectorL2 n) (a : Euc n) :
    LocallyIntegrable (fun x ↦ inner ℝ a (u x)) volume :=
  ((innerSL ℝ a).comp_memLp u).locallyIntegrable (by norm_num)

theorem div_curl_smooth_representative {u : VectorL2 n} {U : Set (Euc n)}
    (hd : DivFreeLpOn u U) (hc : CurlFreeLpOn u U) (hn : 0<n)
    (c : Euc n) {r : ℝ} (hr : 0<r) (hU : Metric.ball c (2*r) ⊆ U) :
    ∃ G : Euc n → Euc n, ContDiff ℝ ∞ G ∧
      (u : Euc n → Euc n)=ᵐ[volume.restrict (Metric.ball c r)] G := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have he (j : Fin n) := weakHarmonic_smooth_representative_ball
    (vectorLp_component_locallyIntegrable u (b j)) (div_curl_weak_harmonic hd hc (b j)) hn c hr hU
  choose f hf hfe using he
  refine ⟨fun x ↦ ∑ j : Fin n, f j x • b j,ContDiff.sum (fun j _ ↦ (hf j).smul contDiff_const),?_⟩
  filter_upwards [ae_all_iff.mpr hfe] with x hx
  calc
    u x = ∑ j : Fin n, inner ℝ (b j) (u x) • b j := by simpa only [OrthonormalBasis.repr_apply_apply] using (b.sum_repr (u x)).symm
    _ = _ := Finset.sum_congr rfl (fun j _ ↦ by rw [hx j])

end RPISingularHarnack

end

end OAI
