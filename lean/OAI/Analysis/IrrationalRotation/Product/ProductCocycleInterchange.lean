import OAI.Analysis.IrrationalRotation.Product.ProductCocycle
import OAI.Analysis.IrrationalRotation.Model.ProductPairIdentity

namespace OAI

noncomputable section
open MeasureTheory Set Function

namespace Invariant233.ProductCocycle

theorem cocycleVersion_ratio_interchange_of_add {I : Type*}
    (θ c : I → ℝ) (k n : ℤ) (x : Space I)
    (hkn : cocycleVersion θ c (k + n) x =
      cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x)
    (hnk : cocycleVersion θ c (n + k) x =
      cocycleVersion θ c k (rotate θ n x) * cocycleVersion θ c n x) :
    cocycleVersion θ c k (rotate θ n x) / cocycleVersion θ c k x =
      cocycleVersion θ c n (rotate θ k x) / cocycleVersion θ c n x := by
  apply (div_eq_div_iff (cocycleVersion_pos θ c k x).ne'
    (cocycleVersion_pos θ c n x).ne').mpr
  calc
    cocycleVersion θ c k (rotate θ n x) * cocycleVersion θ c n x =
        cocycleVersion θ c (n + k) x := hnk.symm
    _ = cocycleVersion θ c (k + n) x := by rw [add_comm n k]
    _ = cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x := hkn

theorem exists_invariant_ratio_interchange_core {I : Type*} [Countable I]
    (θ : I → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∃ s : Set (Space I), MeasurableSet s ∧ (∀ᵐ x ∂haar I, x ∈ s) ∧
      (∀ k : ℤ, rotate θ k ⁻¹' s = s) ∧
      (∀ x ∈ s, ∀ (c : I → ℝ) (k n : ℤ),
        cocycleVersion θ c k (rotate θ n x) / cocycleVersion θ c k x =
          cocycleVersion θ c n (rotate θ k x) / cocycleVersion θ c n x) := by
  obtain ⟨s, hs, hfull, hinv, _hsupport, hlaw⟩ :=
    exists_invariant_cocycle_core θ hθ0 hθ
  refine ⟨s, hs, hfull, hinv, ?_⟩
  intro x hx c k n
  exact cocycleVersion_ratio_interchange_of_add θ c k n x
    (hlaw x hx c k n) (hlaw x hx c n k)

theorem ae_cocycleVersion_ratio_interchange {I : Type*} [Countable I]
    (θ : I → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂haar I, ∀ (c : I → ℝ) (k n : ℤ),
      cocycleVersion θ c k (rotate θ n x) / cocycleVersion θ c k x =
        cocycleVersion θ c n (rotate θ k x) / cocycleVersion θ c n x := by
  obtain ⟨s, _hs, hfull, _hinv, hlaw⟩ :=
    exists_invariant_ratio_interchange_core θ hθ0 hθ
  filter_upwards [hfull] with x hx
  exact hlaw x hx

end Invariant233.ProductCocycle

namespace Invariant233.ProductModel

theorem ae_cocycle_ratio_interchange (θ : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, ∀ (c : ℕ → ℝ) (k n : ℤ),
      ProductCocycle.cocycleVersion θ c k (rotationIterate θ n x) /
          ProductCocycle.cocycleVersion θ c k x =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) /
          ProductCocycle.cocycleVersion θ c n x :=
  ProductCocycle.ae_cocycleVersion_ratio_interchange θ hθ0 hθ

theorem ae_cocycleRatio_rotation (θ : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, ∀ (c : ℕ → ℝ) (k n : ℤ),
      cocycleRatio θ c x (rotationIterate θ n x) k =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) /
          ProductCocycle.cocycleVersion θ c n x :=
  ae_cocycle_ratio_interchange θ hθ0 hθ

end Invariant233.ProductModel

end

end OAI
