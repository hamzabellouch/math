import OAI.MeasureTheory.Falconer.Estimates.ScalarBoundedCoefficients
import OAI.MeasureTheory.Falconer.Estimates.ScalarRatioFamily

namespace OAI

/-! A regular reference set cannot have small projections in every retained
ratio direction. All assumptions are finite-set counts at the original scale. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_negative_sum (X : Finset ℝ) (a : ℝ) :
    X+X.image (fun x => (-a)*x) = X-X.image (fun x => a*x) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sub.mpr ⟨x,hx,a*y,Finset.mem_image_of_mem _ hy,by ring⟩
  · intro hz
    obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_add.mpr ⟨x,hx,(-a)*y,Finset.mem_image_of_mem _ hy,by ring⟩

 theorem scalar_reference_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (M : ℕ) (hM : 1 ≤ M) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (X I J : Finset ℝ) (c A K : ℝ),
      X.Nonempty → J.Nonempty → J ⊆ I → c ≠ 0 → |c| ≤ M → |c⁻¹| ≤ M →
      1 ≤ K → (I.card:ℝ) ≤ A*(J.card:ℝ) →
      (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      (∀ a ∈ I, |a| ≤ M) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 →
      ((scalarCells δ (X+X)).card:ℝ) ≤ W*(X.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ W*r^κ*(X.card:ℝ)) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ K*r^(2*κ)*(I.card:ℝ)) →
      A*K*(M:ℝ)^(2*κ) ≤ W →
      (∀ a ∈ J, ((scalarCells δ (X-X.image (fun x => (a/c)*x))).card:ℝ) ≤ W*(X.card:ℝ)) →
      False := by
  obtain ⟨ε,N0,hε,hN0,hprojection⟩ := Regularization.scalar_bounded_coefficients hκ hκ1 (M*M)
  refine ⟨ε,N0,hε,hN0,?_⟩
  intro N hN
  dsimp only
  intro X I J c A K hX hJ hJI hc hcM hciM hK hIJ hXbound hsep hIbound hsize hd hball hIball hcost hproj
  let δ := (1/2:ℝ)^N
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  let E := J.image (fun a => -a/c)
  have hδ : 0 < δ := by positivity
  have hE : E.Nonempty := hJ.image _
  have hEbound : ∀ a ∈ E, |a| ≤ (M*M:ℕ) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    rw [div_eq_mul_inv,abs_mul,abs_neg,Nat.cast_mul]
    exact mul_le_mul (hIbound b (hJI hb)) hciM (abs_nonneg _) (Nat.cast_nonneg _)
  have hEball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ) := by
    intro u r hr _
    have hh := scalar_ratio_family_ball hδ (by positivity : 0 ≤ 2*κ) hK
      (by exact_mod_cast hM : (1:ℝ) ≤ M) hc hcM I J hJI hIJ hIball u r hr
    have hm := mul_le_mul_of_nonneg_right hcost
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*κ)) (Nat.cast_nonneg E.card))
    change scalarBallMass E u r ≤ (A*K*(M:ℝ)^(2*κ))*r^(2*κ)*(E.card:ℝ) at hh
    nlinarith
  obtain ⟨a,ha,hgain⟩ := hprojection N hN X hX hXbound hsep hsize hd hball E hE hEbound hEball
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  have he : X+X.image (fun x => (-b/c)*x) = X-X.image (fun x => (b/c)*x) := by
    rw [neg_div]
    exact scalar_negative_sum X (b/c)
  rw [he] at hgain
  exact (not_lt_of_ge (hproj b hb)) hgain

end Falconer

end OAI
