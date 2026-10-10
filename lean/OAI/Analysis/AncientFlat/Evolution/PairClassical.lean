import OAI.Analysis.AncientFlat.Evolution.ClassicalRHS
import OAI.Analysis.AncientFlat.Evolution.LocalWeakToStrong

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology ZeroAtInfty BoundedContinuousFunction Laplacian ContDiff
namespace ParametrixVolterra
open FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}

def mildRHS (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
    (hT : 0≤T) (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T) : V →ᵇ ℂ :=
  -(coefficient (A (now t)).toContinuousMap*mildBilaplacian hα A hT d j t)-
    b (now t)*(mildTime hα A hT d j t.val).toBCF

lemma continuous_mildRHS (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
    (hT : 0 ≤ T) (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ))
    (L H : ℝ) (hL : 0≤L) (hH : 0≤H)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hhold : ∀ s : Time T, ∀ x y, ‖unweighted j s.val x-unweighted j s.val y‖ ≤
      H*s.val^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ)) :
    Continuous (mildRHS hα A b hT d j) := by
  have hu : Continuous (fun t : Time T => (mildTime hα A hT d j t.val).toBCF) :=
    ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp
      ((continuousOn_mildTime hα A hT d j).comp_continuous continuous_subtype_val
        (fun t => ⟨t.property.1.le,t.property.2⟩))
  exact ((continuous_coefficient_comp (fun t => A (now t)) (A.continuous.comp continuous_now)).mul
      (continuous_mildBilaplacian hα A hT d j L H hL hH hLip hhold)).neg.sub
    ((b.continuous.comp continuous_now).mul hu)

def realTest (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : SchwartzMap V ℂ :=
  HasCompactSupport.toSchwartzMap (f := Complex.ofRealCLM ∘ φ) (hc.comp_left rfl)
    (Complex.ofRealCLM.contDiff.comp hφ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma realTest_apply (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (x : V) :
    realTest φ hφ hc x = (φ x : ℂ) := rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma compactSupport_realTest (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    HasCompactSupport (realTest φ hφ hc : V → ℂ) := by
  change HasCompactSupport (Complex.ofRealCLM ∘ φ)
  exact hc.comp_left rfl

lemma pair_rhs_eq_neg_adjoint (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
    (t : Time T) (u : C₀(V,ℂ)) (U : V →ᵇ ℂ) (hu : ContDiff ℝ 4 (u : V → ℂ))
    (hU : ∀ x, U x = Δ (Δ (u : V → ℂ)) x)
    (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (ψ : SchwartzMap V ℂ) (hcψ : HasCompactSupport (ψ : V → ℂ))
    (hψ : ∀ x, ψ x = ((A (now t) x).val : ℂ)*(φ x : ℂ)) :
    TestSeparation.pairCLM φ (hφ.continuous.integrable_of_hasCompactSupport hc)
      (-(coefficient (A (now t)).toContinuousMap*U)-b (now t)*u.toBCF) =
      -adjointPair b t (realTest φ hφ hc) ψ u := by
  let P := TestSeparation.pairCLM (E := ℂ) φ (hφ.continuous.integrable_of_hasCompactSupport hc)
  have h0 : P (coefficient (A (now t)).toContinuousMap*U) =
      KernelPairing.pairCLM (Δ (Δ ψ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
        (Δ (Δ ψ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable u := by
    change (∫ x, φ x • (((A (now t) x).val : ℂ)*U x)) = _
    have he (x : V) : φ x • (((A (now t) x).val : ℂ)*U x) =
        ψ x*Δ (Δ (u : V → ℂ)) x := by
      rw [hψ,hU]
      simp only [Complex.real_smul]
      ring
    simp_rw [he]
    rw [ClassicalIBP.integral_bilaplacian_right _ _ (ψ.smooth 4) hcψ hu,
      KernelPairing.pairCLM_apply]
    congr 1
    funext x
    have heψ : ((Δ ψ : SchwartzMap V ℂ) : V → ℂ) = Δ (ψ : V → ℂ) :=
      funext (SchwartzMap.laplacian_apply ψ)
    rw [SchwartzMap.laplacian_apply,heψ]
  have h1 : P (b (now t)*u.toBCF) =
      KernelPairing.pairCLM (fun x => realTest φ hφ hc x*b (now t) x)
        (KernelPairing.integrable_pair _ (realTest φ hφ hc).integrable (b (now t))) u := by
    change (∫ x, φ x • (b (now t) x*u x)) = ∫ x, (φ x : ℂ)*b (now t) x*u x
    congr 1
    funext x
    simp only [Complex.real_smul]
    ring
  change P (-(coefficient (A (now t)).toContinuousMap*U)-b (now t)*u.toBCF) = _
  rw [map_sub,map_neg,h0,h1]
  simp only [adjointPair, add_apply]
  ring
end ParametrixVolterra

end

end OAI
