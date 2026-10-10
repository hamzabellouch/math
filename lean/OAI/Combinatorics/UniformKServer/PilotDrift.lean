import Mathlib
import OAI.Combinatorics.UniformKServer.PilotCredits

namespace OAI

section
namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

attribute [local instance] Classical.propDecidable

/-- Companion §06, Lemma pilot-drift, in increasing scale order (the finite
source list is its reversal). The integer p is any fixed scale-shift with
2^p γ ≥ 100R; the source uses ceil(log₂(100R/γ)). No drift estimate is assumed. -/
theorem pilot_drift (r τ σ R γ δ L : ℝ) (N p k : ℕ)
    (hr : 0 < r) (hτ : 2 ≤ τ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hγL : γ ≤ 1/(1+L))
    (hδ : 0 < δ) (hδbound : δ ≤ 1/4112) (hk : 2 ≤ k)
    (hp : 100*R ≤ γ*(2:ℝ)^p)
    (μ ν : X → ℝ) (g : ℕ → X → ℝ) (x : X)
    (hμ : ∀ y, 0 ≤ μ y) (hμk : ∑ y, μ y = k)
    (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (hνμ : ∀ y, ν y ≤ μ y)
    (hg : ∀ j y, g j y ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ j y z, |g j y-g j z| ≤ L*(dist y z/(r*τ^j))) :
    (∑ j ∈ Finset.range N,
      max (value (r*τ^j) σ R (fun y => μ y-ν y+if y=x then 1 else 0) (g j) -
        value (r*τ^j) σ R μ (g j)) 0) ≤
      driftConstant σ γ δ L p * (1+Real.log (k+1)) * (∑ y, ν y*dist x y) := by
  classical
  let e := ∑ y, ν y*dist x y
  have he : 0 ≤ e := Finset.sum_nonneg fun y _ => mul_nonneg (hν y) dist_nonneg
  have hτ0 : 0 < τ := by linarith
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨m,hmN,hsmall,hcoarse⟩ := scale_cut r τ γ e N hγ
  have hsm := small_drift r τ σ R γ e m hr hτ hσ hσ1 hR hγ he μ ν g x hν hν1 hg hsmall
  have hco : (∑ j ∈ Finset.range (N-m), positiveDrift (r*τ^(m+j)) σ R μ ν (g (m+j)) x) ≤
      coarseConstant σ γ δ L p k*e := by
    rcases hcoarse with hm | hcoarse
    · subst m
      simp only [Nat.sub_self,Finset.range_zero,Finset.sum_empty]
      exact mul_nonneg (coarseConstant_nonneg σ γ δ L p k hσ hγ hδ hL (by linarith)) he
    · have hrm : 0 < r*τ^m := by positivity
      have hM := inner_mass_half (r*τ^m) γ hrm hγ μ ν hμ hν hν1 hνμ x hcoarse
      have hh := coarse_drift (r*τ^m) τ σ R γ δ L (N-m) p k hrm hτ hσ hσ1 hR
        hL hγ hγσ hγL hδ hδbound (by linarith) hp μ ν (fun j => g (m+j)) x hμ hμk
        hν hν1 (fun j => hg (m+j)) (fun j y z => by
          simpa only [pow_add,mul_assoc] using hgLip (m+j) y z) hM
      simpa only [pow_add,mul_assoc] using hh
  have hsum : (∑ j ∈ Finset.range N, positiveDrift (r*τ^j) σ R μ ν (g j) x) =
      (∑ j ∈ Finset.range m, positiveDrift (r*τ^j) σ R μ ν (g j) x)+
        ∑ j ∈ Finset.range (N-m), positiveDrift (r*τ^(m+j)) σ R μ ν (g (m+j)) x := by
    conv_lhs => rw [show N = m+(N-m) by omega,Finset.sum_range_add]
  change (∑ j ∈ Finset.range N, positiveDrift (r*τ^j) σ R μ ν (g j) x) ≤ _
  rw [hsum]
  calc
    _ ≤ (2056/γ)*e+coarseConstant σ γ δ L p k*e := add_le_add hsm hco
    _ = (2056/γ+coarseConstant σ γ δ L p k)*e := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (driftConstant_log σ γ δ L p k hσ hγ hδ hL hkR) he

end
end UniformKServer.PilotCompact

end



end OAI
