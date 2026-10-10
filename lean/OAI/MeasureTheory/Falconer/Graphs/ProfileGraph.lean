import OAI.MeasureTheory.Falconer.Recursion.ProfileNear
import OAI.MeasureTheory.Falconer.Graphs.ProfileGraphDegree

namespace OAI

/-! # Profile normalization of the retained graph contribution

The sum is over the actual occupied descendants and retains both endpoint
symbols. The degree is the integer degree used in the graph energy estimate.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem two_profile_graph_prefactor {N : ℕ} (hN : 0 < N)
    (d : ℕ) (m₁ m₂ : ℝ → ℝ) (a p : ℕ) (lam : ℝ) :
    ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
      (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) *
      ((2:ℝ)^N)^((m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N))+
        (m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) =
    ((2:ℝ)^N)^(-((m₁ ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
      (m₁ ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))-
      ((m₂ ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
      (m₂ ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hr (m : ℝ → ℝ) : profileModelMass m N p/profileModelMass m N a =
      ((2:ℝ)^N)^(-(m ((p:ℝ)/N)-m ((a:ℝ)/N))) := by
    unfold profileModelMass
    rw [← Real.rpow_sub hR]
    congr 1
    ring
  rw [hr m₁,hr m₂,← Real.rpow_add hR,← Real.rpow_natCast,← Real.rpow_mul hR.le,
    ← dyadic_rpow_change_base hN ((d:ℝ)*((p:ℝ)-a)),
    ← Real.rpow_add hR,← Real.rpow_add hR]
  congr 1
  ring

noncomputable def twoProfileGraphContribution (Q₁ Q₂ : DyadicCube d)
    (ρ₁ ρ₂ : Measure (Space d)) (m₁ m₂ : ℝ → ℝ) (N a p : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    (b c : Space d → Sphere d → ℂ) (degree : ℕ) : ℝ :=
  ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
    ((2:ℝ)^((d:ℝ)*((p:ℝ)-a)) * degree *
      ∑ row ∈ Q₁.occupiedPaths ρ₁ (p-a) ×ˢ Q₂.occupiedPaths ρ₂ (p-a),
        independentAngularEnergy p v Ψ
          (fun z => endpointTransform (ρ₁.restrict (Q₁.descendant row.1).carrier)
            (profileModelMass m₁ N p) b z.1 z.2)
          (fun z => endpointTransform (ρ₂.restrict (Q₂.descendant row.2).carrier)
            (profileModelMass m₂ N p) c z.1 z.2))

theorem two_profile_graph_contribution_bound (Q₁ Q₂ : DyadicCube d)
    (ρ₁ ρ₂ : Measure (Space d)) {m₁ m₂ : ℝ → ℝ} {N : ℕ} {s₁ s₂ lam : ℝ}
    (hreg₁ : Regularization.RegularizedProfileData Q₁ ρ₁ N s₁ lam m₁)
    (hreg₂ : Regularization.RegularizedProfileData Q₂ ρ₂ N s₂ lam m₂) (hN : 0 < N)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (v : ℝ) (Ψ : ℝ → ℝ) (b c : Space d → Sphere d → ℂ)
    (degree : ℕ) {K H E : ℝ} (_hK : 0 ≤ K) (hE : 0 ≤ E)
    (hdegree : (degree:ℝ) ≤ K*((2:ℝ)^N)^H)
    (hchild : ∀ row ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
        (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
      independentAngularEnergy p v Ψ
        (fun z => endpointTransform
          (ρ₁.restrict ((Q₁.descendant X).descendant row.1).carrier)
          (profileModelMass m₁ N p) b z.1 z.2)
        (fun z => endpointTransform
          (ρ₂.restrict ((Q₂.descendant Y).descendant row.2).carrier)
          (profileModelMass m₂ N p) c z.1 z.2) ≤ E) :
    twoProfileGraphContribution (Q₁.descendant X) (Q₂.descendant Y)
      ρ₁ ρ₂ m₁ m₂ N a p v Ψ b c degree ≤
      K*((2:ℝ)^N)^(-((m₁ ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
        (m₁ ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))-
        ((m₂ ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
        (m₂ ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+H+4*((d:ℝ)+1)*lam)*E := by
  have hs := Finset.sum_le_sum hchild
  rw [Finset.sum_const,nsmul_eq_mul] at hs
  have hrows := hreg₁.pair_count_two hreg₂ hap hp X Y hX hY
  have hsum := hs.trans (mul_le_mul_of_nonneg_right hrows hE)
  have hboth : (degree:ℝ) *
      (∑ row ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
        (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
        independentAngularEnergy p v Ψ
          (fun z => endpointTransform
            (ρ₁.restrict ((Q₁.descendant X).descendant row.1).carrier)
            (profileModelMass m₁ N p) b z.1 z.2)
          (fun z => endpointTransform
            (ρ₂.restrict ((Q₂.descendant Y).descendant row.2).carrier)
            (profileModelMass m₂ N p) c z.1 z.2)) ≤
      (K*((2:ℝ)^N)^H) *
        (((2:ℝ)^N)^((m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N))+(m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N))+4*((d:ℝ)+1)*lam)*E) :=
    (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg degree)).trans
      (mul_le_mul_of_nonneg_right hdegree (by positivity))
  unfold twoProfileGraphContribution
  calc
    _ = (((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        (2:ℝ)^((d:ℝ)*((p:ℝ)-a))) * _ := by ring
    _ ≤ (((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        (2:ℝ)^((d:ℝ)*((p:ℝ)-a))) *
        ((K*((2:ℝ)^N)^H) *
          (((2:ℝ)^N)^((m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N))+(m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N))+4*((d:ℝ)+1)*lam)*E)) :=
      mul_le_mul_of_nonneg_left hboth (by positivity)
    _ = K * (((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) *
        ((2:ℝ)^N)^((m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N))+(m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N))+4*((d:ℝ)+1)*lam)) *
        ((2:ℝ)^N)^H * E := by ring
    _ = _ := by
      rw [two_profile_graph_prefactor hN,mul_assoc K,← Real.rpow_add (by positivity)]
      congr 2
      ring_nf

end Falconer

end OAI
