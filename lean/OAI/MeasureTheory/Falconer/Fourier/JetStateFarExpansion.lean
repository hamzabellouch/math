import OAI.MeasureTheory.Falconer.Fourier.JetStateStationary

namespace OAI

/-! # Full-sphere expansion for the actual far-state amplitudes

All angular factors are the original normalized descriptor jets. The
constants precede the scale and list, while each pair keeps both endpoints.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

 theorem exists_descriptorJetSymbol_pair_budget (n K L : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (F : Finset PolicyDescriptor)
      (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
      (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol n K L F Dq) (x y : Space (n+2)) (t : ℕ), t ≤ L →
      ∀ w : Sphere (n+2),
        ‖iteratedFDeriv ℝ t (f.pairAmbient Q ρ m N σ J i S A x y) w‖ ≤
          (B^K*A⁻¹)^2*(2*(E+Dq))^t := by
  obtain ⟨B,hB,hbound⟩ := exists_descriptorJetSymbol_ambient_budget n K L
  refine ⟨B,hB,?_⟩
  intro F Q ρ m N σ J i S hsep Dq Dmask E A hDq hDm hA hscale hE f x y t ht w
  have hE0 : 0 ≤ E := (by positivity : 0 ≤ (F.card:ℝ)*B*Dmask).trans hE
  have hD : 0 ≤ E+Dq := add_nonneg hE0 hDq
  have hC : 0 ≤ B^K*A⁻¹ := by positivity
  have hb (x : Space (n+2)) (j : ℕ) (hj : j ≤ t) :=
    hbound F Q ρ m N σ J i S hsep Dq Dmask E A hDq hDm hA hscale hE f x j (hj.trans ht) w
  have hc (j : ℕ) (hj : j ≤ t) :
      ‖iteratedFDeriv ℝ j (fun z => star (f.ambient Q ρ m N σ J i S A y z)) w‖ ≤
        (B^K*A⁻¹)*(E+Dq)^j := by
    have he := Complex.conjLIE.norm_iteratedFDeriv_comp_left
      (f.ambient Q ρ m N σ J i S A y) (w:Space (n+2)) j
    exact he.le.trans (hb y j hj)
  have h := iteratedFDeriv_mul_bound _ _ (f.ambient_smooth Q ρ m N σ J i S A x)
    (Complex.conjCLE.contDiff.comp (f.ambient_smooth Q ρ m N σ J i S A y))
    hC hC hD hD t (w:Space (n+2)) (hb x) hc
  have he : (fun z => f.ambient Q ρ m N σ J i S A x z *
      (Complex.conjCLE ∘ f.ambient Q ρ m N σ J i S A y) z) =
      f.pairAmbient Q ρ m N σ J i S A x y := rfl
  rw [he] at h
  simpa only [sq,two_mul] using h

 theorem exists_jetState_far_sphere_expansion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m₀ J K L : ℕ) (hJ : 1 ≤ J) (hL : 2*J+(m₀+2)+1 ≤ L) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ ∀ (F : Finset PolicyDescriptor)
      (Q : DyadicCube (m₀+3)) (ρ : Measure (Space (m₀+3))) (m : ℝ → ℝ)
      (N : ℕ) (σ : ℝ) (J₀ i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m₀+3))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol (m₀+1) K L F Dq) (x y : Space (m₀+3))
        (e : Sphere (m₀+3)) (Λ : ℝ), 1 ≤ Λ →
      ‖sphereOscillation Λ e (fun w => f.value Q ρ m N σ J₀ i S A x w*
            star (f.value Q ρ m N σ J₀ i S A y w))-
          stationarySphereApprox m₀ J Λ (f.pairAmbient Q ρ m N σ J₀ i S A x y) e‖ ≤
        C*Λ^(-(J:ℝ)-((m₀+2:ℕ):ℝ)/2)*(B^K*A⁻¹)^2*
          (2*(E+Dq))^(2*J+(m₀+2)+1) := by
  obtain ⟨B,hB,hbound⟩ := exists_descriptorJetSymbol_pair_budget (m₀+1) K L
  obtain ⟨C,hC,hstationary⟩ := sphere_stationary_expansion_unscaled hgnomonic hquadratic m₀ J hJ
  refine ⟨B,C,hB,hC,?_⟩
  intro F Q ρ m N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE f x y e Λ hΛ
  have hb (j : ℕ) (hj : j ≤ 2*J+(m₀+2)+1) (w : Sphere (m₀+3)) :=
    hbound F Q ρ m N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hscale hE f x y j (hj.trans hL) w
  have h := hstationary e (f.pairAmbient Q ρ m N σ J₀ i S A x y)
    (f.pairAmbient_smooth Q ρ m N σ J₀ i S A x y) ((B^K*A⁻¹)^2) (2*(E+Dq))
    (sq_nonneg _) hD hb Λ hΛ
  simpa only [DescriptorJetSymbol.pairAmbient_sphere] using h

end Falconer

end OAI
