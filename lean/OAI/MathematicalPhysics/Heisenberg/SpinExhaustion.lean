import OAI.MathematicalPhysics.Heisenberg.SpinAverage

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
open Filter Topology
namespace Heisenberg
lemma local_coefficients_stabilize_exhausting {d ℓ : ℕ} (Γ : ℕ → Finset (Site d))
    (hΓ : ∀ F : Finset (Site d),∀ᶠ n : ℕ in atTop,F⊆Γ n)
    (F : Finset (Site d)) {A : QuasiLocal d ℓ}
    (hA : A∈localAlgebra d ℓ (F : Set (Site d))) (n : ℕ) :
    ∃ B : QuasiLocal d ℓ,∀ᶠ m : ℕ in atTop,((finiteGenerator d ℓ (Γ m))^n) A=B := by
  let : Monoid (QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ):=inferInstance
  have hh : ∀ n : ℕ,∃ (G : Finset (Site d)) (B : QuasiLocal d ℓ),
      B∈localAlgebra d ℓ (G : Set (Site d)) ∧
      ∀ᶠ m : ℕ in atTop,((finiteGenerator d ℓ (Γ m))^n) A=B := by
    intro n
    induction n with
    | zero=>exact ⟨F,A,hA,by simp⟩
    | succ n ih=>
      obtain ⟨G,B,hB,hlim⟩:=ih
      refine ⟨G∪neighborhood G,finiteGenerator d ℓ (neighborhood G) B,
        finiteGenerator_local _ G hB,?_⟩
      filter_upwards [hlim,hΓ (neighborhood G)] with m hm hmG
      rw [pow_succ',mul_apply_eq_comp,hm]
      exact finiteGenerator_stable _ G hmG hB
  obtain ⟨G,B,hB,hlim⟩:=hh n
  exact ⟨B,hlim⟩

private theorem clm_topologicalRing' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsTopologicalRing (E →L[ℂ] E):=inferInstance
local instance (d ℓ : ℕ) : IsTopologicalRing (QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ):=clm_topologicalRing'

theorem dynamics_exhausting_exists (d ℓ : ℕ) (Γ : ℕ → Finset (Site d))
    (hΓ : ∀ F : Finset (Site d),∀ᶠ n : ℕ in Filter.atTop,F⊆Γ n) :
    ∀ t : ℝ,∀ A : QuasiLocal d ℓ,∃ B,Filter.Tendsto (fun n=>finiteDynamics d ℓ (Γ n) t A) Filter.atTop (nhds B) := by
  let C : ℝ := 8*d*bondBound d ℓ
  have hC : 0 ≤ C := (finiteGenerator_localDecomposition d ℓ (Γ 0)).nonneg
  let δ : ℝ := 1/(C+1)
  have hδ : 0 < δ := one_div_pos.mpr (by linarith)
  have hs : ∀ t : ℝ, |t| < δ → ∀ A : QuasiLocal d ℓ, ∃ B,
      Filter.Tendsto (fun n => finiteDynamics d ℓ (Γ n) t A) Filter.atTop (nhds B) := by
    intro t ht
    apply IsometricLimits.limit_on_dense (fun n => finiteDynamics d ℓ (Γ n) t)
      (fun n => finiteDynamics_isometry _ _ _ _) (localCore d ℓ) (localCore_dense d ℓ)
    intro A hA
    obtain ⟨F,hF⟩ := localCore_finite_support hA
    have hz : ‖(t : ℂ)‖*C < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h := (lt_div_iff₀ (by linarith : 0 < C+1)).mp ht
      nlinarith [abs_nonneg t]
    have hh := SpinEvolution.local_exponential_converges
      (fun n => finiteGenerator d ℓ (Γ n)) (SupportedOnAtMost d ℓ) C
      (fun n => finiteGenerator_localDecomposition d ℓ (Γ n)) F.card A
      ⟨F,Nat.le_succ _,hF⟩ (t : ℂ) hz (local_coefficients_stabilize_exhausting Γ hΓ F hF)
    simpa only [← finiteDynamics_generator] using hh
  have hall := IsometricLimits.all_times (fun n => finiteDynamics d ℓ (Γ n))
    (fun n t => finiteDynamics_isometry _ _ _ _)
    (fun n A => finiteDynamics_zero _ _ _ _)
    (fun n s t A => finiteDynamics_group _ _ _ _ _ _) δ hδ hs
  exact hall

theorem dynamics_tendsto_exhausting (d ℓ : ℕ) (Γ : ℕ → Finset (Site d))
    (hΓ : ∀ F : Finset (Site d),∀ᶠ n : ℕ in atTop,F⊆Γ n) (t : ℝ) (A : QuasiLocal d ℓ) :
    Tendsto (fun n=>finiteDynamics d ℓ (Γ n) t A) atTop (𝓝 (dynamics d ℓ t A)) := by
  let Δ : ℕ → Finset (Site d):=fun n=>if n%2=0 then box d (n/2) else Γ (n/2)
  have hΔ : ∀ F : Finset (Site d),∀ᶠ n : ℕ in atTop,F⊆Δ n := by
    intro F
    obtain ⟨N,hN⟩:=eventually_atTop.mp (hΓ F)
    obtain ⟨M,hM⟩:=eventually_atTop.mp (eventually_subset_box F)
    apply eventually_atTop.mpr
    refine ⟨2*(max N M)+2,?_⟩
    intro n hn
    have hN' : N≤n/2:=by omega
    have hM' : M≤n/2:=by omega
    dsimp only [Δ]
    split_ifs
    · exact hM _ hM'
    · exact hN _ hN'
  obtain ⟨B,hB⟩:=dynamics_exhausting_exists d ℓ Δ hΔ t A
  have heven : Tendsto (fun n : ℕ=>2*n) atTop atTop := tendsto_atTop_mono (fun n=>by change n≤_; omega) tendsto_id
  have hodd : Tendsto (fun n : ℕ=>2*n+1) atTop atTop := tendsto_atTop_mono (fun n=>by change n≤_; omega) tendsto_id
  have he : Tendsto (fun n=>finiteDynamics d ℓ (box d n) t A) atTop (𝓝 B) := by
    convert hB.comp heven using 1
    funext n
    simp [Δ]
  have ho : Tendsto (fun n=>finiteDynamics d ℓ (Γ n) t A) atTop (𝓝 B) := by
    convert hB.comp hodd using 1
    funext n
    simp [Δ,Nat.add_div]
  have hb : B=dynamics d ℓ t A:=tendsto_nhds_unique he (dynamics_converges d ℓ t A)
  rwa [hb] at ho

end Heisenberg
end
end

end OAI
