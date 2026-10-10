import Mathlib
import OAI.Analysis.Conductivity.Sobolev.WallParticularBounds
import OAI.Analysis.Conductivity.Walls.CriticalWallBounds

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

theorem wallParticularTensor_C0 {χ v r₁ r₂ : Box3 → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    {ε M δ κ : ℝ} (hε : 0≤ε) (hM : 0≤M) (hδ : 0≤δ) (hκ : 0<κ)
    (hχ : ∀ p,|χ p|≤1) (hz : ∀ p∈tsupport χ,|p.2|≤δ)
    (hr₁ : ∀ p,|r₁ p|≤ε) (hr₂ : ∀ p,|r₂ p|≤ε)
    (hder : ∀ p,|wallAlong (1,0) r₁ p|≤ε)
    (hvz : ∀ p∈tsupport χ,∀ t∈Icc (0:ℝ) 1,|wallDerivative v (p.1,t*p.2)|≤M)
    (hvs : ∀ p∈tsupport χ,∀ t∈Icc (0:ℝ) 1,|wallAlong (1,0) v (p.1,t*p.2)|≤M)
    (hvsz : ∀ p∈tsupport χ,∀ t∈Icc (0:ℝ) 1,|wallAlong (1,0) (wallDerivative v) (p.1,t*p.2)|≤M)
    (hden : ∀ p∈tsupport χ,κ≤|wallQuotient (wallDerivative v) p|) (x : Coord3) :
    ‖wallParticularTensor χ v r₁ r₂ x‖≤(δ+(1+M+3*δ*M)/κ)*ε := by
  let p := boxCoordinates x
  have hK : 0≤(δ+(1+M+3*δ*M)/κ)*ε := by positivity
  by_cases hp : p∈tsupport χ
  · have hA : |wallPrimitive r₁ p|≤δ*ε :=
      (wallPrimitive_abs_bound (fun t _ => hr₁ _)).trans (mul_le_mul_of_nonneg_right (hz p hp) hε)
    have hnum : |wallQuotient (wallParticularNumerator (1,0) v r₁ r₂) p|≤ε*(1+M+3*δ*M) :=
      wallQuotient_abs_bound (wallParticularNumerator_derivative_bound (1,0) hv h₁ h₂ hε hM
        (hz p hp) (fun _ _ => hr₁ _) (fun _ _ => hr₂ _) (fun _ _ => hder _)
        (hvz p hp) (hvs p hp) (hvsz p hp))
    have hB : |wallQuotient (wallParticularNumerator (1,0) v r₁ r₂) p/
        wallQuotient (wallDerivative v) p|≤ε*(1+M+3*δ*M)/κ := by
      rw [abs_div]
      exact div_le_div₀ (by positivity) hnum hκ (hden p hp)
    apply wallMatrix_norm_le hK
    · change |χ p*wallPrimitive r₁ p|≤_
      rw [abs_mul]
      calc
        _ ≤ 1*(δ*ε) := mul_le_mul (hχ p) hA (abs_nonneg _) (by norm_num)
        _ ≤ _ := by
          have hh : 0≤(1+M+3*δ*M)/κ := by positivity
          nlinarith
    · change |χ p*(_ / _)|≤_
      rw [abs_mul]
      calc
        _ ≤ 1*(ε*(1+M+3*δ*M)/κ) := mul_le_mul (hχ p) hB (abs_nonneg _) (by norm_num)
        _ ≤ _ := by nlinarith [show ε*(1+M+3*δ*M)/κ=((1+M+3*δ*M)/κ)*ε by ring]
  · have hzero : χ p=0 := image_eq_zero_of_notMem_tsupport hp
    apply wallMatrix_norm_le hK <;> change |χ p*_|≤_ <;>
      rw [hzero,zero_mul,abs_zero] <;> exact hK

variable {P : Type*} [TopologicalSpace P]

theorem compact_wall_particular_bound {χ : Box3 → ℝ} (hsχ : HasCompactSupport χ)
    (hχ : ∀ p,|χ p|≤1) {v : P → Box3 → ℝ} {p₀ : P}
    (hvsmooth : ∀ p,ContDiff ℝ (↑(⊤ : ℕ∞)) (v p))
    (hvs : Continuous (fun px : P×Box3 => wallAlong (1,0) (v px.1) px.2))
    (hvz : Continuous (fun px : P×Box3 => wallDerivative (v px.1) px.2))
    (hvsz : Continuous (fun px : P×Box3 => wallAlong (1,0) (wallDerivative (v px.1)) px.2))
    (hD : Continuous (fun px : P×Box3 => wallQuotient (wallDerivative (v px.1)) px.2))
    (hne : ∀ x∈tsupport χ,wallQuotient (wallDerivative (v p₀)) x≠0) :
    ∃ L : ℝ,0<L ∧ ∀ᶠ p in 𝓝 p₀,∀ (r₁ r₂ : Box3 → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) r₁ → ContDiff ℝ (↑(⊤ : ℕ∞)) r₂ →
      ∀ ε : ℝ,0≤ε → (∀ x,|r₁ x|≤ε) → (∀ x,|r₂ x|≤ε) →
      (∀ x,|wallAlong (1,0) r₁ x|≤ε) → ∀ x,
        ‖wallParticularTensor χ (v p) r₁ r₂ x‖≤L*ε := by
  obtain ⟨M,κ,hM,hκ,hfield⟩ := wall_field_uniform_bounds hsχ hvz hvsz hD hne
  obtain ⟨M₁,hM₁,hb₁⟩ := compact_parametric_abs_bound (f:=fun p x => wallAlong (1,0) (v p) x)
    (p₀:=p₀) (wallNormalHull_compact hsχ) hvs
  obtain ⟨δ,hδb⟩ := hsχ.exists_bound_of_continuousOn (continuous_snd : Continuous (fun p : Box3 => p.2)).continuousOn
  have hδ (p) (hp : p∈tsupport χ) : |p.2|≤|δ| := by
    have hh := hδb p hp
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (le_abs_self δ)
  let L := |δ|+(1+(M+M₁)+3*|δ| *(M+M₁))/κ
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨L,hL,?_⟩
  filter_upwards [hfield,hb₁] with p hp hps
  intro r₁ r₂ hr₁ hr₂ ε hε hb₁ hb₂ hder x
  apply wallParticularTensor_C0 (hvsmooth p) hr₁ hr₂ hε (add_pos hM hM₁).le
    (abs_nonneg δ) hκ hχ hδ hb₁ hb₂ hder _ _ _ hp.2.2 x
  · intro y hy t ht
    exact (hp.1 y hy t ht).trans (le_add_of_nonneg_right hM₁.le)
  · intro y hy t ht
    exact (hps _ (mem_wallNormalHull hy ht)).trans (le_add_of_nonneg_left hM.le)
  · intro y hy t ht
    exact (hp.2.1 y hy t ht).trans (le_add_of_nonneg_right hM₁.le)

end ScalarConductivity

end
end

end OAI
