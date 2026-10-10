import OAI.Analysis.AncientFlat.Evolution.PhysicalFromWindow

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
local instance physicalAncientC0SeminormedAddCommGroup : SeminormedAddCommGroup C₀(V,ℂ) := inferInstance
local instance physicalAncientSourceSeminormedAddCommGroup : SeminormedAddCommGroup (ℝ →ᵇ C₀(V,ℂ)) := inferInstance

theorem exists_physical_ancient_inverse (c : ℝ) (Af Bf : V → ℝ)
    (h : SymbolBounds c Af Bf) (hAf : Radial Af) (hBf : Radial Bf) :
    ∃ γ : ℝ, 0<γ ∧ γ<1/2 ∧
    ∃ D : (ℝ →ᵇ C₀(V,ℂ)) →L[ℂ] (ℝ →ᵇ C₀(V,ℂ)),
      (∀ η : ℝ, 0<η → η≤1 → ∀ f : ℝ →ᵇ C₀(V,ℂ),
        (∀ a : ℝ, ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc a (a+1), ∀ x y,
          ‖f t x-f t y‖≤H*‖x-y‖^η) →
        (∀ t : ℝ, ContDiff ℝ 4 (fun x => physical γ (D f) t x)) ∧
        (∀ t : ℝ, t<0 → ∀ x : V,
          HasDerivAt (fun r => physical γ (D f) r x)
            (physicalForce γ f t x-(physicalPrincipal Af t x : ℂ)*
              Δ (Δ (fun y => physical γ (D f) t y)) x-
              (physicalPotential Bf t x : ℂ)*physical γ (D f) t x) t)) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), ∀ t : ℝ, ∀ x : V,
        ‖physical γ (D f) t x‖≤‖D‖*‖f‖*Real.exp ((1/2-γ)*similarityTime t)) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), (∀ τ, Radial (f τ : V → ℂ)) →
        ∀ t, Radial (physical γ (D f) t : V → ℂ)) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), (∀ τ, RealValued (f τ : V → ℂ)) →
        ∀ t, RealValued (physical γ (D f) t : V → ℂ)) := by
  obtain ⟨γ,hγ,hγ1,S,h0,hc,ha,hE,D,hD,hRad,hReal⟩ :=
    exists_preliminary_ancient_inverse c Af Bf h hAf hBf
  obtain ⟨K,hK,hKb⟩ := AncientMild.bounded_on S hc 1
  refine ⟨γ,hγ,hγ1,D,?_,?_,?_,?_⟩
  · intro η hη hη1 f hf
    have hw (τ : ℝ) := classical_window c Af Bf h S h0 hc ⟨K,hKb⟩ ha hE γ hγ.le
      f (D f) (hD f) η hη hη1 (τ-1/2) (hf (τ-1/2))
    have hs : (1/2 : ℝ)∈Ioo (0:ℝ) 1 := by constructor <;> norm_num
    have hreg (τ : ℝ) : ContDiff ℝ 4 (fun x => D f τ x) := by
      obtain ⟨u,hu,hue⟩ := hw τ
      have he : renormalized γ u (1/2)=D f τ := by
        simpa only [sub_add_cancel] using hue (1/2) ⟨hs.1.le,hs.2.le⟩
      rw [←he]
      exact hu.renormalized_contDiff γ hs
    refine ⟨physical_contDiff γ (D f) hreg,?_⟩
    intro t ht x
    obtain ⟨u,hu,hue⟩ := hw (similarityTime t)
    exact physical_deriv_of_window Af Bf γ (similarityTime t-1/2) hγ.le f (D f) u hu hue ht
      (by simpa only [sub_sub_cancel] using hs) x
  · intro f t x
    have hb : ‖D f (similarityTime t) (Real.exp (similarityTime t/4) • x)‖≤‖D‖*‖f‖ :=
      ((D f (similarityTime t)).toBCF.norm_coe_le_norm _).trans
        (((D f).norm_coe_le_norm _).trans (D.le_opNorm f))
    rw [physical_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp ((1/2-γ)*similarityTime t)*(‖D‖*‖f‖) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = _ := by ring
  · intro f hf t R x
    simp only [physical_apply,←R.map_smul]
    rw [hRad f hf (similarityTime t) R]
  · intro f hf t x
    simp only [physical_apply,star_mul,Complex.star_def,Complex.conj_ofReal]
    simpa only [Complex.star_def,mul_comm] using congrArg (fun z : ℂ => (Real.exp ((1/2-γ)*similarityTime t) : ℂ)*z)
      (hReal f hf (similarityTime t) (Real.exp (similarityTime t/4) • x))
end FlatSimilarity

end

end OAI
