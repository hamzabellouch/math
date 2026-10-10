import OAI.Analysis.AncientFlat.Evolution.ClassicalAncientWindow

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem exists_classical_ancient_inverse (c : ℝ) (Af Bf : V → ℝ)
    (h : SymbolBounds c Af Bf) (hAf : Radial Af) (hBf : Radial Bf) :
    ∃ γ : ℝ, 0<γ ∧ γ<1/2 ∧
    ∃ D : (ℝ →ᵇ C₀(V,ℂ)) →L[ℂ] (ℝ →ᵇ C₀(V,ℂ)),
      (∀ η : ℝ, 0<η → η≤1 → ∀ f : ℝ →ᵇ C₀(V,ℂ),
        (∀ a : ℝ, ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc a (a+1), ∀ x y,
          ‖f t x-f t y‖≤H*‖x-y‖^η) → AncientClassical Af Bf γ f (D f)) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), (∀ τ, Radial (f τ : V → ℂ)) →
        ∀ τ, Radial (D f τ : V → ℂ)) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), (∀ τ, RealValued (f τ : V → ℂ)) →
        ∀ τ, RealValued (D f τ : V → ℂ)) := by
  obtain ⟨γ,hγ,hγ1,S,h0,hc,ha,hE,D,hD,hRad,hReal⟩ :=
    exists_preliminary_ancient_inverse c Af Bf h hAf hBf
  obtain ⟨K,hK,hKb⟩ := AncientMild.bounded_on S hc 1
  refine ⟨γ,hγ,hγ1,D,?_,hRad,hReal⟩
  intro η hη hη1 f hf
  have hpoint (t : ℝ) :
      ContDiff ℝ 4 (fun x => D f t x) ∧
      (∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (fun y => D f t y) x‖≤M) ∧
      (∀ x : V, HasDerivAt (fun r => D f r x)
        (f t x-(Af x/16 : ℝ) • Δ (Δ (fun y => D f t y)) x-
          (1/2-γ+Bf x : ℝ) • D f t x-(1/4 : ℝ) • (fderiv ℝ (fun y => D f t y) x x)) t) := by
    obtain ⟨u,hu,hue⟩ := classical_window c Af Bf h S h0 hc ⟨K,hKb⟩ ha hE γ hγ.le
      f (D f) (hD f) η hη hη1 (t-1/2) (hf (t-1/2))
    have ht : (1/2 : ℝ) ∈ Ioo (0:ℝ) 1 := by constructor <;> norm_num
    have ht' : (1/2 : ℝ) ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    have he : renormalized γ u (1/2)=D f t := by
      simpa only [sub_add_cancel] using hue (1/2) ht'
    refine ⟨?_,?_,?_⟩
    · rw [←he]
      exact hu.renormalized_contDiff γ ht
    · rw [←he]
      exact hu.renormalized_jets γ ht
    · intro x
      have hd := hu.renormalized_deriv γ ht x
      have hsrc : (Real.exp (γ*(1/2)) : ℂ) • normalizedSource γ (t-1/2) hγ.le f (1/2) x=f t x := by
        rw [normalizedSource_apply γ (t-1/2) hγ.le f ht']
        change (Real.exp (γ*(1/2)) : ℂ) • ((Real.exp (-γ*(1/2)) : ℂ) • f (t-1/2+1/2) x)=_
        rw [smul_smul,←Complex.ofReal_mul,←Real.exp_add,show γ*(1/2)+ -γ*(1/2)=0 by ring,
          Real.exp_zero,Complex.ofReal_one,one_smul,sub_add_cancel]
      rw [hsrc,he] at hd
      have hs : HasDerivAt (fun r : ℝ => r-t+1/2) 1 t :=
        ((hasDerivAt_id t).sub_const t).add_const (1/2)
      have hh := hd.scomp_of_eq t hs (by simp)
      simp only [one_smul] at hh
      apply hh.congr_of_eventuallyEq
      have hc' : Continuous (fun r : ℝ => r-t+1/2) := (continuous_id.sub continuous_const).add continuous_const
      have hnear : ∀ᶠ r in 𝓝 t, r-t+1/2 ∈ Ioo (0:ℝ) 1 :=
        (hc'.tendsto t).eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
      filter_upwards [hnear] with r hr
      change D f r x=renormalized γ u (r-t+1/2) x
      rw [hue _ ⟨hr.1.le,hr.2.le⟩,show t-1/2+(r-t+1/2)=r by ring]
  exact ⟨fun t => (hpoint t).1,fun t => (hpoint t).2.1,fun t => (hpoint t).2.2⟩
end FlatSimilarity

end

end OAI
