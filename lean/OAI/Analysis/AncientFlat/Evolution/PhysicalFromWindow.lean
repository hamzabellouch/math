import OAI.Analysis.AncientFlat.Evolution.PhysicalWindow

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
lemma physical_deriv_of_window (Af Bf : V → ℝ) (γ a : ℝ) (hγ : 0≤γ)
    (f v : ℝ →ᵇ C₀(V,ℂ)) (u : ℝ → C₀(V,ℂ))
    (hu : MovesWithSource Af Bf (normalizedSource γ a hγ f) (v a) u)
    (hue : ∀ s∈Icc (0:ℝ) 1, renormalized γ u s=v (a+s))
    {t : ℝ} (ht : t<0) (hs : similarityTime t-a∈Ioo (0:ℝ) 1) (x : V) :
    HasDerivAt (fun r => physical γ v r x)
      (physicalForce γ f t x-(physicalPrincipal Af t x : ℂ)*
        Δ (Δ (fun y => physical γ v t y)) x-
        (physicalPotential Bf t x : ℂ)*physical γ v t x) t := by
  have heq (r : ℝ) (hr : similarityTime r-a∈Icc (0:ℝ) 1) :
      physical γ v r=physicalWindow γ a u (similarityTime r-a) := by
    apply physical_eq_window
    simpa only [add_sub_cancel] using hue _ hr
  have hnear : ∀ᶠ r in 𝓝 t, similarityTime r-a∈Ioo (0:ℝ) 1 :=
    ((similarityTime_deriv ht).continuousAt.sub_const a).eventually
      (Ioo_mem_nhds hs.1 hs.2)
  have hfun : (fun r => physical γ v r x)=ᶠ[𝓝 t]
      (fun r => physicalWindow γ a u (similarityTime r-a) x) := by
    filter_upwards [hnear] with r hr
    exact congrArg (fun v : C₀(V,ℂ) => v x) (heq r ⟨hr.1.le,hr.2.le⟩)
  have hd := (hu.physicalWindow_deriv γ a hs x).scomp t ((similarityTime_deriv ht).sub_const a)
  have hh := hd.congr_of_eventuallyEq hfun
  convert hh using 1
  rw [show a+(similarityTime t-a)=similarityTime t by ring,
    normalizedSource_apply γ a hγ f ⟨hs.1.le,hs.2.le⟩,
    show a+(similarityTime t-a)=similarityTime t by ring,
    ←heq t ⟨hs.1.le,hs.2.le⟩]
  simp only [physicalForce]
  rw [physical_apply (γ-1)]
  simp only [physicalPrincipal,physicalPotential,ZeroAtInftyContinuousMap.smul_apply,
    Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,
    smul_eq_mul]
  have hc1 : Real.exp (similarityTime t)*Real.exp (-(similarityTime t))=1 := by
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hc2 : Real.exp (similarityTime t)*Real.exp ((1/2-γ)*a+(similarityTime t-a)/2)*
      Real.exp (-γ*(similarityTime t-a))=Real.exp ((1/2-(γ-1))*similarityTime t) := by
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hc1' := congrArg Complex.ofReal hc1
  have hc2' := congrArg Complex.ofReal hc2
  simp only [Complex.ofReal_mul,Complex.ofReal_one] at hc1' hc2'
  linear_combination
    -(f (similarityTime t) (Real.exp (similarityTime t/4) • x))*hc2' +
    ((Af (Real.exp (similarityTime t/4) • x) : ℂ)/16*
      Δ (Δ (fun y => physical γ v t y)) x)*hc1'
end FlatSimilarity

end

end OAI
