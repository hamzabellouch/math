import OAI.Analysis.AncientFlat.Evolution.ClassicalAncientCore

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma classical_window (c : ℝ) (Af Bf : V → ℝ) (h : SymbolBounds c Af Bf)
    (S : ℝ → (C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)))
    (h0 : S 0=ContinuousLinearMap.id ℂ C₀(V,ℂ))
    (hc : ∀ d : C₀(V,ℂ), ContinuousOn (fun t => S t d) (Ici (0:ℝ)))
    (hb : ∃ K : ℝ, ∀ t ∈ Icc (0:ℝ) 1, ‖S t‖≤K)
    (ha : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s+t)=(S s).comp (S t))
    (hE : ∀ d : C₀(V,ℂ), ∃ u : ℝ → C₀(V,ℂ), MovesClassically Af Bf d u ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S t d x=u t (Real.exp (-t/4) • x))
    (γ : ℝ) (hγ : 0≤γ) (f v : ℝ →ᵇ C₀(V,ℂ))
    (hv : ∀ a t : ℝ, 0 ≤ t → t≤1 →
      v (a+t)=(Real.exp (γ*t) : ℂ) • S t (v a)+
        ∫ s in (0:ℝ)..t, (Real.exp (γ*(t-s)) : ℂ) • S (t-s) (f (a+s)))
    (η : ℝ) (hη : 0<η) (hη1 : η≤1) (a : ℝ)
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc a (a+1), ∀ x y,
      ‖f t x-f t y‖≤H*‖x-y‖^η) :
    ∃ u : ℝ → C₀(V,ℂ), MovesWithSource Af Bf (normalizedSource γ a hγ f) (v a) u ∧
      ∀ s ∈ Icc (0:ℝ) 1, renormalized γ u s=v (a+s) := by
  obtain ⟨u,hu,hue⟩ := classical_duhamel c Af Bf h S h0 hc hb ha hE η hη hη1
    (normalizedSource γ a hγ f) (normalizedSource_holder γ a η hγ f hf) (v a)
  refine ⟨u,hu,fun s hs => ?_⟩
  have hv' := AncientMild.unnormalize_duhamel γ S f v a s (hv a s hs.1 hs.2)
  have hsub : (∫ r in (0:ℝ)..s, S (s-r) (normalizedSource γ a hγ f r))=
      ∫ r in (0:ℝ)..s, S (s-r) ((Real.exp (-γ*r) : ℂ) • f (a+r)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs.1] at hr
    dsimp only
    rw [normalizedSource_apply γ a hγ f ⟨hr.1,hr.2.trans hs.2⟩]
  have huz : dil s (u s)=(Real.exp (-γ*s) : ℂ) • v (a+s) := by
    rw [hv',←hsub]
    apply ZeroAtInftyContinuousMap.ext
    intro x
    have he := hue s hs (Real.exp (-s/4) • x)
    rw [smul_smul,←Real.exp_add,show s/4 + -s/4=0 by ring,Real.exp_zero,one_smul] at he
    exact he
  change (Real.exp (γ*s) : ℂ) • dil s (u s)=_
  rw [huz,smul_smul,←Complex.ofReal_mul,←Real.exp_add,show γ*s + -γ*s=0 by ring,
    Real.exp_zero,Complex.ofReal_one,one_smul]
end FlatSimilarity

end

end OAI
