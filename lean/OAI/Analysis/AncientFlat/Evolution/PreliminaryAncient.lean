import OAI.Analysis.AncientFlat.Spectral.SpectralCircle
import OAI.Analysis.AncientFlat.Kernel.SymbolSemigroup
import OAI.Analysis.AncientFlat.Evolution.SemigroupNormalize
import OAI.Analysis.AncientFlat.Evolution.SemigroupSymmetry
import OAI.Analysis.AncientFlat.Evolution.MildSymmetry

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem exists_preliminary_ancient_inverse (c : ℝ) (Af Bf : V → ℝ)
    (h : SymbolBounds c Af Bf) (hAf : Radial Af) (hBf : Radial Bf) :
    ∃ γ : ℝ, 0<γ ∧ γ<1/2 ∧
    ∃ S : ℝ → (C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)),
      S 0=ContinuousLinearMap.id ℂ C₀(V,ℂ) ∧
      (∀ d : C₀(V,ℂ), ContinuousOn (fun t => S t d) (Ici (0:ℝ))) ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s+t)=(S s).comp (S t)) ∧
      (∀ d : C₀(V,ℂ), ∃ u : ℝ → C₀(V,ℂ), MovesClassically Af Bf d u ∧
        ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S t d x=u t (Real.exp (-t/4) • x)) ∧
    ∃ D : (ℝ →ᵇ C₀(V,ℂ)) →L[ℂ] (ℝ →ᵇ C₀(V,ℂ)),
      (∀ f : ℝ →ᵇ C₀(V,ℂ), ∀ τ t : ℝ, 0 ≤ t → t≤1 →
        D f (τ+t)=(Real.exp (γ*t) : ℂ) • S t (D f τ)+
          ∫ s in (0:ℝ)..t, (Real.exp (γ*(t-s)) : ℂ) • S (t-s) (f (τ+s))) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), (∀ τ, Radial (f τ : V → ℂ)) →
        ∀ τ, Radial (D f τ : V → ℂ)) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), (∀ τ, RealValued (f τ : V → ℂ)) →
        ∀ τ, RealValued (D f τ : V → ℂ)) := by
  obtain ⟨K,hK,S,h0,hbound,hcont,hadd,hE⟩ := exists_symbol_semigroup c Af Bf h
  have ha : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s+t)=(S s).comp (S t) := by
    intro s t hs ht
    rw [add_comm]
    exact hadd t s ht hs
  have hP : TimeOneMap Af Bf (S 1) := by
    intro d
    obtain ⟨u,hu,he⟩ := hE d
    exact ⟨u,hu,he 1 ⟨zero_le_one,le_rfl⟩⟩
  obtain ⟨q,hql,hqu,hqcircle⟩ := exists_nonspectral_circle c Af Bf h (S 1) hP
  have hq : 0<q := (Real.exp_pos _).trans hql
  let γ := -Real.log q
  have hγ : 0<γ := neg_pos.mpr (Real.log_neg hq hqu)
  have hγu : γ<1/2 := by
    have hh := Real.log_lt_log (Real.exp_pos _) hql
    rw [Real.log_exp] at hh
    dsimp [γ]
    linarith
  let T := AncientMild.normalize γ S
  have hT0 : T 0=ContinuousLinearMap.id ℂ C₀(V,ℂ) := AncientMild.normalize_zero γ S h0
  have hTc : ∀ v : C₀(V,ℂ), ContinuousOn (fun t => T t v) (Ici (0:ℝ)) :=
    AncientMild.normalize_continuous γ S hcont
  have hTa : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s+t)=(T s).comp (T t) :=
    AncientMild.normalize_add γ S ha
  have hTb : ∀ t ∈ Icc (0:ℝ) 1, ‖T t‖≤Real.exp γ*K :=
    AncientMild.normalize_bound γ K hγ.le hK S hbound
  have hT1 : T 1=(q⁻¹:ℂ) • S 1 := by
    simp only [T,AncientMild.normalize,mul_one,γ,Real.exp_neg,Real.exp_log hq,Complex.ofReal_inv]
  have hcircle : ∀ z : ℂ, ‖z‖=1 → z ∈ resolventSet ℂ (T 1) := by
    rw [hT1]
    exact AncientMild.normalized_circle (S 1) hq hqcircle
  obtain ⟨D,hD⟩ := AncientMild.exists_bounded_mild_inverse T (Real.exp γ*K) hT0 hTb hTc hTa hcircle
  refine ⟨γ,hγ,hγu,S,h0,hcont,ha,hE,D,?_,?_,?_⟩
  · simpa only [T,AncientMild.normalize_apply] using hD
  · intro f hf τ R x
    have hc (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (v : C₀(V,ℂ)) :
        (FlatSymmetry.rotate R).restrictScalars ℝ (T t v)=T t ((FlatSymmetry.rotate R).restrictScalars ℝ v) := by
      change FlatSymmetry.rotate R ((Real.exp (γ*t):ℂ) • S t v)=
        (Real.exp (γ*t):ℂ) • S t (FlatSymmetry.rotate R v)
      rw [(FlatSymmetry.rotate R).map_smul,actual_rotate h S hE hAf hBf R t ht]
    have hh := AncientMild.fixed_of_fixed_source T hTc hcircle D hD
      ((FlatSymmetry.rotate R).restrictScalars ℝ) hc f
      (fun τ => by ext y; exact hf τ R y) τ
    exact congrArg (fun d : C₀(V,ℂ) => d x) hh
  · intro f hf τ x
    let A := (starL' ℝ : C₀(V,ℂ) ≃L[ℝ] C₀(V,ℂ)).toContinuousLinearMap
    have hc (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (v : C₀(V,ℂ)) : A (T t v)=T t (A v) := by
      change star ((Real.exp (γ*t):ℂ) • S t v)=(Real.exp (γ*t):ℂ) • S t (star v)
      rw [star_smul,Complex.star_def,Complex.conj_ofReal,actual_star h S hE t ht]
    have hh := AncientMild.fixed_of_fixed_source T hTc hcircle D hD A hc f
      (fun τ => by ext y; exact hf τ y) τ
    exact congrArg (fun d : C₀(V,ℂ) => d x) hh
end FlatSimilarity

end

end OAI
