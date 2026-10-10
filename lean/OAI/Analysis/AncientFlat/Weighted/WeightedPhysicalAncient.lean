import OAI.Analysis.AncientFlat.Evolution.PhysicalProfileBridge

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology ENNReal
namespace FlatSimilarity
open FlatWeighted ParabolicAnnular
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
local instance : SeminormedAddCommGroup C₀(V,ℂ) := inferInstance
local instance : SeminormedAddCommGroup (ℝ →ᵇ C₀(V,ℂ)) := inferInstance
theorem exists_weighted_physical_inverse {m : ℕ} (e : OrthonormalBasis (Fin m) ℝ V)
    (G H : ℝ → ℝ) (c κ : ℝ) (hc : 0<c) (hκ : 0<κ)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hH : ContDiffOn ℝ ∞ H (Ici 0))
    (hH0 : H 0=c) (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    (hpos : ∀ y : ℝ, 0≤y → κ≤G y) :
    ∃ γ : ℝ, 0<γ ∧ γ<1/2 ∧
    ∃ D : (ℝ →ᵇ C₀(V,ℂ)) →L[ℂ] (ℝ →ᵇ C₀(V,ℂ)),
      (∀ α a : ℝ, 0<α → α<1 → 0<a → a≤1/16 →
        ∃ C : ℝ, 0<C ∧ ∀ M : ℝ, 0≤M → ∀ f : ℝ →ᵇ C₀(V,ℂ),
          ‖f‖≤M →
          (∀ s : ℝ, ∃ K : ℝ, 0≤K ∧ ∀ t ∈ Icc s (s+1), ∀ x y,
            ‖f t x-f t y‖≤K*‖x-y‖^α) →
          YBound α (-2+4*γ) a M (fun p : V × ℝ => physicalForce γ f p.2 p.1) →
          (∀ t : ℝ, ContDiff ℝ 4 (fun x => physical γ (D f) t x)) ∧
          (∀ t : ℝ, t<0 → ∀ x : V,
            HasDerivAt (fun r => physical γ (D f) r x) (physicalTime γ (profileAf G) (profileBf G) f (D f) t x) t) ∧
          xNorm e α (-2+4*γ) a (fun t x => physical γ (D f) t x)
            (physicalTime γ (profileAf G) (profileBf G) f (D f))≤ENNReal.ofReal (C*M)) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), (∀ τ, Radial (f τ : V → ℂ)) →
        ∀ t, Radial (physical γ (D f) t : V → ℂ)) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), (∀ τ, RealValued (f τ : V → ℂ)) →
        ∀ t, RealValued (physical γ (D f) t : V → ℂ)) := by
  obtain ⟨γ,hγ,hγ1,D,hD,hgrow,hRad,hReal⟩ := exists_finite_physical_inverse c
    (profileAf (V := V) G) (profileBf G) (profile_symbols G H c κ hc hκ hG hH hH0 hmatch hpos)
    (profile_radial G).1 (profile_radial G).2
  refine ⟨γ,hγ,hγ1,D,?_,hRad,hReal⟩
  intro α a hα hα1 ha ha1
  obtain ⟨C,hC,hEst⟩ := weighted_estimate (V := V) G H c κ α (2*γ) a hc hκ hα hα1
    (by positivity) (by linarith) ha ha1 hG hH hH0 hmatch hpos
  let K := 2*((∑ j : Fin 5, (m:ℝ)^j.val)+1)
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K*C*(1+‖D‖),by positivity,?_⟩
  intro M hM f hfn hf hY
  obtain ⟨hs,hd,hj⟩ := hD α a M hα hα1 ha hM f hf hY
  refine ⟨hs,hd,?_⟩
  have hY' : YBound α (-2+2*(2*γ)) a M (fun p : V × ℝ => physicalForce γ f p.2 p.1) := by
    convert hY using 1; ring
  have hg : ∀ p : V × ℝ, p.2<0 → ‖physical γ (D f) p.2 p.1‖≤(‖D‖*M)*(-p.2)^((-1+2*γ)/2) := by
    intro p hp
    have he : Real.exp ((1/2-γ)*similarityTime p.2)=(-p.2)^((-1+2*γ)/2) := by
      rw [exp_similarity p.2 (1/2-γ) hp]
      congr 1
      ring
    have hg0 := hgrow f p.2 p.1
    rw [he] at hg0
    exact hg0.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfn (norm_nonneg D)) (Real.rpow_nonneg (neg_pos.mpr hp).le _))
  have heq : ∀ p : V × ℝ, p.2<0 →
      physicalTime γ (profileAf G) (profileBf G) f (D f) p.2 p.1+
      (profilePrincipal G p:ℂ)*Δ (Δ (fun x => physical γ (D f) p.2 x)) p.1+
      (profilePotential G p:ℂ)*physical γ (D f) p.2 p.1=physicalForce γ f p.2 p.1 := by
    intro p hp
    rw [physicalTime,profile_physical_principal G hp,profile_physical_potential G hp]
    ring
  have hB := hEst (fun t x => physical γ (D f) t x)
    (physicalTime γ (profileAf G) (profileBf G) f (D f)) _ M (‖D‖*M) hM
    (by positivity) hs (fun p hp => hd p.2 hp p.1) hj hY' hg heq
  have hN := xBound_xNorm e (by positivity : 0≤C*(M+‖D‖*M)) hB
  convert hN using 1
  · congr 1; ring
  · dsimp [K]
    congr 1
    ring
end FlatSimilarity

end

end OAI
