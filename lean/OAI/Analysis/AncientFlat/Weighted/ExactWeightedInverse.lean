import OAI.Analysis.AncientFlat.Weighted.WeightedPhysicalAncient
import OAI.Analysis.AncientFlat.Weighted.ExactSourceSpace
import OAI.Analysis.AncientFlat.Weighted.ExactNormCongr

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

def physicalLinear (γ : ℝ) : (ℝ →ᵇ C₀(V,ℂ)) →ₗ[ℝ] (V × ℝ → ℂ) where
  toFun v p := physical γ v p.2 p.1
  map_add' v w := by
    funext p
    simp only [physical_apply,BoundedContinuousFunction.add_apply,ZeroAtInftyContinuousMap.add_apply,
      Pi.add_apply,mul_add]
  map_smul' c v := by
    funext p
    simp only [physical_apply,BoundedContinuousFunction.smul_apply,ZeroAtInftyContinuousMap.smul_apply,
      Pi.smul_apply,Complex.real_smul,RingHom.id_apply]
    ring

def profileTime (G : ℝ → ℝ) (f u : V × ℝ → ℂ) (t : ℝ) (x : V) : ℂ :=
  f (x,t)-(profilePrincipal G (x,t):ℂ)*Δ (Δ (fun z => u (z,t))) x-
    (profilePotential G (x,t):ℂ)*u (x,t)

theorem exact_weighted_inverse {m : ℕ} (e : OrthonormalBasis (Fin m) ℝ V)
    (G H : ℝ → ℝ) (c κ : ℝ) (hc : 0<c) (hκ : 0<κ)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hH : ContDiffOn ℝ ∞ H (Ici 0))
    (hH0 : H 0=c) (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    (hpos : ∀ y : ℝ, 0≤y → κ≤G y) :
    ∃ γ : ℝ, 0<γ ∧ γ<1/2 ∧ ∀ α a : ℝ, 0<α → α<1 → 0<a → a≤1/16 →
      ∃ C : ℝ, 0<C ∧ ∃ D : sourceSpace (V := V) α (-2+4*γ) a →ₗ[ℝ] (V × ℝ → ℂ),
        ∀ f : sourceSpace (V := V) α (-2+4*γ) a,
          (∀ t : ℝ, ContDiff ℝ 4 (fun x => D f (x,t))) ∧
          (∀ t : ℝ, t<0 → ∀ x : V,
            HasDerivAt (fun r => D f (x,r)) (profileTime G f.val (D f) t x) t) ∧
          xNorm e α (-2+4*γ) a (fun t x => D f (x,t)) (profileTime G f.val (D f))≤
            ENNReal.ofReal (C*sourceNorm α (-2+4*γ) a f) ∧
          (∀ t, Radial (fun x => D f (x,t))) ∧ (∀ t, RealValued (fun x => D f (x,t))) := by
  obtain ⟨γ,hγ,hγ1,D,hD,hRad,hReal⟩ := exists_weighted_physical_inverse e G H c κ hc hκ hG hH hH0 hmatch hpos
  refine ⟨γ,hγ,hγ1,?_⟩
  intro α a hα hα1 ha ha1
  obtain ⟨C,hC,hDC⟩ := hD α a hα hα1 ha ha1
  let L := sourceLiftLinear (V := V) γ α a hγ1 hα ha
  let P := (physicalLinear γ).comp ((D.restrictScalars ℝ).toLinearMap.comp L)
  refine ⟨C,hC,P,?_⟩
  intro f
  let M := sourceNorm α (-2+4*γ) a f
  have hM : 0≤M := sourceNorm_nonneg _ _ _ f
  have hlf : ∀ τ z, L f τ z=FlatWeighted.normalizedSource γ f.val τ z := fun τ z => sourceLift_apply γ α a hγ1 hα ha f τ z
  have he (t : ℝ) (ht : t<0) (x : V) : physicalForce γ (L f) t x=f.val (x,t) :=
    force_source_identity γ f.val (L f) hlf ht x
  have hY : YBound α (-2+4*γ) a M (fun p : V × ℝ => physicalForce γ (L f) p.2 p.1) :=
    (finite_yBound f.property.1).congr (fun p hp => (he p.2 hp p.1).symm)
  have hh : ∀ s : ℝ, ∃ K : ℝ, 0≤K ∧ ∀ t ∈ Icc s (s+1), ∀ x y,
      ‖L f t x-L f t y‖≤K*‖x-y‖^α := by
    obtain ⟨K,hK,hKL⟩ := source_lift (V := V) γ α a hγ hγ1 hα hα1 ha (by linarith)
    obtain ⟨j,hj,hjn,hjH⟩ := hKL M hM f.val (finite_yBound f.property.1)
    have hjL : j=L f := by ext τ z; rw [hj,hlf]
    subst j
    exact fun s => ⟨K*M,by positivity,fun t ht x y => hjH t x y⟩
  obtain ⟨hs,hd,hn⟩ := hDC M hM (L f) (sourceLift_norm γ α a hγ1 hα ha f) hh hY
  have htEq (t : ℝ) (ht : t<0) (x : V) :
      physicalTime γ (profileAf G) (profileBf G) (L f) (D (L f)) t x=profileTime G f.val (P f) t x := by
    rw [physicalTime,profile_physical_principal G ht,profile_physical_potential G ht,he t ht x]
    rfl
  refine ⟨hs,fun t ht x => (htEq t ht x) ▸ hd t ht x,?_,?_,?_⟩
  · rw [←xNorm_time_congr e α (-2+4*γ) a _ _ _ htEq]
    exact hn
  · apply hRad
    intro τ R x
    simp only [hlf,FlatWeighted.normalizedSource,←R.map_smul]
    congr 1
    exact f.property.2.2.1 _ (by simpa using neg_neg_of_pos (Real.exp_pos (-τ))) R _
  · apply hReal
    intro τ x
    simp only [hlf,FlatWeighted.normalizedSource,star_smul,star_trivial]
    rw [f.property.2.2.2 _ (by simpa using neg_neg_of_pos (Real.exp_pos (-τ)))]
end FlatSimilarity

end

end OAI
