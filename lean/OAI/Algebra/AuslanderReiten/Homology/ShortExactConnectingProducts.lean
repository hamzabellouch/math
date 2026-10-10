import OAI.Algebra.AuslanderReiten.Homology.ShortExactConnecting
import OAI.Algebra.AuslanderReiten.Cocycles.RawCocycleProducts

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Injective R R]
variable {K F G H : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (p : CochainCokernel G →ₗ[R] CochainCokernel H)
variable (he : Function.Exact (cochainCokernelMap φ) p)
variable (hK : TotallyAcyclicCochain K) (hF : TotallyAcyclicCochain F)
variable (hG : TotallyAcyclicCochain G) (hH : TotallyAcyclicCochain H)
variable (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p)

theorem shortExactConnecting_product_source (n : ℤ) (u : CohomologyClass K H n)
    (s : RawCokernelAt K n →ₗ[R] CochainCokernel H)
    (hs : rawSourceAtStableEquiv (k := k) K H n hK.to_chain
      hH.to_chain.toExactProjectiveComplex u = StableHom.classOf R _ _ s)
    (A : K.X (-n) →ₗ[R] CochainCokernel G)
    (t : RawCokernelAt K (n+1) →ₗ[R] CochainCokernel F)
    (hA : p.comp A = s.comp (LinearMap.range (K.d (-(n+1)) (-n)).hom).mkQ)
    (ht : (cochainCokernelMap φ).comp t = A.comp (rawCokernelAtInclusion K n)) :
    rawSourceAtStableEquiv (k := k) K F (n+1) hK.to_chain
      hF.to_chain.toExactProjectiveComplex
      (fullHomProduct u ((fullHomShiftedHomotopyEquiv k H F 1).symm
        (shortExactTriangle φ p he hF hG hH hi hp).mor₃)) = StableHom.classOf R _ _ t := by
  let := hH.projective 0
  obtain ⟨A₀, hA₀⟩ := Module.projective_lifting_property p
    (LinearMap.range (H.d (-1) 0).hom).mkQ hp
  have hzero : p.comp (A₀.comp (rawSyzygyInclusion H)) = 0 := by
    rw [← LinearMap.comp_assoc, hA₀, rawSyzygyInclusion_cover]
  let w := (A₀.comp (rawSyzygyInclusion H)).codRestrict
    (LinearMap.range (cochainCokernelMap φ)) (fun z => by
      rw [(LinearMap.exact_iff.mp he).symm]
      exact LinearMap.congr_fun hzero z)
  let e := LinearEquiv.ofInjective (cochainCokernelMap φ) hi
  let t₀ := e.symm.toLinearMap.comp w
  have ht₀ : (cochainCokernelMap φ).comp t₀ = A₀.comp (rawSyzygyInclusion H) := by
    apply LinearMap.ext
    intro z
    exact congrArg Subtype.val (e.apply_symm_apply (w z))
  let d := (fullHomShiftedHomotopyEquiv k H F 1).symm
    (shortExactTriangle φ p he hF hG hH hi hp).mor₃
  obtain ⟨y, hy⟩ := CohomologyClass.mk_surjective d
  have hySource : StableHom.classOf R _ _ (rawSourceAt y) =
      StableHom.classOf R _ _ t₀ := by
    have hh := shortExactConnecting_source_equiv (k := k) φ p he hF hG hH hi hp A₀ t₀ hA₀ ht₀
    change rawSourceStableEquiv (k := k) H F _ _ d = _ at hh
    rw [← hy, rawSourceStableEquiv_mk] at hh
    exact hh
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective u
  rw [rawSourceAtStableEquiv_mk] at hs
  change rawSourceAtStableEquiv (k := k) K F (n+1) _ _
    (fullHomProduct (CohomologyClass.mk x) d) = _
  rw [← hy, fullHomProduct_mk, rawSourceAtStableEquiv_mk, rawSourceAt_product (k := k)]
  rw [← StableHom.comp_classOf, hySource]
  erw [StableHom.comp_classOf]
  let X₀ := (x.val.v (-n) 0 (by omega)).hom
  let x₁ := rawCokernelAtMap (k := k) x (n+1) 1 rfl
  have hfirst : p.comp (A₀.comp X₀) =
      (rawSourceAt x).comp (LinearMap.range (K.d (-(n+1)) (-n)).hom).mkQ := by
    rw [← LinearMap.comp_assoc, hA₀]
    apply LinearMap.ext
    intro z
    exact (rawSourceAt_mk (k := k) x z).symm
  have hsecond : (cochainCokernelMap φ).comp (t₀.comp x₁) =
      (A₀.comp X₀).comp (rawCokernelAtInclusion K n) := by
    rw [← LinearMap.comp_assoc, ht₀, LinearMap.comp_assoc]
    have hx := rawCokernelAtMap_cover (k := k) x n 0 (add_zero n).symm
    change (rawSyzygyInclusion H).comp x₁ = X₀.comp (rawCokernelAtInclusion K n) at hx
    rw [hx, LinearMap.comp_assoc]
  let := hK.finite (-n)
  let := hK.projective (-n)
  exact stable_connecting_congr (rawCokernelAtInclusion K n)
    (LinearMap.range (K.d (-(n+1)) (-n)).hom).mkQ (rawCokernelAtInclusion_cover K n)
    (cochainCokernelMap φ) p hi hp (LinearMap.exact_iff.mp he).symm
    (rawSourceAt x) s (A₀.comp X₀) A (t₀.comp x₁) t hfirst hA hsecond ht hs

end ArExplicit

end

end OAI
