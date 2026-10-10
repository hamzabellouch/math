import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Estimates.ResidualSuccessiveNearFar
import OAI.MeasureTheory.FalconerCompletion.Recursion.PolicyDescriptorAnchorGtStart

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff ENNReal Topology Classical
variable {n : ℕ}

theorem actual_residual_full_child_near_farND
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4)
    (hΨpos : ∀ t, 0≤Ψ t)
    {sig : ℝ} (hsig : 0<sig) (hsig₁ : sig≤1)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B)
    {Jmask : ℕ} (hJmask : 0<Jmask) (Cq : ℝ) (hCq : 0≤Cq)
    (err T D : ℝ) (ell : ℕ) (hK : 32*(n+2:ℝ)≤(2:ℝ)^ell) :
    ∃ J : ℕ, ∃ Dnear H : ℝ, 1≤Dnear ∧ 0≤H ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (A : ℕ → ℝ) (q a₀ t₀ a h tend : ℕ), 0<q → t₀≤N → a₀≤a → tend≤t₀ →
      ∀ (words₁ words₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
        (X Y : Fin (n+1) → ℤ) (v ma : ℝ) (mb : ℕ → ℝ),
      Measurable f → Measurable g → (∀ x, ‖f x‖≤1) → (∀ x, ‖g x‖≤1) →
      (∀ b∈policyDescriptorList A N q a₀ t₀, words₁ b∈W) →
      (∀ b∈policyDescriptorList A N q a₀ t₀, words₂ b∈W) →
      (∑ b∈policyDescriptorList A N q a₀ t₀, (words₁ b).length≤total) →
      (∑ b∈policyDescriptorList A N q a₀ t₀, (words₂ b).length≤total) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j P.1 w‖≤Cq) →
      ∀ (hX : ρ (Attempt4FullFar.ambientGridCell a X)≠0)
        (hY : κ (Attempt4FullFar.ambientGridCell a Y)≠0) (hah : a<h), v-a≤N →
      ((h+ell+2:ℕ):ℝ)≤v-2*(max ((unreachedDescriptorList A N q a₀ t₀ a).sup descriptorLength)
        (Nat.ceil (10*sig*N)):ℕ)+D →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ z∈occupiedDescendantsND ρ a k X,
        ((2:ℝ)^N)^(-mb k-err)≤(ρ (Attempt4FullFar.ambientGridCell k z)).toReal) →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ z∈occupiedDescendantsND κ a k Y,
        ((2:ℝ)^N)^(-mb k-err)≤(κ (Attempt4FullFar.ambientGridCell k z)).toReal) →
      (ρ (Attempt4FullFar.ambientGridCell a X)).toReal≤((2:ℝ)^N)^(-ma+err) →
      (κ (Attempt4FullFar.ambientGridCell a Y)).toReal≤((2:ℝ)^N)^(-ma+err) →
      let b := fun x => (actualResidualSourceSymbol A N q a₀ t₀ a words₁ ρ m sig C Jmask i f Q x).1
      let c := fun x => (actualResidualSourceSymbol A N q a₀ t₀ a words₂ κ m sig C Jmask i g P x).1
      let U := fun k => actualPairAmbientGood A N q k tend ρ m sig C Jmask (i+1)
      let V := fun k => actualPairAmbientGood A N q k tend κ m sig C Jmask (i+1)
      let Aocc := occupiedDescendantsND ρ a h X
      let Docc := occupiedDescendantsND κ a h Y
      let hAD := (original_occupied_nonemptyND ρ hah.le X hX).product
        (original_occupied_nonemptyND κ hah.le Y hY)
      let μ := canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))
      Attempt4Near.sourceAngularHND (n+1) μ a v Ψ
        (originalCellTransformND ρ a (((2:ℝ)^N)^(-ma)) b X)
        (originalCellTransformND κ a (((2:ℝ)^N)^(-ma)) c Y) ≤
      (20*(n+2:ℝ)+5)^(2*(n+1))*
        ((2:ℝ)^N)^(-2*((mb h-(n+1:ℝ)*(h:ℝ)/(2*N))-(ma-(n+1:ℝ)*(a:ℝ)/(2*N)))+4*err)*
        (Dnear^(4*total)*Attempt4Near.graphChildMaxND (n+1) μ h v Ψ Aocc Docc hAD
          (originalCellTransformND ρ h (((2:ℝ)^N)^(-mb h))
            (fun x => (actualResidualSourceSymbol A N q a₀ t₀ h words₁ ρ m sig C Jmask i f Q x).1))
          (originalCellTransformND κ h (((2:ℝ)^N)^(-mb h))
            (fun x => (actualResidualSourceSymbol A N q a₀ t₀ h words₂ κ m sig C Jmask i g P x).1))) +
      H*(∑ k∈Finset.Icc (a+1) (h+ell+2),
        ((2:ℝ)^N)^(-2*((mb k-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k (occupiedFarPairsND ρ a k ((2:ℝ)^ell) X)
            (occupiedFarPairsND κ a k ((2:ℝ)^ell) Y) v (((2:ℝ)^N)^(-mb k)) (U k) (V k)).toReal)+
        ((2:ℝ)^N)^(-T) := by
  obtain ⟨J,Dnear,H,hDnear,hH,hnf⟩ := actual_residual_successive_near_farND hΨ hs hΨpos hsig hsig₁ W B total hW hJmask Cq hCq err T D ell hK
  refine ⟨J,Dnear,H,hDnear,hH,?_⟩
  filter_upwards [hnf] with N hnf
  intro ρ κ hρ hκ A q a₀ t₀ a h tend hq ht₀ ha htend words₁ words₂ m C i f g Q P X Y v ma mb
    hfm hgm hfn hgn hw₁ hw₂ htotal₁ htotal₂ hQ hP hX hY hah hav hdepth hl₁ hl₂ hu₁ hu₂
  have hn := hnf ρ κ A q a₀ t₀ a h hq ht₀ words₁ words₂ m C i f g Q P X Y v ma mb
    hfm hgm hfn hgn hw₁ hw₂ htotal₁ htotal₂ hQ hP hX hY hah hav hdepth hl₁ hl₂ hu₁ hu₂
  let old := fun k => (farChildMaximumND ρ κ k
    (occupiedFarPairsND ρ a k ((2:ℝ)^ell) X) (occupiedFarPairsND κ a k ((2:ℝ)^ell) Y)
    v (((2:ℝ)^N)^(-mb k))
    (actualResidualPairAmbientGood A N q a₀ t₀ a ρ m sig C Jmask (i+1))
    (actualResidualPairAmbientGood A N q a₀ t₀ a κ m sig C Jmask (i+1))).toReal
  let new := fun k => (farChildMaximumND ρ κ k
    (occupiedFarPairsND ρ a k ((2:ℝ)^ell) X) (occupiedFarPairsND κ a k ((2:ℝ)^ell) Y)
    v (((2:ℝ)^N)^(-mb k))
    (actualPairAmbientGood A N q k tend ρ m sig C Jmask (i+1))
    (actualPairAmbientGood A N q k tend κ m sig C Jmask (i+1))).toReal
  have hc (k : ℕ) (hk : k∈Finset.Icc (a+1) (h+ell+2)) : old k≤new k := by
    have hak : a<k := (Finset.mem_Icc.mp hk).1
    exact ENNReal.toReal_mono (farChildMaximumND_ne_top ρ κ k _ _ _ _ _ _)
      (actualResidual_farChildMaximum_le ρ κ A hq ha hak htend m sig C Jmask (i+1) _ _ _ _)
  have hsum : (∑ k∈Finset.Icc (a+1) (h+ell+2),
      ((2:ℝ)^N)^(-2*((mb k-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*old k) ≤
    ∑ k∈Finset.Icc (a+1) (h+ell+2),
      ((2:ℝ)^N)^(-2*((mb k-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*new k := by
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (hc k hk) (by positivity)
  exact hn.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hH)) le_rfl)

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
