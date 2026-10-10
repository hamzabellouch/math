import OAI.MeasureTheory.Falconer.Recursion.PrefixPolicyGeometry
import OAI.MeasureTheory.Falconer.Graphs.PrefixSuccessorEnergy
import OAI.MeasureTheory.Falconer.Estimates.ActualDistanceEquation12

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PositiveDistanceData

noncomputable def policyParentEnergy (d : PositiveDistanceData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ)
    (v : ℝ) (Ψ : ℝ → ℝ) : ℝ≥0∞ :=
  sourceParentHF d.a v Ψ (d.Q.descendant d.X) (d.Q.descendant d.Y) d.ρ d.ρ
    d.levelMass d.levelMass
    (inheritedCircleSymbol d.inverseDescriptorList id (k 0) d.Q d.ρ d.mass
      d.N d.lam d.sig d.J d.i (h 0))
    (inheritedCircleSymbol d.inverseDescriptorList id (k 1) d.Q d.ρ d.mass
      d.N d.lam d.sig d.J d.i (h 1))

theorem uniform_prefix_graph {sig kap lam T eta : ℝ}
    (hsig : 0 < sig) (hgap : 10*sig < kap) (hlam : 0 ≤ lam)
    (hT : 0 ≤ T) (heta : 0 < eta) (K : ℕ) {J : ℕ} (hJ : 0 < J)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData,
    d.sig = sig → d.lam = lam → d.J = J → N₀ ≤ d.N → d.Q.side = 1 →
    ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    0 < d.q → kap*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N → d.i < d.J →
    d.X.length = d.a → d.Y.length = d.a →
    100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
    dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
    let A := fun n : ℕ => d.mass n-(n:ℝ)/d.N
    let p := policyDepth A d.N d.q d.a d.t
    2*p ≤ d.a+d.t →
    ∀ v : ℝ, (d.t:ℝ)-sig*d.N ≤ v → v ≤ d.t →
    ∀ k : Fin 2 → PolicyDescriptor → ℕ,
      (∀ l, ∑ b ∈ d.inverseDescriptorList, k l b ≤ K) →
    ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    d.policyParentEnergy k h v Ψ ≠ ⊤ ∧
    (d.policyParentEnergy k h v Ψ).toReal ≤
      ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eta) *
      finiteEnergyMaximum (sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a))
        (d.policyCellEnergy d.inverseDescriptorList k h p v Ψ) + ((2:ℝ)^d.N)^(-T) := by
  classical
  obtain ⟨N₀,h₀⟩ := uniform_actual_distance_equation12 hsig hgap (by norm_num : (0:ℝ)<1)
    (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ 2*Real.pi) K lam T hlam hT heta hJ hΨ hpos hs
  refine ⟨N₀,?_⟩
  intro d hdSig hdLam hdJ hN hQ B δ hprof hq hblock hw ht hi hX hY hlo hsep A p hpref v hv hvt k hk h hh hhb
  have hg := prefix_policy_geometry A hq ht hw hpref
  have hsc := prefix_policy_scales A hsig hgap hq hblock ht hw hpref hv hvt
  have he : d.a+(p-d.a) = p := hsc.1
  have hprof' : RegularizedProfileData d.Q d.ρ d.N B δ lam d.mass := by
    simpa only [hdLam] using hprof
  have hcard (_index : Fin 2) : d.inverseDescriptorList.card ≤ (d.N+1)^3+1 :=
    (policyDescriptorList_card A hq).trans (Nat.le_succ _)
  have hL (_index : Fin 2) (b : PolicyDescriptor) (hb : b ∈ d.inverseDescriptorList) :
      descriptorLength b ≤ (d.t-d.a)/2 := policyDescriptor_length_le_half A hq hb
  have hdistinguished : PolicyDescriptor.parallel d.a (d.a+(p-d.a)) ∈ d.inverseDescriptorList := by
    rw [he]
    exact hg.2.2.2.2
  have ht' := h₀ d.N hN (fun _ : Fin 2 => d.inverseDescriptorList) (fun _ => id) k hcard hk
    ((d.t-d.a)/2) hL (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) (fun _ => d.mass)
    B δ (fun _ => hprof') d.i h (by omega) hh hhb d.a (p-d.a) v
    hsc.2.1 hsc.2.2.1 hsc.2.2.2.1 hsc.2.2.2.2.1 hsc.2.2.2.2.2.1 hsc.2.2.2.2.2.2
    (fun _ => .parallel d.a (d.a+(p-d.a))) (fun _ => hdistinguished) (fun _ => rfl)
    d.X d.Y hX hY hlo hsep
  dsimp only at ht'
  rw [← hdLam,← hdSig,← hdJ] at ht'
  have heR : (d.a:ℝ)+((p-d.a:ℕ):ℝ) = (p:ℝ) := by exact_mod_cast he
  simp only [he,heR,min_self] at ht'
  have hexp : -(d.mass p-(p:ℝ)/d.N-(d.mass d.a-(d.a:ℝ)/d.N))
      -(d.mass p-(p:ℝ)/d.N-(d.mass d.a-(d.a:ℝ)/d.N))+
      height A d.a p+4000*(d.lam+d.sig)+eta =
      -2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eta := by
    dsimp [A]
    rw [hdLam,hdSig]
    ring
  rw [hexp] at ht'
  exact ht'

end PositiveDistanceData

end PlanarFalconer

end OAI
