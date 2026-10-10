import OAI.MeasureTheory.Falconer.Graphs.PrefixGraphSpecialization
import OAI.MeasureTheory.Falconer.Recursion.PrefixChildDropping
import OAI.MeasureTheory.Falconer.Shells.HighShellSupremum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace PositiveDistanceData

theorem inversePhasedHF_policyParent (d : PositiveDistanceData) (v : ℝ) (Ψ : ℝ → ℝ)
    (k : PairMaskIndex → ℕ) (ξ : Plane) :
    d.inversePhasedHF v Ψ k ξ =
      d.policyParentEnergy (fun l b => k (b,l))
        (fun _ => spatialFourierPhase ((2:ℝ)^(-(d.a:ℝ))) ξ) v Ψ := by
  unfold inversePhasedHF policyParentEnergy inverseEndpointSymbol
  congr 1 <;> funext x u <;> rw [spatialPhased_inherited] <;> simp only [mul_one]

theorem uniform_prefix_inverse_supremum {sig kap lam T eta : ℝ}
    (hsig : 0 < sig) (hgap : 10*sig < kap) (hlam : 0 ≤ lam)
    (hT : 0 ≤ T) (heta : 0 < eta) (n : ℕ) {J : ℕ} (hJ : 0 < J)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData,
    d.sig = sig → d.lam = lam → d.J = J → N₀ ≤ d.N → d.Q.side = 1 →
    ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    0 < d.q → kap*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N → d.i < d.J →
    d.X.length = d.a → d.Y.length = d.a →
    100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
    dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
    let A := fun m : ℕ => d.mass m-(m:ℝ)/d.N
    let p := policyDepth A d.N d.q d.a d.t
    2*p ≤ d.a+d.t →
    ∀ v ∈ Finset.Ioc d.a d.t, (d.t:ℝ)-sig*d.N < (v:ℝ) →
    d.inverseShellSupremum n v Ψ ≤
      (symbolDerivativeConstant (2*n)^(2*n))^4 *
      ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eta) *
        d.prefixSuccessorSupremum (2*n) p Ψ + ((2:ℝ)^d.N)^(-T) := by
  classical
  obtain ⟨N₀,hgraph⟩ := uniform_prefix_graph hsig hgap hlam hT heta (2*n) hJ hΨ hpos hs
  refine ⟨N₀,?_⟩
  intro d hdSig hdLam hdJ hN hQ B δ hprof hq hblock hw ht hi hX hY hlo hsep A p hpref v hv hvhigh
  let := hprof.probability
  have hQpos : 0 < d.Q.side := by rw [hQ]; norm_num
  have hgeom := prefix_policy_geometry A hq ht hw hpref
  obtain ⟨W,hW,hWb⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hsup0 := (d.prefixSuccessorSupremum_majorizes hQpos (2*n) p Ψ hW
    (fun x => (le_abs_self _).trans (hWb x)) hsupport).1
  apply csSup_le (show (d.inverseShellEnergies n v Ψ).Nonempty from ⟨0,Or.inl rfl⟩)
  intro E hE
  rcases hE with rfl | ⟨j,hj,b,hb,ξ,rfl⟩
  · positivity
  · have hbudget (l : Fin 2) : ∑ c ∈ d.inverseDescriptorList, b.2 (c,l) ≤ 2*n :=
      (pair_assignment_endpoint_budget _ _ (2*j) (inverseLeibnizTerms_budget j _ hb) l).trans
        (by have := Finset.mem_range.mp hj; omega)
    let k := fun (l : Fin 2) (c : PolicyDescriptor) => b.2 (c,l)
    let h := fun _ : Fin 2 => spatialFourierPhase ((2:ℝ)^(-(d.a:ℝ))) ξ
    have hm (l : Fin 2) : Measurable (h l) := by
      dsimp [h]
      fun_prop
    have hnorm (l : Fin 2) (x : Plane) : ‖h l x‖ ≤ 1 := (spatialFourierPhase_norm _ _ _).le
    have hG := hgraph d hdSig hdLam hdJ hN hQ B δ hprof hq hblock hw ht hi hX hY hlo hsep
      hpref v hvhigh.le (by exact_mod_cast (Finset.mem_Ioc.mp hv).2) k hbudget h hm hnorm
    have hD := d.prefix_child_maximum_le hQpos (2*n) p hgeom.1.le hX hY v hv
      (by simpa only [hdSig] using hvhigh) k hbudget h hm hnorm hΨ hpos hs
    rw [inversePhasedHF_policyParent]
    apply hG.2.trans
    have hD' := mul_le_mul_of_nonneg_left hD
      (show 0 ≤ ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eta) by positivity)
    nlinarith

end PositiveDistanceData

end PlanarFalconer

end OAI
