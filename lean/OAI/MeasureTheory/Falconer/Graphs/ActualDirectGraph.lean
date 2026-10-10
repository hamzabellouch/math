import OAI.MeasureTheory.Falconer.Recursion.DirectPolicyWitness
import OAI.MeasureTheory.Falconer.Angular.AngularStateDropping
import OAI.MeasureTheory.Falconer.Estimates.ActualProductEquation13

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff
namespace AngularStateData

theorem uniform_direct_graph {lam sig eps : ℝ} (hlam : 0 ≤ lam) (hsig : 0 < sig)
    (heps : 0 < eps) (T : ℝ) (K J : ℕ) (hJ : 0 < J)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : AngularStateData,
      d.lam = lam → d.sig = sig → d.J = J → N₀ ≤ d.N →
      d.Q.side = 1 → 0 < d.q → d.v ≤ d.N → d.i < d.J →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      ∀ e : PolicyDescriptor, DirectPolicyWitness d.profile d.N d.q d.a₀ d.t₀ d.a d.v d.sig e →
      let p := descriptorAnchor e
      d.energy k h Ψ ≠ ⊤ ∧ (∀ row, d.childEnergy k h p Ψ row ≠ ⊤) ∧
      (∀ l, ∑ b ∈ d.retainedList p, k l b ≤ K) ∧
      (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^
        (-2*(d.profile p-d.profile d.a)+height d.profile d.a p+4000*(lam+sig)+eps) *
          d.childMaximum k h p Ψ + ((2:ℝ)^d.N)^(-T) := by
  obtain ⟨N₁,h₁⟩ := uniform_actual_product_equation13 hsig Real.pi_pos
    (by linarith [Real.pi_pos] : Real.pi ≤ 2*Real.pi)
    K lam T hlam (half_pos heps) hJ hΨ hpos hs
  obtain ⟨N₂,h₂⟩ := fixed_constant_absorbed (half_pos heps) ((symbolDerivativeConstant K^K)^4)
  refine ⟨max N₁ N₂,?_⟩
  intro d hdLam hdSig hdJ hN hQ hq hvN hi hX hY B δ hprof k hk h hh hhb e hw
  subst lam
  subst sig
  subst J
  let := hprof.probability
  have hQp : 0 < d.Q.side := by rw [hQ]; norm_num
  let p := descriptorAnchor e
  have hap : d.a ≤ p := hw.anchor_gt.le
  have hpN : p ≤ d.N := hw.anchor_lt.le.trans hvN
  have heq : d.a+(p-d.a) = p := Nat.add_sub_of_le hap
  have heqR : (d.a:ℝ)+((p-d.a:ℕ):ℝ) = (p:ℝ) := by exact_mod_cast heq
  have hcard (_l : Fin 2) : (d.retainedList d.a).card ≤ (d.N+1)^3+1 :=
    (remainingPolicyDescriptors_card d.profile hq).trans (Nat.le_succ _)
  have hL (_l : Fin 2) (b : PolicyDescriptor) (hb : b ∈ d.retainedList d.a) :
      descriptorLength (id b) ≤ descriptorLength e := by
    rw [hw.maximal]
    exact Finset.le_sup hb
  have hdepth : ((p-d.a:ℕ):ℝ) ≤ (d.v:ℝ)-((d.a:ℝ)+((p-d.a:ℕ):ℝ))+2*d.sig*d.N := by
    rw [heqR]
    exact hw.depth_scale
  have hlength : (descriptorLength e:ℝ) ≤ (d.v:ℝ)-((d.a:ℝ)+((p-d.a:ℕ):ℝ))+2*d.sig*d.N := by
    rw [heqR]
    exact hw.length_scale
  have hv : 0 ≤ (d.v:ℝ)-((d.a:ℝ)+((p-d.a:ℕ):ℝ)) := by
    rw [heqR]
    exact sub_nonneg.mpr (Nat.cast_le.mpr hw.anchor_lt.le)
  have hgap : ((max d.a (p-descriptorLength e):ℕ):ℝ)-d.a ≤ 2*d.sig*d.N := by
    have hg := hw.g_slack
    dsimp only [p] at *
    linarith [show 0 ≤ d.sig*(d.N:ℝ) by positivity]
  have hmain := h₁ d.N ((le_max_left _ _).trans hN)
    (fun _ : Fin 2 => d.retainedList d.a) (fun _ => id) k hcard hk
    (descriptorLength e) hL (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) d.mass B δ
    (fun _ => hprof) d.i h hi hh hhb d.a (p-d.a) d.v (by omega) hv hdepth hlength
    (by have htR : (d.v:ℝ) ≤ d.N := Nat.cast_le.mpr hvN; linarith [show (0:ℝ) ≤ (d.a:ℝ) from Nat.cast_nonneg _])
    (.parallel (max d.a (p-descriptorLength e)) p) hw.companion
    (max d.a (p-descriptorLength e)) (by simp only [id_eq,heq])
    (le_max_left _ _) (by rw [heq]; exact hw.g_lt.le) hgap d.X d.Y hX hY
  have hgraph : d.energy k h Ψ ≠ ⊤ ∧
      (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^
        (-2*(d.profile p-d.profile d.a)+height d.profile d.a p+4000*(d.lam+d.sig)+eps/2) *
          finiteEnergyMaximum (d.children p) (d.cellEnergy (d.retainedList d.a) k h p Ψ)
            + ((2:ℝ)^d.N)^(-T) := by
    dsimp only at hmain
    simp only [heqR,heq] at hmain
    exact hmain
  have hk' (l : Fin 2) := d.child_budget hap (k l) (hk l)
  refine ⟨hgraph.1,fun row => d.cellEnergy_finite hQp (d.retainedList p) k K hk' h hh hhb p hΨ hpos hs row,
    hk',hgraph.2.trans ?_⟩
  have hdrop := d.child_maximum_drop hQp p hap hX hY k K hk h hh hhb hΨ hpos hs
  have hconst := h₂ d.N ((le_max_right _ _).trans hN)
  let E := -2*(d.profile p-d.profile d.a)+height d.profile d.a p+4000*(d.lam+d.sig)
  have habs : ((2:ℝ)^d.N)^(E+eps/2)*(symbolDerivativeConstant K^K)^4 ≤
      ((2:ℝ)^d.N)^(E+eps) := by
    calc
      _ ≤ ((2:ℝ)^d.N)^(E+eps/2)*((2:ℝ)^d.N)^(eps/2) := by gcongr
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  calc
    _ ≤ ((2:ℝ)^d.N)^(E+eps/2)*((symbolDerivativeConstant K^K)^4*d.childMaximum k h p Ψ)
        + ((2:ℝ)^d.N)^(-T) := by gcongr
    _ = (((2:ℝ)^d.N)^(E+eps/2)*(symbolDerivativeConstant K^K)^4)*d.childMaximum k h p Ψ
        + ((2:ℝ)^d.N)^(-T) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right habs (d.childMaximum_nonneg k h p Ψ)) le_rfl

end AngularStateData

end PlanarFalconer

end OAI
